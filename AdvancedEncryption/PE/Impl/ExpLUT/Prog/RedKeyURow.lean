import PE.Impl.ExpLUT.Prog.KeyTryVM
import PE.Impl.ExpLUT.Prog.KeyGadget

/-!
# `KGsim` on the VM (package G2, item 5): one row of `M_F (0, z)` and of `(I_W ⊗ g) z`

The generic kernel of the `u` routine (`RedKeyPLAN.md`, module 3), over any `N K`: from the
gadget row `b` of `B⁽¹⁾` (register `10`, `K` words) and the queue of the digits `z` (register
`11`, the next `K` words are the row), with the ring one in register `7`,

* register `12` gets `Σ_c σ_k(b_c) z_c` appended (the row of `M_F (0, z)`, `k` the row's exponent),
* register `13` gets `Σ_j 2^j z_j` appended (the row of `(I_W ⊗ g) z`),
* register `11` drops the row.

`uRowC`, **`exec_uRowC`**, `wf_uRowC`, `uRowC_frame`; `natC_writes_eq`, `writes_false_of_frame`.
-/

set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Lattices.Algo.NegaG SigabaNeo.Tape SigabaNeo.Tape.MVM
  Cslib
open SigabaNeo.Lattices.Algo (encRM)

/-- The gadget row of `B⁽¹⁾`. -/
@[simp, vmreg] abbrev rUb : Fin 64 := 10
/-- The queue of the digits `z`. -/
@[simp, vmreg] abbrev rUz : Fin 64 := 11
/-- The rows of `M_F (0, z)`. -/
@[simp, vmreg] abbrev rUp : Fin 64 := 12
/-- The rows of `(I_W ⊗ g) z`. -/
@[simp, vmreg] abbrev rUg : Fin 64 := 13
/-- The ring one. -/
@[simp, vmreg] abbrev rUo : Fin 64 := 7

variable {N K : ℕ}

/-- `natC d u n` writes exactly `d`. -/
theorem natC_writes_eq (d u : Fin 64) (n : ℕ) (t : Fin 64) : (natC d u n).writes t = (d == t) := by
  by_cases h : t = d
  · subst h
    cases n with
    | zero => simp [natC, Code.writes]
    | succ n => rw [natC]; simp [Code.writes]
  · rw [natC_writes d u n t h]; simp [Ne.symm h]

/-- A footprint list gives the frame. -/
theorem writes_false_of_frame {c : Code} {l : List (Fin 64)} (h : ∀ r, c.writes r = true → r ∈ l)
    {r : Fin 64} (hr : r ∉ l) : c.writes r = false := by
  cases hc : c.writes r
  · rfl
  · exact absurd (h r hc) hr

/-- The gadget part: `13 := 13 ++ [Σ_j 2^j z_j]`, `11 := 11.drop K` (and `rQb := 11` first). -/
def uGadC (K : ℕ) : Code :=
  .seq (.cp rQb rUz) <| .seq (.cp rQa rUz) <| .seq (natC rQc rB1 K) <| .seq (.cp rIa rZ) <|
  .seq (gadRecC rUo) <| .seq (.cp rUz rQa) (.app rUg rIa)

/-- The public part: `12 := 12 ++ [Σ_c σ_k(b_c) z_c]` from `rQb`. -/
def uPubC (K k : ℕ) : Code :=
  .seq (.cp rQa rUb) <| .seq (natC rQc rB1 K) <| .seq (natC rQk rB1 k) <| .seq autQC <|
  .seq (natC rQc rB1 K) <| .seq (.cp rIa rZ) <| .seq ipC (.app rUp rIa)

/-- **One row.** -/
def uRowC (K k : ℕ) : Code := .seq (uGadC K) (uPubC K k)

theorem wf_uRowC (K k : ℕ) : (uRowC K k).WFc := by
  refine ⟨⟨trivial, trivial, natC_wfc _ _ _, trivial, ⟨trivial, grBody_writes_rQc, ?_⟩, trivial,
    trivial⟩, ⟨trivial, natC_wfc _ _ _, natC_wfc _ _ _, ⟨autQBody_writes_rQc, ?_⟩, natC_wfc _ _ _,
    trivial, ⟨ipBody_writes_rQc, ?_⟩, trivial⟩⟩ <;>
  simp [grBody, autQBody, ipBody, Code.WFc]

/-- **The registers one row writes.** -/
theorem uRowC_frame (K k : ℕ) : ∀ r : Fin 64, (uRowC K k).writes r = true →
    r ∈ [rQa, rQb, rQc, rQk, rIa, rQx, rQy, rUz, rUp, rUg] := by
  simp only [uRowC, uGadC, uPubC, gadRecC, grBody, autQC, autQBody, ipC, ipBody, Code.writes,
    natC_writes_eq]
  decide

theorem uGadC_frame (K : ℕ) : ∀ r : Fin 64, (uGadC K).writes r = true →
    r ∈ [rQa, rQb, rQc, rIa, rQx, rQy, rUz, rUg] := by
  simp only [uGadC, gadRecC, grBody, Code.writes, natC_writes_eq]
  decide

theorem uPubC_frame (K k : ℕ) : ∀ r : Fin 64, (uPubC K k).writes r = true →
    r ∈ [rQa, rQb, rQc, rQk, rIa, rQx, rQy, rUp] := by
  simp only [uPubC, autQC, autQBody, ipC, ipBody, Code.writes, natC_writes_eq]
  decide

/-- **The gadget part of one row.** -/
theorem exec_uGadC (hK : 0 < K) (w : St) (zr rest G : List (Rq N K)) (hz : zr.length = K)
    (h11 : w rUz = encL N K (zr ++ rest)) (h13 : w rUg = encL N K G)
    (h1 : w rB1 = [false]) (hZ : w rZ = encRM N K 0) (hO : w rUo = encRM N K 1) :
    exec N K (uGadC K) w rUz = encL N K rest ∧
    exec N K (uGadC K) w rUg = encL N K (G ++ [∑ j ∈ Finset.range K, 2 ^ j * zr.getD j 0]) ∧
    exec N K (uGadC K) w rQb = encL N K (zr ++ rest) ∧
    (∀ r : Fin 64, r ∉ [rQa, rQb, rQc, rIa, rQx, rQy, rUz, rUg] →
      exec N K (uGadC K) w r = w r) := by
  have fr : ∀ r : Fin 64, r ∉ [rQa, rQb, rQc, rIa, rQx, rQy, rUz, rUg] →
      exec N K (uGadC K) w r = w r := fun r hr =>
    exec_writes (N := N) (K := K) (uGadC K) w r (writes_false_of_frame (uGadC_frame K) hr)
  suffices h : exec N K (uGadC K) w rUz = encL N K rest ∧
      exec N K (uGadC K) w rUg = encL N K (G ++ [∑ j ∈ Finset.range K, 2 ^ j * zr.getD j 0]) ∧
      exec N K (uGadC K) w rQb = encL N K (zr ++ rest) from ⟨h.1, h.2.1, h.2.2, fr⟩
  unfold uGadC
  simp only [exec_seq]
  set s2 := exec N K (.cp rQa rUz) (exec N K (.cp rQb rUz) w) with hs2
  have f2 : ∀ r : Fin 64, r ≠ rQa → r ≠ rQb → s2 r = w r := by
    intro r ha hb; simp [hs2, Function.update_of_ne ha, Function.update_of_ne hb]
  have s2a : s2 rQa = encL N K (zr ++ rest) := by simp [hs2, h11]
  have s2b : s2 rQb = encL N K (zr ++ rest) := by simp [hs2, h11]
  have e3 := exec_natC (N := N) (K := K) rQc rB1 (by decide) K s2
    ((f2 rB1 (by decide) (by decide)).trans h1)
  rw [e3]
  set s4 := exec N K (.cp rIa rZ) (Function.update s2 rQc (List.replicate K false)) with hs4
  have f4 : ∀ r : Fin 64, r ≠ rIa → r ≠ rQc → s4 r = s2 r := by
    intro r ha hc; simp [hs4, Function.update_of_ne ha, Function.update_of_ne hc]
  obtain ⟨g1, g2⟩ := exec_gadRecC hK s4 rUo (by decide) zr rest K 0 hz
    ((f4 rQa (by decide) (by decide)).trans s2a) (by simp [hs4])
    (by simp [hs4, f2 rZ (by decide) (by decide), hZ])
    (by rw [f4 rZ (by decide) (by decide), f2 rZ (by decide) (by decide), hZ])
    (by rw [f4 rUo (by decide) (by decide), f2 rUo (by decide) (by decide), hO])
  set s5 := exec N K (gadRecC rUo) s4 with hs5
  have f5 : ∀ r : Fin 64, r ∉ [rQa, rQc, rIa, rQx, rQy] → s5 r = s4 r := fun r hr =>
    exec_writes _ _ _ (writes_false_of_frame (l := [rQa, rQc, rIa, rQx, rQy])
      (by simp only [gadRecC, grBody, Code.writes]; decide) hr)
  refine ⟨?_, ?_, ?_⟩
  · simp [g2]
  · simp only [exec_app, exec_cp, Function.update_apply, rUg, rUz, rIa, Fin.reduceEq, ↓reduceIte]
    rw [f5 13 (by decide), f4 13 (by decide) (by decide), f2 13 (by decide) (by decide), h13, g1,
      encL_append, encL_singleton, zero_add]
  · simp only [exec_app, exec_cp, Function.update_apply, rUg, rUz, rQb, Fin.reduceEq, ↓reduceIte]
    rw [f5 rQb (by decide), f4 rQb (by decide) (by decide), s2b]

/-- **The public part of one row.** -/
theorem exec_uPubC (hN : 0 < N) (hK : 0 < K) (w : St) (b zr rest P : List (Rq N K)) (k : ℕ)
    (hk : 0 < k) (hb : b.length = K) (hz : zr.length = K)
    (h10 : w rUb = encL N K b) (hB : w rQb = encL N K (zr ++ rest)) (h12 : w rUp = encL N K P)
    (h1 : w rB1 = [false]) (hZ : w rZ = encRM N K 0) :
    exec N K (uPubC K k) w rUp =
      encL N K (P ++ [(List.zipWith (· * ·) (b.map (aut N k)) zr).sum]) ∧
    (∀ r : Fin 64, r ∉ [rQa, rQb, rQc, rQk, rIa, rQx, rQy, rUp] → exec N K (uPubC K k) w r = w r) := by
  have fr : ∀ r : Fin 64, r ∉ [rQa, rQb, rQc, rQk, rIa, rQx, rQy, rUp] →
      exec N K (uPubC K k) w r = w r := fun r hr =>
    exec_writes _ _ _ (writes_false_of_frame (uPubC_frame K k) hr)
  refine ⟨?_, fr⟩
  unfold uPubC
  simp only [exec_seq]
  set s1 := exec N K (.cp rQa rUb) w with hs1
  have f1 : ∀ r : Fin 64, r ≠ rQa → s1 r = w r := fun r h => by simp [hs1, Function.update_of_ne h]
  rw [exec_natC (N := N) (K := K) rQc rB1 (by decide) K s1 ((f1 rB1 (by decide)).trans h1)]
  rw [exec_natC (N := N) (K := K) rQk rB1 (by decide) k _ (by
    rw [Function.update_of_ne (by decide), f1 rB1 (by decide), h1])]
  set s3 := Function.update (Function.update s1 rQc (List.replicate K false)) rQk
    (List.replicate k false) with hs3
  have f3 : ∀ r : Fin 64, r ≠ rQc → r ≠ rQk → s3 r = s1 r := by
    intro r hc hk'; simp [hs3, Function.update_of_ne hc, Function.update_of_ne hk']
  have a1 := exec_autQC hN hK s3 b K k hk hb
    (by rw [f3 rQa (by decide) (by decide)]; simp [hs1, h10]) (by simp [hs3])
    (by simp [hs3]) (by rw [f3 rZ (by decide) (by decide), f1 rZ (by decide), hZ])
  set s4 := exec N K autQC s3 with hs4
  have f4 : ∀ r : Fin 64, r ∉ [rQa, rQc, rQx, rQy] → s4 r = s3 r := fun r hr =>
    exec_writes _ _ _ (writes_false_of_frame (l := [rQa, rQc, rQx, rQy])
      (by simp only [autQC, autQBody, Code.writes]; decide) hr)
  rw [exec_natC (N := N) (K := K) rQc rB1 (by decide) K s4 (by
    rw [f4 rB1 (by decide), f3 rB1 (by decide) (by decide), f1 rB1 (by decide), h1])]
  set s6 := exec N K (.cp rIa rZ) (Function.update s4 rQc (List.replicate K false)) with hs6
  have f6 : ∀ r : Fin 64, r ≠ rIa → r ≠ rQc → s6 r = s4 r := by
    intro r ha hc; simp [hs6, Function.update_of_ne ha, Function.update_of_ne hc]
  have hZ6 : s6 rZ = encRM N K 0 := by
    rw [f6 rZ (by decide) (by decide), f4 rZ (by decide), f3 rZ (by decide) (by decide),
      f1 rZ (by decide), hZ]
  obtain ⟨i1, -, -⟩ := exec_ipC hK s6 (b.map (aut N k)) zr [] rest K 0 (by simp [hb]) hz
    (by rw [f6 rQa (by decide) (by decide), a1, List.append_nil])
    (by rw [f6 rQb (by decide) (by decide), f4 rQb (by decide), f3 rQb (by decide) (by decide),
      f1 rQb (by decide), hB])
    (by simp [hs6]) (by simp [hs6]; exact hZ6) hZ6
  have h12' : exec N K ipC s6 rUp = encL N K P := by
    rw [exec_writes _ _ _ (by decide), f6 rUp (by decide) (by decide), f4 rUp (by decide),
      f3 rUp (by decide) (by decide), f1 rUp (by decide), h12]
  simp only [exec_app, Function.update_self, h12', i1, zero_add, encL_append, encL_singleton]

/-- **One row**: `11` drops the row `zr`, `12` gets `Σ_c σ_k(b_c) z_c`, `13` gets `Σ_j 2^j z_j`. -/
theorem exec_uRowC (hN : 0 < N) (hK : 0 < K) (w : St) (b zr rest P G : List (Rq N K)) (k : ℕ)
    (hk : 0 < k) (hb : b.length = K) (hz : zr.length = K)
    (h10 : w rUb = encL N K b) (h11 : w rUz = encL N K (zr ++ rest))
    (h12 : w rUp = encL N K P) (h13 : w rUg = encL N K G)
    (h1 : w rB1 = [false]) (hZ : w rZ = encRM N K 0) (hO : w rUo = encRM N K 1) :
    exec N K (uRowC K k) w rUz = encL N K rest ∧
    exec N K (uRowC K k) w rUp =
      encL N K (P ++ [(List.zipWith (· * ·) (b.map (aut N k)) zr).sum]) ∧
    exec N K (uRowC K k) w rUg = encL N K (G ++ [∑ j ∈ Finset.range K, 2 ^ j * zr.getD j 0]) := by
  obtain ⟨g11, g13, gB, gf⟩ := exec_uGadC hK w zr rest G hz h11 h13 h1 hZ hO
  set v := exec N K (uGadC K) w
  have v10 : v rUb = encL N K b := (gf rUb (by decide)).trans h10
  have v12 : v rUp = encL N K P := (gf rUp (by decide)).trans h12
  have v1 : v rB1 = [false] := (gf rB1 (by decide)).trans h1
  have vZ : v rZ = encRM N K 0 := (gf rZ (by decide)).trans hZ
  obtain ⟨p12, pf⟩ := exec_uPubC hN hK v b zr rest P k hk hb hz v10 gB v12 v1 vZ
  rw [uRowC, exec_seq]
  exact ⟨(pf rUz (by decide)).trans g11, p12, (pf rUg (by decide)).trans g13⟩

end AdvancedEncryption.ExpLUT.Prog
