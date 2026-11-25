import PE.Impl.ExpLUT.Prog.RedKeySimEJ

/-!
# `KGsim` on the VM (module 6b, part 4): the paired step and evaluator (generic VM)

One step of `EvalPK` (F3's `stepK`) paired with the slab twin of `slabEvalAt`:

* the slab pre (`slabMul (A_i, C^in_i, X^{z_i}, s, Zin, Rin)` on lists of rows, `seLc`): every row
  `· G⁻¹(C^in_i)`, row `0 += pz_i · z_i + (A_i ⋆ rd_i)₀`;
* the table: F3's `j` loop paired with the slab table (`exec_seJLoop`, `seTab`).

The per-step data come from the stream `rAinS = 0`, one record per step (`seStepRec`):
`adL A^in_i ++ matL C^in_i ++ [pz_i] ++ vecL z_i ++ adL rd_i ++ [pu_i]`.

* `seSlabPre`, **`exec_seSlabPre`**; `seStepK cf`, **`exec_seStepK`**;
* `seEvalC` (`T = 16`: 15 `α`-steps, the `v`-step), **`exec_seEvalC`**: `rA = evalVM …` (F3's
  public evaluation) and `seSc = seEvalVM …` (the slab).
-/

set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)

variable {N K : ℕ}

/-! ### The slab of `Mul` -/

/-- **The slab pre of a step** (`slabMul` on lists of rows): every row `· G⁻¹(C^in)`, then
row `0 += pz · z + (A ⋆ rd)₀`. -/
def seLc (A Cin : Fin 2 → Fin 2 × Fin K → Rq N K) (pz : Rq N K) (z : Fin 2 × Fin K → Rq N K)
    (rd : DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (L : List (Fin 2 × Fin K → Rq N K)) :
    List (Fin 2 × Fin K → Rq N K) :=
  seAddAt (seAddAt (L.map fun v => seGRow v Cin) 0 (seRowSmul pz z)) 0 (mulPKm A rd 0)

theorem length_seLc (A Cin : Fin 2 → Fin 2 × Fin K → Rq N K) (pz : Rq N K)
    (z : Fin 2 × Fin K → Rq N K) (rd : DigI K → Fin 2 → Fin 2 × Fin K → Rq N K)
    (L : List (Fin 2 × Fin K → Rq N K)) : (seLc A Cin pz z rd L).length = L.length := by
  simp [seLc, length_seAddAt]

/-- The record of a step in the stream `rAinS`. -/
def seStepRec (Ain : DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (Cin : Fin 2 → Fin 2 × Fin K → Rq N K)
    (pz : Rq N K) (z : Fin 2 × Fin K → Rq N K) (rd : DigI K → Fin 2 → Fin 2 × Fin K → Rq N K)
    (pu : Rq N K) : List (Rq N K) :=
  adL Ain ++ (matL Cin ++ (pz :: (vecL z ++ (adL rd ++ [pu]))))

/-- The zero slab: `seAcc := n` zero rows. -/
def seZeroC : Code := .seq (.clr seAcc) <| .seq (.cp seC rTW) (.rep seC (.app seAcc rT2KNK))

theorem seVecL_zero : vecL (fun _ : Fin 2 × Fin K => (0 : Rq N K)) = List.replicate (2 * K) 0 := by
  simp [vecL, List.map_const', length_enum_col]

theorem exec_seZeroC (w : St) (n : ℕ) (hn : (w rTW).length = n) (hT : MulTmpl N K w) :
    exec N K seZeroC w seAcc = encL N K (seRows (List.replicate n fun _ => 0)) := by
  unfold seZeroC
  simp only [exec_seq]
  have key := exec_rep_inv2 (N := N) (K := K) seC (.app seAcc rT2KNK) (by decide)
    (fun m w' => w' seAcc = encL N K (seRows (List.replicate m fun _ => 0)))
    (exec N K (.cp seC rTW) (exec N K (.clr seAcc) w)) (by vm_simp; simp) ?_
  · have hc : ((exec N K (.cp seC rTW) (exec N K (.clr seAcc) w)) seC).length = n := by
      vm_simp; simp [Function.update_apply, hn]
    rw [hc] at key; exact key
  · intro m w' _ hP _ hfr
    have h2 : w' rT2KNK = encL N K (List.replicate (2 * K) 0) := by
      rw [hfr _ (by decide) (by decide)]; vm_simp; simp [Function.update_apply, hT.t2KNK]
    vm_simp
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, hP, h2, List.replicate_succ',
      seRows_append, seRows_cons, seRows_nil, List.append_nil, seVecL_zero, encL_append]

/-- The slab pre, part 1: `B`, the row map `· G⁻¹(C^in)`, row `0 += pz · z` (in `seQ`). -/
def sePre1 : Code :=
  .seq (.cp rMA rA) <| .seq (.cp rMAd rAinS) <| .seq mulPKC <| .seq (.cp rAinS rMAd) <|
  .seq (.cp rB rMOut) <|
  .seq (.cp seY rT4KNK) <| .seq (.mv seY rAinS rT4KNK) <| .seq (.cp seQ seSc) <| .seq seMapC <|
  .seq (.cp seQ seO) <|
  .seq (.cp seMu rZ) <| .seq (.mvR seMu rAinS) <| .seq (.cp seV rT2KNK) <|
  .seq (.mv seV rAinS rT2KNK) <| .seq seScaleC seAdd0C

/-- The slab pre, part 2: row `0 += (A ⋆ rd)₀`, into `seSc`. -/
def sePre2 : Code :=
  .seq (.cp seSc seQ) <| .seq (.cp rMA rA) <| .seq (.cp rMAd rAinS) <| .seq mulPKC <|
  .seq (.cp rAinS rMAd) <| .seq seRow0C <| .seq (.cp seQ seSc) <| .seq seAdd0C (.cp seSc seQ)

/-- The slab pre, part 3: the accumulators (F3's and the slab's). -/
def sePre3 : Code :=
  .seq (.cp rAccL rT4KNK) <| .seq (.cp rJ rZ) <| .seq (.cp rMu rMu0) <| .seq (.cp rCj2 rTW) seZeroC

/-- **The slab pre of a step**, with F3's `stepPre`. -/
def seSlabPre : Code := .seq sePre1 (.seq sePre2 sePre3)

theorem seSlabPre_keep : ∀ r : Fin 64, seRoJ r = true → r.val ∉ [0, 8, 16] →
    seSlabPre.writes r = false := by decide

theorem exec_sePre1 (hK : 0 < K) (w : St) (A Cin : Fin 2 → Fin 2 × Fin K → Rq N K)
    (Ain rd : DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (pz pu : Rq N K)
    (z : Fin 2 × Fin K → Rq N K) (L : List (Fin 2 × Fin K → Rq N K)) (rest : List (Rq N K))
    (hA : w rA = encL N K (matL A)) (hSc : w seSc = encL N K (seRows L))
    (hS : w rAinS = encL N K (seStepRec Ain Cin pz z rd pu ++ rest))
    (hn : (w rTW).length = L.length) (hL0 : 0 < L.length) (hT : MulTmpl N K w) :
    exec N K sePre1 w rB = encL N K (matL (mulPKm A Ain)) ∧
    exec N K sePre1 w seQ = encL N K (seRows (seAddAt (L.map fun v => seGRow v Cin) 0
      (seRowSmul pz z))) ∧
    exec N K sePre1 w rAinS = encL N K (adL rd ++ (pu :: rest)) ∧ MulTmpl N K (exec N K sePre1 w) := by
  unfold sePre1
  simp only [exec_seq]
  -- `B`
  generalize hW1 : exec N K (.cp rMAd rAinS) (exec N K (.cp rMA rA) w) = W1
  have T1 : MulTmpl N K W1 := hT.of_writes fun q hq => by
    rw [← hW1]; vm_simp
    have h1 : q ≠ rMA := by intro e; subst e; simp at hq
    have h2 : q ≠ rMAd := by intro e; subst e; simp at hq
    simp [Function.update_apply, h1, h2]
  obtain ⟨m2, n2⟩ := exec_mulPKC hK W1 A Ain (matL Cin ++ (pz :: (vecL z ++ (adL rd ++ (pu :: rest)))))
    (by rw [← hW1]; vm_simp; simp [hA])
    (by rw [← hW1]; vm_simp; simp [Function.update_apply, hS, seStepRec]) T1
  generalize hW2 : exec N K mulPKC W1 = W2
  rw [hW2] at m2 n2
  have T2 : MulTmpl N K W2 := T1.of_writes fun q hq => by
    rw [← hW2]; exact exec_writes _ _ _ (mulPKC_writes_ge q hq)
  have f2 : ∀ r : Fin 64, r.val < 32 → W2 r = w r := fun r hr => by
    rw [← hW2, exec_writes _ _ _ (by revert r; decide), ← hW1]; vm_simp
    have h1 : r ≠ rMA := by intro e; subst e; simp at hr
    have h2 : r ≠ rMAd := by intro e; subst e; simp at hr
    simp [Function.update_apply, h1, h2]
  -- `C^in`, the row map
  generalize hW3 : exec N K (.cp seQ seSc) (exec N K (.mv seY rAinS rT4KNK) (exec N K (.cp seY rT4KNK)
    (exec N K (.cp rB rMOut) (exec N K (.cp rAinS rMAd) W2)))) = W3
  have hlC : (matL Cin).length = 2 * (2 * K) := by simp; ring
  have a3 : W3 rB = encL N K (matL (mulPKm A Ain)) ∧ W3 seY = encL N K (matL Cin) ∧
      W3 rAinS = encL N K (pz :: (vecL z ++ (adL rd ++ (pu :: rest)))) ∧
      W3 seQ = encL N K (seRows L) ∧ (W3 rTW).length = L.length := by
    rw [← hW3]; vm_simp
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, m2, n2, T2.t4KNK, length_encL,
      List.length_replicate, f2 seSc (by decide), hSc, f2 rTW (by decide), hn, true_and, and_true]
    rw [shiftIn_encL' _ _ (List.length_replicate)]
    refine ⟨takeD_encL _ _ hlC, ?_⟩
    rw [drop_encL _ _ hlC]
  have T3 : MulTmpl N K W3 := T2.of_writes fun q hq => by
    rw [← hW3]; vm_simp
    have h1 : q ≠ seQ := by intro e; subst e; simp at hq
    have h2 : q ≠ seY := by intro e; subst e; simp at hq
    have h3 : q ≠ rAinS := by intro e; subst e; simp at hq
    have h4 : q ≠ rB := by intro e; subst e; simp at hq
    simp [Function.update_apply, h1, h2, h3, h4]
  obtain ⟨m4, T4⟩ := exec_seMapC hK W3 L Cin a3.2.2.2.2 a3.2.2.2.1 a3.2.1 T3
  generalize hW4 : exec N K seMapC W3 = W4
  rw [hW4] at m4 T4
  have f4 : ∀ r : Fin 64, r.val < 29 → W4 r = W3 r := fun r hr => by
    rw [← hW4]; exact exec_writes _ _ _ (by revert r; decide)
  -- `pz · z`
  generalize hW5 : exec N K (.mv seV rAinS rT2KNK) (exec N K (.cp seV rT2KNK)
    (exec N K (.mvR seMu rAinS) (exec N K (.cp seMu rZ) (exec N K (.cp seQ seO) W4)))) = W5
  have a5 : W5 seQ = encL N K (seRows (L.map fun v => seGRow v Cin)) ∧ W5 seMu = encRM N K pz ∧
      W5 seV = encL N K (vecL z) ∧ W5 rAinS = encL N K (adL rd ++ (pu :: rest)) := by
    rw [← hW5]; vm_simp
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, m4, T4.z, T4.t2KNK,
      f4 rAinS (by decide), a3.2.2.1, encL_cons, shiftIn_encRM', takeD_encRM_append,
      drop_encRM_append, length_encL, List.length_replicate, true_and]
    rw [shiftIn_encL' _ _ (List.length_replicate)]
    exact ⟨by rw [encL_append, takeD_encL' _ _ (length_vecL _)],
      by rw [encL_append, drop_encL' _ _ (length_vecL _)]⟩
  have T5 : MulTmpl N K W5 := T4.of_writes fun q hq => by
    rw [← hW5]; vm_simp
    have h1 : q ≠ seQ := by intro e; subst e; simp at hq
    have h2 : q ≠ seMu := by intro e; subst e; simp at hq
    have h3 : q ≠ rAinS := by intro e; subst e; simp at hq
    have h4 : q ≠ seV := by intro e; subst e; simp at hq
    simp [Function.update_apply, h1, h2, h3, h4]
  have o6 := exec_seScaleC hK W5 pz z a5.2.2.1 a5.2.1 T5
  generalize hW6 : exec N K seScaleC W5 = W6
  rw [hW6] at o6
  have T6 : MulTmpl N K W6 := T5.of_writes fun q hq => by
    rw [← hW6]; exact se_exec_frame _ _ seScaleC_writes _ _ (by revert q; decide)
  have f6 : ∀ r : Fin 64, r ∉ [seO, seE, rX0, seV] → W6 r = W5 r := fun r hr => by
    rw [← hW6]; exact se_exec_frame _ _ seScaleC_writes _ _ hr
  have q7 := exec_seAdd0C hK W6 (seRowSmul pz z) (L.map fun v => seGRow v Cin)
    (by rw [f6 _ (by decide), ← hW5]; vm_simp
        simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, f4 _ (by decide : (22 : Fin 64).val < 29),
          a3.2.2.2.2, List.length_map])
    (by rw [List.length_map]; exact hL0) (by rw [f6 _ (by decide), a5.1]) o6 T6
  generalize hW7 : exec N K seAdd0C W6 = W7
  rw [hW7] at q7
  have T7 : MulTmpl N K W7 := T6.of_writes fun q hq => by
    rw [← hW7]; exact se_exec_frame _ _ seAdd0C_writes _ _ (by revert q; decide)
  refine ⟨?_, q7, ?_, T7⟩
  · rw [← hW7, se_exec_frame _ _ seAdd0C_writes _ _ (by decide), f6 _ (by decide), ← hW5]
    vm_simp
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, f4 _ (by decide : (8 : Fin 64).val < 29),
      a3.1]
  · rw [← hW7, se_exec_frame _ _ seAdd0C_writes _ _ (by decide), f6 _ (by decide), a5.2.2.2]

theorem exec_sePre2 (hK : 0 < K) (w : St) (A : Fin 2 → Fin 2 × Fin K → Rq N K)
    (rd : DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (pu : Rq N K)
    (L : List (Fin 2 × Fin K → Rq N K)) (rest : List (Rq N K))
    (hA : w rA = encL N K (matL A)) (hQ : w seQ = encL N K (seRows L))
    (hS : w rAinS = encL N K (adL rd ++ (pu :: rest)))
    (hn : (w rTW).length = L.length) (hL0 : 0 < L.length) (hT : MulTmpl N K w) :
    exec N K sePre2 w seSc = encL N K (seRows (seAddAt L 0 (mulPKm A rd 0))) ∧
    exec N K sePre2 w rAinS = encRM N K pu ++ encL N K rest ∧ MulTmpl N K (exec N K sePre2 w) := by
  unfold sePre2
  simp only [exec_seq]
  generalize hW1 : exec N K (.cp rMAd rAinS) (exec N K (.cp rMA rA) (exec N K (.cp seSc seQ) w)) = W1
  have T1 : MulTmpl N K W1 := hT.of_writes fun q hq => by
    rw [← hW1]; vm_simp
    have h1 : q ≠ rMA := by intro e; subst e; simp at hq
    have h2 : q ≠ rMAd := by intro e; subst e; simp at hq
    have h3 : q ≠ seSc := by intro e; subst e; simp at hq
    simp [Function.update_apply, h1, h2, h3]
  obtain ⟨m2, n2⟩ := exec_mulPKC hK W1 A rd (pu :: rest) (by rw [← hW1]; vm_simp; simp [hA])
    (by rw [← hW1]; vm_simp; simp [Function.update_apply, hS]) T1
  generalize hW2 : exec N K mulPKC W1 = W2
  rw [hW2] at m2 n2
  have T2 : MulTmpl N K W2 := T1.of_writes fun q hq => by
    rw [← hW2]; exact exec_writes _ _ _ (mulPKC_writes_ge q hq)
  have sc2 : W2 seSc = encL N K (seRows L) := by
    rw [← hW2, exec_writes _ _ _ (by decide), ← hW1]; vm_simp; simp [hQ]
  have tw2 : (W2 rTW).length = L.length := by
    rw [← hW2, exec_writes _ _ _ (by decide), ← hW1]; vm_simp; simp [hn]
  generalize hW3 : exec N K seRow0C (exec N K (.cp rAinS rMAd) W2) = W3
  have o3 : W3 seO = encL N K (vecL (mulPKm A rd 0)) := by
    rw [← hW3]
    exact exec_seRow0C _ _ (by rw [exec_cp, Function.update_of_ne (by decide), m2])
      (T2.of_writes fun q hq => by rw [exec_cp, Function.update_of_ne (by intro e; subst e; simp at hq)])
  have g3 : ∀ r : Fin 64, (r = seSc ∨ r = rTW ∨ r = rAinS) → W3 r = exec N K (.cp rAinS rMAd) W2 r :=
    fun r hr => by
      rw [← hW3]; exact exec_writes _ _ _ (by rcases hr with rfl | rfl | rfl <;> decide)
  have T3 : MulTmpl N K W3 := T2.of_writes fun q hq => by
    rw [← hW3, exec_writes _ _ _ (by unfold seRow0C; revert q; decide), exec_cp,
      Function.update_of_ne (by intro e; subst e; simp at hq)]
  have q4 := exec_seAdd0C hK (exec N K (.cp seQ seSc) W3) (mulPKm A rd 0) L
    (by rw [exec_cp, Function.update_of_ne (by decide), g3 _ (by simp), exec_cp,
      Function.update_of_ne (by decide), tw2]) hL0
    (by rw [exec_cp, Function.update_self, g3 _ (by simp), exec_cp, Function.update_of_ne (by decide),
      sc2])
    (by rw [exec_cp, Function.update_of_ne (by decide), o3])
    (T3.of_writes fun q hq => by rw [exec_cp, Function.update_of_ne (by intro e; subst e; simp at hq)])
  refine ⟨?_, ?_, ?_⟩
  · rw [exec_cp, Function.update_self, q4]
  · rw [exec_cp, Function.update_of_ne (by decide), se_exec_frame _ _ seAdd0C_writes _ _ (by decide),
      exec_cp, Function.update_of_ne (by decide), g3 _ (by simp), exec_cp, Function.update_self, n2,
      encL_cons]
  · refine T3.of_writes fun q hq => ?_
    rw [exec_cp, Function.update_of_ne (by intro e; subst e; simp at hq),
      se_exec_frame _ _ seAdd0C_writes _ _ (by revert q; decide), exec_cp,
      Function.update_of_ne (by intro e; subst e; simp at hq)]

theorem exec_sePre3 (w : St) (μ0 : Rq N K) (n : ℕ) (hn : (w rTW).length = n)
    (hM0 : w rMu0 = encRM N K μ0) (hT : MulTmpl N K w) :
    exec N K sePre3 w rAccL = encL N K (matL fun _ _ => 0) ∧
    exec N K sePre3 w rJ = encRM N K 0 ∧ exec N K sePre3 w rMu = encRM N K μ0 ∧
    (exec N K sePre3 w rCj2).length = n ∧
    exec N K sePre3 w seAcc = encL N K (seRows (List.replicate n fun _ => 0)) ∧
    MulTmpl N K (exec N K sePre3 w) := by
  unfold sePre3
  simp only [exec_seq]
  generalize hW1 : exec N K (.cp rCj2 rTW) (exec N K (.cp rMu rMu0) (exec N K (.cp rJ rZ)
    (exec N K (.cp rAccL rT4KNK) w))) = W1
  have a1 : W1 rAccL = encL N K (matL fun _ _ => 0) ∧ W1 rJ = encRM N K 0 ∧
      W1 rMu = encRM N K μ0 ∧ (W1 rCj2).length = n ∧ (W1 rTW).length = n := by
    rw [← hW1]; vm_simp
    simp [Function.update_apply, hT.t4KNK, hT.z, hM0, hn, matL_zero]
  have T1 : MulTmpl N K W1 := hT.of_writes fun q hq => by
    rw [← hW1]; vm_simp
    have h1 : q ≠ rCj2 := by intro e; subst e; simp at hq
    have h2 : q ≠ rMu := by intro e; subst e; simp at hq
    have h3 : q ≠ rJ := by intro e; subst e; simp at hq
    have h4 : q ≠ rAccL := by intro e; subst e; simp at hq
    simp [Function.update_apply, h1, h2, h3, h4]
  refine ⟨?_, ?_, ?_, ?_, exec_seZeroC W1 n a1.2.2.2.2 T1, ?_⟩
  · rw [exec_writes _ _ _ (by decide), a1.1]
  · rw [exec_writes _ _ _ (by decide), a1.2.1]
  · rw [exec_writes _ _ _ (by decide), a1.2.2.1]
  · rw [exec_writes _ _ _ (by decide), a1.2.2.2.1]
  · exact T1.of_writes fun q hq => exec_writes _ _ _ (by unfold seZeroC; revert q; decide)

/-- **The slab pre of a step.** -/
theorem exec_seSlabPre (hK : 0 < K) (w : St) (A Cin : Fin 2 → Fin 2 × Fin K → Rq N K)
    (Ain rd : DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (pz pu μ0 : Rq N K)
    (z : Fin 2 × Fin K → Rq N K) (L : List (Fin 2 × Fin K → Rq N K)) (rest : List (Rq N K))
    (hA : w rA = encL N K (matL A)) (hSc : w seSc = encL N K (seRows L))
    (hS : w rAinS = encL N K (seStepRec Ain Cin pz z rd pu ++ rest))
    (hn : (w rTW).length = L.length) (hL0 : 0 < L.length) (hM0 : w rMu0 = encRM N K μ0)
    (hT : MulTmpl N K w) :
    exec N K seSlabPre w rB = encL N K (matL (mulPKm A Ain)) ∧
    exec N K seSlabPre w seSc = encL N K (seRows (seLc A Cin pz z rd L)) ∧
    exec N K seSlabPre w rAinS = encRM N K pu ++ encL N K rest ∧
    exec N K seSlabPre w rAccL = encL N K (matL fun _ _ => 0) ∧
    exec N K seSlabPre w rJ = encRM N K 0 ∧ exec N K seSlabPre w rMu = encRM N K μ0 ∧
    (exec N K seSlabPre w rCj2).length = L.length ∧
    exec N K seSlabPre w seAcc = encL N K (seRows (List.replicate L.length fun _ => 0)) ∧
    MulTmpl N K (exec N K seSlabPre w) := by
  unfold seSlabPre
  rw [exec_seq, exec_seq]
  obtain ⟨b1, b2, b3, T1⟩ := exec_sePre1 hK w A Cin Ain rd pz pu z L rest hA hSc hS hn hL0 hT
  generalize hW1 : exec N K sePre1 w = W1
  rw [hW1] at b1 b2 b3 T1
  have e1 : ∀ r : Fin 64, (r = rA ∨ r = rTW ∨ r = rMu0) → W1 r = w r := fun r hr => by
    rw [← hW1]; exact exec_writes _ _ _ (by rcases hr with rfl | rfl | rfl <;> decide)
  obtain ⟨c1, c2, T2⟩ := exec_sePre2 hK W1 A rd pu _ rest (by rw [e1 _ (by simp), hA]) b2 b3
    (by rw [e1 _ (by simp), hn, seAddAt, List.length_modify, List.length_map])
    (by rw [seAddAt, List.length_modify, List.length_map]; exact hL0) T1
  generalize hW2 : exec N K sePre2 W1 = W2
  rw [hW2] at c1 c2 T2
  have e2 : ∀ r : Fin 64, (r = rTW ∨ r = rMu0 ∨ r = rB) → W2 r = W1 r := fun r hr => by
    rw [← hW2]; exact exec_writes _ _ _ (by rcases hr with rfl | rfl | rfl <;> decide)
  obtain ⟨d1, d2, d3, d4, d5, T3⟩ := exec_sePre3 W2 μ0 L.length
    (by rw [e2 _ (by simp), e1 _ (by simp), hn]) (by rw [e2 _ (by simp), e1 _ (by simp), hM0]) T2
  refine ⟨?_, ?_, ?_, d1, d2, d3, d4, d5, T3⟩
  · rw [exec_writes _ _ _ (by decide), e2 _ (by simp), b1]
  · rw [exec_writes _ _ _ (by decide), c1]; rfl
  · rw [exec_writes _ _ _ (by decide), c2]

/-! ### One step -/

/-- **One paired step** with the coefficient routine `cf`. -/
def seStepK (cf : Code) : Code :=
  .seq seSlabPre <| .seq (.rep rCj2 (seJBody cf)) <| .seq (.cp rA rAccL) <|
  .seq (.cp seSc seAcc) <| .seq (.drop rCs rTtab) (.drop rAinS rZ)

/-- The registers of a step (read only). -/
structure SeStepIn (w : St) (g b n tl : ℕ) (D : SeBits N K) (μ0 : Rq N K) : Prop where
  ch : SeChainIn w g b n D
  one : w rOne = encRM N K 1
  mu0 : w rMu0 = encRM N K μ0
  t4K : w rT4K = List.replicate (4 * K) false
  ttab : w rTtab = List.replicate tl false

/-- The registers a step keeps. -/
def seRoS (r : Fin 64) : Bool := seRoJ r && !([0, 3, 4, 8, 16] : List ℕ).contains r.val

theorem SeStepIn.of_roS {w w' : St} {g b n tl : ℕ} {D : SeBits N K} {μ0 : Rq N K}
    (h : SeStepIn w g b n tl D μ0)
    (hw : ∀ r : Fin 64, seRoS r = true → r ≠ rCst → w' r = w r) :
    SeStepIn w' g b n tl D μ0 :=
  ⟨⟨by rw [hw _ (by decide) (by decide)]; exact h.ch.sw,
    by rw [hw _ (by decide) (by decide)]; exact h.ch.tb,
    by rw [hw _ (by decide) (by decide)]; exact h.ch.bit1,
    by rw [hw _ (by decide) (by decide)]; exact h.ch.trec,
    by rw [hw _ (by decide) (by decide)]; exact h.ch.tw,
    by rw [hw _ (by decide) (by decide)]; exact h.ch.kc,
    h.ch.tm.of_writes fun q hq => hw q (by revert q; decide) (by intro e; subst e; simp at hq)⟩,
   by rw [hw _ (by decide) (by decide)]; exact h.one, by rw [hw _ (by decide) (by decide)]; exact h.mu0,
   by rw [hw _ (by decide) (by decide)]; exact h.t4K,
   by rw [hw _ (by decide) (by decide)]; exact h.ttab⟩

theorem seStepK_roS (cf : Code) (hcf : CoefW cf) : ∀ r : Fin 64, seRoS r = true →
    (seStepK cf).writes r = false := by
  intro r hr
  have h1 : seRoJ r = true := by simp only [seRoS, Bool.and_eq_true] at hr; exact hr.1
  have h2 : r.val ∉ [0, 8, 16] := by revert r; decide
  have h3 : (seJBody cf).writes r = false := seJBody_roJ cf hcf r h1
  have h4 : ∀ r : Fin 64, seRoS r = true → (Code.seq (.cp rA rAccL) <| .seq (.cp seSc seAcc) <|
      .seq (.drop rCs rTtab) (.drop rAinS rZ)).writes r = false := by decide
  have h5 : r ≠ rCj2 := by intro e; subst e; simp [seRoS, seRoJ] at hr
  show (seSlabPre.writes r || ((rCj2 == r || (cf.writes r || seJRest.writes r)) ||
    (Code.seq (.cp rA rAccL) <| .seq (.cp seSc seAcc) <|
      .seq (.drop rCs rTtab) (.drop rAinS rZ)).writes r)) = false
  rw [seSlabPre_keep r h1 h2, hcf.ro r (seRoJ_roJ r h1), seJRest_roJ r h1, h4 r hr,
    beq_eq_false_iff_ne.mpr (Ne.symm h5)]
  rfl

/-- **One paired step**: `rA := Σ_j A_j G⁻¹(α_j G)` (F3's `accM`), `seSc := seTab …`. -/
theorem exec_seStepK (hN : 0 < N) (hK : 0 < K) (cf : Code) (hcfw : CoefW cf)
    (cv : Rq N K → Rq N K) (w : St)
    (hcf : ∀ w' : St, (∀ r : Fin 64, roC r = true → w' r = w r) → ∀ μ : Rq N K,
      w' rMu = encRM N K μ → exec N K cf w' rAl = encRM N K (cv μ))
    (g b n tl : ℕ) (hg : 0 < g) (hn : n ≤ 2 ^ K - 1) (D : SeBits N K) (μ0 : Rq N K)
    (hin : SeStepIn w g b n tl D μ0) (A Cin : Fin 2 → Fin 2 × Fin K → Rq N K)
    (Ain rd : DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (pz pu : Rq N K)
    (z : Fin 2 × Fin K → Rq N K) (L : List (Fin 2 × Fin K → Rq N K)) (rest : List (Rq N K))
    (hL : L.length = n) (hbL : 2 ^ b ≤ n) (hL0 : 0 < n)
    (hA : w rA = encL N K (matL A)) (hSc : w seSc = encL N K (seRows L))
    (hS : w rAinS = encL N K (seStepRec Ain Cin pz z rd pu ++ rest)) :
    exec N K (seStepK cf) w rA = encL N K (matL (accM cv g D.Hf D.Aa b (mulPKm A Ain) μ0 n)) ∧
    exec N K (seStepK cf) w seSc = encL N K (seRows (seTab cv g D b (mulPKm A Ain) pu μ0
      (seLc A Cin pz z rd L) n)) ∧
    exec N K (seStepK cf) w rAinS = encL N K rest ∧
    exec N K (seStepK cf) w rCs = (w rCs).drop tl := by
  have hT := hin.ch.tm
  unfold seStepK
  simp only [exec_seq]
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, T1⟩ := exec_seSlabPre hK w A Cin Ain rd pz pu μ0 z L rest
    hA hSc hS (by rw [hin.ch.tw, hL]) (by rw [hL]; exact hL0) hin.mu0 hT
  generalize hW1 : exec N K seSlabPre w = W1
  rw [hW1] at p1 p2 p3 p4 p5 p6 p7 p8 T1
  have k1 : ∀ r : Fin 64, seRoJ r = true → r.val ∉ [0, 8, 16] → W1 r = w r := fun r hr h => by
    rw [← hW1]; exact exec_writes _ _ _ (seSlabPre_keep r hr h)
  have hlc : (seLc A Cin pz z rd L).length = n := by rw [length_seLc, hL]
  have hin1 : SeChainIn W1 g b (seLc A Cin pz z rd L).length D := by
    rw [hlc]
    exact ⟨by rw [k1 _ (by decide) (by decide)]; exact hin.ch.sw,
      by rw [k1 _ (by decide) (by decide)]; exact hin.ch.tb,
      by rw [k1 _ (by decide) (by decide)]; exact hin.ch.bit1,
      by rw [k1 _ (by decide) (by decide)]; exact hin.ch.trec,
      by rw [k1 _ (by decide) (by decide)]; exact hin.ch.tw,
      by rw [k1 _ (by decide) (by decide)]; exact hin.ch.kc, T1⟩
  obtain ⟨l1, l2, l3⟩ := exec_seJLoop hN hK cf hcfw cv W1
    (fun w' hw' μ hμ => hcf w' (fun r hr => by
      rw [hw' r hr, k1 r (roC_seRoJ r hr) (by revert r; decide)]) μ hμ)
    g b n hg hn D (mulPKm A Ain) pu μ0 (seLc A Cin pz z rd L) (encL N K rest) hin1
    (by rw [hlc]; exact hbL) p1 p2 p3 (by rw [k1 _ (by decide) (by decide), hin.one])
    (by rw [k1 _ (by decide) (by decide), hin.t4K]) p4 (by rw [length_seLc, p8]) p5 p6
    (by rw [p7, hL])
  generalize hW2 : exec N K (.rep rCj2 (seJBody cf)) W1 = W2
  rw [hW2] at l1 l2 l3
  have e3 := l3 rAinS (by decide)
  have e4 := l3 rCs (by decide)
  have e5 := l3 rTtab (by decide)
  have e6 := l3 rZ (by decide)
  have e7 := k1 rCs (by decide) (by decide)
  have e8 := k1 rTtab (by decide) (by decide)
  have e9 := k1 rZ (by decide) (by decide)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> vm_simp
  · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, l1]
  · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, l2]
  · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, e3, e6, e9, p3, hT.z, Algo.length_encRM,
      drop_encRM_append]
  · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, e4, e5, e7, e8, hin.ttab,
      List.length_replicate]

/-! ### The evaluation -/

/-- **The paired `EvalPK`**: `T = 16` steps (15 `α`-steps, the `v`-step). -/
def seEvalC : Code := .seq (.cp rCst rT15) <| .seq (.rep rCst (seStepK cfA)) (seStepK cfV)

/-- **The slab of the evaluation**, step by step (the public matrices are F3's `evalVM`). -/
def seEvalVM (cvs : ℕ → Rq N K → Rq N K) (g : ℕ) (D : SeBits N K) (b : ℕ) (μ0 : Rq N K) (n : ℕ)
    (Ain : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (A0 : Fin 2 → Fin 2 × Fin K → Rq N K)
    (Cin : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K) (pz pu : ℕ → Rq N K)
    (z : ℕ → Fin 2 × Fin K → Rq N K) (rd : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K)
    (L0 : List (Fin 2 × Fin K → Rq N K)) : ℕ → List (Fin 2 × Fin K → Rq N K)
  | 0 => L0
  | i + 1 => seTab (cvs i) g D b (mulPKm (evalVM cvs g D.Hf D.Aa b μ0 n Ain A0 i) (Ain i)) (pu i) μ0
      (seLc (evalVM cvs g D.Hf D.Aa b μ0 n Ain A0 i) (Cin i) (pz i) (z i) (rd i)
        (seEvalVM cvs g D b μ0 n Ain A0 Cin pz pu z rd L0 i)) n

theorem length_seEvalVM (cvs : ℕ → Rq N K → Rq N K) (g : ℕ) (D : SeBits N K) (b : ℕ) (μ0 : Rq N K)
    (n : ℕ) (Ain : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K)
    (A0 : Fin 2 → Fin 2 × Fin K → Rq N K) (Cin : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K)
    (pz pu : ℕ → Rq N K) (z : ℕ → Fin 2 × Fin K → Rq N K)
    (rd : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (L0 : List (Fin 2 × Fin K → Rq N K))
    (hL0 : L0.length = n) :
    ∀ i, (seEvalVM cvs g D b μ0 n Ain A0 Cin pz pu z rd L0 i).length = n
  | 0 => hL0
  | i + 1 => by
    rw [seEvalVM, length_seTab, length_seLc,
      length_seEvalVM cvs g D b μ0 n Ain A0 Cin pz pu z rd L0 hL0 i]

/-- The stream of the step records `i ∈ l`. -/
def seStepsL (Ain : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K)
    (Cin : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K) (pz : ℕ → Rq N K) (z : ℕ → Fin 2 × Fin K → Rq N K)
    (rd : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (pu : ℕ → Rq N K) (l : List ℕ) :
    List (Rq N K) :=
  l.flatMap fun i => seStepRec (Ain i) (Cin i) (pz i) (z i) (rd i) (pu i)

theorem roC_seRoS : ∀ r : Fin 64, roC r = true → r ≠ rCs → seRoS r = true := by decide

/-- **`seEvalC` computes the paired `EvalPK`.** -/
theorem exec_seEvalC (hN : 0 < N) (hK : 0 < K) (w : St) (g b n tl e : ℕ) (hg : 0 < g)
    (hb : b ≤ K) (hn : n ≤ 2 ^ K - 1) (D : SeBits N K) (μ0 xc : Rq N K)
    (hin : SeStepIn w g b n tl D μ0) (hco : CoefIn w e n b xc)
    (Ain : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (A0 : Fin 2 → Fin 2 × Fin K → Rq N K)
    (Cin : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K) (pz pu : ℕ → Rq N K)
    (z : ℕ → Fin 2 × Fin K → Rq N K) (rd : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K)
    (L0 : List (Fin 2 × Fin K → Rq N K)) (C : List Bool)
    (hL0 : L0.length = n) (hbL : 2 ^ b ≤ n) (hn0 : 0 < n)
    (hA : w rA = encL N K (matL A0)) (hSc : w seSc = encL N K (seRows L0))
    (hS : w rAinS = encL N K (seStepsL Ain Cin pz z rd pu (List.range 16))) (hC : w rCs = C)
    (h15 : w rT15 = List.replicate 15 false) :
    exec N K seEvalC w rA = encL N K (matL (evalVM (fun i => if i < 15 then
      cvA e n b xc (C.drop (tl * i)) else cvV n b (C.drop (tl * 15))) g D.Hf D.Aa b μ0 n Ain A0 16)) ∧
    exec N K seEvalC w seSc = encL N K (seRows (seEvalVM (fun i => if i < 15 then
      cvA e n b xc (C.drop (tl * i)) else cvV n b (C.drop (tl * 15))) g D b μ0 n Ain A0 Cin pz pu z rd
      L0 16)) := by
  set cvs : ℕ → Rq N K → Rq N K := fun i => if i < 15 then
      cvA e n b xc (C.drop (tl * i)) else cvV n b (C.drop (tl * 15)) with hcvs
  unfold seEvalC
  simp only [exec_seq]
  generalize hW1 : exec N K (.cp rCst rT15) w = W1
  have r1 : ∀ r : Fin 64, r ≠ rCst → W1 r = w r := fun r hr => by
    rw [← hW1, exec_cp, Function.update_of_ne hr]
  have co : ∀ {w' : St}, (∀ r : Fin 64, seRoS r = true → r ≠ rCst → w' r = w r) →
      CoefIn w' e n b xc :=
    fun hw => ⟨by rw [hw _ (by decide) (by decide), hco.one],
      by rw [hw _ (by decide) (by decide), hco.xc], by rw [hw _ (by decide) (by decide), hco.bit1],
      by rw [hw _ (by decide) (by decide), hco.te], by rw [hw _ (by decide) (by decide), hco.tw],
      by rw [hw _ (by decide) (by decide), hco.tb], by rw [hw _ (by decide) (by decide), hco.z]⟩
  have key := exec_rep_inv2 (N := N) (K := K) rCst (seStepK cfA)
    (seStepK_roS cfA coefW_cfA rCst (by decide))
    (fun i w' => w' rA = encL N K (matL (evalVM cvs g D.Hf D.Aa b μ0 n Ain A0 i)) ∧
      w' seSc = encL N K (seRows (seEvalVM cvs g D b μ0 n Ain A0 Cin pz pu z rd L0 i)) ∧
      w' rAinS = encL N K (seStepsL Ain Cin pz z rd pu ((List.range 16).drop i)) ∧
      w' rCs = C.drop (tl * i)) W1
    ⟨by rw [r1 _ (by decide), hA]; rfl, by rw [r1 _ (by decide), hSc]; rfl,
      by rw [r1 _ (by decide), hS]; rfl, by rw [r1 _ (by decide), hC]; simp⟩ ?_
  · have hc : (W1 rCst).length = 15 := by rw [← hW1]; vm_simp; simp [h15]
    rw [hc] at key
    obtain ⟨k1, k2, k3, k4⟩ := key
    generalize hW2 : exec N K (.rep rCst (seStepK cfA)) W1 = W2
    rw [hW2] at k1 k2 k3 k4
    have f2 : ∀ r : Fin 64, seRoS r = true → r ≠ rCst → W2 r = w r := fun r hr hrc => by
      have hw : (Code.rep rCst (seStepK cfA)).writes r = false := by
        simp only [Code.writes, seStepK_roS cfA coefW_cfA r hr, Bool.or_false, beq_eq_false_iff_ne]
        exact Ne.symm hrc
      rw [← hW2, exec_writes _ _ _ hw, r1 r hrc]
    have hin2 := hin.of_roS f2
    have hco2 := co f2
    rw [drop_range_succ (by norm_num : 15 < 16)] at k3
    simp only [seStepsL, List.flatMap_cons] at k3
    have hdrop : (List.range 16).drop 16 = [] := by simp
    rw [hdrop, List.flatMap_nil, List.append_nil] at k3
    have hcfV := hcf_cfV hK W2 e n b hb xc hco2
    obtain ⟨s1, s2, -, -⟩ := exec_seStepK hN hK cfV coefW_cfV (cvV n b (W2 rCs)) W2 hcfV
      g b n tl hg hn D μ0 hin2 _ (Cin 15) (Ain 15) (rd 15) (pz 15) (pu 15) (z 15) _ []
      (length_seEvalVM cvs g D b μ0 n Ain A0 Cin pz pu z rd L0 hL0 15) hbL hn0 k1 k2
      (by rw [k3, List.append_nil])
    rw [k4] at s1 s2
    refine ⟨?_, ?_⟩
    · rw [s1]; rfl
    · rw [s2]; rfl
  · intro i w' hi hP _ hfr
    have hc : (W1 rCst).length = 15 := by rw [← hW1]; vm_simp; simp [h15]
    rw [hc] at hi
    obtain ⟨p1, p2, p3, p4⟩ := hP
    generalize hW0 : Function.update w' rCst (w' rCst).tail = W0
    have f0 : ∀ r : Fin 64, seRoS r = true → r ≠ rCst → W0 r = w r := fun r hr hr' => by
      rw [← hW0, Function.update_of_ne hr', hfr r (seStepK_roS cfA coefW_cfA r hr) hr', r1 r hr']
    have hin0 := hin.of_roS f0
    have hco0 := co f0
    have q1 : W0 rA = encL N K (matL (evalVM cvs g D.Hf D.Aa b μ0 n Ain A0 i)) := by
      rw [← hW0, Function.update_of_ne (by decide), p1]
    have q2 : W0 seSc = encL N K (seRows (seEvalVM cvs g D b μ0 n Ain A0 Cin pz pu z rd L0 i)) := by
      rw [← hW0, Function.update_of_ne (by decide), p2]
    have q3 : W0 rAinS = encL N K (seStepRec (Ain i) (Cin i) (pz i) (z i) (rd i) (pu i) ++
        seStepsL Ain Cin pz z rd pu ((List.range 16).drop (i + 1))) := by
      rw [← hW0, Function.update_of_ne (by decide), p3, drop_range_succ (by omega)]
      simp [seStepsL]
    have q4 : W0 rCs = C.drop (tl * i) := by rw [← hW0, Function.update_of_ne (by decide), p4]
    obtain ⟨s1, s2, s3, s4⟩ := exec_seStepK hN hK cfA coefW_cfA (cvA e n b xc (W0 rCs)) W0
      (hcf_cfA hN hK W0 e n b hb xc hco0) g b n tl hg hn D μ0 hin0 _ (Cin i) (Ain i) (rd i) (pz i)
      (pu i) (z i) _ _ (length_seEvalVM cvs g D b μ0 n Ain A0 Cin pz pu z rd L0 hL0 i) hbL hn0 q1 q2 q3
    rw [q4] at s1 s2
    have hcv : cvA e n b xc (C.drop (tl * i)) = cvs i := by
      rw [hcvs]; simp only [if_pos (show i < 15 by omega)]
    refine ⟨?_, ?_, s3, ?_⟩
    · rw [s1, hcv]; rfl
    · rw [s2, hcv]; rfl
    · rw [s4, q4, List.drop_drop]
      congr 1

end AdvancedEncryption.ExpLUT.Prog
