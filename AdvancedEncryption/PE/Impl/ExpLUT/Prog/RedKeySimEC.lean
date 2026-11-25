import PE.Impl.ExpLUT.Prog.RedKeySimEK

/-!
# `KGsim` on the VM (module 6b, part 2): one step of the paired chain (generic VM)

The rounds of a table are the index-carrying paired bit chain `slabChainStep`
(`RedKeySimSlab.slabChain_eq`): at the bit `t`, the public matrix takes `Aut_{g_t}` and the slab
takes `slabAut (2^t)`. On the VM (lists of rows, `seRows`), the slab step is

* `σ_g^{2^t}` on every row, rotate the rows right by `2^t`, every row `· G⁻¹(C_t)` (`gc t`);
* row `2^t += (σ^{2^t}(A) ⋆ ad_t)` (row `0` of `mulPKm`: the digit term of the `inl` slabs);
* row `2^t += σ^{2^t}(μ_k) · crow_t` (the `C_{g_t}` term of the `inr` slabs), `μ_{k+2^t} = σ^{2^t}(μ_k)`;
* row `0 += hrow_t · G⁻¹(A')`, `A' = mulPKm(σ^{2^t}(A), A^aut_t)` (the `H_{g_t}` term);
* the public matrix `A ↦ H_{g_t} · G⁻¹(A')` (`autVM`).

`seStep` is this map, `seAutStep` its code, **`exec_seAutStep`**. The per-bit data come from one
stream (`rSs = 12`), one record per bit `t` (`seRec`): `gc_t`, `ad_t`, `crow_t`, `A^aut_t`,
`hrow_t`, `H_{g_t}`.

Registers: the chain's public matrix `seA = 4`, the slab `seSl = 13`, the payload `seMu = 2`, the
stream `rSs = 12`; read: `rPw2 = 15` (`2^t`), `rTW = 22` (`n` rows), `rKc = 31` (`g`). The step
writes only `2, 4, 12, 13` and the library scratch `29 … 56`.
-/

set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)

/-- The chain's public matrix. -/
@[simp, vmreg] abbrev seA : Fin 64 := 4
/-- The chain's slab. -/
@[simp, vmreg] abbrev seSl : Fin 64 := 13

variable {N K : ℕ}

/-! ### The data and the step -/

/-- The per-bit data of the paired chain. -/
structure SeBits (N K : ℕ) where
  /-- The gadget matrices `C_{g_t}` (`gcAut`). -/
  gc : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K
  /-- The digit rows of `R^aut_t` (row `0`). -/
  ad : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K
  /-- The row of `R_{C_{g_t}}`. -/
  crow : ℕ → Fin 2 × Fin K → Rq N K
  /-- `A^aut_t`. -/
  Aa : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K
  /-- The row of `R_{H_{g_t}}`. -/
  hrow : ℕ → Fin 2 × Fin K → Rq N K
  /-- `H_{g_t}`. -/
  Hf : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K

/-- The record of the bit `t` in the stream. -/
def seRec (D : SeBits N K) (t : ℕ) : List (Rq N K) :=
  matL (D.gc t) ++ (adL (D.ad t) ++ (vecL (D.crow t) ++ (adL (D.Aa t) ++
    (vecL (D.hrow t) ++ matL (D.Hf t)))))

theorem length_seRec (D : SeBits N K) (t : ℕ) : (seRec D t).length = 32 * K ^ 3 + 12 * K := by
  simp [seRec, length_adL]; ring

/-- `σ_g^m` on a matrix. -/
def seMatAut (g m : ℕ) (A : Fin 2 → Fin 2 × Fin K → Rq N K) : Fin 2 → Fin 2 × Fin K → Rq N K :=
  fun a c => (aut N g)^[m] (A a c)

/-- **One step of the paired chain** at the bit `t`: `(A, μ, L) ↦ (A_new, μ', L')`. -/
def seStep (g : ℕ) (D : SeBits N K) (t : ℕ)
    (st : (Fin 2 → Fin 2 × Fin K → Rq N K) × Rq N K × List (Fin 2 × Fin K → Rq N K)) :
    (Fin 2 → Fin 2 × Fin K → Rq N K) × Rq N K × List (Fin 2 × Fin K → Rq N K) :=
  let σA := seMatAut g (2 ^ t) st.1
  let L1 := ((st.2.2.map (seRowAut g (2 ^ t))).rotate (st.2.2.length - 2 ^ t)).map
    fun v => seGRow v (D.gc t)
  let L2 := seAddAt L1 (2 ^ t) (mulPKm σA (D.ad t) 0)
  let μ' := (aut N g)^[2 ^ t] st.2.1
  let L3 := seAddAt L2 (2 ^ t) (seRowSmul μ' (D.crow t))
  let A' := mulPKm σA (D.Aa t)
  (ginvMulm (D.Hf t) A', μ', seAddAt L3 0 (seGRow (D.hrow t) A'))

/-! ### Phase (a): the slab's permutation and `· G⁻¹(C_t)` -/

/-- Phase (a). -/
def seSA : Code :=
  .seq (.cp seQ seSl) <| .seq (.cp rP rPw2) <| .seq seAutC <| .seq (.cp seC rTW) <|
  .seq (.drop seC rPw2) <| .seq seRotC <| .seq (.cp seY rT4KNK) <| .seq (.mv seY rSs rT4KNK) <|
  .seq seMapC (.cp seSl seO)

theorem seSA_writes : ∀ r : Fin 64, seSA.writes r = true →
    r = seSl ∨ r = rSs ∨ (29 ≤ r.val ∧ r.val < 57) := by decide

theorem seAutC_writes : ∀ r : Fin 64, seAutC.writes r = true → r ∈ [rP, seC, seE, rX0, seQ] := by
  decide

theorem exec_seSA (hN : 0 < N) (hK : 0 < K) (w : St) (L : List (Fin 2 × Fin K → Rq N K))
    (Y : Fin 2 → Fin 2 × Fin K → Rq N K) (rest : List (Rq N K))
    (hn : (w rTW).length = L.length)
    (hSl : w seSl = encL N K (seRows L)) (hSs : w rSs = encL N K (matL Y ++ rest))
    (hk : 0 < (w rKc).length) (hT : MulTmpl N K w) :
    exec N K seSA w seSl = encL N K (seRows ((((L.map (seRowAut (w rKc).length
      (w rPw2).length)).rotate (L.length - (w rPw2).length))).map fun v => seGRow v Y)) ∧
    exec N K seSA w rSs = encL N K rest ∧ MulTmpl N K (exec N K seSA w) := by
  unfold seSA
  simp only [exec_seq]
  set w1 := exec N K (.cp rP rPw2) (exec N K (.cp seQ seSl) w) with hw1
  have f1 : ∀ r : Fin 64, r ≠ rP → r ≠ seQ → w1 r = w r := fun r h1 h2 => by
    rw [hw1]; vm_simp; simp [Function.update_apply, h1, h2]
  have T1 : MulTmpl N K w1 := hT.of_writes fun q hq => f1 q (by intro e; subst e; simp at hq)
    (by intro e; subst e; simp at hq)
  have a1 := exec_seAutC hN hK w1 L (by rw [f1 _ (by decide) (by decide), hn])
    (by rw [hw1]; vm_simp; simp [Function.update_apply, hSl])
    (by rw [f1 _ (by decide) (by decide)]; exact hk) T1
  have e1 : (w1 rP).length = (w rPw2).length := by rw [hw1]; vm_simp; simp [Function.update_apply]
  rw [e1, f1 _ (by decide) (by decide)] at a1
  set w2 := exec N K seAutC w1 with hw2
  have f2 : ∀ r : Fin 64, r ∉ [rP, seC, seE, rX0, seQ] → w2 r = w r := fun r h => by
    rw [hw2, se_exec_frame _ _ seAutC_writes _ _ h, f1 r (by intro e; subst e; simp at h)
      (by intro e; subst e; simp at h)]
  set w3 := exec N K (.drop seC rPw2) (exec N K (.cp seC rTW) w2) with hw3
  have r3 := exec_seRotC (N := N) (K := K) w3 (L.map (seRowAut (w rKc).length (w rPw2).length))
    (L.length - (w rPw2).length) (by simp)
    (by rw [hw3]; vm_simp; simp [Function.update_apply, a1])
    (by rw [hw3]; vm_simp; simp [Function.update_apply, f2 rTW (by decide), f2 rPw2 (by decide), hn])
    (by rw [hw3]; vm_simp; simp [Function.update_apply, f2 rT2KNK (by decide), hT.t2KNK])
  set w4 := exec N K seRotC w3 with hw4
  have f4 : ∀ r : Fin 64, r ∉ [rP, seC, seE, rX0, seQ, seR] → w4 r = w r := fun r h => by
    rw [hw4, se_exec_frame _ _ seRotC_writes _ _ (fun h' => h (by simp at h' ⊢; tauto)), hw3]
    vm_simp
    have h1 : r ≠ seC := by intro e; subst e; simp at h
    simp only [Function.update_apply, h1, ↓reduceIte]
    exact f2 r (fun h' => h (by simp at h' ⊢; tauto))
  set w5 := exec N K (.mv seY rSs rT4KNK) (exec N K (.cp seY rT4KNK) w4) with hw5
  have h4 : w4 rT4KNK = encL N K (List.replicate (2 * (2 * K)) 0) := by
    rw [f4 _ (by decide), hT.t4KNK]
  have a5 : w5 seY = encL N K (matL Y) ∧ w5 rSs = encL N K rest ∧
      w5 seQ = w4 seQ ∧ w5 rTW = w rTW := by
    rw [hw5]; vm_simp
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, h4, f4 rSs (by decide), hSs,
      length_encL, List.length_replicate, f4 rTW (by decide), and_true, true_and]
    have hl : (matL Y).length = 2 * (2 * K) := by simp; ring
    rw [shiftIn_encL' _ _ (List.length_replicate)]
    exact ⟨takeD_encL _ _ hl, drop_encL _ _ hl⟩
  obtain ⟨a5, b5, c5, d5⟩ := a5
  have T5 : MulTmpl N K w5 := hT.of_writes fun q hq => by
    rw [hw5]; vm_simp
    have h1 : q ≠ seY := by intro e; subst e; simp at hq
    have h2 : q ≠ rSs := by intro e; subst e; simp at hq
    simp only [Function.update_apply, h1, h2, ↓reduceIte]
    exact f4 q (by revert q; decide)
  obtain ⟨m6, T6⟩ := exec_seMapC hK w5 ((L.map (seRowAut (w rKc).length
    (w rPw2).length)).rotate (L.length - (w rPw2).length)) Y
    (by rw [d5, hn, List.length_rotate, List.length_map]) (by rw [c5, r3]) a5 T5
  refine ⟨?_, ?_, ?_⟩
  · rw [exec_cp, Function.update_self, m6]
  · rw [exec_cp, Function.update_of_ne (by decide), exec_writes _ _ _ (by decide), b5]
  · exact T6.of_writes fun q hq => by
      rw [exec_cp, Function.update_of_ne (by intro e; subst e; simp at hq)]

/-- The registers the step keeps: the caller's `0 … 28` but `2, 4, 12, 13`, and the templates. -/
def seKeep (r : Fin 64) : Bool :=
  (decide (r.val < 29) && !([2, 4, 12, 13] : List ℕ).contains r.val) || r == rKc ||
    decide (57 ≤ r.val)

theorem seSA_keep : ∀ r : Fin 64, seKeep r = true → seSA.writes r = false := by decide

/-- Row `0` of `rMOut` into `seO`. -/
def seRow0C : Code := .seq (.cp seO rT2KNK) (.mv seO rMOut rT2KNK)

theorem exec_seRow0C (w : St) (M : Fin 2 → Fin 2 × Fin K → Rq N K)
    (hO : w rMOut = encL N K (matL M)) (hT : MulTmpl N K w) :
    exec N K seRow0C w seO = encL N K (vecL (M 0)) := by
  have h2 := hT.t2KNK
  unfold seRow0C
  vm_simp
  simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, h2, hO, length_encL,
    List.length_replicate, matL_rows]
  rw [shiftIn_encL' _ _ (List.length_replicate), takeD_encL _ _ (length_vecL _)]

/-! ### Phases (b), (c): `σ^{2^t}(A)` and the digit row -/

/-- Phases (b), (c). -/
def seSB : Code :=
  .seq (.cp rMA seA) <| .seq (.cp rP rPw2) <| .seq (.rep rP aStep) <| .seq (.cp rMAd rSs) <|
  .seq mulPKC <| .seq (.cp rSs rMAd) <| .seq seRow0C <| .seq (.cp seQ seSl) <|
  .seq seAddTC (.cp seSl seQ)

theorem seSB_keep : ∀ r : Fin 64, seKeep r = true → seSB.writes r = false := by decide

theorem exec_seSB (hN : 0 < N) (hK : 0 < K) (w : St) (A : Fin 2 → Fin 2 × Fin K → Rq N K)
    (Ad : DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (rest : List (Rq N K))
    (L : List (Fin 2 × Fin K → Rq N K)) (hA : w seA = encL N K (matL A))
    (hSs : w rSs = encL N K (adL Ad ++ rest)) (hSl : w seSl = encL N K (seRows L))
    (hn : (w rTW).length = L.length) (hp : (w rPw2).length < L.length)
    (hk : 0 < (w rKc).length) (hT : MulTmpl N K w) :
    exec N K seSB w rMA = encL N K (matL (seMatAut (w rKc).length (w rPw2).length A)) ∧
    exec N K seSB w seSl = encL N K (seRows (seAddAt L (w rPw2).length
      (mulPKm (seMatAut (w rKc).length (w rPw2).length A) Ad 0))) ∧
    exec N K seSB w rSs = encL N K rest ∧ MulTmpl N K (exec N K seSB w) := by
  unfold seSB
  simp only [exec_seq]
  generalize hW1 : exec N K (.cp rP rPw2) (exec N K (.cp rMA seA) w) = W1
  have f1 : ∀ r : Fin 64, r ≠ rP → r ≠ rMA → W1 r = w r := fun r h1 h2 => by
    rw [← hW1]; vm_simp; simp [Function.update_apply, h1, h2]
  have T1 : MulTmpl N K W1 := hT.of_writes fun q hq => f1 q (by intro e; subst e; simp at hq)
    (by intro e; subst e; simp at hq)
  obtain ⟨r2, T2⟩ := exec_aRep hN hK W1 A (by rw [← hW1]; vm_simp; simp [Function.update_apply, hA])
    (by rw [f1 _ (by decide) (by decide)]; exact hk) T1
  have e1 : (W1 rP).length = (w rPw2).length := by rw [← hW1]; vm_simp; simp [Function.update_apply]
  rw [e1, f1 _ (by decide) (by decide)] at r2
  generalize hW2 : exec N K (.rep rP aStep) W1 = W2
  rw [hW2] at r2 T2
  have f2 : ∀ r : Fin 64, r.val < 32 → r ≠ rP → W2 r = w r := fun r h h' => by
    rw [← hW2, exec_writes _ _ _ (by simp [Code.writes, Ne.symm h', aStep_writes_lt r h]),
      f1 r h' (by intro e; subst e; simp at h)]
  generalize hW3 : exec N K (.cp rMAd rSs) W2 = W3
  have T3 : MulTmpl N K W3 := T2.of_writes fun q hq => by
    rw [← hW3, exec_cp, Function.update_of_ne (by intro e; subst e; simp at hq)]
  obtain ⟨m4, n4⟩ := exec_mulPKC hK W3 (seMatAut (w rKc).length (w rPw2).length A) Ad rest
    (by rw [← hW3, exec_cp, Function.update_of_ne (by decide), r2]; rfl)
    (by rw [← hW3, exec_cp, Function.update_self, f2 _ (by decide) (by decide), hSs]) T3
  generalize hW4 : exec N K mulPKC W3 = W4
  rw [hW4] at m4 n4
  have T4 : MulTmpl N K W4 := T3.of_writes fun q hq => by
    rw [← hW4]; exact exec_writes _ _ _ (mulPKC_writes_ge q hq)
  have f4 : ∀ r : Fin 64, (r.val < 32 ∧ r ≠ rP) → r ≠ rMAd → W4 r = w r := fun r h h' => by
    rw [← hW4, exec_writes _ _ _ (by revert r; decide), ← hW3, exec_cp, Function.update_of_ne h',
      f2 r h.1 h.2]
  generalize hW5 : exec N K seRow0C (exec N K (.cp rSs rMAd) W4) = W5
  have o5 : W5 seO = encL N K (vecL (mulPKm (seMatAut (w rKc).length (w rPw2).length A) Ad 0)) := by
    rw [← hW5]
    exact exec_seRow0C _ _ (by rw [exec_cp, Function.update_of_ne (by decide), m4])
      (T4.of_writes fun q hq => by rw [exec_cp, Function.update_of_ne (by intro e; subst e; simp at hq)])
  have f5 : ∀ r : Fin 64, (r.val < 32 ∧ r ≠ rP ∧ r ≠ rSs) → W5 r = w r := fun r h => by
    rw [← hW5, exec_writes _ _ _ (by revert r; decide), exec_cp, Function.update_of_ne h.2.2,
      f4 r ⟨h.1, h.2.1⟩ (by intro e; subst e; simp at h)]
  have s5 : W5 rSs = encL N K rest := by
    rw [← hW5, exec_writes _ _ _ (by decide), exec_cp, Function.update_self, n4]
  have T5 : MulTmpl N K W5 := T4.of_writes fun q hq => by
    rw [← hW5, exec_writes _ _ _ (by revert q; decide), exec_cp,
      Function.update_of_ne (by intro e; subst e; simp at hq)]
  have ma5 : W5 rMA = encL N K (matL (seMatAut (w rKc).length (w rPw2).length A)) := by
    rw [← hW5, exec_writes _ _ _ (by decide), exec_cp, Function.update_of_ne (by decide),
      ← hW4, exec_writes _ _ _ mulPKC_writes_rMA, ← hW3, exec_cp, Function.update_of_ne (by decide),
      r2]; rfl
  generalize hW6 : exec N K (.cp seQ seSl) W5 = W6
  have g6 : ∀ r : Fin 64, r ≠ seQ → W6 r = W5 r := fun r h => by
    rw [← hW6, exec_cp, Function.update_of_ne h]
  have hn6 : (W6 rTW).length = L.length := by rw [g6 _ (by decide), f5 _ (by decide), hn]
  have hp6 : (W6 rPw2).length < L.length := by rw [g6 _ (by decide), f5 _ (by decide)]; exact hp
  have hq6 : W6 seQ = encL N K (seRows L) := by
    rw [← hW6, exec_cp, Function.update_self, f5 _ (by decide), hSl]
  have T6 : MulTmpl N K W6 := T5.of_writes fun q hq => g6 q (by intro e; subst e; simp at hq)
  have a7 := exec_seAddTC hK W6 _ L hn6 hp6 hq6 (by rw [g6 _ (by decide), o5]) T6
  have p6 : (W6 rPw2).length = (w rPw2).length := by
    rw [← hW6, exec_cp, Function.update_of_ne (by decide), f5 _ (by decide)]
  rw [p6] at a7
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [exec_cp, Function.update_of_ne (by decide), se_exec_frame _ _ seAddTC_writes _ _ (by decide),
      ← hW6, exec_cp, Function.update_of_ne (by decide), ma5]
  · rw [exec_cp, Function.update_self, a7]
  · rw [exec_cp, Function.update_of_ne (by decide), se_exec_frame _ _ seAddTC_writes _ _ (by decide),
      ← hW6, exec_cp, Function.update_of_ne (by decide), s5]
  · refine T5.of_writes fun q hq => ?_
    rw [exec_cp, Function.update_of_ne (by intro e; subst e; simp at hq),
      se_exec_frame _ _ seAddTC_writes _ _ (by revert q; decide), ← hW6, exec_cp,
      Function.update_of_ne (by intro e; subst e; simp at hq)]

/-! ### Phase (d): the payload and the `C_{g_t}` row -/

/-- `seMu := σ_g^{|rP|}(seMu)`. -/
def seMuAutC : Code := .rep rP (.op .aut seMu seMu rKc)

theorem exec_seMuAutC (hN : 0 < N) (hK : 0 < K) (w : St) (μ : Rq N K)
    (hM : w seMu = encRM N K μ) (hk : 0 < (w rKc).length) :
    exec N K seMuAutC w seMu = encRM N K ((aut N (w rKc).length)^[(w rP).length] μ) := by
  have key := exec_rep_inv2 (N := N) (K := K) rP (.op .aut seMu seMu rKc) (by decide)
    (fun m w' => w' seMu = encRM N K ((aut N (w rKc).length)^[m] μ)) w (by simp [hM]) ?_
  · exact key
  · intro m w' _ hP _ hfr
    have hk' : w' rKc = w rKc := hfr _ (by decide) (by decide)
    vm_simp
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, hP, hk', takeD_encRM,
      canonW_aut hK hN hk, Function.iterate_succ_apply']

/-- Phase (d). -/
def seSD : Code :=
  .seq (.cp rP rPw2) <| .seq seMuAutC <| .seq (.cp seV rT2KNK) <| .seq (.mv seV rSs rT2KNK) <|
  .seq seScaleC <| .seq (.cp seQ seSl) <| .seq seAddTC (.cp seSl seQ)

theorem seSD_keep : ∀ r : Fin 64, seKeep r = true → seSD.writes r = false := by decide

theorem exec_seSD (hN : 0 < N) (hK : 0 < K) (w : St) (μ : Rq N K) (v : Fin 2 × Fin K → Rq N K)
    (rest : List (Rq N K)) (L : List (Fin 2 × Fin K → Rq N K)) (hM : w seMu = encRM N K μ)
    (hSs : w rSs = encL N K (vecL v ++ rest)) (hSl : w seSl = encL N K (seRows L))
    (hn : (w rTW).length = L.length) (hp : (w rPw2).length < L.length)
    (hk : 0 < (w rKc).length) (hT : MulTmpl N K w) :
    exec N K seSD w seMu = encRM N K ((aut N (w rKc).length)^[(w rPw2).length] μ) ∧
    exec N K seSD w seSl = encL N K (seRows (seAddAt L (w rPw2).length
      (seRowSmul ((aut N (w rKc).length)^[(w rPw2).length] μ) v))) ∧
    exec N K seSD w rSs = encL N K rest ∧ exec N K seSD w rMA = w rMA ∧
    MulTmpl N K (exec N K seSD w) := by
  unfold seSD
  simp only [exec_seq]
  generalize hW1 : exec N K (.cp rP rPw2) w = W1
  have f1 : ∀ r : Fin 64, r ≠ rP → W1 r = w r := fun r h => by
    rw [← hW1, exec_cp, Function.update_of_ne h]
  have m2 := exec_seMuAutC hN hK W1 μ (by rw [f1 _ (by decide), hM])
    (by rw [f1 _ (by decide)]; exact hk)
  have e1 : (W1 rP).length = (w rPw2).length := by rw [← hW1, exec_cp, Function.update_self]
  rw [e1, f1 _ (by decide)] at m2
  generalize hW2 : exec N K seMuAutC W1 = W2
  rw [hW2] at m2
  have f2 : ∀ r : Fin 64, r ≠ rP → r ≠ seMu → W2 r = w r := fun r h h' => by
    rw [← hW2, exec_writes _ _ _ (by simp [seMuAutC, Code.writes, Ne.symm h, Ne.symm h']), f1 r h]
  generalize hW3 : exec N K (.mv seV rSs rT2KNK) (exec N K (.cp seV rT2KNK) W2) = W3
  have f3 : ∀ r : Fin 64, r ≠ rP → r ≠ seMu → r ≠ seV → r ≠ rSs → W3 r = w r := fun r h h' h1 h2 => by
    rw [← hW3]; vm_simp; simp only [Function.update_apply, h1, h2, ↓reduceIte]; exact f2 r h h'
  have h2 : W2 rT2KNK = encL N K (List.replicate (2 * K) 0) := by
    rw [f2 _ (by decide) (by decide), hT.t2KNK]
  have v3 : W3 seV = encL N K (vecL v) ∧ W3 rSs = encL N K rest := by
    rw [← hW3]; vm_simp
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, h2, f2 rSs (by decide) (by decide),
      hSs, length_encL, List.length_replicate]
    rw [shiftIn_encL' _ _ (List.length_replicate)]
    exact ⟨takeD_encL _ _ (length_vecL _), drop_encL _ _ (length_vecL _)⟩
  have T3 : MulTmpl N K W3 := hT.of_writes fun q hq => f3 q (by intro e; subst e; simp at hq)
    (by intro e; subst e; simp at hq) (by intro e; subst e; simp at hq)
    (by intro e; subst e; simp at hq)
  have mu3 : W3 seMu = encRM N K ((aut N (w rKc).length)^[(w rPw2).length] μ) := by
    rw [← hW3]; vm_simp; simp [Function.update_apply, m2]
  have o4 := exec_seScaleC hK W3 _ v v3.1 mu3 T3
  generalize hW4 : exec N K (.cp seQ seSl) (exec N K seScaleC W3) = W4
  have g4 : ∀ r : Fin 64, r ∉ [seO, seE, rX0, seV] → r ≠ seQ → W4 r = W3 r := fun r h h' => by
    rw [← hW4, exec_cp, Function.update_of_ne h', se_exec_frame _ _ seScaleC_writes _ _ h]
  have T4 : MulTmpl N K W4 := T3.of_writes fun q hq => g4 q (by revert q; decide)
    (by intro e; subst e; simp at hq)
  have a5 := exec_seAddTC hK W4 _ L
    (by rw [g4 _ (by decide) (by decide), f3 _ (by decide) (by decide) (by decide) (by decide), hn])
    (by rw [g4 _ (by decide) (by decide), f3 _ (by decide) (by decide) (by decide) (by decide)]; exact hp)
    (by rw [← hW4, exec_cp, Function.update_self, se_exec_frame _ _ seScaleC_writes _ _ (by decide),
      f3 _ (by decide) (by decide) (by decide) (by decide), hSl])
    (by rw [← hW4, exec_cp, Function.update_of_ne (by decide), o4]) T4
  rw [g4 _ (by decide) (by decide), f3 _ (by decide) (by decide) (by decide) (by decide)] at a5
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [exec_cp, Function.update_of_ne (by decide), se_exec_frame _ _ seAddTC_writes _ _ (by decide),
      g4 _ (by decide) (by decide), mu3]
  · rw [exec_cp, Function.update_self, a5]
  · rw [exec_cp, Function.update_of_ne (by decide), se_exec_frame _ _ seAddTC_writes _ _ (by decide),
      g4 _ (by decide) (by decide), v3.2]
  · rw [exec_cp, Function.update_of_ne (by decide), se_exec_frame _ _ seAddTC_writes _ _ (by decide),
      g4 _ (by decide) (by decide), f3 _ (by decide) (by decide) (by decide) (by decide)]
  · refine T4.of_writes fun q hq => ?_
    rw [exec_cp, Function.update_of_ne (by intro e; subst e; simp at hq),
      se_exec_frame _ _ seAddTC_writes _ _ (by revert q; decide)]

/-! ### Phases (e), (f): `A'` and the `H_{g_t}` row -/

/-- Phases (e), (f). -/
def seSE : Code :=
  .seq (.cp rMAd rSs) <| .seq mulPKC <| .seq (.cp rSs rMAd) <| .seq (.cp rMA rMOut) <|
  .seq (.cp rGX rT2KNK) <| .seq (.mv rGX rSs rT2KNK) <| .seq (.app rGX rGX) <| .seq ginvMulC <|
  .seq seRow0C <| .seq (.cp seQ seSl) <| .seq seAdd0C (.cp seSl seQ)

theorem seSE_keep : ∀ r : Fin 64, seKeep r = true → seSE.writes r = false := by decide

theorem exec_seSE (hK : 0 < K) (w : St) (B : Fin 2 → Fin 2 × Fin K → Rq N K)
    (Ad : DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (v : Fin 2 × Fin K → Rq N K)
    (rest : List (Rq N K)) (L : List (Fin 2 × Fin K → Rq N K)) (hB : w rMA = encL N K (matL B))
    (hSs : w rSs = encL N K (adL Ad ++ (vecL v ++ rest))) (hSl : w seSl = encL N K (seRows L))
    (hn : (w rTW).length = L.length) (hL0 : 0 < L.length) (hT : MulTmpl N K w) :
    exec N K seSE w rMA = encL N K (matL (mulPKm B Ad)) ∧
    exec N K seSE w seSl = encL N K (seRows (seAddAt L 0 (seGRow v (mulPKm B Ad)))) ∧
    exec N K seSE w rSs = encL N K rest ∧ MulTmpl N K (exec N K seSE w) := by
  unfold seSE
  simp only [exec_seq]
  generalize hW1 : exec N K (.cp rMAd rSs) w = W1
  have T1 : MulTmpl N K W1 := hT.of_writes fun q hq => by
    rw [← hW1, exec_cp, Function.update_of_ne (by intro e; subst e; simp at hq)]
  obtain ⟨m2, n2⟩ := exec_mulPKC hK W1 B Ad (vecL v ++ rest)
    (by rw [← hW1, exec_cp, Function.update_of_ne (by decide), hB])
    (by rw [← hW1, exec_cp, Function.update_self, hSs]) T1
  generalize hW2 : exec N K mulPKC W1 = W2
  rw [hW2] at m2 n2
  have T2 : MulTmpl N K W2 := T1.of_writes fun q hq => by
    rw [← hW2]; exact exec_writes _ _ _ (mulPKC_writes_ge q hq)
  have f2 : ∀ r : Fin 64, r.val < 33 → r ≠ rMAd → W2 r = w r := fun r h h' => by
    rw [← hW2, exec_writes _ _ _ (by revert r; decide), ← hW1, exec_cp, Function.update_of_ne h']
  generalize hW3 : exec N K (.app rGX rGX) (exec N K (.mv rGX rSs rT2KNK) (exec N K (.cp rGX rT2KNK)
    (exec N K (.cp rMA rMOut) (exec N K (.cp rSs rMAd) W2)))) = W3
  have a3 : W3 rGX = encL N K (matL fun _ => v) ∧ W3 rMA = encL N K (matL (mulPKm B Ad)) ∧
      W3 rSs = encL N K rest ∧ W3 seSl = w seSl ∧ W3 rTW = w rTW := by
    rw [← hW3]; vm_simp
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, T2.t2KNK, n2, m2, length_encL,
      List.length_replicate, f2 seSl (by decide) (by decide), f2 rTW (by decide) (by decide),
      and_true, true_and, matL_const, encL_append]
    rw [shiftIn_encL' _ _ (List.length_replicate)]
    simp [length_vecL]
  have T3 : MulTmpl N K W3 := T2.of_writes fun q hq => by
    rw [← hW3]; vm_simp
    have h1 : q ≠ rGX := by intro e; subst e; simp at hq
    have h2 : q ≠ rSs := by intro e; subst e; simp at hq
    have h3 : q ≠ rMA := by intro e; subst e; simp at hq
    have h4 : q ≠ rMAd := by intro e; subst e; simp at hq
    simp [Function.update_apply, h1, h2, h3, h4]
  have g4 := exec_ginvMulC hK W3 (fun _ => v) (mulPKm B Ad) a3.1 a3.2.1 T3
  generalize hW4 : exec N K ginvMulC W3 = W4
  rw [hW4] at g4
  have T4 : MulTmpl N K W4 := T3.of_writes fun q hq => by
    rw [← hW4]; exact exec_writes _ _ _ (ginvMulC_writes_ge q hq)
  have o5 := exec_seRow0C W4 _ g4 T4
  generalize hW5 : exec N K (.cp seQ seSl) (exec N K seRow0C W4) = W5
  have g5 : ∀ r : Fin 64, (r.val < 33 ∨ r = seO) → r ≠ seQ → r ≠ seO → W5 r = W3 r := fun r h h1 h2 => by
    rw [← hW5, exec_cp, Function.update_of_ne h1, exec_writes _ _ _ (by
      unfold seRow0C; simp [Code.writes, Ne.symm h2]
      intro e; subst e; simp at h), ← hW4, exec_writes _ _ _ (by
        rcases h with h | h
        · exact ginvMulC_writes_lt r h
        · exact absurd h h2)]
  have T5 : MulTmpl N K W5 := T4.of_writes fun q hq => by
    rw [← hW5, exec_cp, Function.update_of_ne (by intro e; subst e; simp at hq)]
    exact exec_writes _ _ _ (by unfold seRow0C; revert q; decide)
  have a6 := exec_seAdd0C hK W5 _ L (by rw [g5 _ (by decide) (by decide) (by decide), a3.2.2.2.2, hn])
    hL0 (by rw [← hW5, exec_cp, Function.update_self, exec_writes _ _ _ (by decide), ← hW4,
      exec_writes _ _ _ (by decide), a3.2.2.2.1, hSl])
    (by rw [← hW5, exec_cp, Function.update_of_ne (by decide), o5]) T5
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [exec_cp, Function.update_of_ne (by decide), se_exec_frame _ _ seAdd0C_writes _ _ (by decide),
      g5 _ (by decide) (by decide) (by decide), a3.2.1]
  · rw [exec_cp, Function.update_self, a6]; rfl
  · rw [exec_cp, Function.update_of_ne (by decide), se_exec_frame _ _ seAdd0C_writes _ _ (by decide),
      g5 _ (by decide) (by decide) (by decide), a3.2.2.1]
  · refine T5.of_writes fun q hq => ?_
    rw [exec_cp, Function.update_of_ne (by intro e; subst e; simp at hq),
      se_exec_frame _ _ seAdd0C_writes _ _ (by revert q; decide)]

/-! ### Phase (g): the new public matrix -/

/-- Phase (g). -/
def seSG : Code :=
  .seq (.cp rGX rT4KNK) <| .seq (.mv rGX rSs rT4KNK) <| .seq ginvMulC (.cp seA rMOut)

theorem seSG_keep : ∀ r : Fin 64, seKeep r = true → seSG.writes r = false := by decide

theorem exec_seSG (hK : 0 < K) (w : St) (B H : Fin 2 → Fin 2 × Fin K → Rq N K)
    (rest : List (Rq N K)) (hB : w rMA = encL N K (matL B))
    (hSs : w rSs = encL N K (matL H ++ rest)) (hT : MulTmpl N K w) :
    exec N K seSG w seA = encL N K (matL (ginvMulm H B)) ∧
    exec N K seSG w rSs = encL N K rest ∧ exec N K seSG w seSl = w seSl ∧
    exec N K seSG w seMu = w seMu ∧ MulTmpl N K (exec N K seSG w) := by
  unfold seSG
  simp only [exec_seq]
  generalize hW1 : exec N K (.mv rGX rSs rT4KNK) (exec N K (.cp rGX rT4KNK) w) = W1
  have hl : (matL H).length = 2 * (2 * K) := by simp; ring
  have a1 : W1 rGX = encL N K (matL H) ∧ W1 rSs = encL N K rest ∧ W1 rMA = encL N K (matL B) ∧
      W1 seSl = w seSl ∧ W1 seMu = w seMu := by
    rw [← hW1]; vm_simp
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, hT.t4KNK, hSs, hB, length_encL,
      List.length_replicate, and_true, true_and]
    rw [shiftIn_encL' _ _ (List.length_replicate)]
    exact ⟨takeD_encL _ _ hl, drop_encL _ _ hl⟩
  have T1 : MulTmpl N K W1 := hT.of_writes fun q hq => by
    rw [← hW1]; vm_simp
    have h1 : q ≠ rGX := by intro e; subst e; simp at hq
    have h2 : q ≠ rSs := by intro e; subst e; simp at hq
    simp [Function.update_apply, h1, h2]
  have g2 := exec_ginvMulC hK W1 H B a1.1 a1.2.2.1 T1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [exec_cp, Function.update_self, g2]
  · rw [exec_cp, Function.update_of_ne (by decide), exec_writes _ _ _ (by decide), a1.2.1]
  · rw [exec_cp, Function.update_of_ne (by decide), exec_writes _ _ _ (by decide), a1.2.2.2.1]
  · rw [exec_cp, Function.update_of_ne (by decide), exec_writes _ _ _ (by decide), a1.2.2.2.2]
  · exact T1.of_writes fun q hq => by
      rw [exec_cp, Function.update_of_ne (by intro e; subst e; simp at hq)]
      exact exec_writes _ _ _ (ginvMulC_writes_ge q hq)

/-! ### The step -/

/-- **One step of the paired chain** (the bit `t` is set). -/
def seAutStep : Code := .seq seSA <| .seq seSB <| .seq seSD <| .seq seSE seSG

theorem seAutStep_keep : ∀ r : Fin 64, seKeep r = true → seAutStep.writes r = false := by decide

theorem seKeep_frame {c : Code} (hc : ∀ r : Fin 64, seKeep r = true → c.writes r = false) (w : St)
    {r : Fin 64} (hr : seKeep r = true) : exec N K c w r = w r := exec_writes _ _ _ (hc r hr)

theorem MulTmpl.of_keep {c : Code} (hc : ∀ r : Fin 64, seKeep r = true → c.writes r = false)
    {w : St} (hT : MulTmpl N K w) : MulTmpl N K (exec N K c w) :=
  hT.of_writes fun q hq => seKeep_frame hc w (by revert q; decide)

theorem length_seAddAt (L : List (Fin 2 × Fin K → Rq N K)) (p : ℕ) (v : Fin 2 × Fin K → Rq N K) :
    (seAddAt L p v).length = L.length := List.length_modify _ _ _

/-- The step, unfolded. -/
theorem seStep_eq (g t : ℕ) (D : SeBits N K) (A : Fin 2 → Fin 2 × Fin K → Rq N K) (μ : Rq N K)
    (L : List (Fin 2 × Fin K → Rq N K)) :
    seStep g D t (A, μ, L) =
      (ginvMulm (D.Hf t) (mulPKm (seMatAut g (2 ^ t) A) (D.Aa t)), (aut N g)^[2 ^ t] μ,
        seAddAt (seAddAt (seAddAt (((L.map (seRowAut g (2 ^ t))).rotate (L.length - 2 ^ t)).map
          fun v => seGRow v (D.gc t)) (2 ^ t) (mulPKm (seMatAut g (2 ^ t) A) (D.ad t) 0)) (2 ^ t)
          (seRowSmul ((aut N g)^[2 ^ t] μ) (D.crow t))) 0
          (seGRow (D.hrow t) (mulPKm (seMatAut g (2 ^ t) A) (D.Aa t)))) := rfl

/-- **`seAutStep` computes `seStep`.** -/
theorem exec_seAutStep (hN : 0 < N) (hK : 0 < K) (w : St) (g t : ℕ) (D : SeBits N K)
    (A : Fin 2 → Fin 2 × Fin K → Rq N K) (μ : Rq N K) (L : List (Fin 2 × Fin K → Rq N K))
    (rest : List (Rq N K)) (hA : w seA = encL N K (matL A)) (hM : w seMu = encRM N K μ)
    (hSl : w seSl = encL N K (seRows L)) (hSs : w rSs = encL N K (seRec D t ++ rest))
    (hn : (w rTW).length = L.length) (hp : (w rPw2).length = 2 ^ t) (hpL : 2 ^ t < L.length)
    (hk : (w rKc).length = g) (hg : 0 < g) (hT : MulTmpl N K w) :
    exec N K seAutStep w seA = encL N K (matL (seStep g D t (A, μ, L)).1) ∧
    exec N K seAutStep w seMu = encRM N K (seStep g D t (A, μ, L)).2.1 ∧
    exec N K seAutStep w seSl = encL N K (seRows (seStep g D t (A, μ, L)).2.2) ∧
    exec N K seAutStep w rSs = encL N K rest ∧ MulTmpl N K (exec N K seAutStep w) := by
  rw [seStep_eq]
  unfold seAutStep
  simp only [exec_seq]
  have hk' : 0 < (w rKc).length := by rw [hk]; exact hg
  -- (a)
  obtain ⟨a1, a2, a3⟩ := exec_seSA hN hK w L (D.gc t)
    (adL (D.ad t) ++ (vecL (D.crow t) ++ (adL (D.Aa t) ++ (vecL (D.hrow t) ++ (matL (D.Hf t) ++
      rest))))) hn hSl (by rw [hSs, seRec]; simp only [List.append_assoc]) hk' hT
  generalize hW1 : exec N K seSA w = W1
  rw [hW1] at a1 a2 a3
  have k1 : ∀ r : Fin 64, seKeep r = true → W1 r = w r := fun r hr => by
    rw [← hW1]; exact seKeep_frame seSA_keep w hr
  rw [hk, hp] at a1
  generalize hL1 : ((L.map (seRowAut g (2 ^ t))).rotate (L.length - 2 ^ t)).map
    (fun v => seGRow v (D.gc t)) = L1 at a1
  have hL1l : L1.length = L.length := by rw [← hL1]; simp
  have hA1 : W1 seA = encL N K (matL A) := by
    rw [← hW1, exec_writes _ _ _ (by decide), hA]
  have hM1 : W1 seMu = encRM N K μ := by rw [← hW1, exec_writes _ _ _ (by decide), hM]
  -- (b), (c)
  obtain ⟨b1, b2, b3, b4⟩ := exec_seSB hN hK W1 A (D.ad t) _ L1 hA1 a2 a1
    (by rw [k1 _ (by decide), hn, hL1l]) (by rw [k1 _ (by decide), hp, hL1l]; exact hpL)
    (by rw [k1 _ (by decide)]; exact hk') a3
  generalize hW2 : exec N K seSB W1 = W2
  rw [hW2] at b1 b2 b3 b4
  rw [k1 _ (by decide), k1 _ (by decide), hk, hp] at b1 b2
  have k2 : ∀ r : Fin 64, seKeep r = true → W2 r = w r := fun r hr => by
    rw [← hW2, seKeep_frame seSB_keep W1 hr, k1 r hr]
  have hM2 : W2 seMu = encRM N K μ := by rw [← hW2, exec_writes _ _ _ (by decide), hM1]
  generalize hL2 : seAddAt L1 (2 ^ t) (mulPKm (seMatAut g (2 ^ t) A) (D.ad t) 0) = L2 at b2
  have hL2l : L2.length = L.length := by rw [← hL2, length_seAddAt, hL1l]
  -- (d)
  obtain ⟨d1, d2, d3, d4, d5⟩ := exec_seSD hN hK W2 μ (D.crow t) _ L2 hM2 b3 b2
    (by rw [k2 _ (by decide), hn, hL2l]) (by rw [k2 _ (by decide), hp, hL2l]; exact hpL)
    (by rw [k2 _ (by decide)]; exact hk') b4
  generalize hW3 : exec N K seSD W2 = W3
  rw [hW3] at d1 d2 d3 d4 d5
  rw [k2 _ (by decide), k2 _ (by decide), hk, hp] at d1 d2
  have k3 : ∀ r : Fin 64, seKeep r = true → W3 r = w r := fun r hr => by
    rw [← hW3, seKeep_frame seSD_keep W2 hr, k2 r hr]
  generalize hL3 : seAddAt L2 (2 ^ t) (seRowSmul ((aut N g)^[2 ^ t] μ) (D.crow t)) = L3 at d2
  have hL3l : L3.length = L.length := by rw [← hL3, length_seAddAt, hL2l]
  -- (e), (f)
  obtain ⟨e1, e2, e3, e4⟩ := exec_seSE hK W3 (seMatAut g (2 ^ t) A) (D.Aa t) (D.hrow t) _ L3
    (by rw [d4, b1]) d3 d2 (by rw [k3 _ (by decide), hn, hL3l]) (by rw [hL3l]; omega) d5
  generalize hW4 : exec N K seSE W3 = W4
  rw [hW4] at e1 e2 e3 e4
  -- (g)
  obtain ⟨g1, g2, g3, g4, g5⟩ := exec_seSG hK W4 _ (D.Hf t) rest e1 e3 e4
  have hM4 : W4 seMu = encRM N K ((aut N g)^[2 ^ t] μ) := by
    rw [← hW4, exec_writes _ _ _ (by decide), d1]
  exact ⟨g1, by rw [g4, hM4], by rw [g3, e2], g2, g5⟩

/-! ### The chain -/

/-- The master stream of the per-bit records. -/
@[simp, vmreg] abbrev seSW : Fin 64 := 1
/-- The template of one record (`(32 K³ + 12 K) · N K` bits). -/
@[simp, vmreg] abbrev seTRec : Fin 64 := 26

/-- The stream of the records of the bits `t ∈ l`. -/
def seStream (D : SeBits N K) (l : List ℕ) : List (Rq N K) := l.flatMap (seRec D)

/-- Before the branch: the digit `t` of `j` in `rS2`. -/
def seChPre : Code := .seq (.cp rS rTb) <| .seq (.tl rS) <| .seq (.drop rS rCt) (.op .dig rS2 rJ rS)

/-- One round `t` of the paired chain. -/
def seChBody : Code :=
  .seq seChPre <| .seq (.ifb rS2 seAutStep (.drop rSs seTRec)) (.app rPw2 rPw2)

/-- **The paired chain**: `b` rounds from `(seA, seMu, seSl)`. -/
def seChainC : Code :=
  .seq (.cp rSs seSW) <| .seq (.cp rPw2 rBit1) <| .seq (.cp rCt rTb) (.rep rCt seChBody)

theorem seChBody_writes_rCt : seChBody.writes rCt = false := by decide

theorem seChBody_keep : ∀ r : Fin 64, seKeep r = true → r ≠ rPw2 → seChBody.writes r = false := by
  decide

theorem seChainC_keep : ∀ r : Fin 64, seKeep r = true → r ≠ rPw2 → r ≠ rCt →
    seChainC.writes r = false := by decide

theorem length_seStep (g t : ℕ) (D : SeBits N K)
    (st : (Fin 2 → Fin 2 × Fin K → Rq N K) × Rq N K × List (Fin 2 × Fin K → Rq N K)) :
    (seStep g D t st).2.2.length = st.2.2.length := by
  obtain ⟨A, μ, L⟩ := st
  rw [seStep_eq]; simp [length_seAddAt]

theorem length_bitChain_seStep (g : ℕ) (D : SeBits N K)
    (st : (Fin 2 → Fin 2 × Fin K → Rq N K) × Rq N K × List (Fin 2 × Fin K → Rq N K)) :
    ∀ t j, (bitChain (seStep g D) t j st).2.2.length = st.2.2.length
  | 0, _ => rfl
  | t + 1, j => by
    simp only [bitChain]
    split_ifs
    · rw [length_seStep, length_bitChain_seStep g D st t j]
    · exact length_bitChain_seStep g D st t j

/-- The registers the chain reads. -/
structure SeChainIn (w : St) (g b n : ℕ) (D : SeBits N K) : Prop where
  sw : w seSW = encL N K (seStream D (List.range b))
  tb : w rTb = List.replicate b false
  bit1 : w rBit1 = [false]
  trec : (w seTRec).length = (32 * K ^ 3 + 12 * K) * (N * K)
  tw : (w rTW).length = n
  kc : (w rKc).length = g
  tm : MulTmpl N K w

theorem SeChainIn.of_keep {w w' : St} {g b n : ℕ} {D : SeBits N K} (h : SeChainIn w g b n D)
    (hw : ∀ r : Fin 64, seKeep r = true → r ≠ rPw2 → r ≠ rCt → w' r = w r) :
    SeChainIn w' g b n D :=
  ⟨by rw [hw _ (by decide) (by decide) (by decide)]; exact h.sw,
   by rw [hw _ (by decide) (by decide) (by decide)]; exact h.tb,
   by rw [hw _ (by decide) (by decide) (by decide)]; exact h.bit1,
   by rw [hw _ (by decide) (by decide) (by decide)]; exact h.trec,
   by rw [hw _ (by decide) (by decide) (by decide)]; exact h.tw,
   by rw [hw _ (by decide) (by decide) (by decide)]; exact h.kc,
   h.tm.of_writes fun q hq => hw q (by revert q; decide) (by intro e; subst e; simp at hq)
     (by intro e; subst e; simp at hq)⟩

/-- **The chain loop.** -/
theorem exec_seChainLoop (hN : 0 < N) (hK : 0 < K) (w : St) (g b j : ℕ) (hg : 0 < g)
    (hj : j < 2 ^ K - 1) (D : SeBits N K) (A : Fin 2 → Fin 2 × Fin K → Rq N K) (μ : Rq N K)
    (L : List (Fin 2 × Fin K → Rq N K)) (hbL : 2 ^ b ≤ L.length) (hin : SeChainIn w g b L.length D)
    (hJ : w rJ = encRM N K (j : Rq N K)) (hA : w seA = encL N K (matL A))
    (hM : w seMu = encRM N K μ) (hSl : w seSl = encL N K (seRows L))
    (hSs : w rSs = encL N K (seStream D (List.range b))) (hP2 : w rPw2 = [false])
    (hCt : w rCt = List.replicate b false) :
    exec N K (.rep rCt seChBody) w seA = encL N K (matL (bitChain (seStep g D) b j (A, μ, L)).1) ∧
    exec N K (.rep rCt seChBody) w seMu = encRM N K (bitChain (seStep g D) b j (A, μ, L)).2.1 ∧
    exec N K (.rep rCt seChBody) w seSl =
      encL N K (seRows (bitChain (seStep g D) b j (A, μ, L)).2.2) ∧
    MulTmpl N K (exec N K (.rep rCt seChBody) w) := by
  have key := exec_rep_inv2 (N := N) (K := K) rCt seChBody seChBody_writes_rCt
    (fun t w' => w' seA = encL N K (matL (bitChain (seStep g D) t j (A, μ, L)).1) ∧
      w' seMu = encRM N K (bitChain (seStep g D) t j (A, μ, L)).2.1 ∧
      w' seSl = encL N K (seRows (bitChain (seStep g D) t j (A, μ, L)).2.2) ∧
      w' rSs = encL N K (seStream D ((List.range b).drop t)) ∧
      w' rPw2 = List.replicate (2 ^ t) false ∧ MulTmpl N K w') w
    ⟨hA, hM, hSl, by simp [hSs], by simp [hP2], hin.tm⟩ ?_
  · rw [hCt, List.length_replicate] at key
    exact ⟨key.1, key.2.1, key.2.2.1, key.2.2.2.2.2⟩
  · intro t w' ht hP hc hfr
    rw [hCt, List.length_replicate] at ht
    rw [hCt, List.drop_replicate] at hc
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hP
    have fr : ∀ r : Fin 64, seKeep r = true → r ≠ rPw2 → r ≠ rCt → w' r = w r := fun r hr h1 h2 =>
      hfr r (seChBody_keep r hr h1) h2
    have hin' := hin.of_keep fr
    rw [drop_range_succ ht] at p4
    simp only [seStream, List.flatMap_cons] at p4
    unfold seChBody
    rw [exec_seq, exec_seq]
    generalize hW1 : exec N K seChPre (Function.update w' rCt (w' rCt).tail) = W1
    have f1 : ∀ r : Fin 64, r ≠ rS → r ≠ rS2 → r ≠ rCt → W1 r = w' r := fun r h1 h2 h3 => by
      rw [← hW1, exec_writes _ _ _ (by unfold seChPre; simp [Code.writes, Ne.symm h1, Ne.symm h2]),
        Function.update_of_ne h3]
    have q1 : W1 rS2 = encRM N K (binaryDigit (j : Rq N K) t) := by
      rw [← hW1]; unfold seChPre; vm_simp
      simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, fr rTb (by decide) (by decide)
        (by decide), hin.tb, fr rJ (by decide) (by decide) (by decide), hJ, hc,
        takeD_encRM, List.length_drop, List.length_tail, List.length_replicate]
      rw [show b - 1 - (b - t - 1) = t by omega, canonW_dig hK]
    have hT1 : MulTmpl N K W1 := p6.of_writes fun q hq => f1 q (by intro e; subst e; simp at hq)
      (by intro e; subst e; simp at hq) (by intro e; subst e; simp at hq)
    rw [exec_ifb, q1, hd_dig_natCast hN hK j t hj]
    have hlen := length_bitChain_seStep g D (A, μ, L) t j
    by_cases hbit : j.testBit t
    · rw [if_pos hbit]
      have ht2 : 2 ^ t < L.length := lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) ht) hbL
      obtain ⟨s1, s2, s3, s4, s5⟩ := exec_seAutStep hN hK W1 g t D _ _ _ _
        (by rw [f1 _ (by decide) (by decide) (by decide), p1])
        (by rw [f1 _ (by decide) (by decide) (by decide), p2])
        (by rw [f1 _ (by decide) (by decide) (by decide), p3])
        (by rw [f1 _ (by decide) (by decide) (by decide), p4])
        (by rw [f1 _ (by decide) (by decide) (by decide), hin'.tw, hlen])
        (by rw [f1 _ (by decide) (by decide) (by decide), p5, List.length_replicate])
        (by rw [hlen]; exact ht2)
        (by rw [f1 _ (by decide) (by decide) (by decide), hin'.kc]) hg hT1
      have k2 : exec N K seAutStep W1 rPw2 = List.replicate (2 ^ t) false := by
        rw [seKeep_frame seAutStep_keep W1 (by decide), f1 _ (by decide) (by decide) (by decide), p5]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [exec_app, Function.update_of_ne (by decide), s1]; simp only [bitChain, hbit, ↓reduceIte]
      · rw [exec_app, Function.update_of_ne (by decide), s2]; simp only [bitChain, hbit, ↓reduceIte]
      · rw [exec_app, Function.update_of_ne (by decide), s3]; simp only [bitChain, hbit, ↓reduceIte]
      · rw [exec_app, Function.update_of_ne (by decide), s4]; rfl
      · rw [exec_app, Function.update_self, k2, ← List.replicate_add, pow_succ, mul_two]
      · exact s5.of_writes fun q hq => by
          rw [exec_app, Function.update_of_ne (by intro e; subst e; simp at hq)]
    · rw [if_neg hbit]
      have hl : (encL N K (seRec D t)).length = (W1 seTRec).length := by
        rw [f1 _ (by decide) (by decide) (by decide), hin'.trec, length_encL, length_seRec]
      have hW : ∀ r : Fin 64, r ≠ rPw2 → r ≠ rSs → r ≠ rS → r ≠ rS2 → r ≠ rCt →
          exec N K (.app rPw2 rPw2) (exec N K (.drop rSs seTRec) W1) r = w' r := by
        intro r h1 h2 h3 h4 h5
        rw [exec_app, Function.update_of_ne h1, exec_drop, if_neg (by decide),
          Function.update_of_ne h2, f1 r h3 h4 h5]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hW seA (by decide) (by decide) (by decide) (by decide) (by decide), p1]
        simp only [bitChain, hbit, Bool.false_eq_true, ↓reduceIte]
      · rw [hW seMu (by decide) (by decide) (by decide) (by decide) (by decide), p2]
        simp only [bitChain, hbit, Bool.false_eq_true, ↓reduceIte]
      · rw [hW seSl (by decide) (by decide) (by decide) (by decide) (by decide), p3]
        simp only [bitChain, hbit, Bool.false_eq_true, ↓reduceIte]
      · rw [exec_app, Function.update_of_ne (by decide), exec_drop, if_neg (by decide),
          Function.update_self, f1 rSs (by decide) (by decide) (by decide), p4, encL_append, ← hl,
          List.drop_left]
        rfl
      · rw [exec_app, Function.update_self, exec_drop, if_neg (by decide),
          Function.update_of_ne (by decide), f1 rPw2 (by decide) (by decide) (by decide), p5,
          ← List.replicate_add, pow_succ, mul_two]
      · refine hT1.of_writes fun q hq => ?_
        rw [exec_app, Function.update_of_ne (by intro e; subst e; simp at hq), exec_drop,
          if_neg (by decide), Function.update_of_ne (by intro e; subst e; simp at hq)]

/-- **`seChainC` computes the paired chain** `bitChain (seStep g D) b j (A, μ, L)`. -/
theorem exec_seChainC (hN : 0 < N) (hK : 0 < K) (w : St) (g b j : ℕ) (hg : 0 < g)
    (hj : j < 2 ^ K - 1) (D : SeBits N K) (A : Fin 2 → Fin 2 × Fin K → Rq N K) (μ : Rq N K)
    (L : List (Fin 2 × Fin K → Rq N K)) (hbL : 2 ^ b ≤ L.length) (hin : SeChainIn w g b L.length D)
    (hJ : w rJ = encRM N K (j : Rq N K)) (hA : w seA = encL N K (matL A))
    (hM : w seMu = encRM N K μ) (hSl : w seSl = encL N K (seRows L)) :
    exec N K seChainC w seA = encL N K (matL (bitChain (seStep g D) b j (A, μ, L)).1) ∧
    exec N K seChainC w seMu = encRM N K (bitChain (seStep g D) b j (A, μ, L)).2.1 ∧
    exec N K seChainC w seSl = encL N K (seRows (bitChain (seStep g D) b j (A, μ, L)).2.2) ∧
    MulTmpl N K (exec N K seChainC w) := by
  unfold seChainC
  simp only [exec_seq]
  generalize hW1 : exec N K (.cp rCt rTb) (exec N K (.cp rPw2 rBit1) (exec N K (.cp rSs seSW) w)) = W1
  have f1 : ∀ r : Fin 64, r ≠ rCt → r ≠ rPw2 → r ≠ rSs → W1 r = w r := fun r h1 h2 h3 => by
    rw [← hW1]; vm_simp; simp [Function.update_apply, h1, h2, h3]
  exact exec_seChainLoop hN hK W1 g b j hg hj D A μ L hbL
    (hin.of_keep fun r hr h1 h2 => f1 r h2 h1 (by intro e; subst e; simp [seKeep] at hr))
    (by rw [f1 _ (by decide) (by decide) (by decide), hJ])
    (by rw [f1 _ (by decide) (by decide) (by decide), hA])
    (by rw [f1 _ (by decide) (by decide) (by decide), hM])
    (by rw [f1 _ (by decide) (by decide) (by decide), hSl])
    (by rw [← hW1]; vm_simp; simp [Function.update_apply, hin.sw])
    (by rw [← hW1]; vm_simp; simp [Function.update_apply, hin.bit1])
    (by rw [← hW1]; vm_simp; simp [Function.update_apply, hin.tb])

end AdvancedEncryption.ExpLUT.Prog
