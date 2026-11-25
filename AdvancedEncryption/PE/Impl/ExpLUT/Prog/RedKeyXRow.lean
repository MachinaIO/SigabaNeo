import PE.Impl.ExpLUT.Prog.RedKeyMatVec

/-!
# `KGsim` on the VM (package G2, item 5, module 5a): one row of `X` (generic VM kernel)

Lemma 11's matrices `V_j` act **row by row**: a row `v` of `V_j` becomes the row
`v · G̃⁻¹(σ_j(H_a⁽¹⁾)) − (J̃_{η_{j,a}})_ℓ` of `V_{j·a}`, and the correction row is either `0` or a
unit row `e_{c'}`. This file computes, for one start row `v₀` (`2K` ring words), the rows
`v_j`, `j < 2^b`, of all `V_j` by the doubling recursion of `vRounds` (round `t` appends the
images of the first `2^t` rows under the step along `g_t`), and appends the first `K` entries of
every `v_j` to register `16`, i.e. one row of `X` (`simX`) in the order of `ZIdx = Fin W × Fin τ`.

* `xsubC`: `rxV := rxV − rxE` entrywise (`exec_xsubC`);
* `xStepBody`: one step `v ↦ ginvMulm (mask v) Y 0 − [cur = tag] e`, then `Y := σ_g(Y)`
  (`exec_xStepBody`); the mask keeps the entries `(0, i)` (`G̃⁻¹` has zero rows on `(1, i)`);
* `xRoundBody`, `xRowC`, **`exec_xRowC`**: `16 := 16 ++ ⋯ take K (v_j) ⋯`, `v_j = xRow … b j`.

Everything is generic over `N K` (`Rq N K`); the identification with `simX` is in `RedKeyX`.
-/

set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)

/-! ### Registers (`0 … 28`, avoiding `8`, `14`, `16`) -/

/-- The queue of the current rows `v_j`, `j < 2^t`. -/
@[simp, vmreg] abbrev rxQ : Fin 64 := 0
/-- The rows still to step in the current round. -/
@[simp, vmreg] abbrev rxQs : Fin 64 := 1
/-- The new row. -/
@[simp, vmreg] abbrev rxV : Fin 64 := 2
/-- The helper stream of the current row. -/
@[simp, vmreg] abbrev rxHs : Fin 64 := 3
/-- Unary `2^t`. -/
@[simp, vmreg] abbrev rxP : Fin 64 := 4
/-- The step counter of a round. -/
@[simp, vmreg] abbrev rxPc : Fin 64 := 5
/-- Unary `t`. -/
@[simp, vmreg] abbrev rxT : Fin 64 := 6
/-- Unary `j` (the row index inside a round). -/
@[simp, vmreg] abbrev rxJ : Fin 64 := 7
/-- The comparison word `0^t 1 0^j`. -/
@[simp, vmreg] abbrev rxCur : Fin 64 := 9
/-- The comparison flag. -/
@[simp, vmreg] abbrev rxF : Fin 64 := 10
/-- The tag of the row (input). -/
@[simp, vmreg] abbrev rxTag : Fin 64 := 11
/-- The correction row `e` (input). -/
@[simp, vmreg] abbrev rxE : Fin 64 := 12
/-- The start row `v₀` (input). -/
@[simp, vmreg] abbrev rxV0 : Fin 64 := 13
/-- The helper matrices `H_k`, `k ∈ Fin b × Fin 2` (input). -/
@[simp, vmreg] abbrev rxH : Fin 64 := 15
/-- Unary `b` (input). -/
@[simp, vmreg] abbrev rxTb : Fin 64 := 17
/-- The round counter. -/
@[simp, vmreg] abbrev rxRc : Fin 64 := 18
/-- `[true]` (input). -/
@[simp, vmreg] abbrev rxTru : Fin 64 := 19
/-- `[false]` (input). -/
@[simp, vmreg] abbrev rxFal : Fin 64 := 20
/-- Unary `2^b` (input). -/
@[simp, vmreg] abbrev rxW : Fin 64 := 21
/-- The output counter. -/
@[simp, vmreg] abbrev rxOc : Fin 64 := 22
/-- A temporary word. -/
@[simp, vmreg] abbrev rxTmp : Fin 64 := 23

variable {N K : ℕ}

/-! ### Rows and their words -/

/-- The word list of a row (in the order of `Enum (Fin 2 × Fin K)`). -/
def vecL (v : Fin 2 × Fin K → Rq N K) : List (Rq N K) := (Enum.list (α := Fin 2 × Fin K)).map v

@[simp] theorem length_vecL (v : Fin 2 × Fin K → Rq N K) : (vecL v).length = 2 * K := by
  simp [vecL, length_enum_col]

theorem vecL_eq (v : Fin 2 × Fin K → Rq N K) :
    vecL v = (List.finRange K).map (fun i => v (0, i)) ++ (List.finRange K).map (fun i => v (1, i)) :=
  rowL_eq v

theorem matL_rows (A : Fin 2 → Fin 2 × Fin K → Rq N K) : matL A = vecL (A 0) ++ vecL (A 1) := by
  rw [matL, enum_fin2]; simp [vecL]

theorem vecL_sub (a b : Fin 2 × Fin K → Rq N K) :
    vecL (fun c => a c - b c) = List.zipWith (· - ·) (vecL a) (vecL b) := by
  simp only [vecL]; rw [List.zipWith_map, List.zipWith_self]

/-- The row with only its entries `(0, i)`, as the row `0` of a `2 × 2K` matrix. -/
def maskM (v : Fin 2 × Fin K → Rq N K) : Fin 2 → Fin 2 × Fin K → Rq N K :=
  fun a c => if a = 0 ∧ c.1 = 0 then v c else 0

theorem matL_maskM (v : Fin 2 × Fin K → Rq N K) :
    matL (maskM v) = (vecL v).take K ++ (List.replicate (2 * K) 0 ++ List.replicate K 0) := by
  rw [matL_eq, vecL_eq, List.take_left' (by simp)]
  simp only [segL, maskM, List.append_assoc]
  have e : 2 * K = K + K := by omega
  simp [List.map_const', e]
  omega

/-! ### `rxV := rxV − rxE` -/

/-- One entry. -/
def xsBody : Code :=
  .seq (.cp rX0 rZ) <| .seq (.mvR rX0 rRo0) <| .seq (.cp rX1 rZ) <| .seq (.mvR rX1 rRo1) <|
  .seq (.op .sub rX0 rX0 rX1) (.app rxV rX0)

/-- **`rxV := rxV − rxE`** entrywise (`2K` entries). -/
def xsubC : Code :=
  .seq (.cp rRo0 rxV) <| .seq (.cp rRo1 rxE) <| .seq (.clr rxV) <| .seq (.cp rCi rT2K)
    (.rep rCi xsBody)

theorem xsBody_writes_rCi : xsBody.writes rCi = false := by decide

theorem exec_xsLoop (hK : 0 < K) (w : St) (l1 l2 : List (Rq N K)) (n : ℕ)
    (h1 : l1.length = n) (h2 : l2.length = n) (hA : w rRo0 = encL N K l1)
    (hO : w rRo1 = encL N K l2) (hC : w rCi = List.replicate n false) (hAcc : w rxV = [])
    (hZ : w rZ = encRM N K 0) :
    exec N K (.rep rCi xsBody) w rxV = encL N K (List.zipWith (· - ·) l1 l2) := by
  have key := exec_rep_inv (N := N) (K := K) rCi xsBody xsBody_writes_rCi
    (fun m w' => w' rRo0 = encL N K (l1.drop m) ∧ w' rRo1 = encL N K (l2.drop m) ∧
      w' rxV = encL N K (List.zipWith (· - ·) (l1.take m) (l2.take m)) ∧ w' rZ = encRM N K 0) w
    ⟨by simp [hA], by simp [hO], by simp [hAcc], hZ⟩ ?_
  · rw [hC, List.length_replicate] at key
    rw [key.2.2.1, List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
  · intro m w' hm hP _
    rw [hC, List.length_replicate] at hm
    obtain ⟨p1, p2, p3, p4⟩ := hP
    have e1 := drop_cons_getElem l1 (show m < l1.length by omega)
    have e2 := drop_cons_getElem l2 (show m < l2.length by omega)
    have t1 := take_succ_getElem l1 (show m < l1.length by omega)
    have t2 := take_succ_getElem l2 (show m < l2.length by omega)
    rw [e1, encL_cons] at p1
    rw [e2, encL_cons] at p2
    unfold xsBody
    vm_simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [Function.update_apply, p1, p4]
    · simp [Function.update_apply, p2, p4]
    · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, p1, p2, p3, p4,
        shiftIn_encRM', takeD_encRM_append, takeD_encRM, canonW_sub hK, t1, t2]
      rw [List.zipWith_append (by simp; omega), encL_append]
      simp
    · simp [Function.update_apply, p4]

/-- **`rxV := rxV − rxE`.** -/
theorem exec_xsubC (hK : 0 < K) (w : St) (a e : Fin 2 × Fin K → Rq N K)
    (hV : w rxV = encL N K (vecL a)) (hE : w rxE = encL N K (vecL e)) (hT : MulTmpl N K w) :
    exec N K xsubC w rxV = encL N K (vecL fun c => a c - e c) := by
  rw [vecL_sub]
  unfold xsubC
  simp only [exec_seq]
  refine exec_xsLoop hK _ _ _ (2 * K) (by simp) (by simp) ?_ ?_ ?_ ?_ ?_ <;>
    (vm_simp; simp [hV, hE, hT.t2K, hT.z])

theorem xsubC_writes : ∀ r : Fin 64, xsubC.writes r = true →
    r ∈ [rRo0, rRo1, rxV, rCi, rX0, rX1] := by decide

/-! ### One step -/

/-- The comparison word of round `t`, row `j`: `0^t 1 0^j`. -/
def curW (t j : ℕ) : List Bool := List.replicate t false ++ true :: List.replicate j false

/-- **One step** at round `t`, row `j`: `v ↦ (mask v) G⁻¹(Y)` (row `0`), minus `e` when the tag
is `0^t 1 0^j`. -/
def xStep (Y : Fin 2 → Fin 2 × Fin K → Rq N K) (tag : List Bool) (e : Fin 2 × Fin K → Rq N K)
    (t j : ℕ) (v : Fin 2 × Fin K → Rq N K) : Fin 2 × Fin K → Rq N K :=
  if curW t j = tag then fun c => ginvMulm (maskM v) Y 0 c - e c else ginvMulm (maskM v) Y 0

/-- `rGX := mask(v)` from the head row of `rxQs`. -/
def xLoadC : Code :=
  .seq (.cp rGX rTKNK) <| .seq (.mv rGX rxQs rTKNK) <| .seq (.drop rxQs rTKNK) <|
  .seq (.app rGX rT2KNK) (.app rGX rTKNK)

/-- `rxV := ` row `0` of `rMOut`. -/
def xRowOutC : Code := .seq (.cp rxV rT2KNK) (.mv rxV rMOut rT2KNK)

/-- The correction: `rxV −= rxE` when `0^t 1 0^j = tag`. -/
def xCorrC : Code :=
  .seq (.cp rxCur rxT) <| .seq (.app rxCur rxTru) <| .seq (.app rxCur rxJ) <|
  .seq (.eqb rxF rxCur rxTag) (.ifb rxF xsubC .nop)

/-- **One step of a round.** -/
def xStepBody : Code :=
  .seq xLoadC <| .seq ginvMulC <| .seq xRowOutC <| .seq xCorrC <| .seq (.app rxQ rxV) <|
  .seq aStep (.app rxJ rxFal)

theorem exec_xLoadC (w : St) (a b rest : List (Rq N K)) (ha : a.length = K) (hb : b.length = K)
    (hQs : w rxQs = encL N K (a ++ b ++ rest)) (hT : MulTmpl N K w) :
    exec N K xLoadC w rGX = encL N K (a ++ (List.replicate (2 * K) 0 ++ List.replicate K 0)) ∧
    exec N K xLoadC w rxQs = encL N K rest := by
  have hTK := hT.tKNK
  have h2 := hT.t2KNK
  unfold xLoadC
  vm_simp
  simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, hTK, h2, hQs, length_encL,
    List.length_replicate]
  refine ⟨?_, ?_⟩
  · rw [shiftIn_encL' _ _ (List.length_replicate),
      show a ++ b ++ rest = a ++ (b ++ rest) by simp, takeD_encL _ _ ha]
    simp only [encL_append, List.append_assoc]
  · rw [show a ++ b ++ rest = a ++ (b ++ rest) by simp, drop_encL _ _ ha]
    exact drop_encL _ _ hb

theorem exec_xRowOutC (w : St) (M : Fin 2 → Fin 2 × Fin K → Rq N K)
    (hO : w rMOut = encL N K (matL M)) (hT : MulTmpl N K w) :
    exec N K xRowOutC w rxV = encL N K (vecL (M 0)) := by
  have h2 := hT.t2KNK
  unfold xRowOutC
  vm_simp
  simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, h2, hO, length_encL,
    List.length_replicate, matL_rows]
  rw [shiftIn_encL' _ _ (List.length_replicate), takeD_encL _ _ (length_vecL _)]

theorem hd_singleton (b : Bool) : hd [b] = b := rfl

theorem exec_xCorrC (hK : 0 < K) (w : St) (g e : Fin 2 × Fin K → Rq N K) (t j : ℕ)
    (tag : List Bool) (hV : w rxV = encL N K (vecL g)) (hE : w rxE = encL N K (vecL e))
    (hTt : w rxT = List.replicate t false) (hJ : w rxJ = List.replicate j false)
    (hTru : w rxTru = [true]) (hTag : w rxTag = tag) (hT : MulTmpl N K w) :
    exec N K xCorrC w rxV =
      encL N K (vecL (if curW t j = tag then fun c => g c - e c else g)) := by
  unfold xCorrC
  simp only [exec_seq]
  set w1 := exec N K (.eqb rxF rxCur rxTag) (exec N K (.app rxCur rxJ)
    (exec N K (.app rxCur rxTru) (exec N K (.cp rxCur rxT) w))) with hw1
  have hF : w1 rxF = [decide (curW t j = tag)] := by
    rw [hw1]; vm_simp
    simp [Function.update_apply, hTt, hTru, hJ, hTag, curW]
    congr
  have f : ∀ r : Fin 64, r ≠ rxCur → r ≠ rxF → w1 r = w r := by
    intro r h1 h2
    rw [hw1]; vm_simp
    simp [Function.update_apply, h1, h2]
  rw [exec_ifb, hF, hd_singleton]
  by_cases hc : curW t j = tag
  · simp only [hc, decide_true, ↓reduceIte]
    refine exec_xsubC hK w1 g e ?_ ?_ (hT.of_writes fun q hq => f q (by
      intro h; subst h; simp at hq) (by intro h; subst h; simp at hq))
    · rw [f _ (by decide) (by decide), hV]
    · rw [f _ (by decide) (by decide), hE]
  · simp only [hc, decide_false, ↓reduceIte, Bool.false_eq_true, exec_nop]
    rw [f _ (by decide) (by decide), hV]

theorem ginvMulC_writes_lt : ∀ r : Fin 64, r.val < 33 → ginvMulC.writes r = false := by decide
theorem ginvMulC_writes_ge : ∀ r : Fin 64, 57 ≤ r.val → ginvMulC.writes r = false := by decide
theorem aStep_writes_lt : ∀ r : Fin 64, r.val < 32 → aStep.writes r = false := by decide
theorem aStep_writes_ge : ∀ r : Fin 64, 57 ≤ r.val → aStep.writes r = false := by decide
theorem xCorrC_writes_ge : ∀ r : Fin 64, 57 ≤ r.val → xCorrC.writes r = false := by decide

/-- **One step of a round**: the head row `v` of `rxQs` is popped, its image
`xStep Y tag e t j v` is appended to `rxQ`, `Y := σ_g(Y)` (`g = |rKc|`) and `j := j + 1`. -/
theorem exec_xStepBody (hN : 0 < N) (hK : 0 < K) (w : St) (Y : Fin 2 → Fin 2 × Fin K → Rq N K)
    (v e : Fin 2 × Fin K → Rq N K) (rest Qp : List (Rq N K)) (t j : ℕ) (tag : List Bool)
    (hQs : w rxQs = encL N K (vecL v ++ rest)) (hQ : w rxQ = encL N K Qp)
    (hMA : w rMA = encL N K (matL Y)) (hTt : w rxT = List.replicate t false)
    (hJ : w rxJ = List.replicate j false) (hTru : w rxTru = [true]) (hFal : w rxFal = [false])
    (hTag : w rxTag = tag) (hE : w rxE = encL N K (vecL e)) (hk : 0 < (w rKc).length)
    (hT : MulTmpl N K w) :
    exec N K xStepBody w rxQs = encL N K rest ∧
    exec N K xStepBody w rxQ = encL N K (Qp ++ vecL (xStep Y tag e t j v)) ∧
    exec N K xStepBody w rMA = encL N K (matL fun a c => aut N (w rKc).length (Y a c)) ∧
    exec N K xStepBody w rxJ = List.replicate (j + 1) false ∧
    MulTmpl N K (exec N K xStepBody w) := by
  unfold xStepBody
  simp only [exec_seq]
  -- load
  have l := exec_xLoadC w ((vecL v).take K) ((vecL v).drop K) rest
    (by simp only [List.length_take, length_vecL]; omega)
    (by simp only [List.length_drop, length_vecL]; omega)
    (by rw [hQs, List.take_append_drop]) hT
  set w1 := exec N K xLoadC w with hw1
  have f1 : ∀ r : Fin 64, r ≠ rGX → r ≠ rxQs → w1 r = w r := by
    intro r h1 h2
    exact exec_writes _ _ _ (by unfold xLoadC; simp [Code.writes, Ne.symm h1, Ne.symm h2])
  have T1 : MulTmpl N K w1 := hT.of_writes fun q hq =>
    f1 q (by intro h; subst h; simp at hq) (by intro h; subst h; simp at hq)
  -- multiply
  have g := exec_ginvMulC hK w1 (maskM v) Y (by rw [matL_maskM, l.1])
    (by rw [f1 _ (by decide) (by decide), hMA]) T1
  set w2 := exec N K ginvMulC w1 with hw2
  have f2 : ∀ r : Fin 64, r.val < 33 → w2 r = w1 r := fun r hr =>
    exec_writes _ _ _ (ginvMulC_writes_lt r hr)
  have T2 : MulTmpl N K w2 := T1.of_writes fun q hq => exec_writes _ _ _ (ginvMulC_writes_ge q hq)
  -- the row
  have ro := exec_xRowOutC w2 _ g T2
  set w3 := exec N K xRowOutC w2 with hw3
  have f3 : ∀ r : Fin 64, r ≠ rxV → r ≠ rMOut → w3 r = w2 r := by
    intro r h1 h2
    exact exec_writes _ _ _ (by unfold xRowOutC; simp [Code.writes, Ne.symm h1, Ne.symm h2])
  have T3 : MulTmpl N K w3 := T2.of_writes fun q hq =>
    f3 q (by intro h; subst h; simp at hq) (by intro h; subst h; simp at hq)
  have e3 : ∀ r : Fin 64, r.val < 33 → r ≠ rxV → r ≠ rxQs → w3 r = w r := fun r hr hv hq => by
    rw [f3 r hv (by intro h; subst h; simp at hr), f2 r hr,
      f1 r (by intro h; subst h; simp at hr) hq]
  -- the correction
  have co := exec_xCorrC hK w3 _ e t j tag ro (by rw [e3 _ (by decide) (by decide) (by decide), hE])
    (by rw [e3 _ (by decide) (by decide) (by decide), hTt]) (by rw [e3 _ (by decide) (by decide) (by decide), hJ])
    (by rw [e3 _ (by decide) (by decide) (by decide), hTru]) (by rw [e3 _ (by decide) (by decide) (by decide), hTag]) T3
  set w4 := exec N K xCorrC w3 with hw4
  have f4 : ∀ r : Fin 64, r.val < 33 → r ≠ rxV → r ≠ rxCur → r ≠ rxF → w4 r = w3 r := by
    intro r hr h1 h2 h3
    refine exec_writes _ _ _ ?_
    revert r; decide
  have T4 : MulTmpl N K w4 := T3.of_writes fun q hq => exec_writes _ _ _ (xCorrC_writes_ge q hq)
  -- push, then `σ_g`
  set w5 := exec N K (.app rxQ rxV) w4 with hw5
  have T5 : MulTmpl N K w5 := T4.of_writes fun q hq => by
    rw [hw5, exec_app, Function.update_of_ne (by intro h; subst h; simp at hq)]
  have e5 : ∀ r : Fin 64, r.val < 33 → r ≠ rxV → r ≠ rxCur → r ≠ rxF → r ≠ rxQ → r ≠ rxQs →
      w5 r = w r := by
    intro r hr h1 h2 h3 h4 h5
    rw [hw5, exec_app, Function.update_of_ne h4, f4 r hr h1 h2 h3, e3 r hr h1 h5]
  have am := exec_autMatC hN hK w5 Y (by
      rw [show rMA = (32 : Fin 64) from rfl, e5 _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hMA])
    (by rw [e5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hk) T5
  rw [e5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] at am
  set w6 := exec N K aStep w5 with hw6
  have f6 : ∀ r : Fin 64, r.val < 32 → w6 r = w5 r := fun r hr =>
    exec_writes _ _ _ (aStep_writes_lt r hr)
  have T6 : MulTmpl N K w6 := T5.of_writes fun q hq => exec_writes _ _ _ (aStep_writes_ge q hq)
  have hMA6 : w6 rMA = encL N K (matL fun a c => aut N (w rKc).length (Y a c)) := by
    rw [hw6, aStep, exec_seq, exec_cp, Function.update_self, am.1]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [exec_app, Function.update_of_ne (by decide), f6 _ (by decide), hw5, exec_app,
      Function.update_of_ne (by decide), f4 _ (by decide) (by decide) (by decide) (by decide),
      f3 _ (by decide) (by decide), f2 _ (by decide), l.2]
  · rw [exec_app, Function.update_of_ne (by decide), f6 _ (by decide), hw5, exec_app,
      Function.update_self, f4 _ (by decide) (by decide) (by decide) (by decide), co,
      e3 _ (by decide) (by decide) (by decide), hQ, encL_append]
    rfl
  · rw [exec_app, Function.update_of_ne (by decide), hMA6]
  · rw [exec_app, Function.update_self, f6 _ (by decide),
      e5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hJ,
      f6 _ (by decide), e5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hFal,
      List.replicate_succ']
  · exact T6.of_writes fun q hq => by
      rw [exec_app, Function.update_of_ne (by intro h; subst h; simp at hq)]

/-! ### The rows `v_j` by doubling -/

/-- `σ_g^j(H)` entrywise. -/
def xY (g : ℕ) (H : Fin 2 → Fin 2 × Fin K → Rq N K) (j : ℕ) : Fin 2 → Fin 2 × Fin K → Rq N K :=
  fun a c => (aut N g)^[j] (H a c)

theorem xY_succ (g : ℕ) (H : Fin 2 → Fin 2 × Fin K → Rq N K) (j : ℕ) :
    xY g H (j + 1) = fun a c => aut N g (xY g H j a c) := by
  funext a c; simp only [xY, Function.iterate_succ_apply']

/-- **The rows `v_j` after `t` rounds** (`j < 2^t`), from the start row `v₀`; round `t` uses the
helper `Hs t`. -/
def xRow (g : ℕ) (Hs : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K) (tag : List Bool)
    (e v₀ : Fin 2 × Fin K → Rq N K) : ℕ → ℕ → Fin 2 × Fin K → Rq N K
  | 0, _ => v₀
  | t + 1, j => if j < 2 ^ t then xRow g Hs tag e v₀ t j else
      xStep (xY g (Hs t) (j - 2 ^ t)) tag e t (j - 2 ^ t) (xRow g Hs tag e v₀ t (j - 2 ^ t))

/-- The queue after `t` rounds. -/
def xQ (g : ℕ) (Hs : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K) (tag : List Bool)
    (e v₀ : Fin 2 × Fin K → Rq N K) (t : ℕ) : List (Rq N K) :=
  (List.range (2 ^ t)).flatMap fun j => vecL (xRow g Hs tag e v₀ t j)

theorem xQ_succ (g : ℕ) (Hs : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K) (tag : List Bool)
    (e v₀ : Fin 2 × Fin K → Rq N K) (t : ℕ) :
    xQ g Hs tag e v₀ (t + 1) = xQ g Hs tag e v₀ t ++ (List.range (2 ^ t)).flatMap fun j =>
      vecL (xStep (xY g (Hs t) j) tag e t j (xRow g Hs tag e v₀ t j)) := by
  unfold xQ
  rw [pow_succ, mul_two, List.range_add, List.flatMap_append, List.flatMap_map]
  congr 1
  · refine List.flatMap_congr fun j hj => ?_
    rw [List.mem_range] at hj
    simp only [xRow, hj, ↓reduceIte]
  · refine List.flatMap_congr fun j _ => ?_
    simp only [xRow, show ¬ (2 ^ t + j < 2 ^ t) by omega, ↓reduceIte, Nat.add_sub_cancel_left]

theorem xStepBody_writes_rxPc : xStepBody.writes rxPc = false := by decide

/-- **The steps of round `t`.** -/
theorem exec_xStepLoop (hN : 0 < N) (hK : 0 < K) (w : St) (g : ℕ)
    (Hs : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K) (tag : List Bool) (e v₀ : Fin 2 × Fin K → Rq N K)
    (t : ℕ) (hQs : w rxQs = encL N K (xQ g Hs tag e v₀ t))
    (hQ : w rxQ = encL N K (xQ g Hs tag e v₀ t)) (hMA : w rMA = encL N K (matL (Hs t)))
    (hTt : w rxT = List.replicate t false) (hJ : w rxJ = [])
    (hPc : (w rxPc).length = 2 ^ t) (hTru : w rxTru = [true])
    (hFal : w rxFal = [false]) (hTag : w rxTag = tag) (hE : w rxE = encL N K (vecL e))
    (hk : (w rKc).length = g) (hg : 0 < g) (hT : MulTmpl N K w) :
    exec N K (.rep rxPc xStepBody) w rxQ = encL N K (xQ g Hs tag e v₀ (t + 1)) ∧
    MulTmpl N K (exec N K (.rep rxPc xStepBody) w) := by
  have key := exec_rep_inv2 (N := N) (K := K) rxPc xStepBody xStepBody_writes_rxPc
    (fun m w' => w' rxQs = encL N K (((List.range (2 ^ t)).drop m).flatMap fun j =>
        vecL (xRow g Hs tag e v₀ t j)) ∧
      w' rxQ = encL N K (xQ g Hs tag e v₀ t ++ (List.range m).flatMap fun j =>
        vecL (xStep (xY g (Hs t) j) tag e t j (xRow g Hs tag e v₀ t j))) ∧
      w' rMA = encL N K (matL (xY g (Hs t) m)) ∧ w' rxJ = List.replicate m false ∧
      MulTmpl N K w') w
    ⟨by rw [hQs]; rfl, by simp [hQ], by rw [hMA]; rfl, by simp [hJ], hT⟩ ?_
  · rw [hPc] at key
    exact ⟨by rw [key.2.1, xQ_succ], key.2.2.2.2⟩
  · intro m w' hm hP _ hfr
    rw [hPc] at hm
    obtain ⟨p1, p2, p3, p4, p5⟩ := hP
    set W1 := Function.update w' rxPc (w' rxPc).tail with hW1
    have u : ∀ r : Fin 64, r ≠ rxPc → W1 r = w' r := fun r h => Function.update_of_ne h _ _
    have fr : ∀ r : Fin 64, xStepBody.writes r = false → r ≠ rxPc → W1 r = w r := fun r h h' =>
      by rw [u r h', hfr r h h']
    rw [drop_range_cons hm, List.flatMap_cons] at p1
    obtain ⟨s1, s2, s3, s4, s5⟩ := exec_xStepBody hN hK W1 (xY g (Hs t) m) (xRow g Hs tag e v₀ t m) e
      _ _ t m tag (by rw [u _ (by decide), p1]) (by rw [u _ (by decide), p2])
      (by rw [u _ (by decide), p3]) (by rw [fr _ (by decide) (by decide), hTt]) (by rw [u _ (by decide), p4])
      (by rw [fr _ (by decide) (by decide), hTru]) (by rw [fr _ (by decide) (by decide), hFal])
      (by rw [fr _ (by decide) (by decide), hTag]) (by rw [fr _ (by decide) (by decide), hE])
      (by rw [fr _ (by decide) (by decide), hk]; exact hg)
      (p5.of_writes fun q hq => u q (by intro e; subst e; simp at hq))
    refine ⟨s1, ?_, ?_, s4, s5⟩
    · rw [s2, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    · rw [s3, fr _ (by decide) (by decide), hk, xY_succ]

/-- Before the steps of a round. -/
def xRoundPre : Code :=
  .seq (.cp rMA rT4KNK) <| .seq (.mv rMA rxHs rT4KNK) <| .seq (.drop rxHs rT4KNK) <|
  .seq (.clr rxJ) <| .seq (.cp rxQs rxQ) (.cp rxPc rxP)

/-- **One round**: `Y := H_{(t,0)}` (popped from `rxHs`, which also loses `H_{(t,1)}`), the
`2^t` steps, then `2^t := 2^{t+1}`, `t := t + 1`. -/
def xRoundBody : Code :=
  .seq xRoundPre <| .seq (.rep rxPc xStepBody) <| .seq (.app rxP rxP) (.app rxT rxFal)

/-- The helper stream: for every round `t < b`, the matrix of round `t`, then a second matrix
(skipped). -/
def xHL (Hs Hi : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K) (l : List ℕ) : List (Rq N K) :=
  l.flatMap fun t => matL (Hs t) ++ matL (Hi t)

theorem xRoundBody_writes_rxRc : xRoundBody.writes rxRc = false := by decide
theorem xRoundBody_writes_ge : ∀ r : Fin 64, 57 ≤ r.val → xRoundBody.writes r = false := by
  decide

/-- **The rounds**: after `b` rounds, `rxQ` holds the rows `v_j`, `j < 2^b`. -/
theorem exec_xRounds (hN : 0 < N) (hK : 0 < K) (w : St) (g b : ℕ)
    (Hs Hi : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K) (tag : List Bool) (e v₀ : Fin 2 × Fin K → Rq N K)
    (hQ : w rxQ = encL N K (vecL v₀)) (hHs : w rxHs = encL N K (xHL Hs Hi (List.range b)))
    (hTt : w rxT = []) (hP : (w rxP).length = 1) (hRc : w rxRc = List.replicate b false)
    (hTru : w rxTru = [true]) (hFal : w rxFal = [false]) (hTag : w rxTag = tag)
    (hE : w rxE = encL N K (vecL e)) (hk : (w rKc).length = g) (hg : 0 < g)
    (hT : MulTmpl N K w) :
    exec N K (.rep rxRc xRoundBody) w rxQ = encL N K (xQ g Hs tag e v₀ b) ∧
    MulTmpl N K (exec N K (.rep rxRc xRoundBody) w) := by
  have key := exec_rep_inv2 (N := N) (K := K) rxRc xRoundBody xRoundBody_writes_rxRc
    (fun t w' => w' rxQ = encL N K (xQ g Hs tag e v₀ t) ∧
      w' rxHs = encL N K (xHL Hs Hi ((List.range b).drop t)) ∧
      w' rxT = List.replicate t false ∧ (w' rxP).length = 2 ^ t ∧ MulTmpl N K w') w
    ⟨by rw [hQ]; simp [xQ, xRow], by simp [hHs], by simp [hTt], by simp [hP], hT⟩ ?_
  · rw [hRc, List.length_replicate] at key
    exact ⟨key.1, key.2.2.2.2⟩
  · intro t w' ht hI _ hfr
    rw [hRc, List.length_replicate] at ht
    obtain ⟨p1, p2, p3, p4, p5⟩ := hI
    set W1 := Function.update w' rxRc (w' rxRc).tail with hW1
    have u : ∀ r : Fin 64, r ≠ rxRc → W1 r = w' r := fun r h => Function.update_of_ne h _ _
    have fr : ∀ r : Fin 64, xRoundBody.writes r = false → r ≠ rxRc → W1 r = w r := fun r h h' =>
      by rw [u r h', hfr r h h']
    have T1 : MulTmpl N K W1 := p5.of_writes fun q hq => u q (by intro e; subst e; simp at hq)
    rw [drop_range_cons ht, xHL, List.flatMap_cons, List.append_assoc] at p2
    have h4 := T1.t4KNK
    have hlen : (matL (Hs t)).length = 2 * (2 * K) := by simp; ring
    have hlen' : (matL (Hi t)).length = 2 * (2 * K) := by simp; ring
    set W2 := exec N K xRoundPre W1 with hW2
    have q : W2 rMA = encL N K (matL (Hs t)) ∧
        W2 rxHs = encL N K (xHL Hs Hi ((List.range b).drop (t + 1))) ∧
        W2 rxQs = encL N K (xQ g Hs tag e v₀ t) ∧ W2 rxQ = encL N K (xQ g Hs tag e v₀ t) ∧
        W2 rxJ = [] ∧ (W2 rxPc).length = 2 ^ t ∧ W2 rxT = List.replicate t false := by
      rw [hW2]; unfold xRoundPre; vm_simp
      simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, h4, u _ (by decide : rxHs ≠ rxRc),
        u _ (by decide : rxQ ≠ rxRc), u _ (by decide : rxP ≠ rxRc), u _ (by decide : rxT ≠ rxRc),
        p1, p2, p3, p4, length_encL, List.length_replicate]
      refine ⟨?_, ?_, trivial, trivial, trivial, trivial, trivial⟩
      · rw [shiftIn_encL' _ _ (List.length_replicate), takeD_encL _ _ hlen]
      · rw [drop_encL _ _ hlen, drop_encL _ _ hlen']; rfl
    obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := q
    have f2 : ∀ r : Fin 64, xRoundPre.writes r = false → W2 r = W1 r := fun r h =>
      exec_writes _ _ _ h
    have T2 : MulTmpl N K W2 := T1.of_writes fun q hq => f2 q (by revert q; decide)
    have lp := exec_xStepLoop hN hK W2 g Hs tag e v₀ t q3 q4 q1 q7 q5 q6
      (by rw [f2 _ (by decide), fr _ (by decide) (by decide), hTru])
      (by rw [f2 _ (by decide), fr _ (by decide) (by decide), hFal])
      (by rw [f2 _ (by decide), fr _ (by decide) (by decide), hTag])
      (by rw [f2 _ (by decide), fr _ (by decide) (by decide), hE])
      (by rw [f2 _ (by decide), fr _ (by decide) (by decide), hk]) hg T2
    set W3 := exec N K (.rep rxPc xStepBody) W2 with hW3
    have f3 : ∀ r : Fin 64, (Code.rep rxPc xStepBody).writes r = false → W3 r = W2 r :=
      fun r h => exec_writes _ _ _ h
    unfold xRoundBody
    simp only [exec_seq, exec_app]
    rw [← hW2, ← hW3]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact lp.1
    · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), f3 _ (by decide), q2]
    · rw [Function.update_self, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        f3 _ (by decide), q7, f3 _ (by decide), f2 _ (by decide), fr _ (by decide) (by decide),
        hFal, List.replicate_succ']
    · rw [Function.update_of_ne (by decide), Function.update_self, List.length_append,
        f3 _ (by decide), f2 _ (by decide), u _ (by decide), p4, pow_succ]; ring
    · exact lp.2.of_writes fun q hq => by
        rw [Function.update_of_ne (by intro h; subst h; simp at hq),
          Function.update_of_ne (by intro h; subst h; simp at hq)]

/-! ### The output and the row routine -/

/-- One output row: the first `K` entries of the head row of `rxQ` are appended to `16`. -/
def xOutBody : Code :=
  .seq (.cp rxTmp rTKNK) <| .seq (.mv rxTmp rxQ rTKNK) <| .seq (.app 16 rxTmp) (.drop rxQ rTKNK)

theorem xOutBody_writes_rxOc : xOutBody.writes rxOc = false := by decide

theorem exec_xOutLoop (w : St) (vs : List (Fin 2 × Fin K → Rq N K)) (pre : List Bool)
    (h16 : w 16 = pre) (hQ : w rxQ = encL N K (vs.flatMap vecL))
    (hOc : (w rxOc).length = vs.length) (hT : MulTmpl N K w) :
    exec N K (.rep rxOc xOutBody) w 16 = pre ++ encL N K (vs.flatMap fun v => (vecL v).take K) := by
  have key := exec_rep_inv2 (N := N) (K := K) rxOc xOutBody xOutBody_writes_rxOc
    (fun m w' => w' 16 = pre ++ encL N K ((vs.take m).flatMap fun v => (vecL v).take K) ∧
      w' rxQ = encL N K ((vs.drop m).flatMap vecL)) w ⟨by simp [h16], by simp [hQ]⟩ ?_
  · rw [hOc, List.take_length] at key
    exact key.1
  · intro m w' hm hP _ hfr
    rw [hOc] at hm
    obtain ⟨p1, p2⟩ := hP
    have hTK : w' rTKNK = encL N K (List.replicate K 0) := by
      rw [hfr _ (by decide) (by decide), hT.tKNK]
    have hlen : ((vecL (vs[m]'hm)).take K).length = K := by
      simp only [List.length_take, length_vecL]; omega
    have hlen' : ((vecL (vs[m]'hm)).drop K).length = K := by
      simp only [List.length_drop, length_vecL]; omega
    rw [drop_cons_getElem vs hm, List.flatMap_cons,
      ← List.take_append_drop K (vecL (vs[m]'hm)), List.append_assoc] at p2
    unfold xOutBody
    vm_simp
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, hTK, p1, p2, length_encL,
      List.length_replicate]
    refine ⟨?_, ?_⟩
    · rw [shiftIn_encL' _ _ (List.length_replicate), takeD_encL _ _ hlen,
        take_succ_getElem vs hm, List.flatMap_append, encL_append, List.append_assoc]
      simp
    · rw [← List.drop_drop, drop_encL _ _ hlen, drop_encL _ _ hlen']

/-- **One row of `X`**: from `v₀` (`rxV0`), the helpers (`rxH`), the tag (`rxTag`) and the
correction row (`rxE`), `16 := 16 ++ ⋯ take K (v_j) ⋯` for `j < 2^b`. -/
def xRowC : Code :=
  .seq (.cp rxQ rxV0) <| .seq (.clr rxT) <| .seq (.cp rxP rxTru) <| .seq (.cp rxHs rxH) <|
  .seq (.cp rxRc rxTb) <| .seq (.rep rxRc xRoundBody) <| .seq (.cp rxOc rxW) (.rep rxOc xOutBody)

theorem wf_xRowC : xRowC.WFc := by repeat constructor

/-- **The registers `xRowC` writes**: its work registers and the library's (`≥ 29`, below the
templates), and register `16`. -/
theorem xRowC_writes : ∀ r : Fin 64, xRowC.writes r = true →
    r ∈ [rxQ, rxQs, rxV, rxHs, rxP, rxPc, rxT, rxJ, rxCur, rxF, rxRc, rxOc, rxTmp, 16] ∨
      (29 ≤ r.val ∧ r.val < 57 ∧ r ≠ rKc) := by
  decide

theorem xRowC_writes_ge : ∀ r : Fin 64, 57 ≤ r.val → xRowC.writes r = false := by decide

/-- The output of one row: the first `K` entries of every `v_j`, `j < 2^b`. -/
def xOut (g : ℕ) (Hs : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K) (tag : List Bool)
    (e v₀ : Fin 2 × Fin K → Rq N K) (b : ℕ) : List (Rq N K) :=
  (List.range (2 ^ b)).flatMap fun j => (vecL (xRow g Hs tag e v₀ b j)).take K

/-- **The row routine.** -/
theorem exec_xRowC (hN : 0 < N) (hK : 0 < K) (w : St) (g b : ℕ)
    (Hs Hi : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K) (tag : List Bool) (e v₀ : Fin 2 × Fin K → Rq N K)
    (hV0 : w rxV0 = encL N K (vecL v₀)) (hH : w rxH = encL N K (xHL Hs Hi (List.range b)))
    (hTb : w rxTb = List.replicate b false) (hTru : w rxTru = [true]) (hFal : w rxFal = [false])
    (hTag : w rxTag = tag) (hE : w rxE = encL N K (vecL e)) (hk : (w rKc).length = g)
    (hg : 0 < g) (hW : (w rxW).length = 2 ^ b) (hT : MulTmpl N K w) :
    exec N K xRowC w 16 = w 16 ++ encL N K (xOut g Hs tag e v₀ b) ∧
    MulTmpl N K (exec N K xRowC w) := by
  unfold xRowC
  simp only [exec_seq]
  set W1 := exec N K (.cp rxRc rxTb) (exec N K (.cp rxHs rxH) (exec N K (.cp rxP rxTru)
    (exec N K (.clr rxT) (exec N K (.cp rxQ rxV0) w)))) with hW1
  have f1 : ∀ r : Fin 64, r ≠ rxQ → r ≠ rxT → r ≠ rxP → r ≠ rxHs → r ≠ rxRc → W1 r = w r := by
    intro r h1 h2 h3 h4 h5
    rw [hW1]; simp only [exec_cp, exec_clr]
    rw [Function.update_of_ne h5, Function.update_of_ne h4, Function.update_of_ne h3,
      Function.update_of_ne h2, Function.update_of_ne h1]
  have T1 : MulTmpl N K W1 := hT.of_writes fun q hq => f1 q
    (by intro h; subst h; simp at hq) (by intro h; subst h; simp at hq)
    (by intro h; subst h; simp at hq) (by intro h; subst h; simp at hq)
    (by intro h; subst h; simp at hq)
  have rd := exec_xRounds hN hK W1 g b Hs Hi tag e v₀
    (by rw [hW1]; vm_simp; simp [Function.update_apply, hV0])
    (by rw [hW1]; vm_simp; simp [Function.update_apply, hH])
    (by rw [hW1]; vm_simp; simp [Function.update_apply])
    (by rw [hW1]; vm_simp; simp [Function.update_apply, hTru])
    (by rw [hW1]; vm_simp; simp [Function.update_apply, hTb])
    (by rw [f1 _ (by decide) (by decide) (by decide) (by decide) (by decide), hTru])
    (by rw [f1 _ (by decide) (by decide) (by decide) (by decide) (by decide), hFal])
    (by rw [f1 _ (by decide) (by decide) (by decide) (by decide) (by decide), hTag])
    (by rw [f1 _ (by decide) (by decide) (by decide) (by decide) (by decide), hE])
    (by rw [f1 _ (by decide) (by decide) (by decide) (by decide) (by decide), hk]) hg T1
  set W2 := exec N K (.rep rxRc xRoundBody) W1 with hW2
  have f2 : ∀ r : Fin 64, (Code.rep rxRc xRoundBody).writes r = false → W2 r = W1 r :=
    fun r h => exec_writes _ _ _ h
  set W3 := exec N K (.cp rxOc rxW) W2 with hW3
  have T3 : MulTmpl N K W3 := rd.2.of_writes fun q hq => by
    rw [hW3, exec_cp, Function.update_of_ne (by intro h; subst h; simp at hq)]
  have o := exec_xOutLoop W3 ((List.range (2 ^ b)).map (xRow g Hs tag e v₀ b)) (w 16)
    (by rw [hW3, exec_cp, Function.update_of_ne (by decide), f2 _ (by decide),
      f1 _ (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by rw [hW3, exec_cp, Function.update_of_ne (by decide), rd.1, xQ, List.flatMap_map])
    (by rw [hW3, exec_cp, Function.update_self, f2 _ (by decide),
      f1 _ (by decide) (by decide) (by decide) (by decide) (by decide), hW]; simp) T3
  refine ⟨?_, ?_⟩
  · rw [o, xOut, List.flatMap_map]
  · exact T3.of_writes fun q hq => exec_writes _ _ _ (by revert q; decide)

end AdvancedEncryption.ExpLUT.Prog
