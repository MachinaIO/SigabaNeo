import PE.Impl.ExpLUT.Prog.RedKeyXRow

/-!
# `KGsim` on the VM (module 5c): driving the row kernel over all rows of `X` (generic VM)

The rows of `X` come in three groups (the order of `PIdx`): the rows of `V.1` on the `Ā`
columns (start `−R̂_ℓ`, no correction), the rows of `V.1` on the `η` columns (start `−R̂_ℓ`, the
tag `0^s 1 0^i` for the blocks `(i, (s, 0))`, the unit row `e_{c'}`), and the rows of `V.2`
(start `e_r`). This file provides the generic pieces (over `N K`):

* `xNegC` (`rxV0 := −` the next `2K` words of the `R̂` stream `rxRh`), `xEInit`/`xENext`
  (`rxE := e_0`, `e_m ↦ e_{m+1}`), the input bundle `XIn` of the row kernel;
* `exec_xRowsA`: a `rep` over rows with start `−r` and tag `11`;
* `exec_xRowsC`: `2K` rows with stream starts, the tag computed by a tag code, unit rows `e_m`;
* `exec_xRowsE`: `2K` rows with starts `e_m` and tag `11`.
-/

set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)

/-! ### Registers of the drivers (`24 … 30`) -/

/-- The stream of the rows of `R̂`. -/
@[simp, vmreg] abbrev rxRh : Fin 64 := 24
/-- The word of `1`. -/
@[simp, vmreg] abbrev rxOne : Fin 64 := 25
/-- Unary `i` (the block row of an `η` row). -/
@[simp, vmreg] abbrev rxTi : Fin 64 := 26
/-- Unary `s` (the bit of an `η` helper); the row count of the `Ā` rows first. -/
@[simp, vmreg] abbrev rxTs : Fin 64 := 27
/-- Loop counters. -/
@[simp, vmreg] abbrev rxCI : Fin 64 := 28
@[simp, vmreg] abbrev rxCS : Fin 64 := 29
@[simp, vmreg] abbrev rxCC : Fin 64 := 30

variable {N K : ℕ}

/-- The tag that never meets a comparison word `0^t 1 0^j`. -/
def ttW : List Bool := [true, true]

theorem curW_ne_ttW (t j : ℕ) : curW t j ≠ ttW := by
  intro h
  rcases t with _ | t
  · simp only [curW, List.replicate_zero, List.nil_append, ttW, List.cons.injEq, true_and] at h
    rcases j with _ | j <;> simp [List.replicate_succ] at h
  · simp [curW, ttW, List.replicate_succ] at h

/-! ### The inputs of the row kernel -/

/-- The inputs of `xRowC` that stay fixed over all rows. -/
structure XIn (g b : ℕ) (Hs Hi : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K) (w : St) : Prop where
  H : w rxH = encL N K (xHL Hs Hi (List.range b))
  Tb : w rxTb = List.replicate b false
  Tru : w rxTru = [true]
  Fal : w rxFal = [false]
  k : (w rKc).length = g
  W : (w rxW).length = 2 ^ b
  T : MulTmpl N K w

theorem XIn.of_eq {g b : ℕ} {Hs Hi : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K} {w w' : St}
    (h : XIn g b Hs Hi w)
    (hw : ∀ r : Fin 64, (r = rxH ∨ r = rxTb ∨ r = rxTru ∨ r = rxFal ∨ r = rKc ∨ r = rxW ∨
      57 ≤ r.val) → w' r = w r) : XIn g b Hs Hi w' :=
  ⟨by rw [hw _ (by decide)]; exact h.H, by rw [hw _ (by decide)]; exact h.Tb,
    by rw [hw _ (by decide)]; exact h.Tru, by rw [hw _ (by decide)]; exact h.Fal,
    by rw [hw _ (by decide)]; exact h.k, by rw [hw _ (by decide)]; exact h.W,
    h.T.of_writes fun q hq => hw q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hq))))))⟩

/-- A code that writes none of the inputs keeps them. -/
theorem XIn.exec {g b : ℕ} {Hs Hi : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K} {w : St}
    (h : XIn g b Hs Hi w) (c : Code)
    (hc : ∀ r : Fin 64, (r = rxH ∨ r = rxTb ∨ r = rxTru ∨ r = rxFal ∨ r = rKc ∨ r = rxW ∨
      57 ≤ r.val) → c.writes r = false) : XIn g b Hs Hi (exec N K c w) :=
  h.of_eq fun r hr => exec_writes _ _ _ (hc r hr)

theorem xRowC_keeps : ∀ r : Fin 64, (r = rxH ∨ r = rxTb ∨ r = rxTru ∨ r = rxFal ∨ r = rKc ∨
    r = rxW ∨ 57 ≤ r.val) → xRowC.writes r = false := by decide

/-- **The row kernel with the inputs bundled.** -/
theorem exec_xRowC_in (hN : 0 < N) (hK : 0 < K) {g b : ℕ}
    {Hs Hi : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K} (hg : 0 < g) (w : St) (hI : XIn g b Hs Hi w)
    (tag : List Bool) (e v₀ : Fin 2 × Fin K → Rq N K) (hV0 : w rxV0 = encL N K (vecL v₀))
    (hTag : w rxTag = tag) (hE : w rxE = encL N K (vecL e)) :
    exec N K xRowC w 16 = w 16 ++ encL N K (xOut g Hs tag e v₀ b) ∧
    XIn g b Hs Hi (exec N K xRowC w) :=
  ⟨(exec_xRowC hN hK w g b Hs Hi tag e v₀ hV0 hI.H hI.Tb hI.Tru hI.Fal hTag hE hI.k hg hI.W
    hI.T).1, hI.exec _ xRowC_keeps⟩

/-! ### `rxV0 := −r` -/

/-- One entry. -/
def xnBody : Code :=
  .seq (.cp rX0 rZ) <| .seq (.mvR rX0 rxRh) <| .seq (.op .neg rX0 rX0 rX0) (.app rxV0 rX0)

/-- **`rxV0 := −r`** for the next row `r` (`2K` words) of the stream `rxRh`. -/
def xNegC : Code := .seq (.clr rxV0) <| .seq (.cp rCi rT2K) (.rep rCi xnBody)

theorem xnBody_writes_rCi : xnBody.writes rCi = false := by decide

theorem exec_xnLoop (hK : 0 < K) (w : St) (l rest : List (Rq N K)) (n : ℕ) (hl : l.length = n)
    (hS : w rxRh = encL N K (l ++ rest)) (hC : w rCi = List.replicate n false)
    (hV : w rxV0 = []) (hZ : w rZ = encRM N K 0) :
    exec N K (.rep rCi xnBody) w rxV0 = encL N K (l.map (- ·)) ∧
    exec N K (.rep rCi xnBody) w rxRh = encL N K rest := by
  have key := exec_rep_inv (N := N) (K := K) rCi xnBody xnBody_writes_rCi
    (fun m w' => w' rxRh = encL N K (l.drop m ++ rest) ∧
      w' rxV0 = encL N K ((l.take m).map (- ·)) ∧ w' rZ = encRM N K 0) w
    ⟨by simp [hS], by simp [hV], hZ⟩ ?_
  · rw [hC, List.length_replicate] at key
    rw [key.2.1, key.1, List.take_of_length_le (by omega), List.drop_of_length_le (by omega)]
    exact ⟨rfl, rfl⟩
  · intro m w' hm hP _
    rw [hC, List.length_replicate] at hm
    obtain ⟨p1, p2, p3⟩ := hP
    rw [drop_cons_getElem l (show m < l.length by omega), List.cons_append, encL_cons] at p1
    unfold xnBody
    vm_simp
    refine ⟨?_, ?_, ?_⟩
    · simp [Function.update_apply, p1, p3]
    · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, p1, p2, p3,
        shiftIn_encRM', takeD_encRM_append, takeD_encRM, canonW_neg hK,
        take_succ_getElem l (show m < l.length by omega), List.map_append, encL_append]
      simp
    · simp [Function.update_apply, p3]

theorem vecL_neg (v : Fin 2 × Fin K → Rq N K) : vecL (fun c => -v c) = (vecL v).map (- ·) := by
  simp [vecL]

/-- **`rxV0 := −r`.** -/
theorem exec_xNegC (hK : 0 < K) (w : St) (r : Fin 2 × Fin K → Rq N K) (rest : List (Rq N K))
    (hS : w rxRh = encL N K (vecL r ++ rest)) (hT : MulTmpl N K w) :
    exec N K xNegC w rxV0 = encL N K (vecL fun c => -r c) ∧
    exec N K xNegC w rxRh = encL N K rest := by
  rw [vecL_neg]
  unfold xNegC
  simp only [exec_seq]
  exact exec_xnLoop hK _ _ rest (2 * K) (length_vecL r) (by vm_simp; simp [hS])
    (by vm_simp; simp [hT.t2K]) (by vm_simp; simp) (by vm_simp; simp [hT.z])

theorem xNegC_writes : ∀ r : Fin 64, xNegC.writes r = true → r ∈ [rxV0, rCi, rX0, rxRh] := by
  decide

/-! ### The unit rows -/

/-- The words of the unit row `e_m` (all zero for `m ≥ 2K`). -/
def eL (K : ℕ) (m : ℕ) : List (Rq N K) := (List.range (2 * K)).map fun i => if i = m then 1 else 0

/-- The unit row `e_m` (indexed by the position in `Enum (Fin 2 × Fin K)`). -/
def eV (m : ℕ) : Fin 2 × Fin K → Rq N K :=
  fun c => if (Enum.list (α := Fin 2 × Fin K)).idxOf c = m then 1 else 0

theorem vecL_eV (m : ℕ) : vecL (eV (N := N) (K := K) m) = eL K m := by
  unfold vecL eV eL
  apply List.ext_getElem (by simp [length_enum_col])
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [List.Nodup.idxOf_getElem Enum.nodup i (by simpa using h1)]

/-- `rxE := e_0`. -/
def xEInit : Code :=
  .seq (.cp rxTmp rT2KNK) <| .seq (.drop rxTmp rZ) <| .seq (.cp rxE rxOne) (.app rxE rxTmp)

/-- `rxE := e_{m+1}` from `e_m`. -/
def xENext : Code :=
  .seq (.cp rxTmp rZ) <| .seq (.app rxTmp rxE) <| .seq (.cp rxE rT2KNK) (.mv rxE rxTmp rT2KNK)

theorem eL_zero (hK : 0 < K) : eL (N := N) K 0 = 1 :: List.replicate (2 * K - 1) 0 := by
  unfold eL
  obtain ⟨k, hk⟩ : ∃ k, 2 * K = k + 1 := ⟨2 * K - 1, by omega⟩
  rw [hk, List.range_succ_eq_map]
  simp only [List.map_cons, ↓reduceIte, List.map_map, Function.comp_def, Nat.succ_ne_zero,
    ↓reduceIte, List.map_const', List.length_range]
  rfl

theorem eL_succ (m : ℕ) :
    (((0 : Rq N K) :: eL K m)).take (2 * K) = eL (N := N) K (m + 1) := by
  unfold eL
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_take, List.getElem_map, List.getElem_range]
  rcases i with _ | i
  · simp
  · simp

theorem exec_xEInit (hK : 0 < K) (w : St) (hOne : w rxOne = encRM N K 1) (hT : MulTmpl N K w) :
    exec N K xEInit w rxE = encL N K (eL K 0) := by
  unfold xEInit
  vm_simp
  simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, hOne, hT.t2KNK, hT.z,
    SigabaNeo.Lattices.Algo.length_encRM, eL_zero hK, encL_cons]
  congr 1
  obtain ⟨k, hk⟩ : ∃ k, 2 * K = k + 1 := ⟨2 * K - 1, by omega⟩
  rw [hk, List.replicate_succ, encL_cons, drop_encRM_append]
  rfl

theorem exec_xENext (w : St) (m : ℕ) (hE : w rxE = encL N K (eL K m)) (hT : MulTmpl N K w) :
    exec N K xENext w rxE = encL N K (eL K (m + 1)) := by
  unfold xENext
  vm_simp
  simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, hE, hT.t2KNK, hT.z, length_encL,
    List.length_replicate]
  rw [shiftIn_encL' _ _ (List.length_replicate), ← encL_cons, ← eL_succ,
    ← List.take_append_drop (2 * K) ((0 : Rq N K) :: eL K m)]
  rw [takeD_encL _ _ (by simp [eL])]
  simp

theorem xEInit_writes : ∀ r : Fin 64, xEInit.writes r = true → r ∈ [rxTmp, rxE] := by decide
theorem xENext_writes : ∀ r : Fin 64, xENext.writes r = true → r ∈ [rxTmp, rxE] := by decide

/-! ### Tags -/

/-- `rxTag := 11`. -/
def xTagTT : Code := .seq (.cp rxTag rxTru) (.app rxTag rxTru)

/-- `rxTag := 0^s 1 0^i` from `rxTs = 0^s`, `rxTi = 0^i`. -/
def xTagCur : Code := .seq (.cp rxTag rxTs) <| .seq (.app rxTag rxTru) (.app rxTag rxTi)

theorem exec_xTagTT (w : St) (h : w rxTru = [true]) : exec N K xTagTT w rxTag = ttW := by
  unfold xTagTT; vm_simp; simp [Function.update_apply, h, ttW]

theorem exec_xTagCur (w : St) (s i : ℕ) (h : w rxTru = [true]) (hs : w rxTs = List.replicate s false)
    (hi : w rxTi = List.replicate i false) : exec N K xTagCur w rxTag = curW s i := by
  unfold xTagCur; vm_simp; simp [Function.update_apply, h, hs, hi, curW]

/-! ### Part A: rows with start `−r` and tag `11` -/

/-- One row of part A. -/
def xRowABody : Code := .seq xNegC <| .seq xTagTT xRowC

/-- **Part A**: `|rxTs|` rows (`rxTs` is consumed). -/
def xPartA : Code := .seq (.cp rxE rT2KNK) (.rep rxTs xRowABody)

theorem xRowABody_writes_rxTs : xRowABody.writes rxTs = false := by decide

theorem vecL_zero : vecL (0 : Fin 2 × Fin K → Rq N K) = List.replicate (2 * K) 0 := by
  rw [← length_vecL (0 : Fin 2 × Fin K → Rq N K), List.eq_replicate_iff]
  exact ⟨rfl, fun x hx => by simp [vecL] at hx; exact hx.2.symm⟩

theorem flatMap_range_drop {α : Type} (f : ℕ → List α) {m n : ℕ} (h : m < n) :
    ((List.range n).drop m).flatMap f = f m ++ ((List.range n).drop (m + 1)).flatMap f := by
  rw [drop_range_cons h, List.flatMap_cons]

/-- **Part A.** -/
theorem exec_xPartA (hN : 0 < N) (hK : 0 < K) {g b : ℕ}
    {Hs Hi : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K} (hg : 0 < g) (w : St) (hI : XIn g b Hs Hi w)
    (n : ℕ) (f : ℕ → Fin 2 × Fin K → Rq N K) (more : List (Rq N K))
    (hS : w rxRh = encL N K ((List.range n).flatMap (fun m => vecL (f m)) ++ more))
    (hC : (w rxTs).length = n) :
    exec N K xPartA w 16 = w 16 ++ encL N K ((List.range n).flatMap fun m =>
      xOut g Hs ttW 0 (fun c => -f m c) b) ∧
    exec N K xPartA w rxRh = encL N K more ∧ XIn g b Hs Hi (exec N K xPartA w) := by
  unfold xPartA
  simp only [exec_seq]
  set w0 := exec N K (.cp rxE rT2KNK) w with hw0
  have I0 : XIn g b Hs Hi w0 := hI.exec _ (by decide)
  have e0 : ∀ r : Fin 64, r ≠ rxE → w0 r = w r := fun r h => by
    rw [hw0, exec_cp, Function.update_of_ne h]
  have key := exec_rep_inv2 (N := N) (K := K) rxTs xRowABody xRowABody_writes_rxTs
    (fun m w' => w' 16 = w 16 ++ encL N K ((List.range m).flatMap fun m =>
        xOut g Hs ttW 0 (fun c => -f m c) b) ∧
      w' rxRh = encL N K (((List.range n).drop m).flatMap (fun m => vecL (f m)) ++ more) ∧
      w' rxE = encL N K (vecL 0) ∧ XIn g b Hs Hi w') w0
    ⟨by rw [e0 _ (by decide)]; simp, by rw [e0 _ (by decide), hS]; simp,
      by rw [hw0, exec_cp, Function.update_self, hI.T.t2KNK, vecL_zero], I0⟩ ?_
  · rw [e0 _ (by decide), hC] at key
    refine ⟨key.1, ?_, key.2.2.2⟩
    rw [key.2.1, List.drop_of_length_le (by simp)]; rfl
  · intro m w' hm hP _ _
    rw [e0 _ (by decide), hC] at hm
    obtain ⟨p1, p2, p3, p4⟩ := hP
    set W1 := Function.update w' rxTs (w' rxTs).tail with hW1
    have u : ∀ r : Fin 64, r ≠ rxTs → W1 r = w' r := fun r h => Function.update_of_ne h _ _
    have I1 : XIn g b Hs Hi W1 := p4.of_eq fun r hr => u r (by rcases hr with h | h | h | h | h | h | h <;> (try subst h) <;> first | decide | (intro e; subst e; simp at h))
    rw [flatMap_range_drop _ hm, List.append_assoc] at p2
    have ng := exec_xNegC hK W1 (f m) _ (by rw [u _ (by decide), p2]) I1.T
    unfold xRowABody
    simp only [exec_seq]
    set W2 := exec N K xNegC W1 with hW2
    have f2 : ∀ r : Fin 64, xNegC.writes r = false → W2 r = W1 r := fun r h => exec_writes _ _ _ h
    have I2 : XIn g b Hs Hi W2 := I1.exec _ (by decide)
    set W3 := exec N K xTagTT W2 with hW3
    have f3 : ∀ r : Fin 64, r ≠ rxTag → W3 r = W2 r := fun r h => exec_writes _ _ _ (by
      unfold xTagTT; simp [Code.writes, Ne.symm h])
    have I3 : XIn g b Hs Hi W3 := I2.exec _ (by decide)
    have rw3 := exec_xRowC_in hN hK hg W3 I3 ttW 0 (fun c => -f m c)
      (by rw [f3 _ (by decide), ng.1]) (exec_xTagTT W2 I2.Tru)
      (by rw [f3 _ (by decide), f2 _ (by decide), u _ (by decide), p3])
    refine ⟨?_, ?_, ?_, rw3.2⟩
    · rw [rw3.1, f3 _ (by decide), f2 _ (by decide), u _ (by decide), p1, List.range_succ,
        List.flatMap_append, List.flatMap_singleton, encL_append, List.append_assoc]
    · rw [exec_writes _ _ _ (by decide), f3 _ (by decide), ng.2]
    · rw [exec_writes _ _ _ (by decide), f3 _ (by decide), f2 _ (by decide), u _ (by decide), p3]

/-! ### `2K` rows with unit corrections -/

/-- One row with a stream start, the tag of `tc`, the correction `e_m`. -/
def xRowBBody (tc : Code) : Code := .seq xNegC <| .seq tc <| .seq xRowC xENext

/-- **`2K` rows** with stream starts and corrections `e_0, …, e_{2K−1}`. -/
def xCLoopB (tc : Code) : Code := .seq xEInit <| .seq (.cp rxCC rT2K) (.rep rxCC (xRowBBody tc))

/-- A tag code: it writes `rxTag` only, and the tag is a function of `rxTru`, `rxTi`, `rxTs`. -/
structure TagCode (tc : Code) (w : St) (T : List Bool) : Prop where
  writes : ∀ r : Fin 64, r ≠ rxTag → tc.writes r = false
  tag : ∀ w' : St, w' rxTru = w rxTru → w' rxTi = w rxTi → w' rxTs = w rxTs →
    exec N K tc w' rxTag = T
  wf : tc.WFc

theorem TagCode.writes_list {tc : Code} {w : St} {T : List Bool} (h : TagCode (N := N) (K := K) tc w T)
    (r : Fin 64) (hr : r ≠ rxTag) : tc.writes r = false := h.writes r hr

theorem xRowBBody_writes {tc : Code} {w : St} {T : List Bool} (h : TagCode (N := N) (K := K) tc w T)
    (r : Fin 64) (hr : r ≠ rxTag) (h1 : xNegC.writes r = false) (h2 : xRowC.writes r = false)
    (h3 : xENext.writes r = false) : (xRowBBody tc).writes r = false := by
  simp [xRowBBody, Code.writes, h1, h2, h3, h.writes r hr]

/-- **The `2K` rows.** -/
theorem exec_xCLoopB (hN : 0 < N) (hK : 0 < K) {g b : ℕ}
    {Hs Hi : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K} (hg : 0 < g) (w : St) (hI : XIn g b Hs Hi w)
    (tc : Code) (T : List Bool) (htc : TagCode (N := N) (K := K) tc w T)
    (f : ℕ → Fin 2 × Fin K → Rq N K) (more : List (Rq N K))
    (hS : w rxRh = encL N K ((List.range (2 * K)).flatMap (fun m => vecL (f m)) ++ more))
    (hOne : w rxOne = encRM N K 1) :
    exec N K (xCLoopB tc) w 16 = w 16 ++ encL N K ((List.range (2 * K)).flatMap fun m =>
      xOut g Hs T (eV m) (fun c => -f m c) b) ∧
    exec N K (xCLoopB tc) w rxRh = encL N K more ∧ XIn g b Hs Hi (exec N K (xCLoopB tc) w) := by
  unfold xCLoopB
  simp only [exec_seq]
  set w0 := exec N K (.cp rxCC rT2K) (exec N K xEInit w) with hw0
  have e0 : ∀ r : Fin 64, r ≠ rxE → r ≠ rxTmp → r ≠ rxCC → w0 r = w r := fun r h1 h2 h3 => by
    rw [hw0, exec_cp, Function.update_of_ne h3, exec_writes _ _ _ (by
      unfold xEInit; simp [Code.writes, Ne.symm h1, Ne.symm h2])]
  have I0 : XIn g b Hs Hi w0 := hI.of_eq fun r hr => e0 r
    (by rcases hr with h | h | h | h | h | h | h <;> (try subst h) <;> first | decide | (intro e; subst e; simp at h))
    (by rcases hr with h | h | h | h | h | h | h <;> (try subst h) <;> first | decide | (intro e; subst e; simp at h))
    (by rcases hr with h | h | h | h | h | h | h <;> (try subst h) <;> first | decide | (intro e; subst e; simp at h))
  have hb : (xRowBBody tc).writes rxCC = false :=
    xRowBBody_writes htc _ (by decide) (by decide) (by decide) (by decide)
  have key := exec_rep_inv2 (N := N) (K := K) rxCC (xRowBBody tc) hb
    (fun m w' => w' 16 = w 16 ++ encL N K ((List.range m).flatMap fun m =>
        xOut g Hs T (eV m) (fun c => -f m c) b) ∧
      w' rxRh = encL N K (((List.range (2 * K)).drop m).flatMap (fun m => vecL (f m)) ++ more) ∧
      w' rxE = encL N K (eL K m) ∧ XIn g b Hs Hi w') w0
    ⟨by rw [e0 _ (by decide) (by decide) (by decide)]; simp,
      by rw [e0 _ (by decide) (by decide) (by decide), hS]; simp,
      by rw [hw0, exec_cp, Function.update_of_ne (by decide)]; exact exec_xEInit hK w hOne hI.T,
      I0⟩ ?_
  · have hc : (w0 rxCC).length = 2 * K := by
      rw [hw0, exec_cp, Function.update_self, exec_writes _ _ _ (by decide), hI.T.t2K,
        List.length_replicate]
    rw [hc] at key
    refine ⟨key.1, ?_, key.2.2.2⟩
    rw [key.2.1, List.drop_of_length_le (by simp)]; rfl
  · intro m w' hm hP _ hfr
    have hc : (w0 rxCC).length = 2 * K := by
      rw [hw0, exec_cp, Function.update_self, exec_writes _ _ _ (by decide), hI.T.t2K,
        List.length_replicate]
    rw [hc] at hm
    obtain ⟨p1, p2, p3, p4⟩ := hP
    set W1 := Function.update w' rxCC (w' rxCC).tail with hW1
    have u : ∀ r : Fin 64, r ≠ rxCC → W1 r = w' r := fun r h => Function.update_of_ne h _ _
    have I1 : XIn g b Hs Hi W1 := p4.of_eq fun r hr => u r (by rcases hr with h | h | h | h | h | h | h <;> (try subst h) <;> first | decide | (intro e; subst e; simp at h))
    rw [flatMap_range_drop _ hm, List.append_assoc] at p2
    have ng := exec_xNegC hK W1 (f m) _ (by rw [u _ (by decide), p2]) I1.T
    unfold xRowBBody
    simp only [exec_seq]
    set W2 := exec N K xNegC W1 with hW2
    have f2 : ∀ r : Fin 64, xNegC.writes r = false → W2 r = W1 r := fun r h => exec_writes _ _ _ h
    have I2 : XIn g b Hs Hi W2 := I1.exec _ (by decide)
    set W3 := exec N K tc W2 with hW3
    have f3 : ∀ r : Fin 64, r ≠ rxTag → W3 r = W2 r := fun r h => exec_writes _ _ _ (htc.writes r h)
    have I3 : XIn g b Hs Hi W3 := I2.of_eq fun r hr => f3 r (by rcases hr with h | h | h | h | h | h | h <;> (try subst h) <;> first | decide | (intro e; subst e; simp at h))
    -- the frame of the whole loop for the tag inputs
    have fw : ∀ r : Fin 64, (r = rxTru ∨ r = rxTi ∨ r = rxTs) → W2 r = w r := by
      intro r hr
      have hrb : (xRowBBody tc).writes r = false := by
        rcases hr with rfl | rfl | rfl <;>
          exact xRowBBody_writes htc _ (by decide) (by decide) (by decide) (by decide)
      rw [f2 r (by rcases hr with rfl | rfl | rfl <;> decide), u r (by rcases hr with rfl | rfl | rfl <;> decide),
        hfr r hrb (by rcases hr with rfl | rfl | rfl <;> decide),
        e0 r (by rcases hr with rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl <;> decide)
          (by rcases hr with rfl | rfl | rfl <;> decide)]
    have tg := htc.tag W2 (fw _ (Or.inl rfl)) (fw _ (Or.inr (Or.inl rfl))) (fw _ (Or.inr (Or.inr rfl)))
    have rw3 := exec_xRowC_in hN hK hg W3 I3 T (eV m) (fun c => -f m c)
      (by rw [f3 _ (by decide), ng.1]) tg
      (by rw [f3 _ (by decide), f2 _ (by decide), u _ (by decide), p3, vecL_eV])
    set W4 := exec N K xRowC W3 with hW4
    have f4 : ∀ r : Fin 64, xRowC.writes r = false → W4 r = W3 r := fun r h => exec_writes _ _ _ h
    refine ⟨?_, ?_, ?_, rw3.2.exec _ (by decide)⟩
    · rw [exec_writes _ _ _ (by decide), rw3.1, f3 _ (by decide), f2 _ (by decide),
        u _ (by decide), p1, List.range_succ, List.flatMap_append, List.flatMap_singleton,
        encL_append, List.append_assoc]
    · rw [exec_writes _ _ _ (by decide), f4 _ (by decide), f3 _ (by decide), ng.2]
    · refine exec_xENext W4 m ?_ rw3.2.T
      rw [f4 _ (by decide), f3 _ (by decide), f2 _ (by decide), u _ (by decide), p3]

/-- Updating a non-input register keeps the inputs. -/
theorem XIn.update {g b : ℕ} {Hs Hi : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K} {w : St}
    (h : XIn g b Hs Hi w) (c : Fin 64) (v : List Bool)
    (hc : c.val < 57 ∧ c ≠ rxH ∧ c ≠ rxTb ∧ c ≠ rxTru ∧ c ≠ rxFal ∧ c ≠ rKc ∧ c ≠ rxW) :
    XIn g b Hs Hi (Function.update w c v) :=
  h.of_eq fun r hr => Function.update_of_ne (by
    rintro rfl
    rcases hr with h | h | h | h | h | h | h
    · exact hc.2.1 h
    · exact hc.2.2.1 h
    · exact hc.2.2.2.1 h
    · exact hc.2.2.2.2.1 h
    · exact hc.2.2.2.2.2.1 h
    · exact hc.2.2.2.2.2.2 h
    · omega) _ _

/-! ### Part C: the rows of `V.2` -/

/-- One row of part C: start `e_m`, tag `11`. -/
def xRowEBody : Code := .seq (.cp rxV0 rxE) <| .seq xTagTT <| .seq xRowC xENext

/-- **Part C**: `2K` rows with starts `e_0, …, e_{2K−1}`. -/
def xPartC : Code := .seq xEInit <| .seq (.cp rxCC rT2K) (.rep rxCC xRowEBody)

theorem xRowEBody_writes_rxCC : xRowEBody.writes rxCC = false := by decide

/-- **Part C.** -/
theorem exec_xPartC (hN : 0 < N) (hK : 0 < K) {g b : ℕ}
    {Hs Hi : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K} (hg : 0 < g) (w : St) (hI : XIn g b Hs Hi w)
    (hOne : w rxOne = encRM N K 1) :
    exec N K xPartC w 16 = w 16 ++ encL N K ((List.range (2 * K)).flatMap fun m =>
      xOut g Hs ttW (eV m) (eV m) b) ∧ XIn g b Hs Hi (exec N K xPartC w) := by
  unfold xPartC
  simp only [exec_seq]
  set w0 := exec N K (.cp rxCC rT2K) (exec N K xEInit w) with hw0
  have e0 : ∀ r : Fin 64, r ≠ rxE → r ≠ rxTmp → r ≠ rxCC → w0 r = w r := fun r h1 h2 h3 => by
    rw [hw0, exec_cp, Function.update_of_ne h3, exec_writes _ _ _ (by
      unfold xEInit; simp [Code.writes, Ne.symm h1, Ne.symm h2])]
  have I0 : XIn g b Hs Hi w0 := (hI.exec xEInit (by decide)).update _ _ (by decide)
  have key := exec_rep_inv2 (N := N) (K := K) rxCC xRowEBody xRowEBody_writes_rxCC
    (fun m w' => w' 16 = w 16 ++ encL N K ((List.range m).flatMap fun m =>
        xOut g Hs ttW (eV m) (eV m) b) ∧
      w' rxE = encL N K (eL K m) ∧ XIn g b Hs Hi w') w0
    ⟨by rw [e0 _ (by decide) (by decide) (by decide)]; simp,
      by rw [hw0, exec_cp, Function.update_of_ne (by decide)]; exact exec_xEInit hK w hOne hI.T,
      I0⟩ ?_
  · have hc : (w0 rxCC).length = 2 * K := by
      rw [hw0, exec_cp, Function.update_self, exec_writes _ _ _ (by decide), hI.T.t2K,
        List.length_replicate]
    rw [hc] at key
    exact ⟨key.1, key.2.2⟩
  · intro m w' hm hP _ _
    obtain ⟨p1, p2, p3⟩ := hP
    set W1 := Function.update w' rxCC (w' rxCC).tail with hW1
    have u : ∀ r : Fin 64, r ≠ rxCC → W1 r = w' r := fun r h => Function.update_of_ne h _ _
    have I1 : XIn g b Hs Hi W1 := p3.update _ _ (by decide)
    unfold xRowEBody
    simp only [exec_seq]
    set W2 := exec N K (.cp rxV0 rxE) W1 with hW2
    have I2 : XIn g b Hs Hi W2 := I1.update _ _ (by decide)
    set W3 := exec N K xTagTT W2 with hW3
    have f3 : ∀ r : Fin 64, r ≠ rxTag → W3 r = W2 r := fun r h => exec_writes _ _ _ (by
      unfold xTagTT; simp [Code.writes, Ne.symm h])
    have I3 : XIn g b Hs Hi W3 := I2.exec _ (by decide)
    have hE2 : W2 rxE = encL N K (eL K m) := by
      rw [hW2, exec_cp, Function.update_of_ne (by decide), u _ (by decide), p2]
    have rw3 := exec_xRowC_in hN hK hg W3 I3 ttW (eV m) (eV m)
      (by rw [f3 _ (by decide), hW2, exec_cp, Function.update_self, u _ (by decide), p2,
        vecL_eV])
      (exec_xTagTT W2 I2.Tru) (by rw [f3 _ (by decide), hE2, vecL_eV])
    set W4 := exec N K xRowC W3 with hW4
    refine ⟨?_, ?_, rw3.2.exec _ (by decide)⟩
    · rw [exec_writes _ _ _ (by decide), rw3.1, f3 _ (by decide), hW2, exec_cp,
        Function.update_of_ne (by decide), u _ (by decide), p1, List.range_succ,
        List.flatMap_append, List.flatMap_singleton, encL_append, List.append_assoc]
    · refine exec_xENext W4 m ?_ rw3.2.T
      rw [hW4, exec_writes _ _ _ (by decide), f3 _ (by decide), hE2]

/-! ### Part B: the rows of `V.1` on the `η` columns -/

theorem tagCode_xTagCur (w : St) (s i : ℕ) (h : w rxTru = [true])
    (hs : w rxTs = List.replicate s false) (hi : w rxTi = List.replicate i false) :
    TagCode (N := N) (K := K) xTagCur w (curW s i) :=
  ⟨fun r hr => by unfold xTagCur; simp [Code.writes, Ne.symm hr],
    fun w' h1 h2 h3 => exec_xTagCur w' s i (h1.trans h) (h3.trans hs) (h2.trans hi),
    by repeat constructor⟩

theorem tagCode_xTagTT (w : St) (h : w rxTru = [true]) :
    TagCode (N := N) (K := K) xTagTT w ttW :=
  ⟨fun r hr => by unfold xTagTT; simp [Code.writes, Ne.symm hr],
    fun w' h1 _ _ => exec_xTagTT w' (h1.trans h), by repeat constructor⟩

/-- One bit `s` of the block row `i`: the rows `(i, (s, 0), ·)` (tag `0^s 1 0^i`), then the rows
`(i, (s, 1), ·)` (tag `11`), then `s := s + 1`. -/
def xSBody : Code := .seq (xCLoopB xTagCur) <| .seq (xCLoopB xTagTT) (.app rxTs rxFal)

/-- The block row `i`: its `b` bits, then `i := i + 1`. -/
def xIBody : Code :=
  .seq (.clr rxTs) <| .seq (.cp rxCS rxTb) <| .seq (.rep rxCS xSBody) (.app rxTi rxFal)

/-- **Part B**: the `|rxW|` block rows. -/
def xPartB : Code := .seq (.clr rxTi) <| .seq (.cp rxCI rxW) (.rep rxCI xIBody)

theorem xSBody_writes_rxCS : xSBody.writes rxCS = false := by decide
theorem xIBody_writes_rxCI : xIBody.writes rxCI = false := by decide

/-- The stream words of the rows `(i, (s, ·), ·)`. -/
def xBlkS (f : ℕ → ℕ → ℕ → Fin 2 × Fin K → Rq N K) (s : ℕ) : List (Rq N K) :=
  (List.range (2 * K)).flatMap (fun m => vecL (f s 0 m)) ++
    (List.range (2 * K)).flatMap (fun m => vecL (f s 1 m))

/-- The output of the rows `(i, (s, ·), ·)`. -/
def xOutS (g b : ℕ) (Hs : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K) (i : ℕ)
    (f : ℕ → ℕ → ℕ → Fin 2 × Fin K → Rq N K) (s : ℕ) : List (Rq N K) :=
  (List.range (2 * K)).flatMap (fun m => xOut g Hs (curW s i) (eV m) (fun c => -f s 0 m c) b) ++
    (List.range (2 * K)).flatMap (fun m => xOut g Hs ttW (eV m) (fun c => -f s 1 m c) b)

/-- **The bits of one block row.** -/
theorem exec_xSLoop (hN : 0 < N) (hK : 0 < K) {g b : ℕ}
    {Hs Hi : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K} (hg : 0 < g) (w : St) (hI : XIn g b Hs Hi w)
    (i n : ℕ) (f : ℕ → ℕ → ℕ → Fin 2 × Fin K → Rq N K) (more : List (Rq N K))
    (hS : w rxRh = encL N K ((List.range n).flatMap (xBlkS f) ++ more))
    (hOne : w rxOne = encRM N K 1) (hTs : w rxTs = []) (hTi : w rxTi = List.replicate i false)
    (hCS : (w rxCS).length = n) :
    exec N K (.rep rxCS xSBody) w 16 =
      w 16 ++ encL N K ((List.range n).flatMap (xOutS g b Hs i f)) ∧
    exec N K (.rep rxCS xSBody) w rxRh = encL N K more ∧
    XIn g b Hs Hi (exec N K (.rep rxCS xSBody) w) := by
  have key := exec_rep_inv2 (N := N) (K := K) rxCS xSBody xSBody_writes_rxCS
    (fun s w' => w' 16 = w 16 ++ encL N K ((List.range s).flatMap (xOutS g b Hs i f)) ∧
      w' rxRh = encL N K (((List.range n).drop s).flatMap (xBlkS f) ++ more) ∧
      w' rxTs = List.replicate s false ∧ XIn g b Hs Hi w') w
    ⟨by simp, by rw [hS]; simp, by rw [hTs]; rfl, hI⟩ ?_
  · rw [hCS] at key
    refine ⟨key.1, ?_, key.2.2.2⟩
    rw [key.2.1, List.drop_of_length_le (by simp)]; rfl
  · intro s w' hs hP _ hfr
    rw [hCS] at hs
    obtain ⟨p1, p2, p3, p4⟩ := hP
    set W1 := Function.update w' rxCS (w' rxCS).tail with hW1
    have u : ∀ r : Fin 64, r ≠ rxCS → W1 r = w' r := fun r h => Function.update_of_ne h _ _
    have I1 : XIn g b Hs Hi W1 := p4.update _ _ (by decide)
    have hTi1 : W1 rxTi = List.replicate i false := by
      rw [u _ (by decide), hfr _ (by decide) (by decide), hTi]
    have hOne1 : W1 rxOne = encRM N K 1 := by
      rw [u _ (by decide), hfr _ (by decide) (by decide), hOne]
    rw [flatMap_range_drop _ hs, xBlkS, List.append_assoc, List.append_assoc] at p2
    have c1 := exec_xCLoopB hN hK hg W1 I1 xTagCur (curW s i)
      (tagCode_xTagCur W1 s i I1.Tru (by rw [u _ (by decide), p3]) hTi1) (f s 0) _
      (by rw [u _ (by decide), p2]) hOne1
    unfold xSBody
    simp only [exec_seq]
    set W2 := exec N K (xCLoopB xTagCur) W1 with hW2
    have f2 : ∀ r : Fin 64, (xCLoopB xTagCur).writes r = false → W2 r = W1 r :=
      fun r h => exec_writes _ _ _ h
    have c2 := exec_xCLoopB hN hK hg W2 c1.2.2 xTagTT ttW (tagCode_xTagTT W2 c1.2.2.Tru)
      (f s 1) _ c1.2.1 (by rw [f2 _ (by decide), hOne1])
    set W3 := exec N K (xCLoopB xTagTT) W2 with hW3
    have f3 : ∀ r : Fin 64, (xCLoopB xTagTT).writes r = false → W3 r = W2 r :=
      fun r h => exec_writes _ _ _ h
    refine ⟨?_, ?_, ?_, by rw [exec_app]; exact c2.2.2.update _ _ (by decide)⟩
    · rw [exec_app, Function.update_of_ne (by decide), c2.1, c1.1, u _ (by decide), p1,
        List.range_succ,
        List.flatMap_append, List.flatMap_singleton, xOutS]
      simp only [encL_append, List.append_assoc]
    · rw [exec_app, Function.update_of_ne (by decide), c2.2.1]
    · rw [exec_app, Function.update_self, c2.2.2.Fal, f3 _ (by decide), f2 _ (by decide),
        u _ (by decide), p3, List.replicate_succ']

/-- **Part B.** -/
theorem exec_xPartB (hN : 0 < N) (hK : 0 < K) {g b : ℕ}
    {Hs Hi : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K} (hg : 0 < g) (w : St) (hI : XIn g b Hs Hi w)
    (F : ℕ → ℕ → ℕ → ℕ → Fin 2 × Fin K → Rq N K) (more : List (Rq N K))
    (hS : w rxRh = encL N K ((List.range (2 ^ b)).flatMap
      (fun i => (List.range b).flatMap (xBlkS (F i))) ++ more))
    (hOne : w rxOne = encRM N K 1) :
    exec N K xPartB w 16 = w 16 ++ encL N K ((List.range (2 ^ b)).flatMap
      (fun i => (List.range b).flatMap (xOutS g b Hs i (F i)))) ∧
    exec N K xPartB w rxRh = encL N K more ∧ XIn g b Hs Hi (exec N K xPartB w) := by
  unfold xPartB
  simp only [exec_seq]
  set w0 := exec N K (.cp rxCI rxW) (exec N K (.clr rxTi) w) with hw0
  have e0 : ∀ r : Fin 64, r ≠ rxTi → r ≠ rxCI → w0 r = w r := fun r h1 h2 => by
    rw [hw0, exec_cp, Function.update_of_ne h2, exec_clr, Function.update_of_ne h1]
  have I0 : XIn g b Hs Hi w0 := (hI.update _ _ (by decide)).update _ _ (by decide)
  have key := exec_rep_inv2 (N := N) (K := K) rxCI xIBody xIBody_writes_rxCI
    (fun i w' => w' 16 = w 16 ++ encL N K ((List.range i).flatMap
        (fun i => (List.range b).flatMap (xOutS g b Hs i (F i)))) ∧
      w' rxRh = encL N K (((List.range (2 ^ b)).drop i).flatMap
        (fun i => (List.range b).flatMap (xBlkS (F i))) ++ more) ∧
      w' rxTi = List.replicate i false ∧ XIn g b Hs Hi w') w0
    ⟨by rw [e0 _ (by decide) (by decide)]; simp, by rw [e0 _ (by decide) (by decide), hS]; simp,
      by rw [hw0, exec_cp, Function.update_of_ne (by decide), exec_clr, Function.update_self]; rfl,
      I0⟩ ?_
  · have hc : (w0 rxCI).length = 2 ^ b := by
      rw [hw0, exec_cp, Function.update_self, exec_clr, Function.update_of_ne (by decide), hI.W]
    rw [hc] at key
    refine ⟨key.1, ?_, key.2.2.2⟩
    rw [key.2.1, List.drop_of_length_le (by simp)]; rfl
  · intro i w' hi hP _ hfr
    have hc : (w0 rxCI).length = 2 ^ b := by
      rw [hw0, exec_cp, Function.update_self, exec_clr, Function.update_of_ne (by decide), hI.W]
    rw [hc] at hi
    obtain ⟨p1, p2, p3, p4⟩ := hP
    set W1 := Function.update w' rxCI (w' rxCI).tail with hW1
    have u : ∀ r : Fin 64, r ≠ rxCI → W1 r = w' r := fun r h => Function.update_of_ne h _ _
    have I1 : XIn g b Hs Hi W1 := p4.update _ _ (by decide)
    rw [flatMap_range_drop _ hi, List.append_assoc] at p2
    unfold xIBody
    simp only [exec_seq]
    set W2 := exec N K (.cp rxCS rxTb) (exec N K (.clr rxTs) W1) with hW2
    have e2 : ∀ r : Fin 64, r ≠ rxTs → r ≠ rxCS → W2 r = W1 r := fun r h1 h2 => by
      rw [hW2, exec_cp, Function.update_of_ne h2, exec_clr, Function.update_of_ne h1]
    have I2 : XIn g b Hs Hi W2 := (I1.update _ _ (by decide)).update _ _ (by decide)
    have sl := exec_xSLoop hN hK hg W2 I2 i b (F i) _
      (by rw [e2 _ (by decide) (by decide), u _ (by decide), p2])
      (by rw [e2 _ (by decide) (by decide), u _ (by decide), hfr _ (by decide) (by decide),
        e0 _ (by decide) (by decide), hOne])
      (by rw [hW2, exec_cp, Function.update_of_ne (by decide), exec_clr, Function.update_self])
      (by rw [e2 _ (by decide) (by decide), u _ (by decide), p3])
      (by rw [hW2, exec_cp, Function.update_self, exec_clr, Function.update_of_ne (by decide),
        I1.Tb, List.length_replicate])
    set W3 := exec N K (.rep rxCS xSBody) W2 with hW3
    have f3 : ∀ r : Fin 64, (Code.rep rxCS xSBody).writes r = false → W3 r = W2 r :=
      fun r h => exec_writes _ _ _ h
    refine ⟨?_, ?_, ?_, by rw [exec_app]; exact sl.2.2.update _ _ (by decide)⟩
    · rw [exec_app, Function.update_of_ne (by decide), sl.1, e2 _ (by decide) (by decide),
        u _ (by decide), p1, List.range_succ, List.flatMap_append, List.flatMap_singleton]
      simp only [encL_append, List.append_assoc]
    · rw [exec_app, Function.update_of_ne (by decide), sl.2.1]
    · rw [exec_app, Function.update_self, sl.2.2.Fal, f3 _ (by decide),
        e2 _ (by decide) (by decide), u _ (by decide), p3, List.replicate_succ']

/-! ### All rows -/

/-- **The rows of `X` into register `16`**: part A (`|rxTs|` rows), part B (`|rxW|` block rows of
`b` bits), part C (`2K` rows). -/
def simXC : Code := .seq (.clr 16) <| .seq xPartA <| .seq xPartB xPartC

theorem wf_simXC : simXC.WFc := by repeat constructor

/-- The registers `simXC` writes. -/
theorem simXC_writes : ∀ r : Fin 64, simXC.writes r = true →
    r.val < 57 ∧ r ≠ 8 ∧ r ≠ 14 ∧ r ≠ rxH ∧ r ≠ rxTb ∧ r ≠ rxTru ∧ r ≠ rxFal ∧ r ≠ rxW ∧
      r ≠ rKc ∧ r ≠ rxOne := by
  decide

/-- **`simXC`, generic.** -/
theorem exec_simXC_gen (hN : 0 < N) (hK : 0 < K) {g b : ℕ}
    {Hs Hi : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K} (hg : 0 < g) (w : St) (hI : XIn g b Hs Hi w)
    (nA : ℕ) (fA : ℕ → Fin 2 × Fin K → Rq N K) (F : ℕ → ℕ → ℕ → ℕ → Fin 2 × Fin K → Rq N K)
    (hS : w rxRh = encL N K ((List.range nA).flatMap (fun m => vecL (fA m)) ++
      (List.range (2 ^ b)).flatMap (fun i => (List.range b).flatMap (xBlkS (F i)))))
    (hA : (w rxTs).length = nA) (hOne : w rxOne = encRM N K 1) :
    exec N K simXC w 16 = encL N K (
      (List.range nA).flatMap (fun m => xOut g Hs ttW 0 (fun c => -fA m c) b) ++
      (List.range (2 ^ b)).flatMap (fun i => (List.range b).flatMap (xOutS g b Hs i (F i))) ++
      (List.range (2 * K)).flatMap (fun m => xOut g Hs ttW (eV m) (eV m) b)) ∧
    XIn g b Hs Hi (exec N K simXC w) := by
  unfold simXC
  simp only [exec_seq]
  set w0 := exec N K (.clr 16) w with hw0
  have e0 : ∀ r : Fin 64, r ≠ 16 → w0 r = w r := fun r h => by
    rw [hw0, exec_clr, Function.update_of_ne h]
  have I0 : XIn g b Hs Hi w0 := hI.update _ _ (by decide)
  have a := exec_xPartA hN hK hg w0 I0 nA fA _ (by rw [e0 _ (by decide), hS])
    (by rw [e0 _ (by decide), hA])
  set w1 := exec N K xPartA w0 with hw1
  have f1 : ∀ r : Fin 64, xPartA.writes r = false → w1 r = w0 r := fun r h => exec_writes _ _ _ h
  have hOne1 : w1 rxOne = encRM N K 1 := by rw [f1 _ (by decide), e0 _ (by decide), hOne]
  have bb := exec_xPartB hN hK hg w1 a.2.2 F [] (by rw [a.2.1, List.append_nil]) hOne1
  set w2 := exec N K xPartB w1 with hw2
  have f2 : ∀ r : Fin 64, xPartB.writes r = false → w2 r = w1 r := fun r h => exec_writes _ _ _ h
  have cc := exec_xPartC hN hK hg w2 bb.2.2 (by rw [f2 _ (by decide), hOne1])
  refine ⟨?_, cc.2⟩
  rw [cc.1, bb.1, a.1, hw0, exec_clr, Function.update_self]
  simp only [encL_append, List.nil_append, List.append_assoc]

end AdvancedEncryption.ExpLUT.Prog
