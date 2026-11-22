import SigabaNeo.Lib.Lattices.ProgAlgo.ValNand
import SigabaNeo.Lib.Lattices.ProgAlgo.GateListLayout
import SigabaNeo.Lib.Lattices.ProgAlgo.SLPTape

/-!
# The gates of a predicate on the word machine

`gloopC blk`: for a gate list `gs` (the word `gsW W gs` on `GS`, the operands as unary words of
`W` bits) and a block `blk` computing `RES := F (IA, IB)` on slots of `S` bits (`BlockSpec`), each
gate reads its two operands from the **store** `GST` and appends `F` of them.

The store holds `W + 1` slots, rotated: before the gate `t`,
`GST = C^(W − 10 − t) ++ [C, in₀, …, in₉, r₀, …, r_{t−1}]` (`C` the slot of the wire `1`, `inᵢ`
the inputs, `rₘ` the results). An operand `j ≤ W` is read from `GST ++ GST` at the slot
`(W − 10 − t) + j` (`rdC`): this is the slot `j` of `C :: ins ++ rs` when `j < 11 + t`, else `C`
— the value of the wire `ofIdx 10 j` (`1`, the input `j − 1`, the gate `j − 11`, a missing gate
counting as `1`). **`exec_gloopC`**: after the `|gs|` gates, `GST` holds the results `gl F C ins gs`
and `OUTW` the last one.
-/

namespace SigabaNeo.Tape

namespace ValVM

open SigabaNeo.Lattices SigabaNeo.Lattices.SLP SigabaNeo.Tape.Prog

set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

variable {V : ℕ} {f : List Bool → List Bool → List Bool}

/-! ### Registers -/

abbrev GST : Fin 128 := 100
abbrev GS : Fin 128 := 101
abbrev GCNT : Fin 128 := 102
abbrev PADS : Fin 128 := 103
abbrev GD : Fin 128 := 104
abbrev GX : Fin 128 := 105
abbrev JW : Fin 128 := 106
abbrev JB : Fin 128 := 107
abbrev CJW : Fin 128 := 108
abbrev OUTW : Fin 128 := 109
abbrev TSl : Fin 128 := 110
abbrev TST : Fin 128 := 111
abbrev TD2 : Fin 128 := 112
abbrev TW : Fin 128 := 113
abbrev TPAD : Fin 128 := 114

/-! ### Reading an operand -/

/-- One round of the skip: drop a slot when the bit of the operand is set. -/
def jdBody : Code := ofList [.ifb JB (.drop GD TSl) .nop, .tl JB]

/-- **Read an operand** into `dst`: `GD := GST ++ GST`, skip the padding `|PADS|` and `j` slots
(the unary word `JW`), take one slot. -/
def rdC (dst : Fin 128) : Code :=
  ofList [.cp GD TD2, .cp GX GST, .mv GD GX TST, .cp GX GST, .mv GD GX TST, .drop GD PADS,
    .cp JB JW, .cp CJW TW, .rep CJW jdBody, .cp dst TSl, .mv dst GD TSl]

theorem hd_unaryW_drop {W j r : ℕ} (hj : j ≤ W) (hr : r < W) :
    hd ((unaryW W j).drop r) = decide (r < j) := by
  unfold unaryW
  by_cases h : r < j
  · rw [List.drop_append_of_le_length (by simp; omega), List.drop_replicate]
    obtain ⟨m, hm⟩ : ∃ m, j - r = m + 1 := ⟨j - r - 1, by omega⟩
    rw [hm, List.replicate_succ, List.cons_append]; simp [hd, h]
  · rw [List.drop_append, List.drop_replicate, List.drop_replicate, List.length_replicate,
      show j - r = 0 by omega]
    obtain ⟨m, hm⟩ : ∃ m, W - j - (r - j) = m + 1 := ⟨W - j - (r - j) - 1, by omega⟩
    rw [hm, List.replicate_succ]; simp [hd, h]

theorem jdBody_step {S W j : ℕ} (hj : j ≤ W) {L : List (List Bool)} (hL : UV S L) {w₀ : St}
    (hTS : (w₀ TSl).length = S) {r : ℕ} (hr : r < W) {w : St}
    (h : w GD = (L.drop (min r j)).flatten ∧ w JB = (unaryW W j).drop r ∧
      ∀ x, x ≠ GD → x ≠ JB → x ≠ CJW → w x = w₀ x) :
    let w' := exec V f jdBody (Function.update w CJW (w CJW).tail)
    w' GD = (L.drop (min (r + 1) j)).flatten ∧ w' JB = (unaryW W j).drop (r + 1) ∧
      ∀ x, x ≠ GD → x ≠ JB → x ≠ CJW → w' x = w₀ x := by
  obtain ⟨hg, hb, ho⟩ := h
  have hTS' : (w TSl).length = S := by rw [ho TSl (by decide) (by decide) (by decide), hTS]
  simp only [jdBody, exec_ofList, List.foldl_cons, List.foldl_nil, exec_ifb', exec_tl']
  have hh : hd (Function.update w CJW (w CJW).tail JB) = decide (r < j) := by
    rw [Function.update_of_ne (by decide), hb, hd_unaryW_drop hj hr]
  rw [hh]
  by_cases hrj : r < j
  · simp only [decide_eq_true hrj, if_true]
    rw [exec_drop' (by decide)]
    refine ⟨?_, ?_, fun x h1 h2 h3 => ?_⟩
    · simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
      rw [hg, hTS', ← Nat.one_mul S, drop_flatten_uv (hL.drop _), List.drop_drop,
        min_eq_left hrj.le, min_eq_left (by omega : r + 1 ≤ j)]
    · simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
      rw [hb, List.tail_drop]
    · simp only [Function.update_apply, if_neg h1, if_neg h2, if_neg h3]; exact ho x h1 h2 h3
  · simp only [decide_eq_false hrj, Bool.false_eq_true, if_false]
    refine ⟨?_, ?_, fun x h1 h2 h3 => ?_⟩
    · simp (config := {decide := true}) only [exec, Function.update_apply, if_true, if_false]
      rw [hg, min_eq_right (by omega : j ≤ r), min_eq_right (by omega : j ≤ r + 1)]
    · simp (config := {decide := true}) only [exec, Function.update_apply, if_true, if_false]
      rw [hb, List.tail_drop]
    · simp only [exec, Function.update_apply, if_neg h1, if_neg h2, if_neg h3]; exact ho x h1 h2 h3

/-- **Reading an operand**: from the store `R` (`W + 1` slots of `S` bits), the padding `p` and the
operand `j ≤ W`, `dst` gets the slot `p + j` of `R ++ R`. -/
theorem exec_rdC {dst : Fin 128} (hd : dst = IA ∨ dst = IB) {S W : ℕ} {R : List (List Bool)}
    (hR : UV S R) (hRl : R.length = W + 1) (w : St) (hG : w GST = R.flatten)
    (hTD2 : (w TD2).length = 2 * ((W + 1) * S)) (hTST : (w TST).length = (W + 1) * S) {p j : ℕ}
    (hP : (w PADS).length = p * S) (hJ : w JW = unaryW W j) (hj : j ≤ W)
    (hTW : (w TW).length = W) (hTS : (w TSl).length = S) (hpj : p + j < 2 * (W + 1)) :
    exec V f (rdC dst) w dst = (R ++ R)[p + j]'(by simp; omega) ∧
      ∀ x, x ≠ GD → x ≠ GX → x ≠ JB → x ≠ CJW → x ≠ dst → exec V f (rdC dst) w x = w x := by
  have hd1 : dst ≠ GD ∧ dst ≠ GX ∧ dst ≠ JB ∧ dst ≠ CJW ∧ dst ≠ TSl ∧ dst ≠ GST ∧ dst ≠ TD2 ∧
      dst ≠ TST ∧ dst ≠ PADS ∧ dst ≠ JW ∧ dst ≠ TW ∧ dst ≠ 10 := by
    rcases hd with rfl | rfl <;> decide
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12⟩ := hd1
  have hRf : R.flatten.length = (W + 1) * S := by rw [length_flatten_of hR, hRl]
  have hRR : UV S (R ++ R) := hR.append hR
  rw [show rdC dst = ofList ([.cp GD TD2, .cp GX GST, .mv GD GX TST, .cp GX GST, .mv GD GX TST,
    .drop GD PADS, .cp JB JW, .cp CJW TW] ++ [.rep CJW jdBody, .cp dst TSl, .mv dst GD TSl]) from rfl,
    exec_ofList_append]
  -- the doubled store, skipped by the padding
  have h1 : exec V f (ofList [.cp GD TD2, .cp GX GST, .mv GD GX TST, .cp GX GST, .mv GD GX TST,
      .drop GD PADS, .cp JB JW, .cp CJW TW]) w GD = ((R ++ R).drop p).flatten := by
    simp only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
    rw [exec_mv_shift (d := GD) (s := GX) (c := TST) (x := R.flatten) (L := [])
      (w := Function.update (Function.update w GD (w TD2)) GX (Function.update w GD (w TD2) GST))
      (by decide)
      (by simp (config := {decide := true}) [Function.update_apply, hRf, hTST])
      (by simp (config := {decide := true}) [Function.update_apply, hG])]
    rw [exec_mv_shift (d := GD) (s := GX) (c := TST) (x := R.flatten) (L := []) (by decide)
      (by simp (config := {decide := true}) [Function.update_apply, hRf, hTST])
      (by simp (config := {decide := true}) [Function.update_apply, hG])]
    rw [exec_drop' (by decide)]
    simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [hRf, drop_append_drop' (by rw [List.length_append, hTD2, hRf]; omega), List.append_assoc,
      List.drop_left' (by rw [hTD2]; ring), hP, ← List.flatten_append, drop_flatten_uv hRR]
  have h2 : exec V f (ofList [.cp GD TD2, .cp GX GST, .mv GD GX TST, .cp GX GST, .mv GD GX TST,
      .drop GD PADS, .cp JB JW, .cp CJW TW]) w JB = unaryW W j := by
    simp only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
    rw [exec_mv_shift (d := GD) (s := GX) (c := TST) (x := R.flatten) (L := [])
      (w := Function.update (Function.update w GD (w TD2)) GX (Function.update w GD (w TD2) GST))
      (by decide)
      (by simp (config := {decide := true}) [Function.update_apply, hRf, hTST])
      (by simp (config := {decide := true}) [Function.update_apply, hG])]
    rw [exec_mv_shift (d := GD) (s := GX) (c := TST) (x := R.flatten) (L := []) (by decide)
      (by simp (config := {decide := true}) [Function.update_apply, hRf, hTST])
      (by simp (config := {decide := true}) [Function.update_apply, hG])]
    rw [exec_drop' (by decide)]
    simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    exact hJ
  have h3 : (exec V f (ofList [.cp GD TD2, .cp GX GST, .mv GD GX TST, .cp GX GST, .mv GD GX TST,
      .drop GD PADS, .cp JB JW, .cp CJW TW]) w CJW).length = W := by
    simp only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
    simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    exact hTW
  have ho : ∀ x, x ≠ GD → x ≠ GX → x ≠ JB → x ≠ CJW → exec V f (ofList [.cp GD TD2, .cp GX GST,
      .mv GD GX TST, .cp GX GST, .mv GD GX TST, .drop GD PADS, .cp JB JW, .cp CJW TW]) w x = w x :=
    fun x a1 a2 a3 a4 => exec_not_mem _ _ _ (by simp [wr, ofList, a1, a2, a3, a4])
  generalize exec V f (ofList [.cp GD TD2, .cp GX GST, .mv GD GX TST, .cp GX GST, .mv GD GX TST,
    .drop GD PADS, .cp JB JW, .cp CJW TW]) w = u at h1 h2 h3 ho
  -- the skip
  have I := exec_rep_inv (V := V) (f := f) (c := CJW) (B := jdBody)
    (fun r w' => r ≤ W → w' GD = (((R ++ R).drop p).drop (min r j)).flatten ∧
      w' JB = (unaryW W j).drop r ∧ ∀ x, x ≠ GD → x ≠ JB → x ≠ CJW → w' x = u x)
    (fun r w' ih hr => jdBody_step hj (hRR.drop p) (by rw [ho TSl (by decide) (by decide)
      (by decide) (by decide), hTS]) (by omega) (ih (by omega))) u
    (fun _ => ⟨by simp [h1], by simp [h2], fun _ _ _ _ => rfl⟩)
  rw [h3] at I
  obtain ⟨I1, -, I3⟩ := I le_rfl
  simp only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  generalize exec V f (.rep CJW jdBody) u = v at I1 I3
  rw [List.drop_drop, min_eq_right hj] at I1
  have hlt : p + j < (R ++ R).length := by simp; omega
  rw [exec_mv_pop (x := (R ++ R)[p + j]) (L := ((R ++ R).drop (p + j + 1)).flatten)
    (by simp only [not_or]; exact ⟨d1, d5, by decide⟩)
    (by simp [Function.update_apply]) (by simp [Function.update_apply, d5, I3 TSl (by decide)
      (by decide) (by decide), ho TSl (by decide) (by decide) (by decide) (by decide), hTS,
      hRR _ (List.getElem_mem _)])
    (by simp [Function.update_apply, Ne.symm d1, I1, flatten_drop_cons hlt])]
  refine ⟨by simp, fun x a1 a2 a3 a4 a5 => ?_⟩
  simp only [Function.update_apply, if_neg a5, if_neg a1]
  rw [I3 x a1 a3 a4, ho x a1 a2 a3 a4]

end ValVM

end SigabaNeo.Tape
