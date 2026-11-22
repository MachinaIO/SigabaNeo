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

abbrev GST : Fin 120 := 100
abbrev GS : Fin 120 := 101
abbrev GCNT : Fin 120 := 102
abbrev PADS : Fin 120 := 103
abbrev GD : Fin 120 := 104
abbrev GX : Fin 120 := 105
abbrev JW : Fin 120 := 106
abbrev JB : Fin 120 := 107
abbrev CJW : Fin 120 := 108
abbrev OUTW : Fin 120 := 109
abbrev TSl : Fin 120 := 110
abbrev TST : Fin 120 := 111
abbrev TD2 : Fin 120 := 112
abbrev TW : Fin 120 := 113
abbrev TPAD : Fin 120 := 114

/-! ### Reading an operand -/

/-- One round of the skip: drop a slot when the bit of the operand is set. -/
def jdBody : Code := ofList [.ifb JB (.drop GD TSl) .nop, .tl JB]

/-- **Read an operand** into `dst`: `GD := GST ++ GST`, skip the padding `|PADS|` and `j` slots
(the unary word `JW`), take one slot. -/
def rdC (dst : Fin 120) : Code :=
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
theorem exec_rdC {dst : Fin 120} (hd : dst = IA ∨ dst = IB) {S W : ℕ} {R : List (List Bool)}
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

/-! ### The gates -/

/-- **A block**: `RES := F (IA, IB)` on slots of `S` bits, under a context `Ctx` on the words
below `100` other than `IA`, `IB`, `RES`; it writes only words below `100`. -/
structure BlockSpec (V : ℕ) (f : List Bool → List Bool → List Bool) (blk : Code) (S : ℕ)
    (F : List Bool → List Bool → List Bool) (Ctx : St → Prop) : Prop where
  run : ∀ w, Ctx w → (w IA).length = S → (w IB).length = S → (w RES).length = S →
    exec V f blk w RES = F (w IA) (w IB)
  len : ∀ a b, a.length = S → b.length = S → (F a b).length = S
  ctx : ∀ w, Ctx w → Ctx (exec V f blk w)
  frame : ∀ w w', Ctx w → (∀ j : Fin 120, j.val < 100 → j ≠ IA → j ≠ IB → j ≠ RES → w' j = w j) →
    Ctx w'
  wr : ∀ j ∈ wr blk, j.val < 100

/-- One gate: read the two operands, the block, shift its result into the store. -/
def gBody (blk : Code) : Code :=
  ofList [.mv JW GS TW, rdC IA, .mv JW GS TW, rdC IB, .cp RES TSl, blk, .cp OUTW RES,
    .mv GST RES TSl, .drop PADS TSl]

/-- **The gates**: `|GCNT|` gates. -/
def gloopC (blk : Code) : Code := ofList [.cp JW TW, .cp PADS TPAD, .rep GCNT (gBody blk)]

/-- The slot of the operand `j`: the wire `1`, an input, a result (`C` if missing). -/
def slotOf (C : List Bool) (ins rs : List (List Bool)) (j : ℕ) : List Bool := (C :: ins ++ rs).getD j C

/-- One more result. -/
def glStep (F : List Bool → List Bool → List Bool) (C : List Bool) (ins : List (List Bool))
    (rs : List (List Bool)) (g : ℕ × ℕ) : List (List Bool) :=
  rs ++ [F (slotOf C ins rs g.1) (slotOf C ins rs g.2)]

/-- **The results of the gates.** -/
def gl (F : List Bool → List Bool → List Bool) (C : List Bool) (ins : List (List Bool))
    (gs : GateList) : List (List Bool) := gs.foldl (glStep F C ins) []

theorem gl_take_succ (F : List Bool → List Bool → List Bool) (C : List Bool) (ins : List (List Bool))
    (gs : GateList) {t : ℕ} (ht : t < gs.length) :
    gl F C ins (gs.take (t + 1)) = glStep F C ins (gl F C ins (gs.take t)) gs[t] := by
  rw [gl, List.take_succ, List.getElem?_eq_getElem ht, Option.toList_some, List.foldl_append]
  rfl

theorem gl_shape {F : List Bool → List Bool → List Bool} {S : ℕ}
    (hF : ∀ a b, a.length = S → b.length = S → (F a b).length = S) {C : List Bool}
    (hC : C.length = S) {ins : List (List Bool)} (hins : UV S ins) :
    ∀ gs : GateList, UV S (gl F C ins gs) ∧ (gl F C ins gs).length = gs.length := by
  intro gs
  have key : ∀ (gs : GateList) (rs : List (List Bool)), UV S rs →
      UV S (gs.foldl (glStep F C ins) rs) ∧ (gs.foldl (glStep F C ins) rs).length =
        rs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro rs h; simp [h]
    | cons g gs ih =>
      intro rs h
      have hs : ∀ j, (slotOf C ins rs j).length = S := fun j => by
        unfold slotOf
        rw [List.getD_eq_getElem?_getD]
        rcases e : (C :: ins ++ rs)[j]? with _ | x
        · simpa using hC
        · simp only [Option.getD_some]
          have hm := List.mem_of_getElem? e
          simp only [List.cons_append, List.mem_cons, List.mem_append] at hm
          rcases hm with rfl | hm | hm
          · exact hC
          · exact hins x hm
          · exact h x hm
      have h' : UV S (glStep F C ins rs g) := h.append (fun x hx => by
        simp at hx; subst hx; exact hF _ _ (hs _) (hs _))
      obtain ⟨u, l⟩ := ih _ h'
      refine ⟨u, ?_⟩
      rw [List.foldl_cons, l, glStep]; simp; ring
  have := key gs [] (fun _ h => by simp at h)
  simpa [gl] using this

/-- The slot `p + j` of the doubled rotated store. -/
theorem getElem_rot {C : List Bool} {L : List (List Bool)} {p j : ℕ} (hj : j < p + L.length)
    (h : p + j < (List.replicate p C ++ L ++ (List.replicate p C ++ L)).length) :
    (List.replicate p C ++ L ++ (List.replicate p C ++ L))[p + j] = L.getD j C := by
  apply Option.some.inj
  rw [← List.getElem?_eq_getElem h, List.append_assoc,
    List.getElem?_append_right (by simp), List.length_replicate, Nat.add_sub_cancel_left]
  by_cases hjl : j < L.length
  · rw [List.getElem?_append_left hjl, List.getD_eq_getElem _ _ hjl, List.getElem?_eq_getElem hjl]
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_replicate, if_pos (by omega), List.getD_eq_default _ _ (by omega)]

/-- The invariant of the gates after `t` gates. -/
structure GInv (V S W : ℕ) (Ctx : St → Prop) (F : List Bool → List Bool → List Bool)
    (C : List Bool) (ins : List (List Bool)) (gs : GateList) (w₀ : St) (t : ℕ) (w : St) : Prop where
  ctx : Ctx w
  gst : w GST = (List.replicate (W - 10 - t) C ++ (C :: ins ++ gl F C ins (gs.take t))).flatten
  gsw : w GS = gsW W (gs.drop t)
  pads : (w PADS).length = (W - 10 - t) * S
  jw : (w JW).length = W
  outw : 0 < t → w OUTW = (gl F C ins (gs.take t)).getLastD []
  tm : ∀ j, j = TSl ∨ j = TST ∨ j = TD2 ∨ j = TW → w j = w₀ j

/-- The data of the gates: the slots, the gate list, the templates. -/
structure GData (S W : ℕ) (C : List Bool) (ins : List (List Bool)) (gs : GateList) (w₀ : St) :
    Prop where
  hC : C.length = S
  hins : UV S ins
  hinsl : ins.length = 10
  hgs : gs.length + 10 ≤ W
  bnd : ∀ g ∈ gs, g.1 ≤ W ∧ g.2 ≤ W
  tsl : (w₀ TSl).length = S
  tst : (w₀ TST).length = (W + 1) * S
  td2 : (w₀ TD2).length = 2 * ((W + 1) * S)
  tw : (w₀ TW).length = W

theorem gInv_step {blk : Code} {S W : ℕ} {F : List Bool → List Bool → List Bool}
    {Ctx : St → Prop} (hB : BlockSpec V f blk S F Ctx) {C : List Bool} {ins : List (List Bool)}
    {gs : GateList} {w₀ : St} (hD : GData S W C ins gs w₀) {t : ℕ} (ht : t < gs.length) {w : St}
    (h : GInv V S W Ctx F C ins gs w₀ t w) :
    GInv V S W Ctx F C ins gs w₀ (t + 1) (exec V f (gBody blk) (Function.update w GCNT (w GCNT).tail)) := by
  set rs := gl F C ins (gs.take t) with hrs
  obtain ⟨hrsu, hrsl⟩ := gl_shape hB.len hD.hC hD.hins (gs.take t)
  rw [List.length_take, min_eq_left ht.le] at hrsl
  set L := C :: ins ++ rs with hL
  have hLl : L.length = 11 + t := by
    rw [hL, List.length_append, List.length_cons, hD.hinsl, hrsl]
  have hLu : UV S L := by
    intro x hx
    simp only [hL, List.cons_append, List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hx | hx
    exacts [hD.hC, hD.hins x hx, hrsu x hx]
  set p := W - 10 - t with hp
  have hp1 : 1 ≤ p := by have := hD.hgs; omega
  set R := List.replicate p C ++ L with hR
  have hRu : UV S R := UV.append (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact hD.hC) hLu
  have hRl : R.length = W + 1 := by rw [hR, List.length_append, List.length_replicate, hLl]; omega
  set g := gs[t] with hg
  have hgb := hD.bnd g (List.getElem_mem _)
  have hdrop : gs.drop t = g :: gs.drop (t + 1) := List.drop_eq_getElem_cons ht
  -- the state after the round's counter
  have c0 : Ctx (Function.update w GCNT (w GCNT).tail) :=
    hB.frame _ _ h.ctx fun j hj _ _ _ => Function.update_of_ne (by rintro rfl; simp at hj) _ _
  have e0 : ∀ j, j ≠ GCNT → Function.update w GCNT (w GCNT).tail j = w j :=
    fun j hj => Function.update_of_ne hj _ _
  generalize hw0 : Function.update w GCNT (w GCNT).tail = w0 at c0 e0
  have tm0 : ∀ j, j = TSl ∨ j = TST ∨ j = TD2 ∨ j = TW → w0 j = w₀ j := fun j hj => by
    rw [e0 j (by rcases hj with rfl | rfl | rfl | rfl <;> decide), h.tm j hj]
  rw [gBody, show [Code.mv JW GS TW, rdC IA, .mv JW GS TW, rdC IB, .cp RES TSl, blk, .cp OUTW RES,
    .mv GST RES TSl, .drop PADS TSl] = [Code.mv JW GS TW, rdC IA] ++ ([.mv JW GS TW, rdC IB] ++
    [.cp RES TSl, blk, .cp OUTW RES, .mv GST RES TSl, .drop PADS TSl]) from rfl,
    exec_ofList_append, exec_ofList_append]
  -- the first operand
  have hGS0 : w0 GS = unaryW W g.1 ++ (unaryW W g.2 ++ gsW W (gs.drop (t + 1))) := by
    rw [e0 GS (by decide), h.gsw, hdrop, gsW_cons, List.append_assoc]
  have hu1 := length_unaryW hgb.1
  have hu2 := length_unaryW hgb.2
  -- reading an operand
  have RD : ∀ (dst : Fin 120), (dst = IA ∨ dst = IB) → ∀ (u : St) (j : ℕ) (rest : List Bool),
      j ≤ W → u GS = unaryW W j ++ rest → (u JW).length = W → u GST = R.flatten →
      (u PADS).length = p * S → (∀ x, x = TSl ∨ x = TST ∨ x = TD2 ∨ x = TW → u x = w₀ x) →
      exec V f (ofList [.mv JW GS TW, rdC dst]) u dst = slotOf C ins rs j ∧
      exec V f (ofList [.mv JW GS TW, rdC dst]) u GS = rest ∧
      exec V f (ofList [.mv JW GS TW, rdC dst]) u JW = unaryW W j ∧
      ∀ x, x ≠ GD → x ≠ GX → x ≠ JB → x ≠ CJW → x ≠ dst → x ≠ JW → x ≠ GS →
        exec V f (ofList [.mv JW GS TW, rdC dst]) u x = u x := by
    intro dst hdst u j rest hj hGS hJW hG hP htm
    have dd : dst ≠ JW ∧ dst ≠ GS ∧ dst ≠ GD ∧ dst ≠ GX ∧ dst ≠ JB ∧ dst ≠ CJW := by
      rcases hdst with rfl | rfl <;> decide
    simp only [exec_ofList, List.foldl_cons, List.foldl_nil]
    rw [exec_mv_pop (by decide) (by rw [hJW, htm TW (by decide), hD.tw])
      (by rw [length_unaryW hj, htm TW (by decide), hD.tw]) hGS]
    obtain ⟨r1, r2⟩ := exec_rdC (V := V) (f := f) (dst := dst) hdst hRu hRl
      (Function.update (Function.update u GS rest) JW (unaryW W j))
      (by simp (config := {decide := true}) [Function.update_apply, hG])
      (by simp (config := {decide := true}) [Function.update_apply, htm TD2 (by decide), hD.td2])
      (by simp (config := {decide := true}) [Function.update_apply, htm TST (by decide), hD.tst])
      (p := p) (by simp (config := {decide := true}) [Function.update_apply, hP])
      (by simp (config := {decide := true}) [Function.update_apply]) hj
      (by simp (config := {decide := true}) [Function.update_apply, htm TW (by decide), hD.tw])
      (by simp (config := {decide := true}) [Function.update_apply, htm TSl (by decide), hD.tsl])
      (by omega)
    refine ⟨?_, ?_, ?_, fun x a1 a2 a3 a4 a5 a6 a7 => ?_⟩
    · rw [r1, slotOf]; exact getElem_rot (C := C) (L := L) (by omega) _
    · rw [r2 GS (by decide) (by decide) (by decide) (by decide) dd.2.1.symm]
      simp (config := {decide := true}) [Function.update_apply]
    · rw [r2 JW (by decide) (by decide) (by decide) (by decide) dd.1.symm]
      simp (config := {decide := true}) [Function.update_apply]
    · rw [r2 x a1 a2 a3 a4 a5]; simp [Function.update_apply, a6, a7]
  have hG0 : w0 GST = R.flatten := by
    rw [e0 GST (by decide), h.gst, hR, hL, hp, hrs, List.flatten_append]
  obtain ⟨a1, a2, a3, a4⟩ := RD IA (Or.inl rfl) w0 g.1 _ hgb.1 hGS0
    (by rw [e0 JW (by decide), h.jw]) hG0 (by rw [e0 PADS (by decide), h.pads]) tm0
  generalize exec V f (ofList [.mv JW GS TW, rdC IA]) w0 = w1 at a1 a2 a3 a4
  have tm1 : ∀ x, x = TSl ∨ x = TST ∨ x = TD2 ∨ x = TW → w1 x = w₀ x := fun x hx => by
    rw [a4 x (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide), tm0 x hx]
  obtain ⟨b1, b2, b3, b4⟩ := RD IB (Or.inr rfl) w1 g.2 _ hgb.2 a2 (by rw [a3, length_unaryW hgb.1])
    (by rw [a4 GST (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hG0])
    (by rw [a4 PADS (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), e0 PADS (by decide), h.pads]) tm1
  generalize exec V f (ofList [.mv JW GS TW, rdC IB]) w1 = w2 at b1 b2 b3 b4
  have c2 : Ctx w2 := hB.frame _ _ c0 fun j hj h1 h2 h3 => by
    have : j ≠ GD ∧ j ≠ GX ∧ j ≠ JB ∧ j ≠ CJW ∧ j ≠ JW ∧ j ≠ GS := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rintro rfl; simp at hj)
    rw [b4 j this.1 this.2.1 this.2.2.1 this.2.2.2.1 h2 this.2.2.2.2.1 this.2.2.2.2.2,
      a4 j this.1 this.2.1 this.2.2.1 this.2.2.2.1 h1 this.2.2.2.2.1 this.2.2.2.2.2]
  have w2IA : w2 IA = slotOf C ins rs g.1 := by
    rw [b4 IA (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), a1]
  have hsl : ∀ j, (slotOf C ins rs j).length = S := fun j => by
    unfold slotOf
    rw [List.getD_eq_getElem?_getD]
    rcases e : (C :: ins ++ rs)[j]? with _ | x
    · simpa using hD.hC
    · exact hLu x (List.mem_of_getElem? e)
  have tm2 : ∀ x, x = TSl ∨ x = TST ∨ x = TD2 ∨ x = TW → w2 x = w₀ x := fun x hx => by
    rw [b4 x (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide), tm1 x hx]
  -- the block
  simp only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  set r := F (slotOf C ins rs g.1) (slotOf C ins rs g.2) with hr
  have hrl : r.length = S := hB.len _ _ (hsl _) (hsl _)
  have c3 : Ctx (Function.update w2 RES (w2 TSl)) :=
    hB.frame _ _ c2 fun j _ _ _ h3 => Function.update_of_ne h3 _ _
  have hb := hB.run _ c3 (by rw [Function.update_of_ne (by decide), w2IA, hsl])
    (by rw [Function.update_of_ne (by decide), b1, hsl])
    (by rw [Function.update_self, tm2 TSl (by decide), hD.tsl])
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), w2IA, b1, ← hr] at hb
  have hbo : ∀ j : Fin 120, 100 ≤ j.val → exec V f blk (Function.update w2 RES (w2 TSl)) j =
      Function.update w2 RES (w2 TSl) j :=
    fun j hj => exec_not_mem _ _ _ (fun hm => by have := hB.wr j hm; omega)
  have c4 := hB.ctx _ c3
  generalize exec V f blk (Function.update w2 RES (w2 TSl)) = w4 at hb hbo c4
  have w4o : ∀ j : Fin 120, 100 ≤ j.val → j ≠ GS → j ≠ JW → w4 j = w2 j := fun j hj h1 h2 => by
    rw [hbo j hj, Function.update_of_ne (by rintro rfl; simp at hj)]
  rw [exec_mv_push (by decide) (by
    simp (config := {decide := true}) only [Function.update_apply, if_false, if_true]
    rw [hb, hrl, w4o TSl (by decide) (by decide) (by decide), tm2 TSl (by decide), hD.tsl])]
  rw [exec_drop' (by decide)]
  have w4G : w4 GST = R.flatten := by
    rw [w4o GST (by decide) (by decide) (by decide), b4 GST (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), a4 GST (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), hG0]
  have w4P : (w4 PADS).length = p * S := by
    rw [w4o PADS (by decide) (by decide) (by decide), b4 PADS (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), a4 PADS (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), e0 PADS (by decide), h.pads]
  have w4S : (w4 TSl).length = S := by
    rw [w4o TSl (by decide) (by decide) (by decide), tm2 TSl (by decide), hD.tsl]
  have hgl : gl F C ins (gs.take (t + 1)) = rs ++ [r] := by
    rw [gl_take_succ F C ins gs ht, glStep]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_, fun x hx => ?_⟩
  · refine hB.frame _ _ c4 fun j hj _ _ h3 => ?_
    have h1 : j ≠ PADS := by rintro rfl; simp at hj
    have h2 : j ≠ GST := by rintro rfl; simp at hj
    have h4 : j ≠ OUTW := by rintro rfl; simp at hj
    simp only [Function.update_apply, if_neg h1, if_neg h2, if_neg h3, if_neg h4]
  · simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [w4G, hb, w4S, shift_val (V := S) hRu hrl, hR, List.append_assoc,
      List.drop_append_of_le_length (by simp; omega), List.drop_replicate, hgl, hL]
    congr 1
    simp only [List.cons_append, List.append_assoc]
    congr 2
  · simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [hbo GS (by decide), Function.update_of_ne (by decide), b2]
  · simp (config := {decide := true}) only [Function.update_apply, if_true, if_false,
      List.length_drop]
    rw [w4P, w4o TSl (by decide) (by decide) (by decide), tm2 TSl (by decide), hD.tsl]
    rw [show W - 10 - (t + 1) = p - 1 by omega, Nat.sub_one_mul]
  · simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [hbo JW (by decide), Function.update_of_ne (by decide), b3, length_unaryW hgb.2]
  · simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [hb, hgl]; simp
  · have : x ≠ PADS ∧ x ≠ GST ∧ x ≠ RES ∧ x ≠ OUTW := by
      rcases hx with rfl | rfl | rfl | rfl <;> decide
    simp only [Function.update_apply, if_neg this.1, if_neg this.2.1, if_neg this.2.2.1,
      if_neg this.2.2.2]
    rw [w4o x (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide), tm2 x hx]

/-- **The gates of a predicate on the machine**: from the store
`C^(W − 10) ++ [C, in₀, …, in₉]` and the gate word `gsW W gs`, after `|GCNT| = |gs|` gates the
store holds the results `gl F C ins gs` (after `C^(W − 10 − |gs|) ++ [C, in₀, …, in₉]`), `OUTW` the
last one. -/
theorem exec_gloopC {blk : Code} {S W : ℕ} {F : List Bool → List Bool → List Bool}
    {Ctx : St → Prop} (hB : BlockSpec V f blk S F Ctx) {C : List Bool} {ins : List (List Bool)}
    {gs : GateList} (w : St) (hD : GData S W C ins gs w) (hc : Ctx w)
    (hG : w GST = (List.replicate (W - 10) C ++ (C :: ins)).flatten) (hGS : w GS = gsW W gs)
    (hN : (w GCNT).length = gs.length) (hP : (w TPAD).length = (W - 10) * S) :
    exec V f (gloopC blk) w GST =
        (List.replicate (W - 10 - gs.length) C ++ (C :: ins ++ gl F C ins gs)).flatten ∧
      (gs ≠ [] → exec V f (gloopC blk) w OUTW = (gl F C ins gs).getLastD []) ∧
      Ctx (exec V f (gloopC blk) w) ∧
      ∀ j, j ∉ wr (gloopC blk) → exec V f (gloopC blk) w j = w j := by
  refine ⟨?_, ?_, ?_, fun j hj => exec_not_mem _ _ _ hj⟩
  all_goals
    simp only [gloopC, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
    set w1 := Function.update (Function.update w JW (w TW)) PADS
      (Function.update w JW (w TW) TPAD) with hw1
    have e1 : ∀ j, j ≠ JW → j ≠ PADS → w1 j = w j := fun j h1 h2 => by
      simp [hw1, Function.update_apply, h1, h2]
    have hD1 : GData S W C ins gs w1 := ⟨hD.hC, hD.hins, hD.hinsl, hD.hgs, hD.bnd,
      by rw [e1 TSl (by decide) (by decide)]; exact hD.tsl,
      by rw [e1 TST (by decide) (by decide)]; exact hD.tst,
      by rw [e1 TD2 (by decide) (by decide)]; exact hD.td2,
      by rw [e1 TW (by decide) (by decide)]; exact hD.tw⟩
    have I := exec_rep_inv (V := V) (f := f) (c := GCNT) (B := gBody blk)
      (fun t w' => t ≤ gs.length → GInv V S W Ctx F C ins gs w1 t w')
      (fun t w' ih ht => gInv_step hB hD1 (by omega) (ih (by omega))) w1
      (fun _ => ⟨hB.frame _ _ hc fun j hj _ _ _ => e1 j (by rintro rfl; simp at hj)
          (by rintro rfl; simp at hj),
        by rw [e1 GST (by decide) (by decide), hG]; simp [gl],
        by rw [e1 GS (by decide) (by decide), hGS]; simp,
        by simp (config := {decide := true}) [hw1, Function.update_apply, hP],
        by simp (config := {decide := true}) [hw1, Function.update_apply, hD.tw],
        fun h => absurd h (lt_irrefl 0), fun _ _ => rfl⟩)
    rw [show (w1 GCNT).length = gs.length by rw [e1 GCNT (by decide) (by decide), hN]] at I
    have I' := I le_rfl
  · rw [I'.gst, List.take_of_length_le le_rfl]
  · intro hne; rw [I'.outw (List.length_pos_iff.mpr hne), List.take_of_length_le le_rfl]
  · exact I'.ctx

end ValVM

end SigabaNeo.Tape
