import SigabaNeo.Lib.Lattices.ProgAlgo.ValGates

/-!
# Register programs on the word machine

`rloopC blk`: for a **slot program** `sp` (instructions `(d, a, b)`: slot `d := F (slot a, slot b)`,
the word `spW W sp` on `GS`, each slot as a unary word of `W` bits) and a block `blk` computing
`RES := F (IA, IB)` on slots of `S` bits (`BlockSpec`), each instruction reads its two operands
from the **store** `GST` and writes the result back into the slot `d`.

The store holds `W + 1` slots, `C :: ins ++ regs` (the slot of the wire `1`, the inputs, the
registers), and is never rotated. An operand `j ≤ W` is read by `rdC` (with no padding); the result
is written by `wrC`: two shift loops over the `W` bits of the unary word of `d` rebuild the store
as `R.take d ++ [r] ++ R.drop (d + 1)` in a shift register.

* `rl F C R sp`: the semantics on lists of slots (`List.set`);
* **`exec_rloopC`**: after the `|sp|` instructions, `GST` holds `(rl F C R sp).flatten`.

The link to register programs (`RP.run`, `RP.toSLP`) is below, in terms of the slot encoding.
-/

namespace SigabaNeo.Tape

namespace ValVM

open SigabaNeo.Lattices SigabaNeo.Lattices.SLP SigabaNeo.Tape.Prog

set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

variable {V : ℕ} {f : List Bool → List Bool → List Bool}

/-! ### Slot programs and their semantics -/

/-- A slot program: instructions `(d, a, b)`, slot `d := F (slot a, slot b)`. -/
abbrev SProg := List (ℕ × ℕ × ℕ)

/-- The word of a slot program: the three slots of each instruction as unary words of `W` bits. -/
def spW (W : ℕ) (sp : SProg) : List Bool :=
  sp.flatMap fun g => unaryW W g.1 ++ unaryW W g.2.1 ++ unaryW W g.2.2

theorem spW_cons (W : ℕ) (g : ℕ × ℕ × ℕ) (sp : SProg) :
    spW W (g :: sp) = unaryW W g.1 ++ unaryW W g.2.1 ++ unaryW W g.2.2 ++ spW W sp := rfl

theorem length_spW {W : ℕ} {sp : SProg} (h : ∀ g ∈ sp, g.1 ≤ W ∧ g.2.1 ≤ W ∧ g.2.2 ≤ W) :
    (spW W sp).length = sp.length * (3 * W) := by
  induction sp with
  | nil => simp [spW]
  | cons g sp ih =>
    have hg := h g (by simp)
    rw [spW_cons, List.length_append, List.length_append, List.length_append, length_unaryW hg.1,
      length_unaryW hg.2.1, length_unaryW hg.2.2, ih (fun g' hg' => h g' (by simp [hg'])),
      List.length_cons]
    ring

/-- One instruction on the slots. -/
def rlStep (F : List Bool → List Bool → List Bool) (C : List Bool) (R : List (List Bool))
    (g : ℕ × ℕ × ℕ) : List (List Bool) :=
  R.set g.1 (F (R.getD g.2.1 C) (R.getD g.2.2 C))

/-- **The slots after a slot program.** -/
def rl (F : List Bool → List Bool → List Bool) (C : List Bool) (R : List (List Bool))
    (sp : SProg) : List (List Bool) := sp.foldl (rlStep F C) R

theorem rl_nil (F : List Bool → List Bool → List Bool) (C : List Bool) (R : List (List Bool)) :
    rl F C R [] = R := rfl

theorem rl_cons (F : List Bool → List Bool → List Bool) (C : List Bool) (R : List (List Bool))
    (g : ℕ × ℕ × ℕ) (sp : SProg) : rl F C R (g :: sp) = rl F C (rlStep F C R g) sp := rfl

theorem rl_take_succ (F : List Bool → List Bool → List Bool) (C : List Bool) (R : List (List Bool))
    (sp : SProg) {t : ℕ} (ht : t < sp.length) :
    rl F C R (sp.take (t + 1)) = rlStep F C (rl F C R (sp.take t)) sp[t] := by
  rw [rl, List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some, List.foldl_append]
  rfl

theorem rl_shape {F : List Bool → List Bool → List Bool} {S : ℕ}
    (hF : ∀ a b, a.length = S → b.length = S → (F a b).length = S) {C : List Bool}
    (hC : C.length = S) : ∀ (sp : SProg) (R : List (List Bool)), UV S R →
      UV S (rl F C R sp) ∧ (rl F C R sp).length = R.length := by
  intro sp
  induction sp with
  | nil => intro R h; exact ⟨h, rfl⟩
  | cons g sp ih =>
    intro R h
    have hs : ∀ j, (R.getD j C).length = S := fun j => by
      rw [List.getD_eq_getElem?_getD]
      rcases e : R[j]? with _ | x
      · simpa using hC
      · exact h x (List.mem_of_getElem? e)
    have h' : UV S (rlStep F C R g) := fun x hx => by
      rcases List.mem_or_eq_of_mem_set hx with hx | rfl
      · exact h x hx
      · exact hF _ _ (hs _) (hs _)
    obtain ⟨u, l⟩ := ih _ h'
    exact ⟨u, by rw [rl_cons, l, rlStep, List.length_set]⟩

/-! ### Registers -/

/-- The unary word of the destination. -/
abbrev JD : Fin 120 := 114

/-! ### The shift loops of a write -/

/-- One round of a shift loop: when the bit of `JB` is `sel`, shift a slot of `GD` into `GX`. -/
def wBody (sel : Bool) : Code :=
  ofList [if sel then .ifb JB (.mv GX GD TSl) .nop else .ifb JB .nop (.mv GX GD TSl), .tl JB]

/-- The number of slots shifted after `r` rounds. -/
def wcnt (sel : Bool) (d r : ℕ) : ℕ := if sel then min r d else r - min r d

theorem wcnt_succ (sel : Bool) {d r : ℕ} :
    wcnt sel d (r + 1) = wcnt sel d r + if decide (r < d) = sel then 1 else 0 := by
  cases sel <;> by_cases h : r < d <;> simp [wcnt, h] <;> omega

theorem wcnt_le (sel : Bool) (d r : ℕ) : wcnt sel d r ≤ wcnt sel d (r + 1) := by
  rw [wcnt_succ]; omega

theorem wcnt_mono (sel : Bool) (d : ℕ) {r r' : ℕ} (h : r ≤ r') : wcnt sel d r ≤ wcnt sel d r' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (wcnt_le sel d _)

/-- The shift register after shifting `n` slots of `L` into `X`. -/
theorem shift_take {X L : List (List Bool)} {n : ℕ} (hn : n < L.length) (hX : n ≤ X.length) :
    (((X ++ L.take n).drop n) ++ [L[n]]).drop 1 = (X ++ L.take (n + 1)).drop (n + 1) := by
  rw [← List.drop_append_of_le_length (by simp; omega), List.drop_drop, List.append_assoc,
    ← List.take_concat_get' L n hn, Nat.add_comm]

theorem wBody_step {S W d : ℕ} (hdW : d ≤ W) (sel : Bool) {X L : List (List Bool)} (hX : UV S X)
    (hL : UV S L) (hcnt : wcnt sel d W ≤ L.length) (hXl : L.length ≤ X.length) {w₀ : St}
    (hTS : (w₀ TSl).length = S) {r : ℕ} (hr : r < W) {w : St}
    (h : w GD = (L.drop (wcnt sel d r)).flatten ∧
      w GX = ((X ++ L.take (wcnt sel d r)).drop (wcnt sel d r)).flatten ∧
      w JB = (unaryW W d).drop r ∧ ∀ x, x ≠ GD → x ≠ GX → x ≠ JB → x ≠ CJW → w x = w₀ x) :
    let w' := exec V f (wBody sel) (Function.update w CJW (w CJW).tail)
    w' GD = (L.drop (wcnt sel d (r + 1))).flatten ∧
      w' GX = ((X ++ L.take (wcnt sel d (r + 1))).drop (wcnt sel d (r + 1))).flatten ∧
      w' JB = (unaryW W d).drop (r + 1) ∧ ∀ x, x ≠ GD → x ≠ GX → x ≠ JB → x ≠ CJW → w' x = w₀ x := by
  obtain ⟨hg, hx, hb, ho⟩ := h
  have hTS' : (w TSl).length = S := by
    rw [ho TSl (by decide) (by decide) (by decide) (by decide), hTS]
  have hh : hd (Function.update w CJW (w CJW).tail JB) = decide (r < d) := by
    rw [Function.update_of_ne (by decide), hb, hd_unaryW_drop hdW hr]
  have hsucc := wcnt_succ sel (d := d) (r := r)
  have hmono := wcnt_mono sel d (show r + 1 ≤ W by omega)
  set n := wcnt sel d r with hn
  set u := Function.update w CJW (w CJW).tail with hu
  have uo : ∀ x, x ≠ CJW → u x = w x := fun x h => Function.update_of_ne h _ _
  have hJB : (exec V f (.tl JB) u) JB = (unaryW W d).drop (r + 1) := by
    simp only [exec_tl', Function.update_self, uo JB (by decide), hb, List.tail_drop]
  have hbody : exec V f (wBody sel) u = exec V f (.tl JB)
      (if decide (r < d) = sel then exec V f (.mv GX GD TSl) u else u) := by
    cases sel <;> by_cases h : r < d <;>
      simp only [wBody, exec_ofList, List.foldl_cons, List.foldl_nil, exec_ifb', hh, h,
        decide_true, decide_false, if_true, if_false, Bool.false_eq_true, Bool.true_eq_false,
        ite_true, ite_false] <;> rfl
  by_cases hs : decide (r < d) = sel
  · -- a slot is shifted
    rw [if_pos hs] at hsucc
    have hnl : n < L.length := by omega
    have hGD : u GD = L[n] ++ (L.drop (n + 1)).flatten := by
      rw [uo GD (by decide), hg, List.drop_eq_getElem_cons hnl, List.flatten_cons]
    have SH := exec_mv_shift (V := V) (f := f) (d := GX) (s := GD) (c := TSl) (w := u) (by decide)
      (by rw [uo TSl (by decide), hTS', hL _ (List.getElem_mem _)]) hGD
    have hex : exec V f (wBody sel) u = exec V f (.tl JB) (exec V f (.mv GX GD TSl) u) := by
      rw [hbody, if_pos hs]
    show (exec V f (wBody sel) u) GD = _ ∧ _
    rw [hex, SH, hsucc]
    refine ⟨?_, ?_, ?_, fun x a1 a2 a3 a4 => ?_⟩
    · simp (config := {decide := true}) [exec_tl', Function.update_apply]
    · simp only [exec_tl', Function.update_apply, if_true, if_false]
      simp (config := {decide := true}) only [if_true, if_false]
      rw [uo GX (by decide), hx, hL _ (List.getElem_mem _), shift_val (V := S)
        ((hX.append (hL.take n)).drop n) (hL _ (List.getElem_mem _)), shift_take hnl (by omega)]
    · simp only [exec_tl', Function.update_apply]
      simp (config := {decide := true}) only [if_true, if_false]
      rw [uo JB (by decide), hb, List.tail_drop]
    · simp only [exec_tl', Function.update_apply, if_neg a1, if_neg a2, if_neg a3]
      rw [uo x a4, ho x a1 a2 a3 a4]
  · -- no shift
    rw [if_neg hs, Nat.add_zero] at hsucc
    have hex : exec V f (wBody sel) u = exec V f (.tl JB) u := by
      rw [hbody, if_neg hs]
    show (exec V f (wBody sel) u) GD = _ ∧ _
    rw [hex, hsucc, Nat.add_zero]
    refine ⟨?_, ?_, hJB, fun x a1 a2 a3 a4 => ?_⟩
    · simp only [exec_tl', Function.update_apply]
      simp (config := {decide := true}) only [if_true, if_false]
      rw [uo GD (by decide), hg]
    · simp only [exec_tl', Function.update_apply]
      simp (config := {decide := true}) only [if_true, if_false]
      rw [uo GX (by decide), hx]
    · simp only [exec_tl', Function.update_apply, if_neg a3]
      rw [uo x a4, ho x a1 a2 a3 a4]

/-- **A shift loop**: `W` rounds of `wBody sel` shift `wcnt sel d W` slots of `L` (on `GD`) into the
shift register holding `X` (on `GX`). -/
theorem exec_wloop {S W d : ℕ} (hdW : d ≤ W) (sel : Bool) {X L : List (List Bool)} (hX : UV S X)
    (hL : UV S L) (hcnt : wcnt sel d W ≤ L.length) (hXl : L.length ≤ X.length) (u : St)
    (hTS : (u TSl).length = S) (hg : u GD = L.flatten) (hx : u GX = X.flatten)
    (hb : u JB = unaryW W d) (hc : (u CJW).length = W) :
    exec V f (.rep CJW (wBody sel)) u GD = (L.drop (wcnt sel d W)).flatten ∧
      exec V f (.rep CJW (wBody sel)) u GX =
        ((X ++ L.take (wcnt sel d W)).drop (wcnt sel d W)).flatten ∧
      ∀ x, x ≠ GD → x ≠ GX → x ≠ JB → x ≠ CJW → exec V f (.rep CJW (wBody sel)) u x = u x := by
  have I := exec_rep_inv (V := V) (f := f) (c := CJW) (B := wBody sel)
    (fun r w' => r ≤ W → w' GD = (L.drop (wcnt sel d r)).flatten ∧
      w' GX = ((X ++ L.take (wcnt sel d r)).drop (wcnt sel d r)).flatten ∧
      w' JB = (unaryW W d).drop r ∧ ∀ x, x ≠ GD → x ≠ GX → x ≠ JB → x ≠ CJW → w' x = u x)
    (fun r w' ih hr => wBody_step hdW sel hX hL hcnt hXl hTS (by omega) (ih (by omega))) u
    (fun _ => ⟨by simp [wcnt, hg], by simp [wcnt, hx], by simp [hb], fun _ _ _ _ _ => rfl⟩)
  rw [hc] at I
  obtain ⟨I1, I2, -, I4⟩ := I le_rfl
  exact ⟨I1, I2, I4⟩

theorem exec_ofList_single (c : Code) (w : St) : exec V f (ofList [c]) w = exec V f c w := rfl

/-- **Write `RES` into the slot `JD`** of the store `GST`. -/
def wrC : Code :=
  ofList [.cp GD GST, .cp GX GST, .cp JB JD, .cp CJW TW, .rep CJW (wBody true), .mv GX RES TSl,
    .drop GD TSl, .cp JB JD, .cp CJW TW, .rep CJW (wBody false), .cp GST GX]

theorem wr_wrC_mem : ∀ x ∈ wr wrC, x = RES ∨ 100 ≤ x.val := by decide

/-- **Writing a slot**: the store `R` (`W + 1` slots of `S` bits) becomes `R.set d (RES)`. -/
theorem exec_wrC {S W d : ℕ} (hdW : d ≤ W) {R : List (List Bool)} (hR : UV S R)
    (hRl : R.length = W + 1) (w : St) (hG : w GST = R.flatten) (hJ : w JD = unaryW W d)
    (hTW : (w TW).length = W) (hTS : (w TSl).length = S) (hRES : (w RES).length = S) :
    exec V f wrC w GST = (R.set d (w RES)).flatten ∧
      ∀ x, x ∉ wr wrC → exec V f wrC w x = w x := by
  refine ⟨?_, fun x hx => exec_not_mem _ _ _ hx⟩
  set r := w RES with hr
  rw [show wrC = ofList ([.cp GD GST, .cp GX GST, .cp JB JD, .cp CJW TW] ++
    ([.rep CJW (wBody true)] ++ ([.mv GX RES TSl, .drop GD TSl, .cp JB JD, .cp CJW TW] ++
    ([.rep CJW (wBody false)] ++ [.cp GST GX])))) from rfl, exec_ofList_append, exec_ofList_append,
    exec_ofList_append, exec_ofList_append, exec_ofList_single, exec_ofList_single,
    exec_ofList_single]
  -- the first loop
  set u1 := exec V f (ofList [.cp GD GST, .cp GX GST, .cp JB JD, .cp CJW TW]) w with hu1
  have e1 : ∀ x, x ≠ GD → x ≠ GX → x ≠ JB → x ≠ CJW → u1 x = w x :=
    fun x a1 a2 a3 a4 => exec_not_mem _ _ _ (by simp [wr, ofList, a1, a2, a3, a4])
  have u1g : u1 GD = R.flatten := by simp (config := {decide := true}) [hu1, exec_ofList, exec_cp', Function.update_apply, hG]
  have u1x : u1 GX = R.flatten := by simp (config := {decide := true}) [hu1, exec_ofList, exec_cp', Function.update_apply, hG]
  have u1b : u1 JB = unaryW W d := by simp (config := {decide := true}) [hu1, exec_ofList, exec_cp', Function.update_apply, hJ]
  have u1c : (u1 CJW).length = W := by
    simp (config := {decide := true}) [hu1, exec_ofList, exec_cp', Function.update_apply, hTW]
  have hd1 : wcnt true d W = d := by simp [wcnt]; omega
  obtain ⟨L1, L2, L3⟩ := exec_wloop (V := V) (f := f) hdW true hR hR (by rw [hd1]; omega) le_rfl u1
    (by rw [e1 TSl (by decide) (by decide) (by decide) (by decide), hTS]) u1g u1x u1b u1c
  rw [hd1] at L1 L2
  generalize exec V f (.rep CJW (wBody true)) u1 = u2 at L1 L2 L3
  -- the result and the dropped slot
  have hRd : UV S (R.drop d) := hR.drop d
  have hdl : d < R.length := by omega
  have u2r : (u2 RES).length = S := by
    rw [L3 RES (by decide) (by decide) (by decide) (by decide), e1 RES (by decide) (by decide)
      (by decide) (by decide), ← hr, hRES]
  have u2s : (u2 TSl).length = S := by
    rw [L3 TSl (by decide) (by decide) (by decide) (by decide), e1 TSl (by decide) (by decide)
      (by decide) (by decide), hTS]
  have u2rv : u2 RES = r := by
    rw [L3 RES (by decide) (by decide) (by decide) (by decide), e1 RES (by decide) (by decide)
      (by decide) (by decide)]
  have hr' : r.length = S := hRES
  set X2 := (R ++ R.take d ++ [r]).drop (d + 1) with hX2
  set u3 := exec V f (ofList [.mv GX RES TSl, .drop GD TSl, .cp JB JD, .cp CJW TW]) u2 with hu3
  have hX2u : UV S X2 := ((hR.append (hR.take d)).append
    (fun x hx => by simp at hx; subst hx; exact hr')).drop _
  have u3x : u3 GX = X2.flatten := by
    simp only [hu3, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
    rw [exec_mv_push (by decide) (by rw [u2r, u2s])]
    try simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [exec_drop' (by decide)]
    try simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [L2, u2rv, u2s, shift_val (V := S) ((hR.append (hR.take d)).drop d) hr', hX2,
      ← List.drop_append_of_le_length (by simp; omega), List.drop_drop]
  have u3g : u3 GD = (R.drop (d + 1)).flatten := by
    simp only [hu3, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
    rw [exec_mv_push (by decide) (by rw [u2r, u2s])]
    try simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [exec_drop' (by decide)]
    try simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [L1, u2s, ← Nat.one_mul S, drop_flatten_uv hRd, List.drop_drop, Nat.add_comm]
  have u3b : u3 JB = unaryW W d := by
    simp only [hu3, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
    try simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [exec_mv_push (by decide) (by rw [u2r, u2s])]
    try simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [exec_drop' (by decide)]
    try simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [L3 JD (by decide) (by decide) (by decide) (by decide), e1 JD (by decide) (by decide)
      (by decide) (by decide), hJ]
  have u3c : (u3 CJW).length = W := by
    simp only [hu3, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
    try simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [exec_mv_push (by decide) (by rw [u2r, u2s])]
    try simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [exec_drop' (by decide)]
    try simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [L3 TW (by decide) (by decide) (by decide) (by decide), e1 TW (by decide) (by decide)
      (by decide) (by decide), hTW]
  have u3s : (u3 TSl).length = S := by
    simp only [hu3, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
    try simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [exec_mv_push (by decide) (by rw [u2r, u2s])]
    try simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [exec_drop' (by decide)]
    try simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    exact u2s
  -- the second loop
  have hd2 : wcnt false d W = W - d := by simp [wcnt, min_eq_right hdW]
  have hX2l : X2.length = W + 1 := by simp [hX2, hRl]; omega
  have hL2l : (R.drop (d + 1)).length = W - d := by simp [hRl]
  obtain ⟨-, M2, -⟩ := exec_wloop (V := V) (f := f) hdW false hX2u (hR.drop (d + 1))
    (by rw [hd2, hL2l]) (by rw [hL2l, hX2l]; omega) u3 u3s u3g u3x u3b u3c
  rw [exec_cp', Function.update_self]
  rw [M2, hd2, ← hL2l, List.take_length, hX2, ← List.drop_append_of_le_length (by simp; omega),
    List.drop_drop, List.append_assoc, List.append_assoc,
    List.drop_append_of_le_length (by simp; omega)]
  rw [show d + 1 + (R.drop (d + 1)).length = R.length by simp; omega, List.drop_length,
    List.nil_append, List.set_eq_take_cons_drop _ hdl]
  simp

/-! ### Reading an operand of the store -/

theorem getElem_dup {C : List Bool} {R : List (List Bool)} {j : ℕ} (hj : j < R.length)
    (h : 0 + j < (R ++ R).length) : (R ++ R)[0 + j] = R.getD j C := by
  rw [List.getD_eq_getElem _ _ hj]
  simp [List.getElem_append_left hj]

/-- The templates the loop reads, unchanged. -/
def RTm (w₀ w : St) : Prop := ∀ x, x = TSl ∨ x = TST ∨ x = TD2 ∨ x = TW → w x = w₀ x

/-- **Pop an operand and read its slot**: the slot `j` of the store `R` (`W + 1` slots). -/
theorem exec_rdOp {dst : Fin 120} (hdst : dst = IA ∨ dst = IB) {S W : ℕ} {R : List (List Bool)}
    (hR : UV S R) (hRl : R.length = W + 1) (C : List Bool) {w₀ : St}
    (hsl : (w₀ TSl).length = S) (hst : (w₀ TST).length = (W + 1) * S)
    (hd2 : (w₀ TD2).length = 2 * ((W + 1) * S)) (htw : (w₀ TW).length = W)
    (u : St) (j : ℕ) (rest : List Bool) (hj : j ≤ W) (hGS : u GS = unaryW W j ++ rest)
    (hJW : (u JW).length = W) (hG : u GST = R.flatten) (hP : u PADS = []) (htm : RTm w₀ u) :
    exec V f (ofList [.mv JW GS TW, rdC dst]) u dst = R.getD j C ∧
      exec V f (ofList [.mv JW GS TW, rdC dst]) u GS = rest ∧
      exec V f (ofList [.mv JW GS TW, rdC dst]) u JW = unaryW W j ∧
      ∀ x, x ≠ GD → x ≠ GX → x ≠ JB → x ≠ CJW → x ≠ dst → x ≠ JW → x ≠ GS →
        exec V f (ofList [.mv JW GS TW, rdC dst]) u x = u x := by
  have dd : dst ≠ JW ∧ dst ≠ GS ∧ dst ≠ GD ∧ dst ≠ GX ∧ dst ≠ JB ∧ dst ≠ CJW := by
    rcases hdst with rfl | rfl <;> decide
  simp only [exec_ofList, List.foldl_cons, List.foldl_nil]
  rw [exec_mv_pop (by decide) (by rw [hJW, htm TW (by decide), htw])
    (by rw [length_unaryW hj, htm TW (by decide), htw]) hGS]
  obtain ⟨r1, r2⟩ := exec_rdC (V := V) (f := f) (dst := dst) hdst hR hRl
    (Function.update (Function.update u GS rest) JW (unaryW W j))
    (by simp (config := {decide := true}) [Function.update_apply, hG])
    (by simp (config := {decide := true}) [Function.update_apply, htm TD2 (by decide), hd2])
    (by simp (config := {decide := true}) [Function.update_apply, htm TST (by decide), hst])
    (p := 0) (by simp (config := {decide := true}) [Function.update_apply, hP])
    (by simp (config := {decide := true}) [Function.update_apply]) hj
    (by simp (config := {decide := true}) [Function.update_apply, htm TW (by decide), htw])
    (by simp (config := {decide := true}) [Function.update_apply, htm TSl (by decide), hsl])
    (by omega)
  refine ⟨?_, ?_, ?_, fun x a1 a2 a3 a4 a5 a6 a7 => ?_⟩
  · rw [r1]; exact getElem_dup (by omega) _
  · rw [r2 GS (by decide) (by decide) (by decide) (by decide) dd.2.1.symm]
    simp (config := {decide := true}) [Function.update_apply]
  · rw [r2 JW (by decide) (by decide) (by decide) (by decide) dd.1.symm]
    simp (config := {decide := true}) [Function.update_apply]
  · rw [r2 x a1 a2 a3 a4 a5]; simp [Function.update_apply, a6, a7]

/-! ### The instructions -/

/-- One instruction: pop the destination, read the two operands, the block, copy the result to
`OUTW`, write it. -/
def rBody (blk : Code) : Code :=
  ofList [.mv JD GS TW, .mv JW GS TW, rdC IA, .mv JW GS TW, rdC IB, .cp RES TSl, blk, .cp OUTW RES,
    wrC]

/-- **The register loop**: `|GCNT|` instructions. -/
def rloopC (blk : Code) : Code := ofList [.clr PADS, .cp JW TW, .cp JD TW, .rep GCNT (rBody blk)]

/-- The invariant of the loop after `t` instructions. -/
structure RegInv (V S W : ℕ) (Ctx : St → Prop) (F : List Bool → List Bool → List Bool)
    (C : List Bool) (R₀ : List (List Bool)) (sp : SProg) (w₀ : St) (t : ℕ) (w : St) : Prop where
  ctx : Ctx w
  gst : w GST = (rl F C R₀ (sp.take t)).flatten
  gsw : w GS = spW W (sp.drop t)
  pads : w PADS = []
  jw : (w JW).length = W
  jd : (w JD).length = W
  outw : ∀ g ∈ (sp.take t).getLast?, w OUTW = (rl F C R₀ (sp.take t)).getD g.1 []
  tm : RTm w₀ w

/-- The data of the loop: the store, the program, the templates. -/
structure RegData (S W : ℕ) (C : List Bool) (R₀ : List (List Bool)) (sp : SProg) (w₀ : St) :
    Prop where
  hC : C.length = S
  hR : UV S R₀
  hRl : R₀.length = W + 1
  bnd : ∀ g ∈ sp, g.1 ≤ W ∧ g.2.1 ≤ W ∧ g.2.2 ≤ W
  tsl : (w₀ TSl).length = S
  tst : (w₀ TST).length = (W + 1) * S
  td2 : (w₀ TD2).length = 2 * ((W + 1) * S)
  tw : (w₀ TW).length = W

theorem rInv_step {blk : Code} {S W : ℕ} {F : List Bool → List Bool → List Bool}
    {Ctx : St → Prop} (hB : BlockSpec V f blk S F Ctx) {C : List Bool} {R₀ : List (List Bool)}
    {sp : SProg} {w₀ : St} (hD : RegData S W C R₀ sp w₀) {t : ℕ} (ht : t < sp.length) {w : St}
    (h : RegInv V S W Ctx F C R₀ sp w₀ t w) :
    RegInv V S W Ctx F C R₀ sp w₀ (t + 1)
      (exec V f (rBody blk) (Function.update w GCNT (w GCNT).tail)) := by
  set R := rl F C R₀ (sp.take t) with hRdef
  obtain ⟨hRu, hRl'⟩ := rl_shape hB.len hD.hC (sp.take t) R₀ hD.hR
  have hRl : R.length = W + 1 := by rw [hRl', hD.hRl]
  set g := sp[t] with hg
  have hgb := hD.bnd g (List.getElem_mem _)
  have hdrop : sp.drop t = g :: sp.drop (t + 1) := List.drop_eq_getElem_cons ht
  -- the counter
  have c0 : Ctx (Function.update w GCNT (w GCNT).tail) :=
    hB.frame _ _ h.ctx fun j hj _ _ _ => Function.update_of_ne (by rintro rfl; simp at hj) _ _
  have e0 : ∀ j, j ≠ GCNT → Function.update w GCNT (w GCNT).tail j = w j :=
    fun j hj => Function.update_of_ne hj _ _
  generalize hw0 : Function.update w GCNT (w GCNT).tail = w0 at c0 e0
  have tm0 : RTm w₀ w0 := fun j hj => by
    rw [e0 j (by rcases hj with rfl | rfl | rfl | rfl <;> decide), h.tm j hj]
  rw [rBody, show [Code.mv JD GS TW, .mv JW GS TW, rdC IA, .mv JW GS TW, rdC IB, .cp RES TSl, blk,
    .cp OUTW RES, wrC] = [Code.mv JD GS TW] ++ ([.mv JW GS TW, rdC IA] ++ ([.mv JW GS TW, rdC IB] ++
    [.cp RES TSl, blk, .cp OUTW RES, wrC])) from rfl, exec_ofList_append, exec_ofList_append, exec_ofList_append,
    exec_ofList_single]
  have hu1 := length_unaryW hgb.1
  have hu2 := length_unaryW hgb.2.1
  have hu3 := length_unaryW hgb.2.2
  -- the destination
  have hGS0 : w0 GS = unaryW W g.1 ++ (unaryW W g.2.1 ++ (unaryW W g.2.2 ++ spW W (sp.drop (t + 1)))) := by
    rw [e0 GS (by decide), h.gsw, hdrop, spW_cons, List.append_assoc, List.append_assoc]
  rw [exec_mv_pop (by decide) (by rw [e0 JD (by decide), h.jd, tm0 TW (by decide), hD.tw])
    (by rw [hu1, tm0 TW (by decide), hD.tw]) hGS0]
  set w1 := Function.update (Function.update w0 GS
    (unaryW W g.2.1 ++ (unaryW W g.2.2 ++ spW W (sp.drop (t + 1))))) JD (unaryW W g.1) with hw1
  have e1 : ∀ j, j ≠ GS → j ≠ JD → w1 j = w0 j := fun j a b => by
    simp [hw1, Function.update_apply, a, b]
  have c1 : Ctx w1 := hB.frame _ _ c0 fun j hj _ _ _ => e1 j (by rintro rfl; simp at hj)
    (by rintro rfl; simp at hj)
  have tm1 : RTm w₀ w1 := fun j hj => by
    rw [e1 j (by rcases hj with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hj with rfl | rfl | rfl | rfl <;> decide), tm0 j hj]
  have hG1 : w1 GST = R.flatten := by rw [e1 GST (by decide) (by decide), e0 GST (by decide), h.gst]
  have hP1 : w1 PADS = [] := by rw [e1 PADS (by decide) (by decide), e0 PADS (by decide), h.pads]
  -- the operands
  obtain ⟨a1, a2, a3, a4⟩ := exec_rdOp (V := V) (f := f) (dst := IA) (Or.inl rfl) hRu hRl C
    hD.tsl hD.tst hD.td2 hD.tw w1 g.2.1 (unaryW W g.2.2 ++ spW W (sp.drop (t + 1))) hgb.2.1
    (by rw [hw1, Function.update_of_ne (by decide), Function.update_self])
    (by rw [e1 JW (by decide) (by decide), e0 JW (by decide), h.jw]) hG1 hP1 tm1
  generalize exec V f (ofList [.mv JW GS TW, rdC IA]) w1 = w2 at a1 a2 a3 a4
  have o2 : ∀ x, x ≠ GD → x ≠ GX → x ≠ JB → x ≠ CJW → x ≠ IA → x ≠ JW → x ≠ GS → w2 x = w1 x := a4
  have tm2 : RTm w₀ w2 := fun x hx => by
    rw [o2 x (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide), tm1 x hx]
  obtain ⟨b1, b2, b3, b4⟩ := exec_rdOp (V := V) (f := f) (dst := IB) (Or.inr rfl) hRu hRl C
    hD.tsl hD.tst hD.td2 hD.tw w2 g.2.2 _ hgb.2.2 a2 (by rw [a3, hu2])
    (by rw [o2 GST (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hG1])
    (by rw [o2 PADS (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hP1]) tm2
  generalize exec V f (ofList [.mv JW GS TW, rdC IB]) w2 = w3 at b1 b2 b3 b4
  have o3 : ∀ x, x ≠ GD → x ≠ GX → x ≠ JB → x ≠ CJW → x ≠ IA → x ≠ IB → x ≠ JW → x ≠ GS →
      w3 x = w1 x := fun x h1 h2 h3 h4 h5 h6 h7 h8 => by
    rw [b4 x h1 h2 h3 h4 h6 h7 h8, o2 x h1 h2 h3 h4 h5 h7 h8]
  have c3 : Ctx w3 := hB.frame _ _ c1 fun j hj h1 h2 h3 => o3 j
    (by rintro rfl; simp at hj) (by rintro rfl; simp at hj) (by rintro rfl; simp at hj)
    (by rintro rfl; simp at hj) h1 h2 (by rintro rfl; simp at hj) (by rintro rfl; simp at hj)
  have w3IA : w3 IA = R.getD g.2.1 C := by
    rw [b4 IA (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), a1]
  have hsl : ∀ j, (R.getD j C).length = S := fun j => by
    rw [List.getD_eq_getElem?_getD]
    rcases e : R[j]? with _ | x
    · simpa using hD.hC
    · exact hRu x (List.mem_of_getElem? e)
  have tm3 : RTm w₀ w3 := fun x hx => by
    rw [o3 x (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl <;> decide), tm1 x hx]
  -- the block
  simp only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  set r := F (R.getD g.2.1 C) (R.getD g.2.2 C) with hr
  have hrl : r.length = S := hB.len _ _ (hsl _) (hsl _)
  have c4 : Ctx (Function.update w3 RES (w3 TSl)) :=
    hB.frame _ _ c3 fun j _ _ _ h3 => Function.update_of_ne h3 _ _
  have hb := hB.run _ c4 (by rw [Function.update_of_ne (by decide), w3IA, hsl])
    (by rw [Function.update_of_ne (by decide), b1, hsl])
    (by rw [Function.update_self, tm3 TSl (by decide), hD.tsl])
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), w3IA, b1, ← hr] at hb
  have hbo : ∀ j : Fin 120, 100 ≤ j.val → exec V f blk (Function.update w3 RES (w3 TSl)) j =
      Function.update w3 RES (w3 TSl) j :=
    fun j hj => exec_not_mem _ _ _ (fun hm => by have := hB.wr j hm; omega)
  have c5 := hB.ctx _ c4
  generalize exec V f blk (Function.update w3 RES (w3 TSl)) = w5 at hb hbo c5
  have w5o : ∀ j : Fin 120, 100 ≤ j.val → w5 j = w3 j := fun j hj => by
    rw [hbo j hj, Function.update_of_ne (by rintro rfl; simp at hj)]
  -- the copy to `OUTW`
  have w5o' : ∀ j : Fin 120, 100 ≤ j.val → j ≠ OUTW → Function.update w5 OUTW (w5 RES) j = w3 j :=
    fun j hj hj' => by rw [Function.update_of_ne hj', w5o j hj]
  have c5' : Ctx (Function.update w5 OUTW (w5 RES)) :=
    hB.frame _ _ c5 fun j hj _ _ _ => Function.update_of_ne (by rintro rfl; simp at hj) _ _
  have hb' : Function.update w5 OUTW (w5 RES) RES = r := by
    rw [Function.update_of_ne (by decide), hb]
  have hO : Function.update w5 OUTW (w5 RES) OUTW = r := by rw [Function.update_self, hb]
  clear c5
  generalize Function.update w5 OUTW (w5 RES) = w6 at w5o' c5' hb' hO
  -- the write
  have w5J : w6 JD = unaryW W g.1 := by
    rw [w5o' JD (by decide) (by decide), o3 JD (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]; simp [hw1]
  have w5G : w6 GST = R.flatten := by
    rw [w5o' GST (by decide) (by decide), o3 GST (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hG1]
  obtain ⟨W1, W2⟩ := exec_wrC (V := V) (f := f) hgb.1 hRu hRl w6 w5G w5J
    (by rw [w5o' TW (by decide) (by decide), tm3 TW (by decide), hD.tw])
    (by rw [w5o' TSl (by decide) (by decide), tm3 TSl (by decide), hD.tsl]) (by rw [hb', hrl])
  have o6 : ∀ x, x ∉ wr wrC → exec V f wrC w6 x = w6 x := W2
  have hRt : rl F C R₀ (sp.take (t + 1)) = R.set g.1 r := by
    rw [rl_take_succ F C R₀ sp ht, rlStep]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun g' hg' => ?_, fun x hx => ?_⟩
  · refine hB.frame _ _ c5' fun j hj _ _ h3 => ?_
    rw [o6 j (fun hm => by
      rcases wr_wrC_mem j hm with rfl | h4
      · exact h3 rfl
      · omega)]
  · rw [W1, hb', hRt]
  · rw [o6 GS (by decide), w5o' GS (by decide) (by decide), b2]
  · rw [o6 PADS (by decide), w5o' PADS (by decide) (by decide), o3 PADS (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hP1]
  · rw [o6 JW (by decide), w5o' JW (by decide) (by decide), b3, hu3]
  · rw [o6 JD (by decide), w5J, hu1]
  · have hl : (sp.take (t + 1)).getLast? = some g := by
      rw [List.getLast?_eq_getElem?, List.length_take, min_eq_left (by omega),
        List.getElem?_take, if_pos (by omega), Nat.add_sub_cancel, List.getElem?_eq_getElem ht]
    rw [hl, Option.mem_some_iff] at hg'
    subst hg'
    rw [o6 OUTW (by decide), hO, hRt, List.getD_eq_getElem _ _ (by rw [List.length_set]; omega),
      List.getElem_set_self]
  · have hx' : x ∉ wr wrC ∧ 100 ≤ x.val ∧ x ≠ OUTW := by
      rcases hx with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩
    rw [o6 x hx'.1, w5o' x hx'.2.1 hx'.2.2, tm3 x hx]

/-- **A register program on the machine**: from the store `R₀` (`W + 1` slots) and the word
`spW W sp`, after `|GCNT| = |sp|` instructions the store holds `rl F C R₀ sp`. -/
theorem exec_rloopC {blk : Code} {S W : ℕ} {F : List Bool → List Bool → List Bool}
    {Ctx : St → Prop} (hB : BlockSpec V f blk S F Ctx) {C : List Bool} {R₀ : List (List Bool)}
    {sp : SProg} (w : St) (hD : RegData S W C R₀ sp w) (hc : Ctx w) (hG : w GST = R₀.flatten)
    (hGS : w GS = spW W sp) (hN : (w GCNT).length = sp.length) :
    exec V f (rloopC blk) w GST = (rl F C R₀ sp).flatten ∧
      (∀ g ∈ sp.getLast?, exec V f (rloopC blk) w OUTW = (rl F C R₀ sp).getD g.1 []) ∧
      Ctx (exec V f (rloopC blk) w) ∧
      ∀ j, j ∉ wr (rloopC blk) → exec V f (rloopC blk) w j = w j := by
  refine ⟨?_, ?_, ?_, fun j hj => exec_not_mem _ _ _ hj⟩
  all_goals
    simp only [rloopC, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
    set w1 := Function.update (Function.update (exec V f (.clr PADS) w) JW
      (exec V f (.clr PADS) w TW)) JD (Function.update (exec V f (.clr PADS) w) JW
      (exec V f (.clr PADS) w TW) TW) with hw1
    have e1 : ∀ j, j ≠ JW → j ≠ PADS → j ≠ JD → w1 j = w j := fun j h1 h2 h3 => by
      simp [hw1, Function.update_apply, h1, h2, h3, exec_clr']
    have hD1 : RegData S W C R₀ sp w1 := ⟨hD.hC, hD.hR, hD.hRl, hD.bnd,
      by rw [e1 TSl (by decide) (by decide) (by decide)]; exact hD.tsl,
      by rw [e1 TST (by decide) (by decide) (by decide)]; exact hD.tst,
      by rw [e1 TD2 (by decide) (by decide) (by decide)]; exact hD.td2,
      by rw [e1 TW (by decide) (by decide) (by decide)]; exact hD.tw⟩
    have I := exec_rep_inv (V := V) (f := f) (c := GCNT) (B := rBody blk)
      (fun t w' => t ≤ sp.length → RegInv V S W Ctx F C R₀ sp w1 t w')
      (fun t w' ih ht => rInv_step hB hD1 (by omega) (ih (by omega))) w1
      (fun _ => ⟨hB.frame _ _ hc fun j hj _ _ _ => e1 j (by rintro rfl; simp at hj)
          (by rintro rfl; simp at hj) (by rintro rfl; simp at hj),
        by rw [e1 GST (by decide) (by decide) (by decide), hG]; simp [rl],
        by rw [e1 GS (by decide) (by decide) (by decide), hGS]; simp,
        by simp (config := {decide := true}) [hw1, Function.update_apply, exec_clr'],
        by simp (config := {decide := true}) [hw1, Function.update_apply, exec_clr', hD.tw],
        by simp (config := {decide := true}) [hw1, Function.update_apply, exec_clr', hD.tw],
        fun _ hg => by simp at hg, fun _ _ => rfl⟩)
    rw [show (w1 GCNT).length = sp.length by
      rw [e1 GCNT (by decide) (by decide) (by decide), hN]] at I
    have I' := I le_rfl
  · rw [I'.gst, List.take_of_length_le le_rfl]
  · intro g hg
    rw [← List.take_of_length_le (le_refl sp.length)] at hg ⊢
    exact I'.outw g hg
  · exact I'.ctx

end ValVM

end SigabaNeo.Tape
