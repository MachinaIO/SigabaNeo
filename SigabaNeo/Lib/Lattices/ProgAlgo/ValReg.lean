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

/-- The number of slots shifted after `r` rounds, for the bits `u` of `JB`. -/
def wcnt (sel : Bool) (u : List Bool) (r : ℕ) : ℕ :=
  if sel then (u.take r).count true else r - (u.take r).count true

theorem count_take_le (u : List Bool) (r : ℕ) : (u.take r).count true ≤ r :=
  (List.count_le_length).trans (by simp)

theorem wcnt_succ (sel : Bool) {u : List Bool} {r : ℕ} (hr : r < u.length) :
    wcnt sel u (r + 1) = wcnt sel u r + if u[r] = sel then 1 else 0 := by
  have h := count_take_le u r
  have e : (u.take (r + 1)).count true = (u.take r).count true + if u[r] = true then 1 else 0 := by
    rw [List.take_add_one, List.getElem?_eq_getElem hr, Option.toList_some, List.count_append]
    cases u[r] <;> simp
  cases sel <;> cases hu : u[r] <;> simp only [wcnt, e, hu] <;> simp <;> omega

theorem wcnt_le (sel : Bool) {u : List Bool} {r : ℕ} (hr : r < u.length) :
    wcnt sel u r ≤ wcnt sel u (r + 1) := by
  rw [wcnt_succ sel hr]; omega

theorem wcnt_mono (sel : Bool) (u : List Bool) {r r' : ℕ} (h : r ≤ r') (h' : r' ≤ u.length) :
    wcnt sel u r ≤ wcnt sel u r' := by
  induction h with
  | refl => exact le_rfl
  | step h ih => exact (ih (by omega)).trans (wcnt_le sel (by omega))

theorem wcnt_true (u : List Bool) : wcnt true u u.length = u.count true := by
  simp [wcnt]

theorem wcnt_false (u : List Bool) : wcnt false u u.length = u.length - u.count true := by
  simp [wcnt]

theorem hd_drop {u : List Bool} {r : ℕ} (hr : r < u.length) : hd (u.drop r) = u[r] := by
  rw [List.drop_eq_getElem_cons hr]; rfl

/-- The shift register after shifting `n` slots of `L` into `X`. -/
theorem shift_take {X L : List (List Bool)} {n : ℕ} (hn : n < L.length) (hX : n ≤ X.length) :
    (((X ++ L.take n).drop n) ++ [L[n]]).drop 1 = (X ++ L.take (n + 1)).drop (n + 1) := by
  rw [← List.drop_append_of_le_length (by simp; omega), List.drop_drop, List.append_assoc,
    ← List.take_concat_get' L n hn, Nat.add_comm]

theorem wBody_step {S : ℕ} {u : List Bool} (sel : Bool) {X L : List (List Bool)} (hX : UV S X)
    (hL : UV S L) (hcnt : wcnt sel u u.length ≤ L.length) (hXl : L.length ≤ X.length) {w₀ : St}
    (hTS : (w₀ TSl).length = S) {r : ℕ} (hr : r < u.length) {w : St}
    (h : w GD = (L.drop (wcnt sel u r)).flatten ∧
      w GX = ((X ++ L.take (wcnt sel u r)).drop (wcnt sel u r)).flatten ∧
      w JB = u.drop r ∧ ∀ x, x ≠ GD → x ≠ GX → x ≠ JB → x ≠ CJW → w x = w₀ x) :
    let w' := exec V f (wBody sel) (Function.update w CJW (w CJW).tail)
    w' GD = (L.drop (wcnt sel u (r + 1))).flatten ∧
      w' GX = ((X ++ L.take (wcnt sel u (r + 1))).drop (wcnt sel u (r + 1))).flatten ∧
      w' JB = u.drop (r + 1) ∧ ∀ x, x ≠ GD → x ≠ GX → x ≠ JB → x ≠ CJW → w' x = w₀ x := by
  obtain ⟨hg, hx, hb, ho⟩ := h
  have hTS' : (w TSl).length = S := by
    rw [ho TSl (by decide) (by decide) (by decide) (by decide), hTS]
  have hh : hd (Function.update w CJW (w CJW).tail JB) = u[r] := by
    rw [Function.update_of_ne (by decide), hb, hd_drop hr]
  have hsucc := wcnt_succ sel hr
  have hmono := wcnt_mono sel u (show r + 1 ≤ u.length by omega) le_rfl
  set n := wcnt sel u r with hn
  set w1 := Function.update w CJW (w CJW).tail with hw1
  have uo : ∀ x, x ≠ CJW → w1 x = w x := fun x h => Function.update_of_ne h _ _
  have hJB : (exec V f (.tl JB) w1) JB = u.drop (r + 1) := by
    simp only [exec_tl', Function.update_self, uo JB (by decide), hb, List.tail_drop]
  have hbody : exec V f (wBody sel) w1 = exec V f (.tl JB)
      (if u[r] = sel then exec V f (.mv GX GD TSl) w1 else w1) := by
    cases sel <;> cases h : u[r] <;>
      simp only [wBody, exec_ofList, List.foldl_cons, List.foldl_nil, exec_ifb', hh, h,
        if_true, if_false, Bool.false_eq_true, Bool.true_eq_false,
        ite_true, ite_false] <;> rfl
  by_cases hs : u[r] = sel
  · -- a slot is shifted
    rw [if_pos hs] at hsucc
    have hnl : n < L.length := by omega
    have hGD : w1 GD = L[n] ++ (L.drop (n + 1)).flatten := by
      rw [uo GD (by decide), hg, List.drop_eq_getElem_cons hnl, List.flatten_cons]
    have SH := exec_mv_shift (V := V) (f := f) (d := GX) (s := GD) (c := TSl) (w := w1) (by decide)
      (by rw [uo TSl (by decide), hTS', hL _ (List.getElem_mem _)]) hGD
    have hex : exec V f (wBody sel) w1 = exec V f (.tl JB) (exec V f (.mv GX GD TSl) w1) := by
      rw [hbody, if_pos hs]
    show (exec V f (wBody sel) w1) GD = _ ∧ _
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
    have hex : exec V f (wBody sel) w1 = exec V f (.tl JB) w1 := by
      rw [hbody, if_neg hs]
    show (exec V f (wBody sel) w1) GD = _ ∧ _
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
theorem exec_wloop {S : ℕ} {b : List Bool} (sel : Bool) {X L : List (List Bool)} (hX : UV S X)
    (hL : UV S L) (hcnt : wcnt sel b b.length ≤ L.length) (hXl : L.length ≤ X.length) (u : St)
    (hTS : (u TSl).length = S) (hg : u GD = L.flatten) (hx : u GX = X.flatten)
    (hb : u JB = b) (hc : (u CJW).length = b.length) :
    exec V f (.rep CJW (wBody sel)) u GD = (L.drop (wcnt sel b b.length)).flatten ∧
      exec V f (.rep CJW (wBody sel)) u GX =
        ((X ++ L.take (wcnt sel b b.length)).drop (wcnt sel b b.length)).flatten ∧
      ∀ x, x ≠ GD → x ≠ GX → x ≠ JB → x ≠ CJW → exec V f (.rep CJW (wBody sel)) u x = u x := by
  have I := exec_rep_inv (V := V) (f := f) (c := CJW) (B := wBody sel)
    (fun r w' => r ≤ b.length → w' GD = (L.drop (wcnt sel b r)).flatten ∧
      w' GX = ((X ++ L.take (wcnt sel b r)).drop (wcnt sel b r)).flatten ∧
      w' JB = b.drop r ∧ ∀ x, x ≠ GD → x ≠ GX → x ≠ JB → x ≠ CJW → w' x = u x)
    (fun r w' ih hr => wBody_step sel hX hL hcnt hXl hTS (by omega) (ih (by omega))) u
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
theorem exec_wrC {S W d : ℕ} {b : List Bool} (hbl : b.length = W) (hbc : b.count true = d)
    (hdW : d ≤ W) {R : List (List Bool)} (hR : UV S R)
    (hRl : R.length = W + 1) (w : St) (hG : w GST = R.flatten) (hJ : w JD = b)
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
  have u1b : u1 JB = b := by simp (config := {decide := true}) [hu1, exec_ofList, exec_cp', Function.update_apply, hJ]
  have u1c : (u1 CJW).length = b.length := by
    simp (config := {decide := true}) [hu1, exec_ofList, exec_cp', Function.update_apply, hTW, hbl]
  have hd1 : wcnt true b b.length = d := by rw [wcnt_true, hbc]
  obtain ⟨L1, L2, L3⟩ := exec_wloop (V := V) (f := f) true hR hR (by rw [hd1]; omega) le_rfl u1
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
  have u3b : u3 JB = b := by
    simp only [hu3, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
    try simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [exec_mv_push (by decide) (by rw [u2r, u2s])]
    try simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [exec_drop' (by decide)]
    try simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [L3 JD (by decide) (by decide) (by decide) (by decide), e1 JD (by decide) (by decide)
      (by decide) (by decide), hJ]
  have u3c : (u3 CJW).length = b.length := by
    simp only [hu3, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
    try simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [exec_mv_push (by decide) (by rw [u2r, u2s])]
    try simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [exec_drop' (by decide)]
    try simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [L3 TW (by decide) (by decide) (by decide) (by decide), e1 TW (by decide) (by decide)
      (by decide) (by decide), hTW, hbl]
  have u3s : (u3 TSl).length = S := by
    simp only [hu3, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
    try simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [exec_mv_push (by decide) (by rw [u2r, u2s])]
    try simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [exec_drop' (by decide)]
    try simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    exact u2s
  -- the second loop
  have hd2 : wcnt false b b.length = W - d := by rw [wcnt_false, hbc, hbl]
  have hX2l : X2.length = W + 1 := by simp [hX2, hRl]; omega
  have hL2l : (R.drop (d + 1)).length = W - d := by simp [hRl]
  obtain ⟨-, M2, -⟩ := exec_wloop (V := V) (f := f) false hX2u (hR.drop (d + 1))
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

/-- Words of the destination counter (free during the loop): a word `[true]`, a scratch word. -/
abbrev ONE1 : Fin 120 := 118
abbrev ZT : Fin 120 := 119

/-- One instruction: the destination word (`dC`, into `JD`), read the two operands, the block,
copy the result to `OUTW`, write it. -/
def rBodyX (dC blk : Code) : Code :=
  ofList [dC, .mv JW GS TW, rdC IA, .mv JW GS TW, rdC IB, .cp RES TSl, blk, .cp OUTW RES, wrC]

/-- The register loop with the destination code `dC` and its initialisation `iC`. -/
def rloopX (iC dC blk : Code) : Code := ofList [.clr PADS, .cp JW TW, iC, .rep GCNT (rBodyX dC blk)]

/-- **The destination code**: before the instruction `t` the stream `GS` is `G t` and the state of
the destination words `D t (JD) (ONE1)`; afterwards `GS` holds the two operands then `G (t + 1)`,
and `JD` a word of `W` bits with as many `true` as the destination slot. -/
structure DstOk (V : ℕ) (f : List Bool → List Bool → List Bool) (dC : Code) (W : ℕ) (sp : SProg)
    (G : ℕ → List Bool) (D : ℕ → List Bool → List Bool → Prop) : Prop where
  run : ∀ t (ht : t < sp.length) (w : St), w GS = G t → D t (w JD) (w ONE1) → (w TW).length = W →
    exec V f dC w GS = unaryW W sp[t].2.1 ++ (unaryW W sp[t].2.2 ++ G (t + 1)) ∧
    (exec V f dC w JD).length = W ∧ (exec V f dC w JD).count true = sp[t].1 ∧
    D (t + 1) (exec V f dC w JD) (exec V f dC w ONE1)
  wr : ∀ x ∈ wr dC, x = GS ∨ x = JD ∨ x = ONE1 ∨ x = ZT

/-- The invariant of the loop after `t` instructions. -/
structure RegInv (V S W : ℕ) (Ctx : St → Prop) (F : List Bool → List Bool → List Bool)
    (C : List Bool) (R₀ : List (List Bool)) (sp : SProg) (G : ℕ → List Bool)
    (D : ℕ → List Bool → List Bool → Prop) (w₀ : St) (t : ℕ) (w : St) : Prop where
  ctx : Ctx w
  gst : w GST = (rl F C R₀ (sp.take t)).flatten
  gsw : w GS = G t
  pads : w PADS = []
  jw : (w JW).length = W
  dst : D t (w JD) (w ONE1)
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

theorem rInv_step {dC blk : Code} {S W : ℕ} {F : List Bool → List Bool → List Bool}
    {Ctx : St → Prop} (hB : BlockSpec V f blk S F Ctx) {C : List Bool} {R₀ : List (List Bool)}
    {sp : SProg} {G : ℕ → List Bool} {D : ℕ → List Bool → List Bool → Prop}
    (hdC : DstOk V f dC W sp G D) {w₀ : St} (hD : RegData S W C R₀ sp w₀) {t : ℕ}
    (ht : t < sp.length) {w : St} (h : RegInv V S W Ctx F C R₀ sp G D w₀ t w) :
    RegInv V S W Ctx F C R₀ sp G D w₀ (t + 1)
      (exec V f (rBodyX dC blk) (Function.update w GCNT (w GCNT).tail)) := by
  set R := rl F C R₀ (sp.take t) with hRdef
  obtain ⟨hRu, hRl'⟩ := rl_shape hB.len hD.hC (sp.take t) R₀ hD.hR
  have hRl : R.length = W + 1 := by rw [hRl', hD.hRl]
  set g := sp[t] with hg
  have hgb := hD.bnd g (List.getElem_mem _)
  -- the counter
  have c0 : Ctx (Function.update w GCNT (w GCNT).tail) :=
    hB.frame _ _ h.ctx fun j hj _ _ _ => Function.update_of_ne (by rintro rfl; simp at hj) _ _
  have e0 : ∀ j, j ≠ GCNT → Function.update w GCNT (w GCNT).tail j = w j :=
    fun j hj => Function.update_of_ne hj _ _
  generalize hw0 : Function.update w GCNT (w GCNT).tail = w0 at c0 e0
  have tm0 : RTm w₀ w0 := fun j hj => by
    rw [e0 j (by rcases hj with rfl | rfl | rfl | rfl <;> decide), h.tm j hj]
  rw [rBodyX, show [dC, .mv JW GS TW, rdC IA, .mv JW GS TW, rdC IB, .cp RES TSl, blk,
    .cp OUTW RES, wrC] = [dC] ++ ([.mv JW GS TW, rdC IA] ++ ([.mv JW GS TW, rdC IB] ++
    [.cp RES TSl, blk, .cp OUTW RES, wrC])) from rfl, exec_ofList_append, exec_ofList_append,
    exec_ofList_append, exec_ofList_single]
  -- the destination
  obtain ⟨d1, d2, d3, d4⟩ := hdC.run t ht w0 (by rw [e0 GS (by decide), h.gsw])
    (by rw [e0 JD (by decide), e0 ONE1 (by decide)]; exact h.dst)
    (by rw [tm0 TW (by decide), hD.tw])
  have e1' : ∀ j, j ≠ GS → j ≠ JD → j ≠ ONE1 → j ≠ ZT → exec V f dC w0 j = w0 j :=
    fun j a b c d => exec_not_mem _ _ _ (fun hm => by
      rcases hdC.wr j hm with rfl | rfl | rfl | rfl <;> simp_all)
  generalize exec V f dC w0 = w1 at d1 d2 d3 d4 e1'
  generalize hjd : w1 JD = jdw at d2 d3 d4
  have e1 : ∀ j, j ≠ GS → j ≠ JD → j ≠ ONE1 → j ≠ ZT → w1 j = w0 j := e1'
  have hu2 := length_unaryW hgb.2.1
  have hu3 := length_unaryW hgb.2.2
  have c1 : Ctx w1 := hB.frame _ _ c0 fun j hj _ _ _ => e1 j (by rintro rfl; simp at hj)
    (by rintro rfl; simp at hj) (by rintro rfl; simp at hj) (by rintro rfl; simp at hj)
  have tm1 : RTm w₀ w1 := fun j hj => by
    rw [e1 j (by rcases hj with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hj with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hj with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hj with rfl | rfl | rfl | rfl <;> decide), tm0 j hj]
  have hG1 : w1 GST = R.flatten := by
    rw [e1 GST (by decide) (by decide) (by decide) (by decide), e0 GST (by decide), h.gst]
  have hP1 : w1 PADS = [] := by
    rw [e1 PADS (by decide) (by decide) (by decide) (by decide), e0 PADS (by decide), h.pads]
  have h1O : w1 ONE1 = w1 ONE1 := rfl
  -- the operands
  obtain ⟨a1, a2, a3, a4⟩ := exec_rdOp (V := V) (f := f) (dst := IA) (Or.inl rfl) hRu hRl C
    hD.tsl hD.tst hD.td2 hD.tw w1 g.2.1 (unaryW W g.2.2 ++ G (t + 1)) hgb.2.1 d1
    (by rw [e1 JW (by decide) (by decide) (by decide) (by decide), e0 JW (by decide), h.jw])
    hG1 hP1 tm1
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
  have w5J : w6 JD = jdw := by
    rw [w5o' JD (by decide) (by decide), o3 JD (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hjd]
  have w5O : w6 ONE1 = w1 ONE1 := by
    rw [w5o' ONE1 (by decide) (by decide), o3 ONE1 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]
  have w5G : w6 GST = R.flatten := by
    rw [w5o' GST (by decide) (by decide), o3 GST (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hG1]
  obtain ⟨W1, W2⟩ := exec_wrC (V := V) (f := f) d2 d3 hgb.1 hRu hRl w6 w5G w5J
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
  · rw [o6 JD (by decide), o6 ONE1 (by decide), w5J, w5O]; exact d4
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

/-- **A register program on the machine**: from the store `R₀` (`W + 1` slots), the stream `G 0`
on `GS` and the destination state `D 0` after `iC`, after `|GCNT| = |sp|` instructions the store
holds `rl F C R₀ sp` and `OUTW` the last result. -/
theorem exec_rloopX {iC dC blk : Code} {S W : ℕ} {F : List Bool → List Bool → List Bool}
    {Ctx : St → Prop} (hB : BlockSpec V f blk S F Ctx) {C : List Bool} {R₀ : List (List Bool)}
    {sp : SProg} {G : ℕ → List Bool} {D : ℕ → List Bool → List Bool → Prop}
    (hdC : DstOk V f dC W sp G D) (w : St) (hD : RegData S W C R₀ sp w) (hc : Ctx w)
    (hG : w GST = R₀.flatten) (hGS : w GS = G 0) (hN : (w GCNT).length = sp.length)
    (hiW : ∀ x ∈ wr iC, x = JD ∨ x = ONE1 ∨ x = ZT ∨ x = CJW)
    (hi : ∀ u : St, (∀ x, x ≠ PADS → x ≠ JW → u x = w x) →
      D 0 (exec V f iC u JD) (exec V f iC u ONE1)) :
    exec V f (rloopX iC dC blk) w GST = (rl F C R₀ sp).flatten ∧
      (∀ g ∈ sp.getLast?, exec V f (rloopX iC dC blk) w OUTW = (rl F C R₀ sp).getD g.1 []) ∧
      Ctx (exec V f (rloopX iC dC blk) w) ∧
      ∀ j, j ∉ wr (rloopX iC dC blk) → exec V f (rloopX iC dC blk) w j = w j := by
  refine ⟨?_, ?_, ?_, fun j hj => exec_not_mem _ _ _ hj⟩
  all_goals
    simp only [rloopX, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
    set u := Function.update (exec V f (.clr PADS) w) JW (exec V f (.clr PADS) w TW) with hu
    have eu : ∀ x, x ≠ PADS → x ≠ JW → u x = w x := fun x h1 h2 => by
      simp [hu, Function.update_apply, h1, h2, exec_clr']
    have hi0 := hi u eu
    have ei : ∀ x, x ≠ JD → x ≠ ONE1 → x ≠ ZT → x ≠ CJW → exec V f iC u x = u x :=
      fun x a b c d => exec_not_mem _ _ _ (fun hm => by
        rcases hiW x hm with rfl | rfl | rfl | rfl <;> simp_all)
    generalize exec V f iC u = w1 at hi0 ei
    have e1 : ∀ j, j ≠ JW → j ≠ PADS → j ≠ JD → j ≠ ONE1 → j ≠ ZT → j ≠ CJW → w1 j = w j :=
      fun j h1 h2 h3 h4 h5 h6 => by rw [ei j h3 h4 h5 h6, eu j h2 h1]
    have hD1 : RegData S W C R₀ sp w1 := ⟨hD.hC, hD.hR, hD.hRl, hD.bnd,
      by rw [e1 TSl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hD.tsl,
      by rw [e1 TST (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hD.tst,
      by rw [e1 TD2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hD.td2,
      by rw [e1 TW (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hD.tw⟩
    have I := exec_rep_inv (V := V) (f := f) (c := GCNT) (B := rBodyX dC blk)
      (fun t w' => t ≤ sp.length → RegInv V S W Ctx F C R₀ sp G D w1 t w')
      (fun t w' ih ht => rInv_step hB hdC hD1 (by omega) (ih (by omega))) w1
      (fun _ => ⟨hB.frame _ _ hc fun j hj _ _ _ => e1 j (by rintro rfl; simp at hj)
          (by rintro rfl; simp at hj) (by rintro rfl; simp at hj) (by rintro rfl; simp at hj)
          (by rintro rfl; simp at hj) (by rintro rfl; simp at hj),
        by rw [e1 GST (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hG]
           simp [rl],
        by rw [e1 GS (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hGS],
        by rw [ei PADS (by decide) (by decide) (by decide) (by decide)]
           simp (config := {decide := true}) [hu, Function.update_apply, exec_clr'],
        by rw [ei JW (by decide) (by decide) (by decide) (by decide)]
           simp (config := {decide := true}) [hu, Function.update_apply, exec_clr', hD.tw],
        hi0, fun _ hg => by simp at hg, fun _ _ => rfl⟩)
    rw [show (w1 GCNT).length = sp.length by
      rw [e1 GCNT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hN]] at I
    have I' := I le_rfl
  · rw [I'.gst, List.take_of_length_le le_rfl]
  · intro g hg
    rw [← List.take_of_length_le (le_refl sp.length)] at hg ⊢
    exact I'.outw g hg
  · exact I'.ctx

/-! ### The stream of a slot program -/

/-- **The register loop on a stream**: the destination is popped from the stream. -/
def rloopC (blk : Code) : Code := rloopX (.cp JD TW) (.mv JD GS TW) blk

theorem dstOk_stream (W : ℕ) (sp : SProg) (hb : ∀ g ∈ sp, g.1 ≤ W ∧ g.2.1 ≤ W ∧ g.2.2 ≤ W) :
    DstOk V f (.mv JD GS TW) W sp (fun t => spW W (sp.drop t)) (fun _ a _ => a.length = W) where
  run t ht w hG hD hTW := by
    have hg := hb sp[t] (List.getElem_mem _)
    have hGS : w GS = unaryW W sp[t].1 ++ (unaryW W sp[t].2.1 ++ (unaryW W sp[t].2.2 ++
        spW W (sp.drop (t + 1)))) := by
      rw [hG, List.drop_eq_getElem_cons ht, spW_cons, List.append_assoc, List.append_assoc]
    rw [exec_mv_pop (by decide) (by rw [hD, hTW]) (by rw [length_unaryW hg.1, hTW]) hGS]
    simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    simp only [length_unaryW hg.1, count_unaryW, and_self]
  wr := by decide

/-- **A slot program on the machine**: from the store `R₀` (`W + 1` slots) and the word
`spW W sp`, after `|GCNT| = |sp|` instructions the store holds `rl F C R₀ sp`, `OUTW` the last
result. -/
theorem exec_rloopC {blk : Code} {S W : ℕ} {F : List Bool → List Bool → List Bool}
    {Ctx : St → Prop} (hB : BlockSpec V f blk S F Ctx) {C : List Bool} {R₀ : List (List Bool)}
    {sp : SProg} (w : St) (hD : RegData S W C R₀ sp w) (hc : Ctx w) (hG : w GST = R₀.flatten)
    (hGS : w GS = spW W sp) (hN : (w GCNT).length = sp.length) :
    exec V f (rloopC blk) w GST = (rl F C R₀ sp).flatten ∧
      (∀ g ∈ sp.getLast?, exec V f (rloopC blk) w OUTW = (rl F C R₀ sp).getD g.1 []) ∧
      Ctx (exec V f (rloopC blk) w) ∧
      ∀ j, j ∉ wr (rloopC blk) → exec V f (rloopC blk) w j = w j :=
  exec_rloopX hB (dstOk_stream W sp hD.bnd) w hD hc hG (by simpa using hGS) hN (by decide)
    (fun u hu => by
      show (Function.update u JD (u TW) JD).length = W
      rw [Function.update_self, hu TW (by decide) (by decide), hD.tw])

/-! ### A gate list as a register program (each gate its own register) -/

/-- The trivial slot program of a gate list on `n` inputs: gate `t` writes the slot `n + 1 + t`,
its operands are the slots of `gsW`. -/
def gsSP (n : ℕ) (gs : GateList) : SProg := (List.range gs.length).map fun t =>
  (n + 1 + t, (gs.getD t (0, 0)).1, (gs.getD t (0, 0)).2)

theorem length_gsSP (n : ℕ) (gs : GateList) : (gsSP n gs).length = gs.length := by simp [gsSP]

theorem getElem_gsSP (n : ℕ) (gs : GateList) {t : ℕ} (ht : t < (gsSP n gs).length) :
    (gsSP n gs)[t] = (n + 1 + t, (gs[t]'(by simpa [length_gsSP] using ht)).1,
      (gs[t]'(by simpa [length_gsSP] using ht)).2) := by
  have ht' : t < gs.length := by simpa [length_gsSP] using ht
  simp [gsSP, List.getElem?_eq_getElem ht']

theorem bnd_gsSP {n W : ℕ} {gs : GateList} (hW : n + gs.length ≤ W)
    (hb : ∀ g ∈ gs, g.1 ≤ W ∧ g.2 ≤ W) : ∀ g ∈ gsSP n gs, g.1 ≤ W ∧ g.2.1 ≤ W ∧ g.2.2 ≤ W := by
  intro g hg
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
  rw [getElem_gsSP]
  have ht' : t < gs.length := by simpa [length_gsSP] using ht
  have := hb gs[t] (List.getElem_mem _)
  exact ⟨by omega, this.1, this.2⟩

/-- `j` ones at the end of `W` bits. -/
def revU (W j : ℕ) : List Bool := List.replicate (W - j) false ++ List.replicate j true

theorem revU_succ {W j : ℕ} (hj : j < W) : (revU W j ++ [true]).drop 1 = revU W (j + 1) := by
  obtain ⟨m, hm⟩ : ∃ m, W - j = m + 1 := ⟨W - j - 1, by omega⟩
  rw [revU, revU, hm, show W - (j + 1) = m by omega, List.replicate_succ, List.cons_append,
    List.cons_append, List.drop_one, List.tail_cons, List.append_assoc, ← List.replicate_succ']

theorem length_revU {W j : ℕ} (hj : j ≤ W) : (revU W j).length = W := by simp [revU]; omega

theorem count_revU (W j : ℕ) : (revU W j).count true = j := by
  simp [revU, List.count_replicate]

/-- One more `true` at the end of `JD`. -/
def dCtr : Code := ofList [.cp ZT ONE1, .mv JD ZT ONE1]

theorem exec_dCtr (w : St) (h1 : w ONE1 = [true]) :
    exec V f dCtr w = Function.update (Function.update (Function.update w ZT (w ONE1)) ZT [])
      JD ((w JD ++ [true]).drop 1) := by
  simp only [dCtr, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  rw [exec_mv_shift (x := [true]) (L := []) (by decide)
    (by simp (config := {decide := true}) [Function.update_apply, h1])
    (by simp (config := {decide := true}) [Function.update_apply, h1])]
  rfl

/-- The counter's start: `ONE1 := OB`, `JD := revU W |T|`. -/
def iCtr (T : Fin 120) : Code := ofList [.cp ONE1 OB, .cp JD TW, .cp CJW T, .rep CJW dCtr]

theorem dstOk_ctr (W n : ℕ) (gs : GateList) (hW : n + gs.length ≤ W) :
    DstOk V f dCtr W (gsSP n gs) (fun t => gsW W (gs.drop t))
      (fun t a b => a = revU W (n + t) ∧ b = [true]) where
  run t ht w hG hD hTW := by
    have ht' : t < gs.length := by simpa [length_gsSP] using ht
    rw [exec_dCtr w hD.2]
    simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [hD.1, hD.2, revU_succ (by omega), getElem_gsSP, hG, List.drop_eq_getElem_cons ht', gsW_cons,
      List.append_assoc]
    exact ⟨rfl, length_revU (by omega), by rw [count_revU]; omega, by rw [Nat.add_assoc], rfl⟩
  wr := by decide

/-- **The register loop of a gate list** (stage I): gate `t` writes the slot `|T| + 1 + t`. -/
def rloopG (T : Fin 120) (blk : Code) : Code := rloopX (iCtr T) dCtr blk

theorem getD_append_rep {C : List Bool} {L : List (List Bool)} (m j : ℕ) :
    (L ++ List.replicate m C).getD j C = L.getD j C := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases h : j < L.length
  · rw [List.getElem?_append_left h]
  · have e1 : L[j]? = none := List.getElem?_eq_none (by omega)
    rw [e1, List.getElem?_append_right (by omega), List.getElem?_replicate]
    split_ifs <;> rfl

/-- **The trivial program computes the gate loop's results** `gl`, after the inputs, before the
padding. -/
theorem rl_gsSP (F : List Bool → List Bool → List Bool) (C : List Bool) (ins : List (List Bool))
    (gs : GateList) {W : ℕ} (hW : ins.length + gs.length ≤ W) :
    ∀ t, t ≤ gs.length → rl F C (C :: ins ++ List.replicate (W - ins.length) C)
      ((gsSP ins.length gs).take t) =
        C :: ins ++ gl F C ins (gs.take t) ++ List.replicate (W - ins.length - t) C := by
  intro t
  induction t with
  | zero => intro _; simp [rl, gl]
  | succ t ih =>
    intro ht
    have ht' : t < (gsSP ins.length gs).length := by rw [length_gsSP]; omega
    have hgl : (gl F C ins (gs.take t)).length = t := by
      have : ∀ (g : GateList) (rs : List (List Bool)), (g.foldl (glStep F C ins) rs).length =
          rs.length + g.length := by
        intro g; induction g with
        | nil => intro rs; simp
        | cons a g ihg => intro rs; rw [List.foldl_cons, ihg]; simp [glStep]; omega
      rw [gl, this]; simp; omega
    rw [rl_take_succ F C _ _ ht', ih (by omega), getElem_gsSP, rlStep,
      gl_take_succ F C ins gs (by omega), glStep]
    simp only
    rw [getD_append_rep, getD_append_rep]
    obtain ⟨m, hm⟩ : ∃ m, W - ins.length - t = m + 1 := ⟨W - ins.length - t - 1, by omega⟩
    rw [hm, show W - ins.length - (t + 1) = m by omega, List.replicate_succ]
    rw [List.set_append_right _ _ (by simp [hgl])]
    simp [hgl, slotOf, show ins.length + 1 + t - (ins.length + t + 1) = 0 by omega]

/-- **A gate list on the machine** (stage I): from the store `C :: ins ++ C^(W − |ins|)` and the
gate word `gsW W gs`, after `|GCNT| = |gs|` gates the store holds the results `gl F C ins gs`
after the inputs, `OUTW` the last one. -/
theorem exec_rloopG {T : Fin 120} {blk : Code} {S W : ℕ} {F : List Bool → List Bool → List Bool}
    {Ctx : St → Prop} (hB : BlockSpec V f blk S F Ctx) {C : List Bool} {ins : List (List Bool)}
    {gs : GateList} (w : St) (hW : ins.length + gs.length ≤ W)
    (hD : RegData S W C (C :: ins ++ List.replicate (W - ins.length) C) (gsSP ins.length gs) w)
    (hc : Ctx w) (hG : w GST = (C :: ins ++ List.replicate (W - ins.length) C).flatten)
    (hGS : w GS = gsW W gs) (hN : (w GCNT).length = gs.length) (hT : (w T).length = ins.length)
    (hTW : w TW = List.replicate W false) (hOB : w OB = [true])
    (hTn : T ≠ PADS ∧ T ≠ JW ∧ T ≠ ONE1 ∧ T ≠ JD ∧ T ≠ CJW) :
    exec V f (rloopG T blk) w GST =
        (C :: ins ++ gl F C ins gs ++ List.replicate (W - ins.length - gs.length) C).flatten ∧
      (gs ≠ [] → exec V f (rloopG T blk) w OUTW = (gl F C ins gs).getLastD []) ∧
      Ctx (exec V f (rloopG T blk) w) ∧
      ∀ j, j ∉ wr (rloopG T blk) → exec V f (rloopG T blk) w j = w j := by
  have hrl := rl_gsSP F C ins gs hW gs.length le_rfl
  rw [List.take_of_length_le (by rw [length_gsSP])] at hrl
  rw [List.take_of_length_le le_rfl] at hrl
  obtain ⟨E1, E2, E3, E4⟩ := exec_rloopX (iC := iCtr T) hB (dstOk_ctr W ins.length gs hW) w hD hc hG
    (by simpa using hGS) (by rw [hN, length_gsSP])
    (fun x hx => by simp [iCtr, dCtr, wr, ofList] at hx; tauto) (fun u hu => by
      simp only [iCtr, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
      set u1 := Function.update (Function.update (Function.update u ONE1 (u OB)) JD
        (Function.update u ONE1 (u OB) TW)) CJW (Function.update (Function.update u ONE1 (u OB)) JD
        (Function.update u ONE1 (u OB) TW) T) with hu1
      have I := exec_rep_inv (V := V) (f := f) (c := CJW) (B := dCtr)
        (fun r w' => r ≤ ins.length → w' JD = revU W r ∧ w' ONE1 = [true])
        (fun r w' ih hr => by
          obtain ⟨i1, i2⟩ := ih (by omega)
          rw [exec_dCtr _ (by rw [Function.update_of_ne (by decide), i2])]
          simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
          exact ⟨by rw [i1, revU_succ (by omega)], i2⟩) u1
        (fun _ => ⟨by
            simp (config := {decide := true}) [hu1, Function.update_apply, hu TW (by decide)
              (by decide), hTW, revU],
          by simp (config := {decide := true}) [hu1, Function.update_apply, hu OB (by decide)
              (by decide), hOB]⟩)
      have hc : (u1 CJW).length = ins.length := by
        rw [hu1, Function.update_self, Function.update_of_ne hTn.2.2.2.1,
          Function.update_of_ne hTn.2.2.1, hu T hTn.1 hTn.2.1, hT]
      rw [hc] at I
      exact ⟨by rw [(I le_rfl).1, Nat.add_zero], (I le_rfl).2⟩)
  refine ⟨by rw [rloopG, E1, hrl], fun hne => ?_, E3, E4⟩
  have h1 : gs.length - 1 < (gsSP ins.length gs).length := by
    rw [length_gsSP]; exact Nat.sub_lt (List.length_pos_iff.mpr hne) one_pos
  have hl : (gsSP ins.length gs).getLast? = some ((gsSP ins.length gs)[gs.length - 1]'h1) := by
    rw [List.getLast?_eq_getElem?, length_gsSP]
    exact List.getElem?_eq_getElem _
  rw [rloopG, E2 _ (by rw [hl]; rfl), hrl, getElem_gsSP]
  have hgl : (gl F C ins gs).length = gs.length := by
    have : ∀ (g : GateList) (rs : List (List Bool)), (g.foldl (glStep F C ins) rs).length =
        rs.length + g.length := by
      intro g; induction g with
      | nil => intro rs; simp
      | cons a g ihg => intro rs; rw [List.foldl_cons, ihg]; simp [glStep]; omega
    rw [gl, this]; simp
  have hpos : 0 < gs.length := List.length_pos_iff.mpr hne
  simp only
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, hgl,
    List.getElem?_eq_getElem (by omega), Option.getD_some, List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.cons_append, List.append_assoc, show ins.length + 1 + (gs.length - 1) =
    (C :: ins).length + (gs.length - 1) by simp]
  have key : ∀ (A B : List (List Bool)) (k : ℕ) (h1 : A.length + k < (A ++ B).length)
      (h2 : k < B.length), (A ++ B)[A.length + k] = B[k] := by
    intro A B k h1 h2; simp [List.getElem_append_right]
  exact (key (C :: ins) _ _ _ (by simp [hgl]; omega)).trans
    (List.getElem_append_left (by rw [hgl]; omega))

end ValVM

end SigabaNeo.Tape
