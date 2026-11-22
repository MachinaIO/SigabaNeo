import SigabaNeo.Lib.Machines.Prog.ValVM
import SigabaNeo.Lib.Lattices.Homomorphic.SLPShadow

/-!
# Arithmetic on the word machine

Codes of `ValVM` computing the shadows of the arithmetic builders
(`SigabaNeo.Lib.Lattices.Homomorphic.SLPShadow`) on the values held in words of `V` bits, for the
step `fV a b = f (takeD V a) (takeD V b)` of the machine (`gate`):

* `faC`: the full adder on registers (`exec_faC`: `fullAddV`);
* `rippleC`: the ripple adder on two streams of values, into a buffer (`exec_rippleC`: `rippleV`).

Lists of values are held *flattened* (`List.flatten`): a stream is consumed `V` bits at a time
(`mvV d s` with a register `d` of `V` bits), a buffer of `m V` bits receives `m` values shifted in
at its end (`mvV b r`).
-/

namespace SigabaNeo.Tape

namespace ValVM

open SigabaNeo.Lattices SigabaNeo.Lattices.SLP

variable {V : ℕ} {f : List Bool → List Bool → List Bool}

/-- The step of the machine. -/
def fV (V : ℕ) (f : List Bool → List Bool → List Bool) (a b : List Bool) : List Bool :=
  f (takeD V a) (takeD V b)

/-! ### Sequences of instructions -/

/-- A list of instructions, in order. -/
def ofList : List Code → Code
  | [] => .nop
  | c :: l => .seq c (ofList l)

theorem exec_ofList (l : List Code) (w : St) :
    exec V f (ofList l) w = l.foldl (fun w c => exec V f c w) w := by
  induction l generalizing w with
  | nil => rfl
  | cons c l ih => simp only [ofList, exec, ih, List.foldl_cons]

theorem exec_cp' {d s : Fin 40} {w : St} : exec V f (.cp d s) w = Function.update w d (w s) := rfl
theorem exec_rep' {c : Fin 40} {b : Code} {w : St} :
    exec V f (.rep c b) w =
      (fun w' => exec V f b (Function.update w' c (w' c).tail))^[(w c).length] w := rfl

/-! ### Moving values -/

theorem shiftIn_val {r v L : List Bool} (hr : r.length = V) (hv : v.length = V) :
    shiftIn V r (v ++ L) = v := by
  rw [shiftIn, takeD_eq_take (by simp; omega), List.take_left' hv]
  simp [hr]

/-- Pop a value from a stream into a register of `V` bits. -/
theorem exec_mvV_pop {d s : Fin 40} (hds : d ≠ s) {w : St} {v L : List Bool} (hd : (w d).length = V)
    (hv : v.length = V) (hs : w s = v ++ L) :
    exec V f (.mvV d s) w = Function.update (Function.update w s L) d v := by
  simp only [exec, if_neg hds, hs, shiftIn_val hd hv]
  rw [List.drop_left' hv]

/-- Push a register of `V` bits into a buffer (shifted in at the end). -/
theorem exec_mvV_push {d s : Fin 40} (hds : d ≠ s) {w : St} (hs : (w s).length = V) :
    exec V f (.mvV d s) w = Function.update (Function.update w s []) d ((w d ++ w s).drop V) := by
  simp only [exec, if_neg hds, shiftIn, takeD_of_length' hs]
  rw [List.drop_eq_nil_of_le (by omega)]

/-- Shifting values into a buffer of exactly their total width leaves them. -/
theorem drop_append_flatten {b : List Bool} {vs : List (List Bool)} (hv : ∀ x ∈ vs, x.length = V)
    (hb : b.length = vs.length * V) : (b ++ vs.flatten).drop (vs.length * V) = vs.flatten := by
  rw [← hb, List.drop_left]

theorem length_flatten_of {vs : List (List Bool)} (hv : ∀ x ∈ vs, x.length = V) :
    vs.flatten.length = vs.length * V := by
  induction vs with
  | nil => simp
  | cons x vs ih =>
    rw [List.flatten_cons, List.length_append, hv x (by simp), ih (fun y hy => hv y (by simp [hy])),
      List.length_cons, Nat.succ_mul]; ring

/-! ### The full adder on registers -/

/-- `R3, R2 := fullAdd (R0, R1, R2)` (the constant `1` on `R10`; scratch `R4 … R8`). -/
def faC : Code := ofList [.gate 4 0 1, .gate 5 0 4, .gate 6 1 4, .gate 7 5 6, .gate 5 7 2,
  .gate 6 7 5, .gate 8 2 5, .gate 3 6 8, .gate 5 10 0, .gate 6 10 1, .gate 7 5 6, .gate 5 7 2,
  .gate 2 4 5]

theorem exec_faC (w : St) :
    (exec V f faC w 3, exec V f faC w 2) = fullAddV (w 10) (fV V f) (w 0) (w 1) (w 2) ∧
      ∀ j : Fin 40, (j.val < 2 ∨ 8 < j.val) → exec V f faC w j = w j := by
  refine ⟨?_, fun j hj => ?_⟩
  · simp [faC, exec_ofList, exec, Function.update_apply, fullAddV, xorV, orV, fV]
  · have h2 : j ≠ 2 := fun e => by subst e; simp at hj
    have h3 : j ≠ 3 := fun e => by subst e; simp at hj
    have h4 : j ≠ 4 := fun e => by subst e; simp at hj
    have h5 : j ≠ 5 := fun e => by subst e; simp at hj
    have h6 : j ≠ 6 := fun e => by subst e; simp at hj
    have h7 : j ≠ 7 := fun e => by subst e; simp at hj
    have h8 : j ≠ 8 := fun e => by subst e; simp at hj
    simp [faC, exec_ofList, exec, Function.update_apply, h2, h3, h4, h5, h6, h7, h8]

/-! ### The ripple adder on streams -/

section Ripple

variable {α : Type*} (one : α) (step : α → α → α)

/-- The sums and the final carry of the ripple adder. -/
def rippleL : List α → List α → α → List α × α
  | a :: as, b :: bs, c =>
    ((fullAddV one step a b c).1 :: (rippleL as bs (fullAddV one step a b c).2).1,
      (rippleL as bs (fullAddV one step a b c).2).2)
  | _, _, c => ([], c)

theorem rippleV_eq_rippleL : ∀ (as bs : List α) (c : α),
    rippleV one step as bs c = (rippleL one step as bs c).1 ++ [(rippleL one step as bs c).2]
  | [], _, c => rfl
  | _ :: _, [], c => rfl
  | a :: as, b :: bs, c => by
    simp only [rippleV, rippleL, List.cons_append, rippleV_eq_rippleL as bs]

theorem length_rippleL : ∀ (as bs : List α) (c : α), as.length = bs.length →
    (rippleL one step as bs c).1.length = as.length
  | [], _, c, _ => rfl
  | _ :: _, [], c, h => by simp at h
  | a :: as, b :: bs, c, h => by
    simp only [rippleL, List.length_cons, length_rippleL as bs _ (by simpa using h)]

end Ripple

theorem rippleL_len (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) {one : List Bool} :
    ∀ (as bs : List (List Bool)) (c : List Bool), ∀ x ∈ (rippleL one (fV V f) as bs c).1,
      x.length = V
  | [], _, c, x, hx => by simp [rippleL] at hx
  | _ :: _, [], c, x, hx => by simp [rippleL] at hx
  | a :: as, b :: bs, c, x, hx => by
    simp only [rippleL, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hf _ _ (by simp) (by simp)
    · exact rippleL_len hf as bs _ x hx

/-- Stream registers of the arithmetic. -/
abbrev NA : Fin 40 := 17
abbrev NB : Fin 40 := 18
abbrev NC : Fin 40 := 19
abbrev CT0 : Fin 40 := 22

/-- One round of the ripple adder: pop `a`, `b`, add with the carry `R2`, push the sum. -/
def rippleBody : Code := ofList [.mvV 0 NA, .mvV 1 NB, faC, .mvV NC 3]

/-- **The ripple adder**: `NC := rippleV (NA, NB, R2)` (the buffer from the template `tb`, the
rounds counted by the template `tk`). -/
def rippleC (tk tb : Fin 40) : Code := ofList [.cp NC tb, .cp CT0 tk, .rep CT0 rippleBody, .mvV NC 2]

/-- The words the ripple adder may write. -/
def rippleW (j : Fin 40) : Prop := j.val ≤ 8 ∨ j = NA ∨ j = NB ∨ j = NC ∨ j = CT0

theorem fV_len (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) (a b : List Bool) :
    (fV V f a b).length = V := hf _ _ (by simp) (by simp)

theorem exec_faC_len (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) (w : St) :
    (exec V f faC w 3).length = V ∧ (exec V f faC w 2).length = V := by
  constructor <;> simp only [faC, exec_ofList, exec, List.foldl_cons, List.foldl_nil,
    Function.update_self] <;> exact hf _ _ (by simp) (by simp)

/-- The rounds of the ripple adder. -/
theorem iter_rippleBody (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) :
    ∀ (as bs : List (List Bool)) (w : St), as.length = bs.length →
      (∀ x ∈ as, x.length = V) → (∀ x ∈ bs, x.length = V) → (w 0).length = V →
      (w 1).length = V → (w 2).length = V → w NA = as.flatten → w NB = bs.flatten →
      let g := fun w' => exec V f rippleBody (Function.update w' CT0 (w' CT0).tail)
      let r := rippleL (w 10) (fV V f) as bs (w 2)
      (g^[as.length] w) NC = (w NC ++ r.1.flatten).drop (as.length * V) ∧
        (g^[as.length] w) 2 = r.2 ∧ ((g^[as.length] w) 2).length = V ∧
        (g^[as.length] w) 10 = w 10 ∧
        ∀ j, ¬ rippleW j → (g^[as.length] w) j = w j
  | [], bs, w, hl, _, _, _, _, h2, _, _ => by
    simp (config := {decide := true}) [Function.update_apply, rippleL, h2]
  | _ :: _, [], w, hl, _, _, _, _, _, _, _ => by simp at hl
  | a :: as, b :: bs, w, hl, hav, hbv, h0, h1, h2, hA, hB => by
    intro g r
    have ha : a.length = V := hav a (by simp)
    have hb : b.length = V := hbv b (by simp)
    -- one round
    set w1 := Function.update w CT0 (w CT0).tail
    have e2 : exec V f (.mvV 0 NA) w1 = Function.update (Function.update w1 NA as.flatten) 0 a :=
      exec_mvV_pop (by decide) (by simp (config := {decide := true}) [Function.update_apply, w1, h0]) ha (by simp (config := {decide := true}) [Function.update_apply, w1, hA])
    set w2 := Function.update (Function.update w1 NA as.flatten) 0 a
    have e3 : exec V f (.mvV 1 NB) w2 = Function.update (Function.update w2 NB bs.flatten) 1 b :=
      exec_mvV_pop (by decide) (by simp (config := {decide := true}) [Function.update_apply, w2, w1, h1]) hb (by simp (config := {decide := true}) [Function.update_apply, w2, w1, hB])
    set w3 := Function.update (Function.update w2 NB bs.flatten) 1 b
    obtain ⟨efa, eo⟩ := exec_faC (V := V) (f := f) w3
    obtain ⟨l3, l2⟩ := exec_faC_len hf w3
    set w4 := exec V f faC w3
    have e5 : exec V f (.mvV NC 3) w4 = Function.update (Function.update w4 3 []) NC
        ((w4 NC ++ w4 3).drop V) := exec_mvV_push (by decide) l3
    have hg : g w = Function.update (Function.update w4 3 []) NC ((w4 NC ++ w4 3).drop V) := by
      show exec V f rippleBody w1 = _
      rw [rippleBody, exec_ofList]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [e2, e3, e5]
    have v10 : w3 10 = w 10 := by simp (config := {decide := true}) [Function.update_apply, w3, w2, w1]
    have v0 : w3 0 = a := by simp (config := {decide := true}) [Function.update_apply, w3, w2]
    have v1 : w3 1 = b := by simp (config := {decide := true}) [Function.update_apply, w3]
    have v2 : w3 2 = w 2 := by simp (config := {decide := true}) [Function.update_apply, w3, w2, w1]
    have fa : fullAddV (w 10) (fV V f) a b (w 2) = (w4 3, w4 2) := by
      rw [efa, v10, v0, v1, v2]
    -- the next rounds
    have ih := iter_rippleBody hf as bs (g w) (by simpa using hl)
      (fun x hx => hav x (by simp (config := {decide := true}) [Function.update_apply, hx])) (fun x hx => hbv x (by simp (config := {decide := true}) [Function.update_apply, hx]))
      (by rw [hg]; simp (config := {decide := true}) [Function.update_apply]; rw [eo 0 (by decide)]; simp (config := {decide := true}) [Function.update_apply, w3, w2, ha])
      (by rw [hg]; simp (config := {decide := true}) [Function.update_apply]; rw [eo 1 (by decide)]; simp (config := {decide := true}) [Function.update_apply, w3, hb])
      (by rw [hg]; simp (config := {decide := true}) [Function.update_apply]; exact l2)
      (by rw [hg]; simp (config := {decide := true}) [Function.update_apply]; rw [eo NA (by decide)]; simp (config := {decide := true}) [Function.update_apply, w3, w2])
      (by rw [hg]; simp (config := {decide := true}) [Function.update_apply]; rw [eo NB (by decide)]; simp (config := {decide := true}) [Function.update_apply, w3])
    have g10 : g w 10 = w 10 := by rw [hg]; simp (config := {decide := true}) [Function.update_apply]; rw [eo 10 (by decide), v10]
    have g2 : g w 2 = w4 2 := by rw [hg]; simp (config := {decide := true}) [Function.update_apply]
    have gNC : g w NC = (w4 NC ++ w4 3).drop V := by rw [hg]; simp (config := {decide := true}) [Function.update_apply]
    have w4NC : w4 NC = w NC := by rw [eo NC (by decide)]; simp (config := {decide := true}) [Function.update_apply, w3, w2, w1]
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih
    rw [g10, g2] at *
    have hr : r = ((w4 3) :: (rippleL (w 10) (fV V f) as bs (w4 2)).1,
        (rippleL (w 10) (fV V f) as bs (w4 2)).2) := by
      simp only [r, rippleL, fa]
    refine ⟨?_, ?_, by rw [List.length_cons, Function.iterate_succ_apply]; exact i3,
      by rw [List.length_cons, Function.iterate_succ_apply]; exact i4, fun j hj => ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, i1, gNC, w4NC, hr]
      simp only [List.flatten_cons]
      rw [← List.drop_append_of_le_length (show V ≤ (w NC ++ w4 3).length by simp [l3]),
        List.drop_drop, List.append_assoc]
      congr 1; ring
    · rw [List.length_cons, Function.iterate_succ_apply, i2, hr]
    · rw [List.length_cons, Function.iterate_succ_apply, i5 j hj, hg]
      have hj3 : j ≠ 3 := fun e => hj (by subst e; left; decide)
      have hjNC : j ≠ NC := fun e => hj (by subst e; right; right; right; left; rfl)
      simp only [Function.update_of_ne hj3, Function.update_of_ne hjNC]
      rw [eo j (by
        simp only [rippleW, not_or] at hj
        have := hj.1; omega)]
      simp only [rippleW, not_or] at hj
      have hj0 : j ≠ 0 := fun e => by subst e; simp at hj
      have hj1 : j ≠ 1 := fun e => by subst e; simp at hj
      simp [Function.update_apply, w3, w2, w1, hj.2.1, hj.2.2.1, hj.2.2.2.2, hj0, hj1]

/-- **The ripple adder on streams**: with `NA`, `NB` the flattened lists `as`, `bs` of `n` values,
the counter template `tk` of `n` bits and the buffer template `tb` of `(n + 1) V` bits, `NC` ends
with the flattened `rippleV` of the values (`R10` the constant `1`, `R2` the carry). -/
theorem exec_rippleC (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V)
    {tk tb : Fin 40} (htk : ¬ rippleW tk) (htb : ¬ rippleW tb)
    (as bs : List (List Bool)) (w : St) (hl : as.length = bs.length)
    (hav : ∀ x ∈ as, x.length = V) (hbv : ∀ x ∈ bs, x.length = V) (h0 : (w 0).length = V)
    (h1 : (w 1).length = V) (h2 : (w 2).length = V) (hA : w NA = as.flatten)
    (hB : w NB = bs.flatten) (hk : (w tk).length = as.length)
    (hb : (w tb).length = (as.length + 1) * V) :
    exec V f (rippleC tk tb) w NC = (rippleV (w 10) (fV V f) as bs (w 2)).flatten ∧
      exec V f (rippleC tk tb) w 10 = w 10 ∧
      ∀ j, ¬ rippleW j → exec V f (rippleC tk tb) w j = w j := by
  have tkNC : tk ≠ NC := fun e => htk (by subst e; right; right; right; left; rfl)
  have tbNC : tb ≠ NC := fun e => htb (by subst e; right; right; right; left; rfl)
  have tkCT : tk ≠ CT0 := fun e => htk (by subst e; right; right; right; right; rfl)
  set w1 := Function.update (Function.update w NC (w tb)) CT0 (w tk) with hw1
  have hex : exec V f (rippleC tk tb) w =
      exec V f (.mvV NC 2) ((fun w' => exec V f rippleBody (Function.update w' CT0 (w' CT0).tail))^[
        (w tk).length] w1) := by
    simp only [rippleC, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp', exec_rep',
      Function.update_self, Function.update_of_ne tkNC, w1]
  have it := iter_rippleBody hf as bs w1 hl hav hbv (by simp (config := {decide := true}) [w1, Function.update_apply, h0])
    (by simp (config := {decide := true}) [w1, Function.update_apply, h1]) (by simp (config := {decide := true}) [w1, Function.update_apply, h2])
    (by simp (config := {decide := true}) [w1, Function.update_apply, hA]) (by simp (config := {decide := true}) [w1, Function.update_apply, hB])
  rw [hk] at hex
  obtain ⟨i1, i2, i3, i4, i5⟩ := it
  have v10 : w1 10 = w 10 := by simp (config := {decide := true}) [w1, Function.update_apply]
  have v2 : w1 2 = w 2 := by simp (config := {decide := true}) [w1, Function.update_apply]
  have vNC : w1 NC = w tb := by simp (config := {decide := true}) [w1, Function.update_apply]
  rw [v10, v2, vNC] at i1
  rw [v10, v2] at i2
  set w2 := (fun w' => exec V f rippleBody (Function.update w' CT0 (w' CT0).tail))^[as.length] w1
  have e : exec V f (.mvV NC 2) w2 = Function.update (Function.update w2 2 []) NC
      ((w2 NC ++ w2 2).drop V) := exec_mvV_push (by decide) i3
  rw [hex, e]
  refine ⟨?_, ?_, fun j hj => ?_⟩
  · rw [Function.update_self, i1, i2, rippleV_eq_rippleL, List.flatten_append,
      List.flatten_singleton]
    have hl1 := length_rippleL (w 10) (fV V f) as bs (w 2) hl
    have hl2 : ((rippleL (w 10) (fV V f) as bs (w 2)).1.flatten).length = as.length * V := by
      rw [length_flatten_of (V := V) (fun x hx => rippleL_len hf as bs (w 2) x hx), hl1]
    have hb' : (w tb).length = as.length * V + V := by rw [hb, Nat.succ_mul]
    rw [List.drop_append_of_le_length (l₁ := w tb) (i := as.length * V) (by omega),
      List.append_assoc, List.drop_left' (by rw [List.length_drop]; omega)]
  · simp (config := {decide := true}) only [Function.update_apply]; simp; exact i4
  · have hj2 : j ≠ 2 := fun e => hj (by subst e; left; decide)
    have hjNC : j ≠ NC := fun e => hj (by subst e; right; right; right; left; rfl)
    rw [Function.update_of_ne hjNC, Function.update_of_ne hj2, i5 j hj]
    simp only [rippleW, not_or] at hj
    simp (config := {decide := true}) [w1, Function.update_apply, hj.2.2.2.1, hj.2.2.2.2]

end ValVM

end SigabaNeo.Tape
