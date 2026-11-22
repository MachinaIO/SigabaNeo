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

theorem exec_cp' {d s : Fin 64} {w : St} : exec V f (.cp d s) w = Function.update w d (w s) := rfl
theorem exec_rep' {c : Fin 64} {b : Code} {w : St} :
    exec V f (.rep c b) w =
      (fun w' => exec V f b (Function.update w' c (w' c).tail))^[(w c).length] w := rfl

/-! ### The words a code writes -/

/-- The words a code may write. -/
def wr : Code → List (Fin 64)
  | .gate d _ _ => [d]
  | .mvV d s => [d, s]
  | .mv d s _ => [d, s]
  | .cp d _ => [d]
  | .drop t _ => [t]
  | .clr t => [t]
  | .tl t => [t]
  | .rep c b => c :: wr b
  | .seq p q => wr p ++ wr q
  | .ifb _ p q => wr p ++ wr q
  | .nop => []

/-- **A code leaves the words it does not write.** -/
theorem exec_not_mem : ∀ (c : Code) (w : St) (j : Fin 64), j ∉ wr c → exec V f c w j = w j
  | .gate d a b, w, j, h => by simp only [wr, List.mem_singleton] at h; simp [exec, Function.update_of_ne h]
  | .mvV d s, w, j, h => by
    simp only [wr, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    simp only [exec]; split_ifs <;> simp [Function.update_of_ne h.1, Function.update_of_ne h.2]
  | .mv d s c, w, j, h => by
    simp only [wr, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    simp only [exec]; split_ifs <;> simp [Function.update_of_ne h.1, Function.update_of_ne h.2]
  | .cp d s, w, j, h => by simp only [wr, List.mem_singleton] at h; simp [exec, Function.update_of_ne h]
  | .drop t c, w, j, h => by
    simp only [wr, List.mem_singleton] at h
    simp only [exec]; split_ifs <;> simp [Function.update_of_ne h]
  | .clr t, w, j, h => by simp only [wr, List.mem_singleton] at h; simp [exec, Function.update_of_ne h]
  | .tl t, w, j, h => by simp only [wr, List.mem_singleton] at h; simp [exec, Function.update_of_ne h]
  | .rep c b, w, j, h => by
    simp only [wr, List.mem_cons, not_or] at h
    rw [exec_rep']
    generalize (w c).length = n
    induction n generalizing w with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply, ih, exec_not_mem b _ j h.2, Function.update_of_ne h.1]
  | .seq p q, w, j, h => by
    simp only [wr, List.mem_append, not_or] at h
    show exec V f q (exec V f p w) j = w j
    rw [exec_not_mem q _ j h.2, exec_not_mem p _ j h.1]
  | .ifb t p q, w, j, h => by
    simp only [wr, List.mem_append, not_or] at h
    simp only [exec]
    split_ifs
    · exact exec_not_mem p w j h.1
    · exact exec_not_mem q w j h.2
  | .nop, w, j, _ => rfl

theorem exec_ofList_append (l₁ l₂ : List Code) (w : St) :
    exec V f (ofList (l₁ ++ l₂)) w = exec V f (ofList l₂) (exec V f (ofList l₁) w) := by
  rw [exec_ofList, exec_ofList, exec_ofList, List.foldl_append]

theorem wr_ofList : ∀ l : List Code, wr (ofList l) = l.flatMap wr
  | [] => rfl
  | c :: l => by simp [ofList, wr, wr_ofList l]

/-! ### Moving values -/

theorem shiftIn_val {r v L : List Bool} (hr : r.length = V) (hv : v.length = V) :
    shiftIn V r (v ++ L) = v := by
  rw [shiftIn, takeD_eq_take (by simp; omega), List.take_left' hv]
  simp [hr]

/-- Pop a value from a stream into a register of `V` bits. -/
theorem exec_mvV_pop {d s : Fin 64} (hds : d ≠ s) {w : St} {v L : List Bool} (hd : (w d).length = V)
    (hv : v.length = V) (hs : w s = v ++ L) :
    exec V f (.mvV d s) w = Function.update (Function.update w s L) d v := by
  simp only [exec, if_neg hds, hs, shiftIn_val hd hv]
  rw [List.drop_left' hv]

/-- Push a register of `V` bits into a buffer (shifted in at the end). -/
theorem exec_mvV_push {d s : Fin 64} (hds : d ≠ s) {w : St} (hs : (w s).length = V) :
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
      ∀ j : Fin 64, (j.val < 2 ∨ 8 < j.val) → exec V f faC w j = w j := by
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
abbrev NA : Fin 64 := 17
abbrev NB : Fin 64 := 18
abbrev NC : Fin 64 := 19
abbrev CT0 : Fin 64 := 22

/-- One round of the ripple adder: pop `a`, `b`, add with the carry `R2`, push the sum. -/
def rippleBody : Code := ofList [.mvV 0 NA, .mvV 1 NB, faC, .mvV NC 3]

/-- **The ripple adder**: `NC := rippleV (NA, NB, R2)` (the buffer from the template `tb`, the
rounds counted by the template `tk`). -/
def rippleC (tk tb : Fin 64) : Code := ofList [.cp NC tb, .cp CT0 tk, .rep CT0 rippleBody, .mvV NC 2]

/-- The words the ripple adder may write. -/
def rippleW (j : Fin 64) : Prop := j.val ≤ 8 ∨ j = NA ∨ j = NB ∨ j = NC ∨ j = CT0

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
    {tk tb : Fin 64} (htk : ¬ rippleW tk) (htb : ¬ rippleW tb)
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

/-! ### Loops zipping two streams -/

/-- `G` computes `R3 := F (R9, R10, R0, R1)` on registers, writing only `R3 … R8`. -/
def GOk (V : ℕ) (f : List Bool → List Bool → List Bool) (G : Code)
    (F : List Bool → List Bool → List Bool → List Bool → List Bool) : Prop :=
  ∀ w, (w 0).length = V → (w 1).length = V →
    exec V f G w 3 = F (w 9) (w 10) (w 0) (w 1) ∧ (exec V f G w 3).length = V ∧
    ∀ j : Fin 64, (j.val < 3 ∨ 8 < j.val) → exec V f G w j = w j

/-- One round: pop `a`, `b`, compute `G`, push `R3`. -/
def zipBody (G : Code) : Code := ofList [.mvV 0 NA, .mvV 1 NB, G, .mvV NC 3]

/-- **A zip of two streams**: `NC := zipWith F (NA, NB)` (buffer template `tb`, counter template
`tk`). -/
def zipC (G : Code) (tk tb : Fin 64) : Code := ofList [.cp NC tb, .cp CT0 tk, .rep CT0 (zipBody G)]

theorem iter_zipBody {G : Code} {F : List Bool → List Bool → List Bool → List Bool → List Bool}
    (hG : GOk V f G F) :
    ∀ (as bs : List (List Bool)) (w : St), as.length = bs.length →
      (∀ x ∈ as, x.length = V) → (∀ x ∈ bs, x.length = V) → (w 0).length = V →
      (w 1).length = V → ∀ ra rb, w NA = as.flatten ++ ra → w NB = bs.flatten ++ rb →
      let g := fun w' => exec V f (zipBody G) (Function.update w' CT0 (w' CT0).tail)
      (g^[as.length] w) NC =
          (w NC ++ (List.zipWith (F (w 9) (w 10)) as bs).flatten).drop (as.length * V) ∧
        (g^[as.length] w) NA = ra ∧ (g^[as.length] w) NB = rb ∧
        ((g^[as.length] w) 0).length = V ∧ ((g^[as.length] w) 1).length = V ∧
        ∀ j, ¬ rippleW j → (g^[as.length] w) j = w j
  | [], bs, w, hl, _, _, h0, h1, ra, rb, hA, hB => by
    have : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    subst this; simp [hA, hB, h0, h1]
  | _ :: _, [], w, hl, _, _, _, _, _, _, _, _ => by simp at hl
  | a :: as, b :: bs, w, hl, hav, hbv, h0, h1, ra, rb, hA, hB => by
    intro g
    have ha : a.length = V := hav a (by simp)
    have hb : b.length = V := hbv b (by simp)
    set w1 := Function.update w CT0 (w CT0).tail
    have e2 : exec V f (.mvV 0 NA) w1 =
        Function.update (Function.update w1 NA (as.flatten ++ ra)) 0 a :=
      exec_mvV_pop (by decide) (by simp (config := {decide := true}) [w1, Function.update_apply, h0])
        ha (by simp (config := {decide := true}) [w1, Function.update_apply, hA])
    set w2 := Function.update (Function.update w1 NA (as.flatten ++ ra)) 0 a
    have e3 : exec V f (.mvV 1 NB) w2 =
        Function.update (Function.update w2 NB (bs.flatten ++ rb)) 1 b :=
      exec_mvV_pop (by decide) (by simp (config := {decide := true}) [w2, w1, Function.update_apply, h1])
        hb (by simp (config := {decide := true}) [w2, w1, Function.update_apply, hB])
    set w3 := Function.update (Function.update w2 NB (bs.flatten ++ rb)) 1 b
    obtain ⟨efa, l3, eo⟩ := hG w3 (by simp (config := {decide := true}) [w3, w2, Function.update_apply, ha])
      (by simp (config := {decide := true}) [w3, Function.update_apply, hb])
    set w4 := exec V f G w3
    have e5 : exec V f (.mvV NC 3) w4 = Function.update (Function.update w4 3 []) NC
        ((w4 NC ++ w4 3).drop V) := exec_mvV_push (by decide) l3
    have hg : g w = Function.update (Function.update w4 3 []) NC ((w4 NC ++ w4 3).drop V) := by
      show exec V f (zipBody G) w1 = _
      rw [zipBody, exec_ofList]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [e2, e3, e5]
    have v9 : w3 9 = w 9 := by simp (config := {decide := true}) [w3, w2, w1, Function.update_apply]
    have v10 : w3 10 = w 10 := by simp (config := {decide := true}) [w3, w2, w1, Function.update_apply]
    have v0 : w3 0 = a := by simp (config := {decide := true}) [w3, w2, Function.update_apply]
    have v1 : w3 1 = b := by simp (config := {decide := true}) [w3, Function.update_apply]
    rw [v9, v10, v0, v1] at efa
    have ih := iter_zipBody hG as bs (g w) (by simpa using hl)
      (fun x hx => hav x (by simp [hx])) (fun x hx => hbv x (by simp [hx]))
      (by rw [hg]; simp (config := {decide := true}) [Function.update_apply]; rw [eo 0 (by decide)]; simp (config := {decide := true}) [w3, w2, Function.update_apply, ha])
      (by rw [hg]; simp (config := {decide := true}) [Function.update_apply]; rw [eo 1 (by decide)]; simp (config := {decide := true}) [w3, Function.update_apply, hb])
      ra rb
      (by rw [hg]; simp (config := {decide := true}) [Function.update_apply]; rw [eo NA (by decide)]; simp (config := {decide := true}) [w3, w2, Function.update_apply])
      (by rw [hg]; simp (config := {decide := true}) [Function.update_apply]; rw [eo NB (by decide)]; simp (config := {decide := true}) [w3, Function.update_apply])
    have g9 : g w 9 = w 9 := by
      rw [hg]; simp (config := {decide := true}) [Function.update_apply]; rw [eo 9 (by decide), v9]
    have g10 : g w 10 = w 10 := by
      rw [hg]; simp (config := {decide := true}) [Function.update_apply]; rw [eo 10 (by decide), v10]
    have gNC : g w NC = (w4 NC ++ w4 3).drop V := by rw [hg]; simp (config := {decide := true}) [Function.update_apply]
    have w4NC : w4 NC = w NC := by
      rw [eo NC (by decide)]; simp (config := {decide := true}) [w3, w2, w1, Function.update_apply]
    obtain ⟨i1, iA, iB, i0, i1', i5⟩ := ih
    rw [g9, g10, gNC, w4NC] at i1
    refine ⟨?_, by rw [List.length_cons, Function.iterate_succ_apply]; exact iA,
      by rw [List.length_cons, Function.iterate_succ_apply]; exact iB,
      by rw [List.length_cons, Function.iterate_succ_apply]; exact i0,
      by rw [List.length_cons, Function.iterate_succ_apply]; exact i1', fun j hj => ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, i1, List.zipWith_cons_cons,
        List.flatten_cons, ← efa]
      rw [← List.drop_append_of_le_length (show V ≤ (w NC ++ w4 3).length by simp [l3]),
        List.drop_drop, List.append_assoc]
      congr 1; ring
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

/-- **A zip of two streams**: `NC` ends with the flattened `zipWith`. -/
theorem exec_zipC {G : Code} {F : List Bool → List Bool → List Bool → List Bool → List Bool}
    (hG : GOk V f G F) {tk tb : Fin 64} (htk : ¬ rippleW tk) (htb : ¬ rippleW tb)
    (as bs : List (List Bool)) (w : St) (hl : as.length = bs.length)
    (hav : ∀ x ∈ as, x.length = V) (hbv : ∀ x ∈ bs, x.length = V) (h0 : (w 0).length = V)
    (h1 : (w 1).length = V) (ra rb : List Bool) (hA : w NA = as.flatten ++ ra)
    (hB : w NB = bs.flatten ++ rb)
    (hk : (w tk).length = as.length) (hb : (w tb).length = as.length * V) :
    exec V f (zipC G tk tb) w NC = (List.zipWith (F (w 9) (w 10)) as bs).flatten ∧
      exec V f (zipC G tk tb) w NA = ra ∧ exec V f (zipC G tk tb) w NB = rb ∧
      (exec V f (zipC G tk tb) w 0).length = V ∧ (exec V f (zipC G tk tb) w 1).length = V ∧
      ∀ j, ¬ rippleW j → exec V f (zipC G tk tb) w j = w j := by
  have tkNC : tk ≠ NC := fun e => htk (by subst e; right; right; right; left; rfl)
  set w1 := Function.update (Function.update w NC (w tb)) CT0 (w tk) with hw1
  have hex : exec V f (zipC G tk tb) w =
      (fun w' => exec V f (zipBody G) (Function.update w' CT0 (w' CT0).tail))^[(w tk).length] w1 := by
    simp only [zipC, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp', exec_rep',
      Function.update_self, Function.update_of_ne tkNC, w1]
  have it := iter_zipBody hG as bs w1 hl hav hbv
    (by simp (config := {decide := true}) [w1, Function.update_apply, h0])
    (by simp (config := {decide := true}) [w1, Function.update_apply, h1]) ra rb
    (by simp (config := {decide := true}) [w1, Function.update_apply, hA])
    (by simp (config := {decide := true}) [w1, Function.update_apply, hB])
  rw [hk] at hex
  obtain ⟨i1, iA, iB, i0, i1', i5⟩ := it
  have v9 : w1 9 = w 9 := by simp (config := {decide := true}) [w1, Function.update_apply]
  have v10 : w1 10 = w 10 := by simp (config := {decide := true}) [w1, Function.update_apply]
  have vNC : w1 NC = w tb := by simp (config := {decide := true}) [w1, Function.update_apply]
  rw [v9, v10, vNC] at i1
  rw [hex]
  refine ⟨?_, iA, iB, i0, i1', fun j hj => ?_⟩
  · rw [i1, List.drop_left' hb]
  · rw [i5 j hj]
    simp only [rippleW, not_or] at hj
    simp [w1, Function.update_apply, hj.2.2.2.1, hj.2.2.2.2]

/-! ### The register codes of the zips -/

/-- `R3 := muxV (R9, R0, R1)` (the constant `1` on `R10`). -/
def muxG : Code := ofList [.gate 4 9 0, .gate 5 10 9, .gate 6 5 1, .gate 3 4 6]
/-- `R3 := andV (R9, R0)`. -/
def andG : Code := ofList [.gate 4 9 0, .gate 3 10 4]
/-- `R3 := notV R0`. -/
def notG : Code := ofList [.gate 3 10 0]
/-- `R3 := R0`. -/
def idG : Code := .cp 3 0

theorem gOk_muxG (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) :
    GOk V f muxG fun s one a b => muxV one (fV V f) s a b := by
  intro w _ _
  refine ⟨?_, ?_, fun j hj => ?_⟩
  · simp [muxG, exec_ofList, exec, muxV, fV]
  · simp only [muxG, exec_ofList, exec, List.foldl_cons, List.foldl_nil, Function.update_self]
    exact hf _ _ (by simp) (by simp)
  · have h3 : j ≠ 3 := fun e => by subst e; simp at hj
    have h4 : j ≠ 4 := fun e => by subst e; simp at hj
    have h5 : j ≠ 5 := fun e => by subst e; simp at hj
    have h6 : j ≠ 6 := fun e => by subst e; simp at hj
    simp [muxG, exec_ofList, exec, h3, h4, h5, h6]

theorem gOk_andG (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) :
    GOk V f andG fun d one a _ => andV one (fV V f) d a := by
  intro w _ _
  refine ⟨?_, ?_, fun j hj => ?_⟩
  · simp [andG, exec_ofList, exec, andV, fV]
  · simp only [andG, exec_ofList, exec, List.foldl_cons, List.foldl_nil, Function.update_self]
    exact hf _ _ (by simp) (by simp)
  · have h3 : j ≠ 3 := fun e => by subst e; simp at hj
    have h4 : j ≠ 4 := fun e => by subst e; simp at hj
    simp [andG, exec_ofList, exec, h3, h4]

theorem gOk_notG (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) :
    GOk V f notG fun _ one a _ => notV one (fV V f) a := by
  intro w _ _
  refine ⟨?_, ?_, fun j hj => ?_⟩
  · simp [notG, exec_ofList, exec, notV, fV]
  · simp only [notG, exec_ofList, exec, List.foldl_cons, List.foldl_nil, Function.update_self]
    exact hf _ _ (by simp) (by simp)
  · have h3 : j ≠ 3 := fun e => by subst e; simp at hj
    simp [notG, exec_ofList, exec, h3]

theorem gOk_idG : GOk V f idG fun _ _ a _ => a := by
  intro w h0 _
  refine ⟨by simp [idG, exec], by simp [idG, exec, h0], fun j hj => ?_⟩
  have h3 : j ≠ 3 := fun e => by subst e; simp at hj
  simp [idG, exec, h3]

theorem muxLV_eq_zipWith {α : Type*} (one : α) (step : α → α → α) (s : α) :
    ∀ as bs : List α, muxLV one step s as bs = List.zipWith (muxV one step s) as bs
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by rw [muxLV, List.zipWith_cons_cons, muxLV_eq_zipWith one step s as bs]

theorem andLV_eq_zipWith {α : Type*} (one : α) (step : α → α → α) (d : α) :
    ∀ as : List α, andLV one step d as = List.zipWith (fun a _ => andV one step d a) as as
  | [] => rfl
  | a :: as => by rw [andLV, List.zipWith_cons_cons, andLV_eq_zipWith one step d as]

theorem notLV_eq_zipWith {α : Type*} (one : α) (step : α → α → α) :
    ∀ as : List α, notLV one step as = List.zipWith (fun a _ => notV one step a) as as
  | [] => rfl
  | a :: as => by rw [notLV, List.zipWith_cons_cons, notLV_eq_zipWith one step as]

/-! ### Constants -/

/-- Push `|tk|` copies of the register `src` into `NC`. -/
def constC (src tk : Fin 64) : Code := ofList [.cp CT0 tk, .rep CT0 (ofList [.cp 3 src, .mvV NC 3])]

/-- Push the register `src` into `NC`. -/
def pushC (src : Fin 64) : Code := ofList [.cp 3 src, .mvV NC 3]

theorem exec_pushC {src : Fin 64} (h3 : src ≠ 3) (hNC : src ≠ NC) {w : St}
    (hs : (w src).length = V) :
    exec V f (pushC src) w = Function.update (Function.update (Function.update w 3 (w src)) 3 [])
      NC ((w NC ++ w src).drop V) := by
  simp only [pushC, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  rw [exec_mvV_push (by decide) (by simp [hs])]
  simp (config := {decide := true}) [Function.update_apply]

theorem iter_constBody {src : Fin 64} (h3 : src ≠ 3) (hNC : src ≠ NC) (hCT : src ≠ CT0) :
    ∀ (n : ℕ) (w : St), (w src).length = V →
      let g := fun w' => exec V f (ofList [.cp 3 src, .mvV NC 3])
        (Function.update w' CT0 (w' CT0).tail)
      (g^[n] w) NC = (w NC ++ (List.replicate n (w src)).flatten).drop (n * V) ∧
        (g^[n] w) src = w src ∧
        ∀ j, j ≠ 3 → j ≠ NC → j ≠ CT0 → (g^[n] w) j = w j
  | 0, w, _ => by simp
  | n + 1, w, hs => by
    intro g
    have hg : g w = Function.update (Function.update (Function.update (Function.update w CT0
        (w CT0).tail) 3 (w src)) 3 []) NC ((w NC ++ w src).drop V) := by
      show exec V f (pushC src) (Function.update w CT0 (w CT0).tail) = _
      rw [exec_pushC h3 hNC (by simp [Function.update_of_ne hCT, hs])]
      simp [Function.update_of_ne hCT, Function.update_of_ne (show NC ≠ CT0 by decide)]
    have gs : g w src = w src := by rw [hg]; simp [Function.update_of_ne hNC, Function.update_of_ne h3,
      Function.update_of_ne hCT]
    obtain ⟨i1, i2, i3⟩ := iter_constBody h3 hNC hCT n (g w) (by rw [gs]; exact hs)
    rw [gs] at i1 i2
    refine ⟨?_, ?_, fun j hj3 hjN hjC => ?_⟩
    · rw [Function.iterate_succ_apply, i1, hg, Function.update_self, List.replicate_succ,
        List.flatten_cons, ← List.drop_append_of_le_length (show V ≤ (w NC ++ w src).length by
          simp [hs]), List.drop_drop, List.append_assoc]
      congr 1; ring
    · rw [Function.iterate_succ_apply, i2]
    · rw [Function.iterate_succ_apply, i3 j hj3 hjN hjC, hg]
      simp [Function.update_of_ne hj3, Function.update_of_ne hjN, Function.update_of_ne hjC]

theorem exec_constC {src tk : Fin 64} (h3 : src ≠ 3) (hNC : src ≠ NC) (hCT : src ≠ CT0)
    (htkC : tk ≠ CT0) {w : St} (hs : (w src).length = V) :
    exec V f (constC src tk) w NC =
        (w NC ++ (List.replicate (w tk).length (w src)).flatten).drop ((w tk).length * V) ∧
      ∀ j, j ≠ 3 → j ≠ NC → j ≠ CT0 → exec V f (constC src tk) w j = w j := by
  have hex : exec V f (constC src tk) w = (fun w' => exec V f (ofList [.cp 3 src, .mvV NC 3])
      (Function.update w' CT0 (w' CT0).tail))^[(w tk).length] (Function.update w CT0 (w tk)) := by
    simp only [constC, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp', exec_rep',
      Function.update_self]
  obtain ⟨i1, i2, i3⟩ := iter_constBody (V := V) (f := f) h3 hNC hCT (w tk).length
    (Function.update w CT0 (w tk)) (by simp [Function.update_of_ne hCT, hs])
  rw [hex]
  refine ⟨?_, fun j hj3 hjN hjC => ?_⟩
  · rw [i1]; simp [Function.update_of_ne hCT, Function.update_of_ne (show NC ≠ CT0 by decide)]
  · rw [i3 j hj3 hjN hjC]; simp [Function.update_of_ne hjC]

theorem constV_pow {α : Type*} (one zv : α) :
    ∀ (K j m : ℕ), constV one zv (K + j) (m * 2 ^ K) = List.replicate K zv ++ constV one zv j m
  | 0, j, m => by simp
  | K + 1, j, m => by
    rw [show K + 1 + j = (K + j) + 1 by ring, constV, pow_succ]
    have h1 : m * (2 ^ K * 2) % 2 = 0 := by rw [← Nat.mul_assoc]; exact Nat.mul_mod_left _ _
    have h2 : m * (2 ^ K * 2) / 2 = m * 2 ^ K := by
      rw [← Nat.mul_assoc]; exact Nat.mul_div_cancel _ (by norm_num)
    rw [h1, h2, constV_pow one zv K j m]
    simp [List.replicate_succ]

/-! ### Lengths of the shadows -/

section Lengths

variable {α : Type*} (one : α) (step : α → α → α)

theorem length_rippleV (as bs : List α) (c : α) (h : as.length = bs.length) :
    (rippleV one step as bs c).length = as.length + 1 := by
  rw [rippleV_eq_rippleL, List.length_append, length_rippleL one step as bs c h]; rfl

end Lengths

theorem rippleL_carry_len (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V)
    {one : List Bool} : ∀ (as bs : List (List Bool)) (c : List Bool), c.length = V →
      (rippleL one (fV V f) as bs c).2.length = V
  | [], _, c, hc => hc
  | _ :: _, [], c, hc => hc
  | a :: as, b :: bs, c, _ => rippleL_carry_len hf as bs _ (hf _ _ (by simp) (by simp))

theorem rippleV_len (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) {one c : List Bool}
    (hc : c.length = V) (as bs : List (List Bool)) :
    ∀ x ∈ rippleV one (fV V f) as bs c, x.length = V := by
  intro x hx
  rw [rippleV_eq_rippleL, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact rippleL_len hf as bs c x hx
  · exact rippleL_carry_len hf as bs c hc

/-! ### The modular adder -/

/-- Words of the modular arithmetic: `X = 24`, `Y = 25` the operands, `Z = 26` the result,
`S1 = 21`, `T = 23` intermediate; templates `TK = 12` (`k` bits), `TK1 = 13` (`k + 1`),
`TBk = 14`, `TBk1 = 15`, `TBk2 = 16` (`k V`, `(k+1) V`, `(k+2) V` bits), `TKm = 20` (`k - 1`);
constants `ONE = 10`, `ZV = 11`. -/
def madd1 : Code := ofList [.cp 0 10, .cp 1 10, .cp NA 24, .cp NB 25, .cp 2 11, rippleC 12 15, .cp 21 NC]

theorem exec_madd1 (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) (w : St)
    (xs ys : List (List Bool)) (hl : xs.length = ys.length) (hxv : ∀ x ∈ xs, x.length = V)
    (hyv : ∀ x ∈ ys, x.length = V) (h10 : (w 10).length = V) (h11 : (w 11).length = V)
    (hX : w 24 = xs.flatten) (hY : w 25 = ys.flatten) (hk : (w 12).length = xs.length)
    (hb : (w 15).length = (xs.length + 1) * V) :
    exec V f madd1 w 21 = (rippleV (w 10) (fV V f) xs ys (w 11)).flatten := by
  simp only [madd1, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  rw [Function.update_self]
  refine ((exec_rippleC (V := V) (f := f) hf (tk := 12) (tb := 15)
    (by simp (config := {decide := true}) [rippleW]) (by simp (config := {decide := true}) [rippleW])
    xs ys _ hl hxv hyv ?_ ?_ ?_ ?_ ?_ ?_ ?_).1).trans ?_
  all_goals simp (config := {decide := true}) [Function.update_apply, h10, h11, hX, hY, hk, hb]

theorem drop_append_drop' {X Y : List Bool} {a : ℕ} (h : a ≤ X.length) (b : ℕ) :
    (X.drop a ++ Y).drop b = (X ++ Y).drop (a + b) := by
  rw [← List.drop_append_of_le_length h, List.drop_drop]

theorem flatten_replicate_len {v : List Bool} (hv : v.length = V) (n : ℕ) :
    (List.replicate n v).flatten.length = n * V := by
  rw [length_flatten_of (V := V) (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact hv),
    List.length_replicate]

/-- Two constants: `|t1|` copies of `s1`, then `|t2|` copies of `s2`, into `NC`. -/
def const2C (s1 t1 s2 t2 : Fin 64) : Code := .seq (constC s1 t1) (constC s2 t2)

theorem exec_const2C {s1 t1 s2 t2 : Fin 64} (h1 : s1.val ≥ 9 ∧ s1 ≠ NC ∧ s1 ≠ CT0)
    (h2 : s2.val ≥ 9 ∧ s2 ≠ NC ∧ s2 ≠ CT0) (ht1 : t1.val ≥ 9 ∧ t1 ≠ NC ∧ t1 ≠ CT0)
    (ht2 : t2.val ≥ 9 ∧ t2 ≠ NC ∧ t2 ≠ CT0) {w : St} (hs1 : (w s1).length = V)
    (hs2 : (w s2).length = V) (hNC : (w t1).length * V ≤ (w NC).length) :
    exec V f (const2C s1 t1 s2 t2) w NC =
        (w NC ++ (List.replicate (w t1).length (w s1) ++
          List.replicate (w t2).length (w s2)).flatten).drop
          (((w t1).length + (w t2).length) * V) ∧
      ∀ j, j ≠ 3 → j ≠ NC → j ≠ CT0 → exec V f (const2C s1 t1 s2 t2) w j = w j := by
  have n3 : ∀ x : Fin 64, x.val ≥ 9 → x ≠ 3 := fun x hx e => by subst e; simp at hx
  obtain ⟨c1, c2⟩ := exec_constC (V := V) (f := f) (n3 s1 h1.1) h1.2.1 h1.2.2 ht1.2.2 (w := w) hs1
  set w1 := exec V f (constC s1 t1) w
  have e1 : w1 s2 = w s2 := c2 _ (n3 s2 h2.1) h2.2.1 h2.2.2
  have e2 : w1 t2 = w t2 := c2 _ (n3 t2 ht2.1) ht2.2.1 ht2.2.2
  obtain ⟨d1, d2⟩ := exec_constC (V := V) (f := f) (n3 s2 h2.1) h2.2.1 h2.2.2 ht2.2.2 (w := w1)
    (by rw [e1]; exact hs2)
  refine ⟨?_, fun j hj3 hjN hjC => ?_⟩
  · show exec V f (constC s2 t2) w1 NC = _
    rw [d1, e1, e2, c1, drop_append_drop' (by rw [List.length_append]; omega),
      List.append_assoc, List.flatten_append]
    congr 1; ring
  · show exec V f (constC s2 t2) w1 j = _
    rw [d2 j hj3 hjN hjC, c2 j hj3 hjN hjC]

/-- The second ripple: `NC := rippleV (S1, C₁)` with `C₁ = zv^K ++ [1, 1]` (`T2 = 27` a template
of `2` bits). -/
def madd2 : Code := ofList [.cp NC 15, const2C 11 20 10 27, .cp NB NC, .cp NA 21,
  .cp 2 11, .cp 0 10, .cp 1 10, rippleC 13 16]

theorem exec_madd2 (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) (w : St)
    (ss : List (List Bool)) (K : ℕ) (hsv : ∀ x ∈ ss, x.length = V) (hsl : ss.length = K + 2)
    (h10 : (w 10).length = V) (h11 : (w 11).length = V) (hS : w 21 = ss.flatten)
    (hm : (w 20).length = K) (h27 : (w 27).length = 2) (h15 : (w 15).length = (K + 2) * V)
    (h13 : (w 13).length = K + 2) (h16 : (w 16).length = (K + 3) * V) :
    exec V f madd2 w NC = (rippleV (w 10) (fV V f) ss
      (List.replicate K (w 11) ++ [w 10, w 10]) (w 11)).flatten := by
  simp only [madd2, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  set w1 := Function.update w NC (w 15)
  obtain ⟨c1, c2⟩ := exec_const2C (V := V) (f := f) (s1 := 11) (t1 := 20) (s2 := 10) (t2 := 27)
    (by decide) (by decide) (by decide) (by decide) (w := w1)
    (by simp (config := {decide := true}) [w1, Function.update_apply, h11])
    (by simp (config := {decide := true}) [w1, Function.update_apply, h10])
    (by simp (config := {decide := true}) [w1, Function.update_apply, hm, h15]; nlinarith)
  set w2 := exec V f (const2C 11 20 10 27) w1
  have v : ∀ j, j ≠ 3 → j ≠ NC → j ≠ CT0 → w2 j = w1 j := c2
  have hC : w2 NC = (List.replicate K (w 11) ++ [w 10, w 10]).flatten := by
    rw [c1]
    simp (config := {decide := true}) only [w1, Function.update_apply, if_true, if_false]
    rw [hm, h27, List.drop_left' (by rw [h15])]
    simp [List.replicate_succ]
  refine ((exec_rippleC (V := V) (f := f) hf (tk := 13) (tb := 16)
    (by simp (config := {decide := true}) [rippleW]) (by simp (config := {decide := true}) [rippleW])
    ss (List.replicate K (w 11) ++ [w 10, w 10]) _ (by simp [hsl]) hsv ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).1).trans ?_
  · intro x hx
    simp only [List.mem_append, List.mem_cons, List.mem_replicate, List.not_mem_nil, or_false] at hx
    rcases hx with ⟨_, rfl⟩ | rfl | rfl <;> assumption
  all_goals simp (config := {decide := true}) [Function.update_apply, v, w1, h10, h11, hS, h13,
    h16, hC, hsl]

/-- A high word (not a register of the gadgets, not a stream of the loops). -/
def Hi (j : Fin 64) : Prop := 11 ≤ j.val ∧ j ≠ NA ∧ j ≠ NB ∧ j ≠ NC ∧ j ≠ CT0

theorem Hi.ne {j : Fin 64} (h : Hi j) (c : Fin 64) (hc : c.val < 11 ∨ c = NA ∨ c = NB ∨ c = NC ∨
    c = CT0) : j ≠ c := by
  rintro rfl
  rcases hc with hc | hc | hc | hc | hc
  · exact absurd h.1 (by omega)
  · exact h.2.1 hc
  · exact h.2.2.1 hc
  · exact h.2.2.2.1 hc
  · exact h.2.2.2.2 hc

theorem Hi.not_rippleW {j : Fin 64} (h : Hi j) : ¬ rippleW j := by
  simp only [rippleW, not_or]
  exact ⟨by have := h.1; omega, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- Split the `m + 1` values of `NC`: the first `m` into `dst` (counter template `tk` of `m` bits,
buffer template `tb` of `m V` bits), the last into `R9`. -/
def splitC (tk tb dst : Fin 64) : Code :=
  ofList [.cp NA NC, .cp NB NC, .cp 0 10, .cp 1 10, zipC idG tk tb, .cp 9 10, .mvV 9 NA, .cp dst NC]

theorem exec_splitC {tk tb dst : Fin 64} (htk : Hi tk) (htb : Hi tb) (hd : Hi dst)
    (w : St) (vs : List (List Bool)) (v : List Bool) (hvs : ∀ x ∈ vs, x.length = V)
    (hv : v.length = V) (h10 : (w 10).length = V) (hNC : w NC = (vs ++ [v]).flatten)
    (hk : (w tk).length = vs.length) (hb : (w tb).length = vs.length * V) :
    exec V f (splitC tk tb dst) w dst = vs.flatten ∧ exec V f (splitC tk tb dst) w 9 = v ∧
      ∀ j, Hi j → j ≠ dst → exec V f (splitC tk tb dst) w j = w j := by
  rw [show splitC tk tb dst = ofList ([.cp NA NC, .cp NB NC, .cp 0 10, .cp 1 10] ++
    [zipC idG tk tb, .cp 9 10, .mvV 9 NA, .cp dst NC]) from rfl, exec_ofList_append]
  set w1 := Function.update (Function.update (Function.update (Function.update w NA (w NC)) NB
    (w NC)) 0 (w 10)) 1 (w 10) with hw1
  have hpre : exec V f (ofList [.cp NA NC, .cp NB NC, .cp 0 10, .cp 1 10]) w = w1 := by
    simp (config := {decide := true}) only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp',
      Function.update_apply, if_true, if_false, hw1]
  rw [hpre]
  simp only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  have v1 : ∀ j, Hi j → w1 j = w j := fun j hj => by
    simp [w1, Function.update_apply, hj.ne 0 (by decide), hj.ne 1 (by decide),
      hj.ne NA (by decide), hj.ne NB (by decide)]
  have hA : w1 NA = vs.flatten ++ v := by
    simp (config := {decide := true}) [w1, Function.update_apply, hNC]
  have hB : w1 NB = vs.flatten ++ v := by
    simp (config := {decide := true}) [w1, Function.update_apply, hNC]
  obtain ⟨z1, zA, zB, z0, z1', z5⟩ := exec_zipC (V := V) (f := f) gOk_idG htk.not_rippleW
    htb.not_rippleW vs vs w1 rfl hvs hvs
    (by simp (config := {decide := true}) [w1, Function.update_apply, h10])
    (by simp (config := {decide := true}) [w1, Function.update_apply, h10]) v v hA hB
    (by rw [v1 tk htk, hk]) (by rw [v1 tb htb, hb])
  set w2 := exec V f (zipC idG tk tb) w1
  have w2_10 : w2 10 = w 10 := by
    rw [z5 10 (by simp (config := {decide := true}) [rippleW])]
    simp (config := {decide := true}) [w1, Function.update_apply]
  have zw : ∀ l : List (List Bool), List.zipWith (fun a (_ : List Bool) => a) l l = l := by
    intro l; induction l with
    | nil => rfl
    | cons x xs ih => rw [List.zipWith_cons_cons, ih]
  have z1v : w2 NC = vs.flatten := by rw [z1]; exact congrArg List.flatten (zw vs)
  rw [exec_mvV_pop (L := []) (by decide) (by simp [Function.update_apply, w2_10, h10]) hv
    (by simp (config := {decide := true}) [Function.update_apply, zA])]
  refine ⟨?_, ?_, fun j hj hjd => ?_⟩
  · simp (config := {decide := true}) only [Function.update_self, Function.update_apply, if_true,
      if_false, z1v]
  · rw [Function.update_of_ne (hd.ne 9 (by decide)).symm]; simp
  · rw [Function.update_of_ne hjd, Function.update_of_ne (hj.ne 9 (by decide)),
      Function.update_of_ne (hj.ne NA (by decide)), Function.update_of_ne (hj.ne 9 (by decide)),
      z5 j hj.not_rippleW, v1 j hj]

/-- The selection: `NC := muxLV R9 (T, S1)`. -/
def madd4 : Code := ofList [.cp NA 23, .cp NB 21, .cp 0 10, .cp 1 10, zipC muxG 13 15]

theorem exec_madd4 (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) (w : St)
    (as bs : List (List Bool)) (hl : as.length = bs.length) (hav : ∀ x ∈ as, x.length = V)
    (hbv : ∀ x ∈ bs, x.length = V) (h10 : (w 10).length = V) (hT : w 23 = as.flatten)
    (hS : w 21 = bs.flatten) (hk : (w 13).length = as.length) (hb : (w 15).length = as.length * V) :
    exec V f madd4 w NC = (muxLV (w 10) (fV V f) (w 9) as bs).flatten := by
  rw [show madd4 = ofList ([.cp NA 23, .cp NB 21, .cp 0 10, .cp 1 10] ++ [zipC muxG 13 15]) from rfl,
    exec_ofList_append]
  set w1 := Function.update (Function.update (Function.update (Function.update w NA (w 23)) NB
    (w 21)) 0 (w 10)) 1 (w 10) with hw1
  have hpre : exec V f (ofList [.cp NA 23, .cp NB 21, .cp 0 10, .cp 1 10]) w = w1 := by
    simp (config := {decide := true}) only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp',
      Function.update_apply, if_true, if_false, hw1]
  rw [hpre]
  simp only [exec_ofList, List.foldl_cons, List.foldl_nil]
  rw [(exec_zipC (V := V) (f := f) (gOk_muxG hf) (tk := 13) (tb := 15)
    (by simp (config := {decide := true}) [rippleW]) (by simp (config := {decide := true}) [rippleW])
    as bs w1 hl hav hbv (by simp (config := {decide := true}) [w1, Function.update_apply, h10])
    (by simp (config := {decide := true}) [w1, Function.update_apply, h10]) [] []
    (by simp (config := {decide := true}) [w1, Function.update_apply, hT])
    (by simp (config := {decide := true}) [w1, Function.update_apply, hS])
    (by simp (config := {decide := true}) [w1, Function.update_apply, hk])
    (by simp (config := {decide := true}) [w1, Function.update_apply, hb])).1, muxLV_eq_zipWith]
  simp (config := {decide := true}) [w1, Function.update_apply]

/-- **The modular adder** `Z := modAdd (X, Y)` modulo `2^K` on `k = K + 1` bits. -/
def modAddC : Code := ofList [madd1, madd2, splitC 13 15 23, madd4, splitC 12 14 26]

theorem constV_add {α : Type*} (one zv : α) (K : ℕ) :
    constV one zv (K + 1 + 1) (2 ^ (K + 1 + 1) - 2 ^ K) = List.replicate K zv ++ [one, one] := by
  have : 2 ^ (K + 1 + 1) - 2 ^ K = 3 * 2 ^ K := by
    rw [pow_succ, pow_succ]; omega
  rw [this, constV_pow one zv K 2 3]
  rfl

theorem getD_last {α : Type*} (l : List α) (d : α) {n : ℕ} (h : l.length = n + 1) :
    l = l.take n ++ [l.getD n d] := by
  rw [List.getD_eq_getElem _ _ (by omega)]
  conv_lhs => rw [← List.take_append_drop n l]
  congr 1
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_nil_of_le (by omega)]

theorem muxLV_len (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V)
    {one s : List Bool} : ∀ (as bs : List (List Bool)), ∀ x ∈ muxLV one (fV V f) s as bs,
      x.length = V
  | [], _, x, hx => by simp [muxLV] at hx
  | _ :: _, [], x, hx => by simp [muxLV] at hx
  | a :: as, b :: bs, x, hx => by
    simp only [muxLV, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hf _ _ (by simp) (by simp)
    · exact muxLV_len hf as bs x hx

theorem length_muxLV {α : Type*} (one : α) (step : α → α → α) (s : α) :
    ∀ as bs : List α, (muxLV one step s as bs).length = min as.length bs.length
  | [], _ => by simp [muxLV]
  | _ :: _, [] => by simp [muxLV]
  | a :: as, b :: bs => by simp [muxLV, length_muxLV one step s as bs, Nat.succ_min_succ]

/-- **The modular adder on the machine**: `Z = 26` ends with the flattened `modAddV` of the
operands `X = 24`, `Y = 25` (`k = K + 1` values each, `q = 2^K`). -/
theorem exec_modAddC (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) (w : St)
    (K : ℕ) (xs ys : List (List Bool)) (hxl : xs.length = K + 1) (hyl : ys.length = K + 1)
    (hxv : ∀ x ∈ xs, x.length = V) (hyv : ∀ x ∈ ys, x.length = V) (h10 : (w 10).length = V)
    (h11 : (w 11).length = V) (hX : w 24 = xs.flatten) (hY : w 25 = ys.flatten)
    (h12 : (w 12).length = K + 1) (h13 : (w 13).length = K + 2) (h14 : (w 14).length = (K + 1) * V)
    (h15 : (w 15).length = (K + 2) * V) (h16 : (w 16).length = (K + 3) * V)
    (h20 : (w 20).length = K) (h27 : (w 27).length = 2) :
    exec V f modAddC w 26 = (modAddV (w 10) (fV V f) (w 11) (2 ^ K) (K + 1) xs ys).flatten := by
  set one := w 10
  set zv := w 11
  set s₁ := rippleV one (fV V f) xs ys zv with hs₁
  set s₂ := rippleV one (fV V f) s₁ (List.replicate K zv ++ [one, one]) zv with hs₂
  have l₁ : s₁.length = K + 2 := by rw [hs₁, length_rippleV _ _ _ _ _ (by rw [hxl, hyl]), hxl]
  have l₂ : s₂.length = K + 3 := by
    rw [hs₂, length_rippleV _ _ _ _ _ (by simp [l₁]), l₁]
  have v₁ : ∀ x ∈ s₁, x.length = V := rippleV_len hf h11 xs ys
  have v₂ : ∀ x ∈ s₂, x.length = V := rippleV_len hf h11 s₁ _
  simp only [modAddC, exec_ofList, List.foldl_cons, List.foldl_nil]
  -- phase 1
  have u1_21 := exec_madd1 hf w xs ys (by rw [hxl, hyl]) hxv hyv h10 h11 hX hY
    (by rw [h12, hxl]) (by rw [h15, hxl])
  have u1_ : ∀ j : Fin 64, j ∉ wr madd1 → exec V f madd1 w j = w j :=
    fun j hj => exec_not_mem madd1 w j hj
  generalize exec V f madd1 w = u1 at u1_21 u1_ ⊢
  -- phase 2
  have u2_NC := exec_madd2 (V := V) (f := f) hf u1 s₁ K v₁ l₁ (by rw [u1_ 10 (by decide)]; exact h10)
    (by rw [u1_ 11 (by decide)]; exact h11) u1_21 (by rw [u1_ 20 (by decide)]; exact h20)
    (by rw [u1_ 27 (by decide)]; exact h27) (by rw [u1_ 15 (by decide)]; exact h15)
    (by rw [u1_ 13 (by decide)]; exact h13) (by rw [u1_ 16 (by decide)]; exact h16)
  rw [u1_ 10 (by decide), u1_ 11 (by decide)] at u2_NC
  have u2_ : ∀ j : Fin 64, j ∉ wr madd2 → exec V f madd2 u1 j = u1 j :=
    fun j hj => exec_not_mem madd2 u1 j hj
  generalize exec V f madd2 u1 = u2 at u2_NC u2_ ⊢
  -- phase 3
  have hsplit := getD_last s₂ one (n := K + 2) l₂
  obtain ⟨u3_23, u3_9, u3_⟩ := exec_splitC (V := V) (f := f) (tk := 13) (tb := 15) (dst := 23)
    (by simp (config := {decide := true}) [Hi]) (by simp (config := {decide := true}) [Hi])
    (by simp (config := {decide := true}) [Hi]) u2 (s₂.take (K + 2)) (s₂.getD (K + 2) one)
    (fun x hx => v₂ x (List.mem_of_mem_take hx))
    (by rw [List.getD_eq_getElem _ _ (by omega)]; exact v₂ _ (List.getElem_mem _))
    (by rw [u2_ 10 (by decide), u1_ 10 (by decide)]; exact h10) (by rw [u2_NC, ← hsplit])
    (by rw [u2_ 13 (by decide), u1_ 13 (by decide), h13]; simp [l₂])
    (by rw [u2_ 15 (by decide), u1_ 15 (by decide), h15]; simp [l₂])
  have u3_n : ∀ j : Fin 64, j ∉ wr (splitC 13 15 23) → exec V f (splitC 13 15 23) u2 j = u2 j :=
    fun j hj => exec_not_mem _ u2 j hj
  generalize exec V f (splitC 13 15 23) u2 = u3 at u3_23 u3_9 u3_ u3_n ⊢
  have u3_10 : u3 10 = one := by rw [u3_n 10 (by decide), u2_ 10 (by decide), u1_ 10 (by decide)]
  have u3_21 : u3 21 = s₁.flatten := by
    rw [u3_ 21 (by simp (config := {decide := true}) [Hi]) (by decide), u2_ 21 (by decide), u1_21]
  -- phase 4
  set s₃ := muxLV one (fV V f) (s₂.getD (K + 2) one) (s₂.take (K + 2)) s₁ with hs₃
  have l₃ : s₃.length = K + 2 := by rw [hs₃, length_muxLV]; simp [l₁, l₂]
  have v₃ : ∀ x ∈ s₃, x.length = V := muxLV_len hf _ _
  have u4_NC := exec_madd4 (V := V) (f := f) hf u3 (s₂.take (K + 2)) s₁ (by simp [l₁, l₂])
    (fun x hx => v₂ x (List.mem_of_mem_take hx)) v₁ (by rw [u3_10]; exact h10) u3_23 u3_21
    (by rw [u3_n 13 (by decide), u2_ 13 (by decide), u1_ 13 (by decide), h13]; simp [l₂])
    (by rw [u3_n 15 (by decide), u2_ 15 (by decide), u1_ 15 (by decide), h15]; simp [l₂])
  rw [u3_10, u3_9, ← hs₃] at u4_NC
  have u4_ : ∀ j : Fin 64, j ∉ wr madd4 → exec V f madd4 u3 j = u3 j :=
    fun j hj => exec_not_mem madd4 u3 j hj
  generalize exec V f madd4 u3 = u4 at u4_NC u4_ ⊢
  -- phase 5
  have hsplit₃ := getD_last s₃ one (n := K + 1) l₃
  have := (exec_splitC (V := V) (f := f) (tk := 12) (tb := 14) (dst := 26)
    (by simp (config := {decide := true}) [Hi]) (by simp (config := {decide := true}) [Hi])
    (by simp (config := {decide := true}) [Hi]) u4 (s₃.take (K + 1)) (s₃.getD (K + 1) one)
    (fun x hx => v₃ x (List.mem_of_mem_take hx))
    (by rw [List.getD_eq_getElem _ _ (by omega)]; exact v₃ _ (List.getElem_mem _))
    (by rw [u4_ 10 (by decide), u3_10]; exact h10) (by rw [u4_NC, ← hsplit₃])
    (by rw [u4_ 12 (by decide), u3_n 12 (by decide), u2_ 12 (by decide), u1_ 12 (by decide), h12];
        simp [l₃])
    (by rw [u4_ 14 (by decide), u3_n 14 (by decide), u2_ 14 (by decide), u1_ 14 (by decide), h14];
        simp [l₃])).1
  rw [this]
  -- the shadow
  congr 1
  simp only [modAddV]
  rw [constV_add, ← hs₁, ← hs₂]

/-! ### The modular subtractor -/

theorem notLV_len (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V)
    {one : List Bool} : ∀ (as : List (List Bool)), ∀ x ∈ notLV one (fV V f) as, x.length = V
  | [], x, hx => by simp [notLV] at hx
  | a :: as, x, hx => by
    simp only [notLV, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hf _ _ (by simp) (by simp)
    · exact notLV_len hf as x hx

theorem length_notLV {α : Type*} (one : α) (step : α → α → α) :
    ∀ as : List α, (notLV one step as).length = as.length
  | [] => rfl
  | a :: as => by simp [notLV, length_notLV one step as]

/-- `S1 := notLV Y`. -/
def msub1 : Code := ofList [.cp NA 25, .cp NB 25, .cp 0 10, .cp 1 10, zipC notG 12 14, .cp 21 NC]

theorem exec_msub1 (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) (w : St)
    (ys : List (List Bool)) (hyv : ∀ x ∈ ys, x.length = V) (h10 : (w 10).length = V)
    (hY : w 25 = ys.flatten) (hk : (w 12).length = ys.length) (hb : (w 14).length = ys.length * V) :
    exec V f msub1 w 21 = (notLV (w 10) (fV V f) ys).flatten := by
  rw [show msub1 = ofList ([.cp NA 25, .cp NB 25, .cp 0 10, .cp 1 10] ++ [zipC notG 12 14, .cp 21 NC])
    from rfl, exec_ofList_append]
  set w1 := Function.update (Function.update (Function.update (Function.update w NA (w 25)) NB
    (w 25)) 0 (w 10)) 1 (w 10) with hw1
  have hpre : exec V f (ofList [.cp NA 25, .cp NB 25, .cp 0 10, .cp 1 10]) w = w1 := by
    simp (config := {decide := true}) only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp',
      Function.update_apply, if_true, if_false, hw1]
  rw [hpre]
  simp only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp', Function.update_self]
  rw [(exec_zipC (V := V) (f := f) (gOk_notG hf) (tk := 12) (tb := 14)
    (by simp (config := {decide := true}) [rippleW]) (by simp (config := {decide := true}) [rippleW])
    ys ys w1 rfl hyv hyv (by simp (config := {decide := true}) [w1, Function.update_apply, h10])
    (by simp (config := {decide := true}) [w1, Function.update_apply, h10]) [] []
    (by simp (config := {decide := true}) [w1, Function.update_apply, hY])
    (by simp (config := {decide := true}) [w1, Function.update_apply, hY])
    (by simp (config := {decide := true}) [w1, Function.update_apply, hk])
    (by simp (config := {decide := true}) [w1, Function.update_apply, hb])).1, notLV_eq_zipWith]
  simp (config := {decide := true}) [w1, Function.update_apply]

/-- `NC := rippleV (X, S1)` with the carry `1`. -/
def msub2 : Code := ofList [.cp NA 24, .cp NB 21, .cp 2 10, .cp 0 10, .cp 1 10, rippleC 12 15]

theorem exec_msub2 (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) (w : St)
    (xs ys : List (List Bool)) (hl : xs.length = ys.length) (hxv : ∀ x ∈ xs, x.length = V)
    (hyv : ∀ x ∈ ys, x.length = V) (h10 : (w 10).length = V) (hX : w 24 = xs.flatten)
    (hS : w 21 = ys.flatten) (hk : (w 12).length = xs.length)
    (hb : (w 15).length = (xs.length + 1) * V) :
    exec V f msub2 w NC = (rippleV (w 10) (fV V f) xs ys (w 10)).flatten := by
  rw [show msub2 = ofList ([.cp NA 24, .cp NB 21, .cp 2 10, .cp 0 10, .cp 1 10] ++ [rippleC 12 15])
    from rfl, exec_ofList_append]
  set w1 := Function.update (Function.update (Function.update (Function.update (Function.update w
    NA (w 24)) NB (w 21)) 2 (w 10)) 0 (w 10)) 1 (w 10) with hw1
  have hpre : exec V f (ofList [.cp NA 24, .cp NB 21, .cp 2 10, .cp 0 10, .cp 1 10]) w = w1 := by
    simp (config := {decide := true}) only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp',
      Function.update_apply, if_true, if_false, hw1]
  rw [hpre]
  simp only [exec_ofList, List.foldl_cons, List.foldl_nil]
  rw [(exec_rippleC (V := V) (f := f) hf (tk := 12) (tb := 15)
    (by simp (config := {decide := true}) [rippleW]) (by simp (config := {decide := true}) [rippleW])
    xs ys w1 hl hxv hyv (by simp (config := {decide := true}) [w1, Function.update_apply, h10])
    (by simp (config := {decide := true}) [w1, Function.update_apply, h10])
    (by simp (config := {decide := true}) [w1, Function.update_apply, h10])
    (by simp (config := {decide := true}) [w1, Function.update_apply, hX])
    (by simp (config := {decide := true}) [w1, Function.update_apply, hS])
    (by simp (config := {decide := true}) [w1, Function.update_apply, hk])
    (by simp (config := {decide := true}) [w1, Function.update_apply, hb])).1]
  simp (config := {decide := true}) [w1, Function.update_apply]

/-- `NC := rippleV (T, C)` with `C = zv^K ++ [1]` (`T1 = 29` a template of `1` bit) and the
carry `zv`. -/
def msub4 : Code := ofList [.cp NC 14, const2C 11 20 10 29, .cp NB NC, .cp NA 23, .cp 2 11,
  .cp 0 10, .cp 1 10, rippleC 12 15]

theorem exec_msub4 (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) (w : St)
    (ts : List (List Bool)) (K : ℕ) (htv : ∀ x ∈ ts, x.length = V) (htl : ts.length = K + 1)
    (h10 : (w 10).length = V) (h11 : (w 11).length = V) (hT : w 23 = ts.flatten)
    (hm : (w 20).length = K) (h29 : (w 29).length = 1) (h14 : (w 14).length = (K + 1) * V)
    (h12 : (w 12).length = K + 1) (h15 : (w 15).length = (K + 2) * V) :
    exec V f msub4 w NC = (rippleV (w 10) (fV V f) ts
      (List.replicate K (w 11) ++ [w 10]) (w 11)).flatten := by
  simp only [msub4, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  set w1 := Function.update w NC (w 14)
  obtain ⟨c1, c2⟩ := exec_const2C (V := V) (f := f) (s1 := 11) (t1 := 20) (s2 := 10) (t2 := 29)
    (by decide) (by decide) (by decide) (by decide) (w := w1)
    (by simp (config := {decide := true}) [w1, Function.update_apply, h11])
    (by simp (config := {decide := true}) [w1, Function.update_apply, h10])
    (by simp (config := {decide := true}) [w1, Function.update_apply, hm, h14]; nlinarith)
  set w2 := exec V f (const2C 11 20 10 29) w1
  have v : ∀ j, j ≠ 3 → j ≠ NC → j ≠ CT0 → w2 j = w1 j := c2
  have hC : w2 NC = (List.replicate K (w 11) ++ [w 10]).flatten := by
    rw [c1]
    simp (config := {decide := true}) only [w1, Function.update_apply, if_true, if_false]
    rw [hm, h29, List.drop_left' (by rw [h14])]
    simp [List.replicate_succ]
  refine ((exec_rippleC (V := V) (f := f) hf (tk := 12) (tb := 15)
    (by simp (config := {decide := true}) [rippleW]) (by simp (config := {decide := true}) [rippleW])
    ts (List.replicate K (w 11) ++ [w 10]) _ (by simp [htl]) htv ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).1).trans ?_
  · intro x hx
    simp only [List.mem_append, List.mem_cons, List.mem_replicate, List.not_mem_nil, or_false] at hx
    rcases hx with ⟨_, rfl⟩ | rfl <;> assumption
  all_goals simp (config := {decide := true}) [Function.update_apply, v, w1, h10, h11, hT, h12,
    h15, hC, htl]

/-- `Z := muxLV (R28, T, W21)`. -/
def msub6 : Code := ofList [.cp 9 28, .cp NA 23, .cp NB 21, .cp 0 10, .cp 1 10, zipC muxG 12 14,
  .cp 26 NC]

theorem exec_msub6 (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) (w : St)
    (as bs : List (List Bool)) (hl : as.length = bs.length) (hav : ∀ x ∈ as, x.length = V)
    (hbv : ∀ x ∈ bs, x.length = V) (h10 : (w 10).length = V) (hT : w 23 = as.flatten)
    (hS : w 21 = bs.flatten) (hk : (w 12).length = as.length) (hb : (w 14).length = as.length * V) :
    exec V f msub6 w 26 = (muxLV (w 10) (fV V f) (w 28) as bs).flatten := by
  rw [show msub6 = ofList ([.cp 9 28, .cp NA 23, .cp NB 21, .cp 0 10, .cp 1 10] ++
    [zipC muxG 12 14, .cp 26 NC]) from rfl, exec_ofList_append]
  set w1 := Function.update (Function.update (Function.update (Function.update (Function.update w
    9 (w 28)) NA (w 23)) NB (w 21)) 0 (w 10)) 1 (w 10) with hw1
  have hpre : exec V f (ofList [.cp 9 28, .cp NA 23, .cp NB 21, .cp 0 10, .cp 1 10]) w = w1 := by
    simp (config := {decide := true}) only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp',
      Function.update_apply, if_true, if_false, hw1]
  rw [hpre]
  simp only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp', Function.update_self]
  rw [(exec_zipC (V := V) (f := f) (gOk_muxG hf) (tk := 12) (tb := 14)
    (by simp (config := {decide := true}) [rippleW]) (by simp (config := {decide := true}) [rippleW])
    as bs w1 hl hav hbv (by simp (config := {decide := true}) [w1, Function.update_apply, h10])
    (by simp (config := {decide := true}) [w1, Function.update_apply, h10]) [] []
    (by simp (config := {decide := true}) [w1, Function.update_apply, hT])
    (by simp (config := {decide := true}) [w1, Function.update_apply, hS])
    (by simp (config := {decide := true}) [w1, Function.update_apply, hk])
    (by simp (config := {decide := true}) [w1, Function.update_apply, hb])).1, muxLV_eq_zipWith]
  simp (config := {decide := true}) [w1, Function.update_apply]

/-- **The modular subtractor** `Z := modSub (X, Y)` modulo `2^K` on `k = K + 1` bits. -/
def modSubC : Code := ofList [msub1, msub2, splitC 12 14 23, .cp 28 9, msub4, splitC 12 14 21, msub6]

theorem constV_sub {α : Type*} (one zv : α) (K : ℕ) :
    constV one zv (K + 1) (2 ^ K) = List.replicate K zv ++ [one] := by
  have := constV_pow one zv K 1 1
  rw [one_mul] at this
  rw [this]; rfl

/-- **The modular subtractor on the machine**: `Z = 26` ends with the flattened `modSubV` of the
operands `X = 24`, `Y = 25`. -/
theorem exec_modSubC (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) (w : St)
    (K : ℕ) (xs ys : List (List Bool)) (hxl : xs.length = K + 1) (hyl : ys.length = K + 1)
    (hxv : ∀ x ∈ xs, x.length = V) (hyv : ∀ x ∈ ys, x.length = V) (h10 : (w 10).length = V)
    (h11 : (w 11).length = V) (hX : w 24 = xs.flatten) (hY : w 25 = ys.flatten)
    (h12 : (w 12).length = K + 1) (h14 : (w 14).length = (K + 1) * V)
    (h15 : (w 15).length = (K + 2) * V) (h20 : (w 20).length = K) (h29 : (w 29).length = 1) :
    exec V f modSubC w 26 = (modSubV (w 10) (fV V f) (w 11) (2 ^ K) (K + 1) xs ys).flatten := by
  set one := w 10
  set zv := w 11
  set s₁ := notLV one (fV V f) ys with hs₁
  set s₂ := rippleV one (fV V f) xs s₁ one with hs₂
  have l₁ : s₁.length = K + 1 := by rw [hs₁, length_notLV, hyl]
  have l₂ : s₂.length = K + 2 := by rw [hs₂, length_rippleV _ _ _ _ _ (by rw [hxl, l₁]), hxl]
  have v₁ : ∀ x ∈ s₁, x.length = V := notLV_len hf ys
  have v₂ : ∀ x ∈ s₂, x.length = V := rippleV_len hf h10 xs s₁
  set s₃ := rippleV one (fV V f) (s₂.take (K + 1)) (List.replicate K zv ++ [one]) zv with hs₃
  have l₃ : s₃.length = K + 2 := by rw [hs₃, length_rippleV _ _ _ _ _ (by simp [l₂])]; simp [l₂]
  have v₃ : ∀ x ∈ s₃, x.length = V := rippleV_len hf h11 _ _
  simp only [modSubC, exec_ofList, List.foldl_cons, List.foldl_nil]
  -- phase 1
  have u1_21 := exec_msub1 hf w ys hyv h10 hY (by rw [h12, hyl]) (by rw [h14, hyl])
  have u1_ : ∀ j : Fin 64, j ∉ wr msub1 → exec V f msub1 w j = w j :=
    fun j hj => exec_not_mem msub1 w j hj
  generalize exec V f msub1 w = u1 at u1_21 u1_ ⊢
  -- phase 2
  have u2_NC := exec_msub2 (V := V) (f := f) hf u1 xs s₁ (by rw [hxl, l₁]) hxv v₁
    (by rw [u1_ 10 (by decide)]; exact h10) (by rw [u1_ 24 (by decide)]; exact hX) u1_21
    (by rw [u1_ 12 (by decide), h12, hxl]) (by rw [u1_ 15 (by decide), h15, hxl])
  rw [u1_ 10 (by decide)] at u2_NC
  have u2_ : ∀ j : Fin 64, j ∉ wr msub2 → exec V f msub2 u1 j = u1 j :=
    fun j hj => exec_not_mem msub2 u1 j hj
  generalize exec V f msub2 u1 = u2 at u2_NC u2_ ⊢
  -- phase 3
  have hsplit := getD_last s₂ one (n := K + 1) l₂
  obtain ⟨u3_23, u3_9, u3_⟩ := exec_splitC (V := V) (f := f) (tk := 12) (tb := 14) (dst := 23)
    (by simp (config := {decide := true}) [Hi]) (by simp (config := {decide := true}) [Hi])
    (by simp (config := {decide := true}) [Hi]) u2 (s₂.take (K + 1)) (s₂.getD (K + 1) one)
    (fun x hx => v₂ x (List.mem_of_mem_take hx))
    (by rw [List.getD_eq_getElem _ _ (by omega)]; exact v₂ _ (List.getElem_mem _))
    (by rw [u2_ 10 (by decide), u1_ 10 (by decide)]; exact h10) (by rw [u2_NC, ← hsplit])
    (by rw [u2_ 12 (by decide), u1_ 12 (by decide), h12]; simp [l₂])
    (by rw [u2_ 14 (by decide), u1_ 14 (by decide), h14]; simp [l₂])
  have u3_n : ∀ j : Fin 64, j ∉ wr (splitC 12 14 23) → exec V f (splitC 12 14 23) u2 j = u2 j :=
    fun j hj => exec_not_mem _ u2 j hj
  generalize exec V f (splitC 12 14 23) u2 = u3 at u3_23 u3_9 u3_ u3_n ⊢
  -- save the selector
  simp only [exec_cp']
  set u3' := Function.update u3 28 (u3 9) with hu3'
  have u3'_ : ∀ j, j ≠ 28 → u3' j = u3 j := fun j hj => by simp [u3', Function.update_of_ne hj]
  -- phase 4
  have u4_NC := exec_msub4 (V := V) (f := f) hf u3' (s₂.take (K + 1)) K
    (fun x hx => v₂ x (List.mem_of_mem_take hx)) (by simp [l₂])
    (by rw [u3'_ 10 (by decide), u3_n 10 (by decide), u2_ 10 (by decide), u1_ 10 (by decide)]; exact h10)
    (by rw [u3'_ 11 (by decide), u3_n 11 (by decide), u2_ 11 (by decide), u1_ 11 (by decide)]; exact h11)
    (by rw [u3'_ 23 (by decide)]; exact u3_23)
    (by rw [u3'_ 20 (by decide), u3_n 20 (by decide), u2_ 20 (by decide), u1_ 20 (by decide)]; exact h20)
    (by rw [u3'_ 29 (by decide), u3_n 29 (by decide), u2_ 29 (by decide), u1_ 29 (by decide)]; exact h29)
    (by rw [u3'_ 14 (by decide), u3_n 14 (by decide), u2_ 14 (by decide), u1_ 14 (by decide)]; exact h14)
    (by rw [u3'_ 12 (by decide), u3_n 12 (by decide), u2_ 12 (by decide), u1_ 12 (by decide)]; exact h12)
    (by rw [u3'_ 15 (by decide), u3_n 15 (by decide), u2_ 15 (by decide), u1_ 15 (by decide)]; exact h15)
  have e10 : u3' 10 = one := by
    rw [u3'_ 10 (by decide), u3_n 10 (by decide), u2_ 10 (by decide), u1_ 10 (by decide)]
  have e11 : u3' 11 = zv := by
    rw [u3'_ 11 (by decide), u3_n 11 (by decide), u2_ 11 (by decide), u1_ 11 (by decide)]
  rw [e10, e11, ← hs₃] at u4_NC
  have u4_ : ∀ j : Fin 64, j ∉ wr msub4 → exec V f msub4 u3' j = u3' j :=
    fun j hj => exec_not_mem msub4 u3' j hj
  generalize exec V f msub4 u3' = u4 at u4_NC u4_ ⊢
  -- phase 5
  have hsplit₃ := getD_last s₃ one (n := K + 1) l₃
  obtain ⟨u5_21, -, u5_⟩ := exec_splitC (V := V) (f := f) (tk := 12) (tb := 14) (dst := 21)
    (by simp (config := {decide := true}) [Hi]) (by simp (config := {decide := true}) [Hi])
    (by simp (config := {decide := true}) [Hi]) u4 (s₃.take (K + 1)) (s₃.getD (K + 1) one)
    (fun x hx => v₃ x (List.mem_of_mem_take hx))
    (by rw [List.getD_eq_getElem _ _ (by omega)]; exact v₃ _ (List.getElem_mem _))
    (by rw [u4_ 10 (by decide), e10]; exact h10) (by rw [u4_NC, ← hsplit₃])
    (by rw [u4_ 12 (by decide), u3'_ 12 (by decide), u3_n 12 (by decide), u2_ 12 (by decide),
      u1_ 12 (by decide), h12]; simp [l₃])
    (by rw [u4_ 14 (by decide), u3'_ 14 (by decide), u3_n 14 (by decide), u2_ 14 (by decide),
      u1_ 14 (by decide), h14]; simp [l₃])
  have u5_n : ∀ j : Fin 64, j ∉ wr (splitC 12 14 21) → exec V f (splitC 12 14 21) u4 j = u4 j :=
    fun j hj => exec_not_mem _ u4 j hj
  generalize exec V f (splitC 12 14 21) u4 = u5 at u5_21 u5_ u5_n ⊢
  -- phase 6
  have := exec_msub6 (V := V) (f := f) hf u5 (s₂.take (K + 1)) (s₃.take (K + 1)) (by simp [l₂, l₃])
    (fun x hx => v₂ x (List.mem_of_mem_take hx)) (fun x hx => v₃ x (List.mem_of_mem_take hx))
    (by rw [u5_n 10 (by decide), u4_ 10 (by decide), e10]; exact h10)
    (by rw [u5_ 23 (by simp (config := {decide := true}) [Hi]) (by decide), u4_ 23 (by decide),
      u3'_ 23 (by decide)]; exact u3_23) u5_21
    (by rw [u5_n 12 (by decide), u4_ 12 (by decide), u3'_ 12 (by decide), u3_n 12 (by decide),
      u2_ 12 (by decide), u1_ 12 (by decide), h12]; simp [l₂])
    (by rw [u5_n 14 (by decide), u4_ 14 (by decide), u3'_ 14 (by decide), u3_n 14 (by decide),
      u2_ 14 (by decide), u1_ 14 (by decide), h14]; simp [l₂])
  rw [this]
  have e28 : u5 28 = s₂.getD (K + 1) one := by
    rw [u5_ 28 (by simp (config := {decide := true}) [Hi]) (by decide), u4_ 28 (by decide)]
    simp [u3', u3_9]
  rw [e28, u5_n 10 (by decide), u4_ 10 (by decide), e10]
  congr 1
  simp only [modSubV]
  rw [constV_sub, ← hs₁, ← hs₂, ← hs₃]

/-! ### A term of a coefficient -/

theorem andLV_len (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V)
    {one d : List Bool} : ∀ (as : List (List Bool)), ∀ x ∈ andLV one (fV V f) d as, x.length = V
  | [], x, hx => by simp [andLV] at hx
  | a :: as, x, hx => by
    simp only [andLV, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hf _ _ (by simp) (by simp)
    · exact andLV_len hf as x hx

theorem length_andLV {α : Type*} (one : α) (step : α → α → α) (d : α) :
    ∀ as : List α, (andLV one step d as).length = as.length
  | [] => rfl
  | a :: as => by simp [andLV, length_andLV one step d as]

theorem constV_zero {α : Type*} (one zv : α) : ∀ n, constV one zv n 0 = List.replicate n zv
  | 0 => rfl
  | n + 1 => by simp [constV, constV_zero one zv n, List.replicate_succ]

/-- The operands of a term: `Y := andLV (DIG, COEF)`, `X := zv^k` (`COEF = 30`, `DIG = 31`). -/
def term1 : Code := ofList [.cp NA 30, .cp NB 30, .cp 9 31, .cp 0 10, .cp 1 10, zipC andG 12 14,
  .cp 25 NC, .cp NC 14, constC 11 12, .cp 24 NC]

theorem exec_term1 (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) (w : St)
    (cs : List (List Bool)) (hcv : ∀ x ∈ cs, x.length = V) (h10 : (w 10).length = V)
    (h11 : (w 11).length = V) (hC : w 30 = cs.flatten) (hk : (w 12).length = cs.length)
    (hb : (w 14).length = cs.length * V) :
    exec V f term1 w 25 = (andLV (w 10) (fV V f) (w 31) cs).flatten ∧
      exec V f term1 w 24 = (List.replicate cs.length (w 11)).flatten ∧
      ∀ j : Fin 64, j ∉ wr term1 → exec V f term1 w j = w j := by
  refine ⟨?_, ?_, fun j hj => exec_not_mem term1 w j hj⟩
  · rw [show term1 = ofList ([.cp NA 30, .cp NB 30, .cp 9 31, .cp 0 10, .cp 1 10] ++
      [zipC andG 12 14, .cp 25 NC, .cp NC 14, constC 11 12, .cp 24 NC]) from rfl, exec_ofList_append]
    set w1 := Function.update (Function.update (Function.update (Function.update (Function.update w
      NA (w 30)) NB (w 30)) 9 (w 31)) 0 (w 10)) 1 (w 10) with hw1
    have hpre : exec V f (ofList [.cp NA 30, .cp NB 30, .cp 9 31, .cp 0 10, .cp 1 10]) w = w1 := by
      simp (config := {decide := true}) only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp',
        Function.update_apply, if_true, if_false, hw1]
    rw [hpre]
    rw [show [zipC andG 12 14, .cp 25 NC, .cp NC 14, constC 11 12, .cp 24 NC] =
      [zipC andG 12 14, .cp 25 NC] ++ [.cp NC 14, constC 11 12, .cp 24 NC] from rfl,
      exec_ofList_append, exec_not_mem (ofList [.cp NC 14, constC 11 12, .cp 24 NC]) _ 25 (by decide)]
    simp only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp', Function.update_self]
    rw [(exec_zipC (V := V) (f := f) (gOk_andG hf) (tk := 12) (tb := 14)
      (by simp (config := {decide := true}) [rippleW]) (by simp (config := {decide := true}) [rippleW])
      cs cs w1 rfl hcv hcv (by simp (config := {decide := true}) [w1, Function.update_apply, h10])
      (by simp (config := {decide := true}) [w1, Function.update_apply, h10]) [] []
      (by simp (config := {decide := true}) [w1, Function.update_apply, hC])
      (by simp (config := {decide := true}) [w1, Function.update_apply, hC])
      (by simp (config := {decide := true}) [w1, Function.update_apply, hk])
      (by simp (config := {decide := true}) [w1, Function.update_apply, hb])).1, andLV_eq_zipWith]
    simp (config := {decide := true}) [w1, Function.update_apply]
  · rw [show term1 = ofList ([.cp NA 30, .cp NB 30, .cp 9 31, .cp 0 10, .cp 1 10, zipC andG 12 14,
      .cp 25 NC] ++ [.cp NC 14, constC 11 12, .cp 24 NC]) from rfl, exec_ofList_append]
    have e : ∀ j : Fin 64, j ∉ wr (ofList [.cp NA 30, .cp NB 30, .cp 9 31, .cp 0 10, .cp 1 10,
        zipC andG 12 14, .cp 25 NC]) → exec V f (ofList [.cp NA 30, .cp NB 30, .cp 9 31, .cp 0 10,
          .cp 1 10, zipC andG 12 14, .cp 25 NC]) w j = w j := fun j hj => exec_not_mem _ w j hj
    generalize exec V f (ofList [.cp NA 30, .cp NB 30, .cp 9 31, .cp 0 10, .cp 1 10,
      zipC andG 12 14, .cp 25 NC]) w = u at e ⊢
    simp only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp', Function.update_self]
    obtain ⟨c1, -⟩ := exec_constC (V := V) (f := f) (src := 11) (tk := 12) (by decide) (by decide)
      (by decide) (by decide) (w := Function.update u NC (u 14))
      (by simp (config := {decide := true}) [Function.update_apply, e 11 (by decide), h11])
    rw [c1]
    simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [e 14 (by decide), e 12 (by decide), e 11 (by decide), hk, List.drop_left' (by rw [hb])]

/-- **A subtracted term** `Z := modSubV (zv^k, andLV (DIG, COEF))`. -/
def termSubC : Code := .seq term1 modSubC
/-- **An added term** `Z := modAddV (zv^k, andLV (DIG, COEF))`. -/
def termAddC : Code := .seq term1 modAddC

/-- The templates and constants of the modular arithmetic, for `k = K + 1`. -/
structure Tmpl (V K : ℕ) (w : St) : Prop where
  h10 : (w 10).length = V
  h11 : (w 11).length = V
  h12 : (w 12).length = K + 1
  h13 : (w 13).length = K + 2
  h14 : (w 14).length = (K + 1) * V
  h15 : (w 15).length = (K + 2) * V
  h16 : (w 16).length = (K + 3) * V
  h20 : (w 20).length = K
  h27 : (w 27).length = 2
  h29 : (w 29).length = 1

theorem Tmpl.of_eq {K : ℕ} {w w' : St} (h : Tmpl V K w)
    (e : ∀ j : Fin 64, j ∈ ([10, 11, 12, 13, 14, 15, 16, 20, 27, 29] : List (Fin 64)) → w' j = w j) :
    Tmpl V K w' :=
  ⟨by rw [e 10 (by decide)]; exact h.h10, by rw [e 11 (by decide)]; exact h.h11,
    by rw [e 12 (by decide)]; exact h.h12, by rw [e 13 (by decide)]; exact h.h13,
    by rw [e 14 (by decide)]; exact h.h14, by rw [e 15 (by decide)]; exact h.h15,
    by rw [e 16 (by decide)]; exact h.h16, by rw [e 20 (by decide)]; exact h.h20,
    by rw [e 27 (by decide)]; exact h.h27, by rw [e 29 (by decide)]; exact h.h29⟩

theorem Tmpl.exec {K : ℕ} {w : St} (h : Tmpl V K w) (c : Code)
    (hc : ∀ j ∈ ([10, 11, 12, 13, 14, 15, 16, 20, 27, 29] : List (Fin 64)), j ∉ wr c) :
    Tmpl V K (exec V f c w) :=
  h.of_eq fun j hj => exec_not_mem c w j (hc j hj)

theorem exec_termSubC (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) (w : St)
    (K : ℕ) (ht : Tmpl V K w) (cs : List (List Bool)) (hcl : cs.length = K + 1)
    (hcv : ∀ x ∈ cs, x.length = V) (hC : w 30 = cs.flatten) :
    exec V f termSubC w 26 = (modSubV (w 10) (fV V f) (w 11) (2 ^ K) (K + 1)
      (List.replicate (K + 1) (w 11)) (andLV (w 10) (fV V f) (w 31) cs)).flatten := by
  obtain ⟨e25, e24, e⟩ := exec_term1 hf w cs hcv ht.h10 ht.h11 hC (by rw [ht.h12, hcl])
    (by rw [ht.h14, hcl])
  have ht' : Tmpl V K (exec V f term1 w) := ht.exec term1 (by decide)
  have := exec_modSubC (V := V) (f := f) hf (exec V f term1 w) K (List.replicate (K + 1) (w 11))
    (andLV (w 10) (fV V f) (w 31) cs) (by simp) (by
      rw [length_andLV, hcl]) (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact ht.h11)
    (andLV_len hf cs) ht'.h10 ht'.h11 (by rw [e24, hcl]) e25 ht'.h12 ht'.h14
    ht'.h15 ht'.h20 ht'.h29
  rw [show termSubC = .seq term1 modSubC from rfl]
  show exec V f modSubC (exec V f term1 w) 26 = _
  rw [this, e 10 (by decide), e 11 (by decide)]

theorem exec_termAddC (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) (w : St)
    (K : ℕ) (ht : Tmpl V K w) (cs : List (List Bool)) (hcl : cs.length = K + 1)
    (hcv : ∀ x ∈ cs, x.length = V) (hC : w 30 = cs.flatten) :
    exec V f termAddC w 26 = (modAddV (w 10) (fV V f) (w 11) (2 ^ K) (K + 1)
      (List.replicate (K + 1) (w 11)) (andLV (w 10) (fV V f) (w 31) cs)).flatten := by
  obtain ⟨e25, e24, e⟩ := exec_term1 hf w cs hcv ht.h10 ht.h11 hC (by rw [ht.h12, hcl])
    (by rw [ht.h14, hcl])
  have ht' : Tmpl V K (exec V f term1 w) := ht.exec term1 (by decide)
  have := exec_modAddC (V := V) (f := f) hf (exec V f term1 w) K (List.replicate (K + 1) (w 11))
    (andLV (w 10) (fV V f) (w 31) cs) (by simp) (by
      rw [length_andLV, hcl]) (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact ht.h11)
    (andLV_len hf cs) ht'.h10 ht'.h11 (by rw [e24, hcl]) e25 ht'.h12 ht'.h13
    ht'.h14 ht'.h15 ht'.h16 ht'.h20 ht'.h27
  rw [show termAddC = .seq term1 modAddC from rfl]
  show exec V f modAddC (exec V f term1 w) 26 = _
  rw [this, e 10 (by decide), e 11 (by decide)]

end ValVM
