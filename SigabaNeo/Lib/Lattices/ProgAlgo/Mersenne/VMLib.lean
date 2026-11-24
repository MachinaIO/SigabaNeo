import SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.VM

/-!
# Reasoning about codes of the ring-word machine

Tools for the semantics `RingVM.exec` of `SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.VM`:

* `wr c`: the registers a code may write; **`exec_not_mem`**: the others are unchanged;
* **`exec_rep_inv`**: a loop `rep c body` whose body leaves the counter `c` alone, by an invariant
  indexed by the number of rounds;
* `exec_mv_pop`, `exec_mv_push`: moving a word of the width of the template out of a stream into a
  register, and into a buffer (shifted in at its end).
-/

namespace SigabaNeo.Tape

namespace RingVM

open SigabaNeo.Lattices.Algo

variable {N K : ℕ}

theorem length_digitRW' (N K i : ℕ) (w : List Bool) : (digitRW N K i w).length = N * K :=
  length_concatN fun _ _ => length_bitW _ _

/-- The registers a code may write. -/
def wr : Code → List (Fin 200)
  | .add d _ _ | .sub d _ _ | .mul d _ _ | .canon d _ | .neg d _ | .digit d _ _ | .rotB d _ _
  | .aut d _ _ | .rhoJ d _ _ => [d]
  | .mv d s _ => [d, s]
  | .cp d _ => [d]
  | .drop t _ => [t]
  | .clr t => [t]
  | .tl t => [t]
  | .rep c b => c :: wr b
  | .seq p q => wr p ++ wr q
  | .ifb _ p q => wr p ++ wr q
  | .nop => []

theorem exec_rep (c : Fin 200) (b : Code) (w : St) :
    exec N K (.rep c b) w =
      (fun w' => exec N K b (Function.update w' c (w' c).tail))^[(w c).length] w := rfl

/-- **A code leaves the registers it does not write.** -/
theorem exec_not_mem : ∀ (c : Code) (w : St) (j : Fin 200), j ∉ wr c → exec N K c w j = w j
  | .add d a b, w, j, h | .sub d a b, w, j, h | .mul d a b, w, j, h | .digit d a b, w, j, h
  | .rotB d a b, w, j, h | .aut d a b, w, j, h | .rhoJ d a b, w, j, h => by
    simp only [wr, List.mem_singleton] at h; simp [exec, Function.update_of_ne h]
  | .canon d a, w, j, h | .neg d a, w, j, h => by
    simp only [wr, List.mem_singleton] at h; simp [exec, Function.update_of_ne h]
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
    rw [exec_rep]
    generalize (w c).length = n
    induction n generalizing w with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply, ih, exec_not_mem b _ j h.2, Function.update_of_ne h.1]
  | .seq p q, w, j, h => by
    simp only [wr, List.mem_append, not_or] at h
    show exec N K q (exec N K p w) j = w j
    rw [exec_not_mem q _ j h.2, exec_not_mem p _ j h.1]
  | .ifb t p q, w, j, h => by
    simp only [wr, List.mem_append, not_or] at h
    simp only [exec]
    split_ifs
    · exact exec_not_mem p w j h.1
    · exact exec_not_mem q w j h.2
  | .nop, w, j, _ => rfl

/-- **Loops by an invariant**: the body leaves the counter alone, and the invariant after `i`
rounds (with the counter at `(w c).drop i`) gives it after `i + 1`. -/
theorem exec_rep_inv (c : Fin 200) (body : Code) (hc : c ∉ wr body) (P : ℕ → St → Prop) (w : St)
    (h0 : P 0 w) (hs : ∀ i < (w c).length, ∀ w', P i w' → w' c = (w c).drop i →
      P (i + 1) (exec N K body (Function.update w' c (w' c).tail))) :
    P (w c).length (exec N K (.rep c body) w) := by
  rw [exec_rep]
  have key : ∀ m ≤ (w c).length,
      P m ((fun w' => exec N K body (Function.update w' c (w' c).tail))^[m] w) ∧
        ((fun w' => exec N K body (Function.update w' c (w' c).tail))^[m] w) c = (w c).drop m := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨h0, rfl⟩
    | succ m ih =>
      intro hm
      obtain ⟨hP, hcm⟩ := ih (by omega)
      rw [Function.iterate_succ_apply']
      refine ⟨hs m (by omega) _ hP hcm, ?_⟩
      rw [exec_not_mem body _ c hc, Function.update_self, hcm, List.tail_drop]
  exact (key _ le_rfl).1

theorem opd_eq {x : List Bool} (h : x.length = N * K) : opd N K x = x := takeD_of_length' h

@[simp] theorem opd_mulRMW (a b : List Bool) : opd N K (mulRMW N K a b) = mulRMW N K a b :=
  opd_eq (length_mulRMW N K a b)

@[simp] theorem opd_digitRW (i : ℕ) (a : List Bool) : opd N K (digitRW N K i a) = digitRW N K i a :=
  opd_eq (length_digitRW' N K i a)

/-- Membership transfers along a checked inclusion of register lists. -/
theorem mem_of_all {l l' : List (Fin 200)} (h : l.all (fun x => l'.contains x) = true) {j : Fin 200}
    (hj : j ∈ l) : j ∈ l' := by
  have := List.all_eq_true.mp h j hj
  simpa using this

/-- A list of instructions, in order. -/
def ofList : List Code → Code
  | [] => .nop
  | c :: l => .seq c (ofList l)

theorem exec_ofList_cons (c : Code) (l : List Code) (w : St) :
    exec N K (ofList (c :: l)) w = exec N K (ofList l) (exec N K c w) := rfl

theorem exec_ofList_nil (w : St) : exec N K (ofList []) w = w := rfl

theorem exec_ofList_append (l₁ l₂ : List Code) (w : St) :
    exec N K (ofList (l₁ ++ l₂)) w = exec N K (ofList l₂) (exec N K (ofList l₁) w) := by
  induction l₁ generalizing w with
  | nil => rfl
  | cons c l ih => exact ih _

theorem wr_ofList : ∀ l : List Code, wr (ofList l) = l.flatMap wr
  | [] => rfl
  | c :: l => by simp [ofList, wr, wr_ofList l]

/-- Shifting a word of the register's width in. -/
theorem shiftIn_eq {r v L : List Bool} {n : ℕ} (hr : r.length = n) (hv : v.length = n) :
    ValVM.shiftIn n r (v ++ L) = v := by
  rw [ValVM.shiftIn, takeD_eq_take (by simp; omega), List.take_left' hv]
  simp [hr]

/-- **Pop** a word from a stream into a register of the template's width. -/
theorem exec_mv_pop {d s c : Fin 200} (h : ¬(d = s ∨ d = c ∨ s = c)) {w : St} {v L : List Bool}
    (hd : (w d).length = (w c).length) (hv : v.length = (w c).length) (hs : w s = v ++ L) :
    exec N K (.mv d s c) w = Function.update (Function.update w s L) d v := by
  simp only [exec, if_neg h, hs, shiftIn_eq hd hv]
  rw [List.drop_left' hv]

/-- **Push** a word of the template's width into a buffer (shifted in at its end). -/
theorem exec_mv_push {d s c : Fin 200} (h : ¬(d = s ∨ d = c ∨ s = c)) {w : St}
    (hs : (w s).length = (w c).length) :
    exec N K (.mv d s c) w =
      Function.update (Function.update w s []) d ((w d ++ w s).drop (w c).length) := by
  simp only [exec, if_neg h, ValVM.shiftIn, takeD_of_length' hs]
  rw [List.drop_eq_nil_of_le (by omega)]

/-- Shifting words into a buffer of exactly their total width leaves them. -/
theorem drop_append_flatten {b : List Bool} {vs : List (List Bool)} {n : ℕ}
    (hb : b.length = vs.length * n) :
    (b ++ vs.flatten).drop (vs.length * n) = vs.flatten := by
  rw [← hb, List.drop_left]

theorem length_flatten_of {vs : List (List Bool)} {n : ℕ} (hv : ∀ x ∈ vs, x.length = n) :
    vs.flatten.length = vs.length * n := by
  induction vs with
  | nil => simp
  | cons x vs ih =>
    rw [List.flatten_cons, List.length_append, hv x (by simp), ih (fun y hy => hv y (by simp [hy])),
      List.length_cons, Nat.succ_mul]; ring

/-- A buffer of `m n` bits after `i ≤ m` words of `n` bits were shifted in. -/
theorem drop_append_flatten_le {b : List Bool} {vs : List (List Bool)} {n m : ℕ}
    (hv : ∀ x ∈ vs, x.length = n) (hb : b.length = m * n) :
    ((b ++ vs.flatten).drop (vs.length * n)).length = m * n := by
  rw [List.length_drop, List.length_append, length_flatten_of hv, hb]; omega

theorem drop_append_flatten_succ {b x : List Bool} {vs : List (List Bool)} {n : ℕ}
    (hx : x.length = n) (hv : ∀ y ∈ vs, y.length = n) :
    ((b ++ vs.flatten).drop (vs.length * n) ++ x).drop n =
      (b ++ (vs ++ [x]).flatten).drop ((vs ++ [x]).length * n) := by
  have := drop_append_drop b vs.flatten x
  rw [length_flatten_of hv, hx] at this
  rw [this, List.flatten_append, List.flatten_singleton, List.length_append, List.length_singleton,
    Nat.succ_mul]

end RingVM

end SigabaNeo.Tape
