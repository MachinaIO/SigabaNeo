import SigabaNeo.Lib.Machines.Compose.Plumbing

/-!
# The guard: a two-tape machine testing the first cell of a word

`guardTM` (tapes: a buffer, the flag of a virtual input) starts on a word `y` on the buffer with
the head at `0`, and the flag mark at `-1` with the head at `0` (as `rewTM` and `prepTM` leave
them).

* If `y = true :: w`, it erases the leading `true`, moves the flag mark from `-1` to `0` and moves
  both heads to `1`, in exactly `3` steps (`runs_guard`): the buffer and the flag are those of the
  virtual input `w` translated by one cell.
* Otherwise it enters a state `3` it never leaves (`law_guard_rej`), touching nothing.
-/

namespace SigabaNeo.Compose

open Cslib Turing MultiTapeMachine

variable {x : List Bool}

/-- The action of the guard in state `q` reading `w`: tape `0` is the buffer, tape `1` the flag. -/
def guardAct (q : Fin 4) (w : Fin 2 → Option Bool) : Turing.Action 2 Bool (Fin 4) :=
  if q.val = 0 then
    if w 0 = some true then act2 (some none, 1) (none, -1) (some 1)
    else act2 (none, 0) (none, 0) (some 3)
  else if q.val = 1 then act2 (none, 0) (some none, 1) (some 2)
  else if q.val = 2 then act2 (none, 0) (some (some true), 1) none
  else act2 (none, 0) (none, 0) (some 3)

/-- **The guard.** -/
def guardTM : MultiTapePTM 2 Bool (Fin 4) (Fin 0) where
  initial := 0
  tr q _ w _ := fun _ => .step (guardAct q w) Fin.elim0 Fin.elim0

theorem guard_one (i : Fin 4) (ip : Fin (x.length + 2)) (out : List Bool)
    (t0 t1 : ℤ → Option Bool) (h0 h1 : ℤ) :
    law guardTM 1 (pc (some i) ip out t0 t1 h0 h1) =
      PMF.pure ((pc (some i) ip out t0 t1 h0 h1).step (guardAct i ![t0 h0, t1 h1])
        Fin.elim0 Fin.elim0) := by
  refine law_one_det _ _ rfl _ _ _ (fun _ => ?_)
  have : (pc (some i) ip out t0 t1 h0 h1).tapes.workTapeSymbols = ![t0 h0, t1 h1] := by
    funext j; fin_cases j <;> rfl
  rw [this]; rfl

/-- A word translated by one cell. -/
def shiftTape (t : ℤ → Option Bool) : ℤ → Option Bool := fun p => t (p - 1)

theorem erase_head (w : List Bool) :
    Function.update (tapeOfList (true :: w)) 0 none = shiftTape (tapeOfList w) := by
  funext p
  rcases p with (_ | n) | n
  · simp [shiftTape]; rfl
  · rw [Function.update_of_ne (by simp; omega), shiftTape,
      show ((Int.ofNat (n + 1)) - 1 : ℤ) = ((n : ℕ) : ℤ) by simp]
    exact (tapeOfList_ofNat (true :: w) (n + 1)).trans (by simp)
  · rw [Function.update_of_ne (by omega), shiftTape,
      show (Int.negSucc n - 1 : ℤ) = Int.negSucc (n + 1) by omega]
    rfl

theorem move_flag :
    Function.update (Function.update flagTape (-1) none) 0 (some true) = shiftTape flagTape := by
  funext p
  simp only [shiftTape, flagTape, Function.update_apply]
  by_cases h0 : p = 0
  · subst h0; simp
  · by_cases h1 : p = -1
    · subst h1; simp
    · simp [h0, h1, show p - 1 ≠ -1 by omega]

/-- The end of the guard on `true :: w`. -/
def guardFin (w : List Bool) (ip : Fin (x.length + 2)) (out : List Bool) :
    Config 2 Bool (Fin 4) (Fin 0) x :=
  pc none ip out (shiftTape (tapeOfList w)) (shiftTape flagTape) 1 1

/-- **On `true :: w` the guard runs exactly `3` steps**, translating the virtual input `w` by one
cell. -/
theorem runs_guard (w : List Bool) (ip : Fin (x.length + 2)) (out : List Bool) :
    Runs guardTM (pc (some 0) ip out (tapeOfList (true :: w)) flagTape 0 0) 3
      (guardFin w ip out) := by
  have hT : tapeOfList (true :: w) 0 = some true := rfl
  refine runs_cons (by simp) (guard_one ..) ?_
  simp only [guardAct, Matrix.cons_val_zero, hT, Fin.isValue, Fin.val_zero, ↓reduceIte]
  rw [pc_step]
  refine runs_cons (by simp) (guard_one ..) ?_
  simp only [guardAct, Fin.isValue, Fin.val_one, one_ne_zero, ↓reduceIte]
  rw [pc_step]
  refine runs_halt (c' := guardFin w ip out) (by simp) ?_ rfl
  rw [guard_one]
  have h2 : (2 : Fin 4).val = 2 := rfl
  simp only [guardAct, h2, Fin.isValue, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one]
  rw [pc_step]
  simp only [upd, guardFin, erase_head, SignType.coe_neg, SignType.coe_one,
    SignType.coe_zero, add_zero]
  norm_num [move_flag]

/-- The rejecting state `3` is never left. -/
theorem guard_loop (ip : Fin (x.length + 2)) (out : List Bool) (t0 t1 : ℤ → Option Bool)
    (h0 h1 : ℤ) : ∀ n, law guardTM n (pc (some 3) ip out t0 t1 h0 h1) =
      PMF.pure (pc (some 3) ip out t0 t1 h0 h1) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [law_add, ih, PMF.pure_bind, guard_one]
    have h3 : (3 : Fin 4).val = 3 := rfl
    simp only [guardAct, h3, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one,
      show (3 : ℕ) ≠ 2 by decide]
    rw [pc_step]
    simp [upd]

theorem tapeOfList_zero (y : List Bool) : tapeOfList y 0 = y.head? := by
  cases y <;> rfl

/-- **Off `true :: _` the guard rejects**: it enters the state `3` and stays there. -/
theorem law_guard_rej (y : List Bool) (hy : y.head? ≠ some true) (ip : Fin (x.length + 2))
    (out : List Bool) (t1 : ℤ → Option Bool) (h1 : ℤ) (n : ℕ) :
    law guardTM (n + 1) (pc (some 0) ip out (tapeOfList y) t1 0 h1) =
      PMF.pure (pc (some 3) ip out (tapeOfList y) t1 0 h1) := by
  rw [Nat.add_comm, law_add, guard_one, PMF.pure_bind]
  simp only [guardAct, Matrix.cons_val_zero, tapeOfList_zero, hy, Fin.isValue, Fin.val_zero,
    ↓reduceIte]
  rw [pc_step]
  simp only [upd, SignType.coe_zero, add_zero]
  exact guard_loop ..

end SigabaNeo.Compose
