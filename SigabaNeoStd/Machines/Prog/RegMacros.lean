import SigabaNeoStd.Machines.Prog.Stream

/-!
# Loop macros on arbitrary tapes

Small loops of the fragment `NoGrow`, stated on any tapes of any store (with explicit
distinctness hypotheses instead of a relabelling):

* `dropBy x y c`: drop `|s y|` bits of `x` (`run_dropBy`);
* `shiftIn b x y c`: shift `|s y|` copies of `b` into the register `x` (`run_shiftIn`);
* `skipZ x y c`: drop the leading `false`s of `x`, at most `|s y|` (`run_skipZ`);
* `countOnes x o y c`: drop the leading `true`s of `x`, at most `|s y|`, and as many bits of `o`
  (`run_countOnes`);
* `moveBits r x c`: shift the whole word `x` into the register `r`, consuming it (`run_moveBits`).

The counter `c` is a scratch tape, blank afterwards.
-/

namespace SigabaNeo.Tape

namespace Prog

open scoped Prog

variable {k : ℕ}

/-! ### Loops whose body acts on one or two tapes -/

theorem run_loop_one (c x : Fin k) (body : Prog k) (f : List Bool → List Bool) (hcx : c ≠ x)
    (hb : ∀ s, run body s = Function.update s x (f (s x))) (s : Store k) :
    run (loop c body) s = Function.update (Function.update s c []) x (f^[(s c).length] (s x)) := by
  have h := run_loop_iter c body (fun a => Function.update s x a) f (fun _ => True)
    (fun a w _ => by
      rw [hb, Function.update_of_ne hcx.symm, Function.update_self]
      funext i; simp only [Function.update_apply]; split_ifs <;> simp_all) (fun _ _ => trivial) (s c) (s x) trivial
  have e : Function.update (Function.update s x (s x)) c (s c) = s := by simp
  rw [e] at h
  rw [h]; funext i; simp only [Function.update_apply]; split_ifs <;> simp_all

theorem run_loop_two (c x y : Fin k) (body : Prog k) (f : List Bool × List Bool → List Bool × List Bool)
    (hcx : c ≠ x) (hcy : c ≠ y) (hxy : x ≠ y)
    (hb : ∀ s, run body s = Function.update (Function.update s x (f (s x, s y)).1) y (f (s x, s y)).2)
    (s : Store k) :
    run (loop c body) s = Function.update (Function.update (Function.update s c []) x
      (f^[(s c).length] (s x, s y)).1) y (f^[(s c).length] (s x, s y)).2 := by
  have h := run_loop_iter c body (fun a => Function.update (Function.update s x a.1) y a.2) f
    (fun _ => True)
    (fun a w _ => by
      rw [hb]
      simp only [Function.update_of_ne hcx.symm, Function.update_of_ne hcy.symm,
        Function.update_self, Function.update_of_ne hxy]
      funext i; simp only [Function.update_apply]; split_ifs <;> simp_all)
    (fun _ _ => trivial) (s c) (s x, s y) trivial
  have e : Function.update (Function.update (Function.update s x (s x, s y).1) y (s x, s y).2) c
      (s c) = s := by simp
  rw [e] at h
  rw [h]; funext i; simp only [Function.update_apply]; split_ifs <;> simp_all

/-! ### `dropBy` -/

/-- Drop `|s y|` bits of `x`, with the counter `c`. -/
def dropBy (x y c : Fin k) : Prog k := cp c y ⨾ loop c (tl x)

theorem iterate_tail (m : ℕ) (w : List Bool) : List.tail^[m] w = w.drop m := by
  induction m generalizing w with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, ih, List.drop_tail]

theorem run_dropBy (x y c : Fin k) (hcx : c ≠ x) (s : Store k) :
    run (dropBy x y c) s =
      Function.update (Function.update s c []) x ((s x).drop (s y).length) := by
  rw [dropBy, run_seq, run_copy, run_loop_one c x _ List.tail hcx (fun s => by rw [run_tail])]
  simp only [Function.update_self, Function.update_of_ne hcx.symm, Function.update_idem,
    iterate_tail]

/-! ### `shiftIn` -/

/-- Shift `|s y|` copies of `b` into the register `x`. -/
def shiftIn (b : Bool) (x y c : Fin k) : Prog k := cp c y ⨾ loop c (sin b x)

theorem iterate_sin (b : Bool) (m : ℕ) (r : List Bool) :
    (fun r : List Bool => (r ++ [b]).tail)^[m] r = (r ++ List.replicate m b).drop m := by
  induction m generalizing r with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ_apply, ih, List.replicate_succ, tail_append_drop]

theorem run_shiftIn (b : Bool) (x y c : Fin k) (hcx : c ≠ x) (s : Store k) :
    run (shiftIn b x y c) s = Function.update (Function.update s c []) x
      ((s x ++ List.replicate (s y).length b).drop (s y).length) := by
  rw [shiftIn, run_seq, run_copy,
    run_loop_one c x _ (fun r => (r ++ [b]).tail) hcx (fun s => by rw [run_sin])]
  simp only [Function.update_self, Function.update_of_ne hcx.symm, Function.update_idem,
    iterate_sin]

/-! ### Leading runs -/

/-- The number of leading copies of `b`. -/
def lead (b : Bool) : List Bool → ℕ
  | [] => 0
  | x :: w => if x = b then lead b w + 1 else 0

@[simp] theorem lead_nil (b : Bool) : lead b [] = 0 := rfl

theorem lead_append_replicate (b : Bool) (m : ℕ) (w : List Bool) (hw : hd w ≠ b ∨ w = []) :
    lead b (List.replicate m b ++ w) = m := by
  induction m with
  | zero =>
    rcases w with _ | ⟨x, w⟩
    · rfl
    · simp only [hd_cons] at hw
      rcases hw with hw | hw
      · simp [lead, hw]
      · simp at hw
  | succ m ih => simp [List.replicate_succ, lead, ih]

/-- The step of `countOnes`: drop a leading `true` of the first word and a bit of the second. -/
def onesStep : List Bool × List Bool → List Bool × List Bool
  | (a, o) => if hd a = true then (a.tail, o.tail) else (a, o)

theorem onesStep_iter : ∀ (m : ℕ) (a o : List Bool),
    onesStep^[m] (a, o) = (a.drop (min m (lead true a)), o.drop (min m (lead true a)))
  | 0, a, o => by simp
  | m + 1, a, o => by
    rw [Function.iterate_succ_apply]
    rcases a with _ | ⟨x, a⟩
    · have : onesStep ([], o) = ([], o) := rfl
      rw [this, onesStep_iter m]; simp
    · cases x
      · have : onesStep (false :: a, o) = (false :: a, o) := rfl
        rw [this, onesStep_iter m]; simp [lead]
      · have : onesStep (true :: a, o) = (a, o.tail) := rfl
        rw [this, onesStep_iter m]
        simp only [lead, ite_true, List.drop_tail]
        rw [show min (m + 1) (lead true a + 1) = min m (lead true a) + 1 by omega,
          List.drop_succ_cons]

/-- The step of `skipZ`: drop a leading `false`. -/
def zerosStep (a : List Bool) : List Bool := if hd a = true then a else a.tail

theorem zerosStep_iter : ∀ (m : ℕ) (a : List Bool),
    zerosStep^[m] a = a.drop (min m (lead false a))
  | 0, a => by simp
  | m + 1, a => by
    rw [Function.iterate_succ_apply]
    rcases a with _ | ⟨x, a⟩
    · have : zerosStep [] = [] := rfl
      rw [this, zerosStep_iter m]; simp
    · cases x
      · have : zerosStep (false :: a) = a := rfl
        rw [this, zerosStep_iter m]
        simp only [lead, ite_true]
        rw [show min (m + 1) (lead false a + 1) = min m (lead false a) + 1 by omega]
        rfl
      · have : zerosStep (true :: a) = true :: a := rfl
        rw [this, zerosStep_iter m]; simp [lead]

/-- Drop the leading `true`s of `x` (at most `|s y|`) and as many bits of `o`. -/
def countOnes (x o y c : Fin k) : Prog k :=
  cp c y ⨾ loop c (ifBit x (tl x ⨾ tl o) (nop x))

theorem run_countOnes (x o y c : Fin k) (hcx : c ≠ x) (hco : c ≠ o) (hxo : x ≠ o) (s : Store k) :
    run (countOnes x o y c) s = Function.update (Function.update (Function.update s c []) x
      ((s x).drop (min (s y).length (lead true (s x))))) o
      ((s o).drop (min (s y).length (lead true (s x)))) := by
  rw [countOnes, run_seq, run_copy, run_loop_two c x o _ onesStep hcx hco hxo (fun s => by
    rw [run_ifBit]
    split_ifs with h
    · simp only [run_seq, run_tail, onesStep, h, ite_true, Function.update_of_ne hxo.symm]
    · simp only [run_nop, onesStep, h, Bool.false_eq_true, ite_false]
      simp)]
  simp only [Function.update_self, Function.update_of_ne hcx.symm, Function.update_of_ne hco.symm,
    Function.update_idem, onesStep_iter]

/-- Drop the leading `false`s of `x` (at most `|s y|`). -/
def skipZ (x y c : Fin k) : Prog k := cp c y ⨾ loop c (ifBit x (nop x) (tl x))

theorem run_skipZ (x y c : Fin k) (hcx : c ≠ x) (s : Store k) :
    run (skipZ x y c) s = Function.update (Function.update s c []) x
      ((s x).drop (min (s y).length (lead false (s x)))) := by
  rw [skipZ, run_seq, run_copy, run_loop_one c x _ zerosStep hcx (fun s => by
    rw [run_ifBit]
    split_ifs with h
    · simp [zerosStep, h]
    · simp [zerosStep, h])]
  simp only [Function.update_self, Function.update_of_ne hcx.symm, Function.update_idem,
    zerosStep_iter]

/-! ### Moving a word into a register -/

/-- Shift the word `x` into the register `r`, bit by bit, consuming `x`. -/
def moveBits (r x c : Fin k) : Prog k := cp c x ⨾ loop c (push r x ⨾ tl x)

theorem run_moveBits (r x c : Fin k) (hcr : c ≠ r) (hcx : c ≠ x) (hrx : r ≠ x) (s : Store k) :
    run (moveBits r x c) s = Function.update (Function.update (Function.update s c []) r
      ((s r ++ s x).drop (s x).length)) x [] := by
  rw [moveBits, run_seq, run_copy, run_loop_two c r x _ (fun a => ((a.1 ++ [hd a.2]).tail, a.2.tail))
    hcr hcx hrx (fun s => by
      simp only [run_seq, run_push, run_tail, Function.update_of_ne hrx.symm])]
  have it : ∀ (m : ℕ) (a b : List Bool), (fun a : List Bool × List Bool =>
      ((a.1 ++ [hd a.2]).tail, a.2.tail))^[m] (a, b) = ((a ++ takeD m b).drop m, b.drop m) := by
    intro m
    induction m with
    | zero => intro a b; simp [takeD]
    | succ m ih =>
      intro a b
      rw [Function.iterate_succ_apply, ih, takeD, tail_append_drop, List.drop_tail]
  simp only [Function.update_self, Function.update_of_ne hcr.symm, Function.update_of_ne hcx.symm,
    Function.update_idem, it, takeD_of_length, List.drop_length]

theorem noGrow_dropBy (x y c : Fin k) : (dropBy x y c).NoGrow := rfl
theorem noGrow_shiftIn (b : Bool) (x y c : Fin k) : (shiftIn b x y c).NoGrow := rfl
theorem noGrow_countOnes (x o y c : Fin k) : (countOnes x o y c).NoGrow := rfl
theorem noGrow_skipZ (x y c : Fin k) : (skipZ x y c).NoGrow := rfl
theorem noGrow_moveBits (r x c : Fin k) : (moveBits r x c).NoGrow := rfl

end Prog

end SigabaNeo.Tape
