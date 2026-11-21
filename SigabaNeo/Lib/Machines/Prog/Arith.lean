import SigabaNeo.Lib.Machines.Prog.Basic

/-!
# Fixed-width arithmetic of the tape language

Words are big-endian binary numbers (`bitsVal`). On words of equal length `n`, the primitive
`carry addBit i j` adds modulo `2^n` (`bitsVal_add`) and `carry subBit i j` subtracts modulo `2^n`
(`bitsVal_sub`); the final carry is the overflow (`addC_spec`) and the final borrow the comparison
`s i < s j` (`subC_spec`).
-/

namespace SigabaNeo.Tape

/-- The value of a big-endian word. -/
def bitsVal : List Bool → ℕ
  | [] => 0
  | x :: xs => x.toNat * 2 ^ xs.length + bitsVal xs

theorem bitsVal_lt (a : List Bool) : bitsVal a < 2 ^ a.length := by
  induction a with
  | nil => simp [bitsVal]
  | cons x xs ih =>
    simp only [bitsVal, List.length_cons, pow_succ]
    cases x <;> simp <;> omega

/-- **Addition with carry**: the carry out, at weight `2^n`, plus the result is the sum. -/
theorem addC_spec (a b : List Bool) (h : a.length = b.length) :
    (carryOp addBit a b).1.toNat * 2 ^ a.length + bitsVal (carryOp addBit a b).2 =
      bitsVal a + bitsVal b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [bitsVal]
  | cons x xs ih =>
    obtain ⟨y, ys, rfl⟩ : ∃ y ys, b = y :: ys := by
      cases b with
      | nil => simp at h
      | cons y ys => exact ⟨y, ys, rfl⟩
    have h' : xs.length = ys.length := by simpa using h
    have ih' := ih ys h'
    simp only [carryOp, List.headD_cons, List.tail_cons, bitsVal, List.length_cons,
      length_carryOp] at ih' ⊢
    generalize (carryOp addBit xs ys).1 = c at ih' ⊢
    generalize bitsVal (carryOp addBit xs ys).2 = r at ih' ⊢
    rw [← h'] at ⊢
    rw [pow_succ]
    cases x <;> cases y <;> cases c <;> simp [addBit] at ih' ⊢ <;> omega

/-- **Addition modulo `2^n`** on words of equal length `n`. -/
theorem bitsVal_add (a b : List Bool) (h : a.length = b.length) :
    bitsVal (carryOp addBit a b).2 = (bitsVal a + bitsVal b) % 2 ^ a.length := by
  have hs := addC_spec a b h
  have hlt := bitsVal_lt (carryOp addBit a b).2
  rw [length_carryOp] at hlt
  rw [← hs, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]

/-- **Subtraction with borrow**: the result minus the borrow out, at weight `2^n`, is the
difference. -/
theorem subC_spec (a b : List Bool) (h : a.length = b.length) :
    (bitsVal (carryOp subBit a b).2 : ℤ) - (carryOp subBit a b).1.toNat * 2 ^ a.length =
      bitsVal a - bitsVal b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [bitsVal]
  | cons x xs ih =>
    obtain ⟨y, ys, rfl⟩ : ∃ y ys, b = y :: ys := by
      cases b with
      | nil => simp at h
      | cons y ys => exact ⟨y, ys, rfl⟩
    have h' : xs.length = ys.length := by simpa using h
    have ih' := ih ys h'
    simp only [carryOp, List.headD_cons, List.tail_cons, bitsVal, List.length_cons,
      length_carryOp] at ih' ⊢
    generalize (carryOp subBit xs ys).1 = c at ih' ⊢
    generalize bitsVal (carryOp subBit xs ys).2 = r at ih' ⊢
    rw [← h'] at ⊢
    rw [pow_succ]
    push_cast
    cases x <;> cases y <;> cases c <;> simp [subBit] at ih' ⊢ <;> linarith

/-- **Subtraction modulo `2^n`** on words of equal length `n`. -/
theorem bitsVal_sub (a b : List Bool) (h : a.length = b.length) :
    (bitsVal (carryOp subBit a b).2 : ℤ) = (bitsVal a - bitsVal b) % 2 ^ a.length := by
  have hs := subC_spec a b h
  have hlt := bitsVal_lt (carryOp subBit a b).2
  rw [length_carryOp] at hlt
  rw [← hs, sub_eq_add_neg, ← neg_mul, Int.add_mul_emod_self_right,
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hlt)]

/-- The borrow out of a subtraction of words of equal length is the comparison `a < b`. -/
theorem subC_borrow (a b : List Bool) (h : a.length = b.length) :
    (carryOp subBit a b).1 = decide (bitsVal a < bitsVal b) := by
  have hs := subC_spec a b h
  have hlt := bitsVal_lt (carryOp subBit a b).2
  have hlt' := bitsVal_lt b
  rw [length_carryOp] at hlt
  rw [← h] at hlt'
  cases hc : (carryOp subBit a b).1
  · simp only [hc, Bool.toNat_false, Nat.cast_zero, zero_mul, sub_zero] at hs
    simp only [Bool.false_eq, decide_eq_false_iff_not, not_lt]
    omega
  · simp only [hc, Bool.toNat_true, Nat.cast_one, one_mul] at hs
    have : (bitsVal (carryOp subBit a b).2 : ℤ) < 2 ^ a.length := by exact_mod_cast hlt
    exact (decide_eq_true (by omega)).symm

/-! ### Derived programs -/

namespace Prog

variable {k : ℕ}

/-- `i := s i + s j mod 2^|s i|`. -/
abbrev add (i j : Fin k) : Prog k := prim (.carry addBit i j)

/-- `i := s i - s j mod 2^|s i|`. -/
abbrev sub (i j : Fin k) : Prog k := prim (.carry subBit i j)

/-- `i := w`, by clearing tape `i` and putting the bits of `w` in front, the last first. -/
def setConst (i : Fin k) (w : List Bool) : Prog k :=
  w.foldr (fun b p => seq p (prim (.cons i b))) (prim (.clear i))

theorem denote_setConst (i : Fin k) (w : List Bool) (s : Store k) :
    (setConst i w).denote s = pure (Function.update s i w) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [setConst, List.foldr_cons] at ih ⊢
    rw [denote, ih, pure_bind]
    simp [denote, Prim.apply, Function.update_idem]

theorem wf_setConst (i : Fin k) (w : List Bool) : (setConst i w).WF := by
  induction w with
  | nil => trivial
  | cons b w ih => exact ⟨ih, trivial⟩

end Prog

end SigabaNeo.Tape
