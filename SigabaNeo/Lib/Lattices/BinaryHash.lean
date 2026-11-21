import CslibFrontier.Probability.UniversalHash
import Mathlib.Data.Matrix.Mul

/-!
# Binary inputs hashed by a uniform matrix

Over any finite commutative ring `R`, the family `x ↦ A · x` with a uniform matrix
`A ∈ R^{r × m}` and inputs `x ∈ {0,1}^m` is two-universal (`isTwoUniversal_binaryHash`): two
distinct inputs differ by `±1` at some coordinate `j`, a unit, so for each value of the other
columns exactly one column `j` makes them collide. No structure of `R` is needed (for instance
`R = ℤ_{2^K}[X]/(X^N + 1)`, where small polynomials need not be units). With cslib's leftover hash
lemma this is the statistical step of the simulated setup of BTVW17 §4.2.
-/

namespace SigabaNeo.Lattices

open Cslib.Probability Matrix
open scoped ENNReal

variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
  {rr mm : Type*} [Fintype rr] [Fintype mm] [DecidableEq rr] [DecidableEq mm]

/-- A bit as `0/1` in `R`. -/
def bitVal (b : Bool) : R := if b then 1 else 0

/-- The hash of a binary input: `A · x`. -/
def binaryHash (A : Matrix rr mm R) (x : mm → Bool) : rr → R :=
  A *ᵥ fun i => bitVal (x i)

/-- The matrices whose rows annihilate `d`, where `d j² = 1`, are those whose column `j` is
determined by the other columns. -/
def annihEquiv (d : mm → R) (j : mm) (hd : d j * d j = 1) :
    {A : Matrix rr mm R // A *ᵥ d = 0} ≃ (rr → {i // i ≠ j} → R) where
  toFun A a i := A.1 a i
  invFun B := ⟨Matrix.of fun a i =>
      if h : i = j then -(d j) * ∑ i' : {i // i ≠ j}, B a i' * d i' else B a ⟨i, h⟩, by
    funext a
    simp only [mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ j, dite_eq_left_of_eq_true (eq_self j)]
    simp only [show ∀ i : {i // i ≠ j}, (if h : (i : mm) = j then
        -(d j) * ∑ i' : {i // i ≠ j}, B a i' * d i' else B a ⟨i, h⟩) = B a i from
      fun i => by simp only [i.2, dite_false]]
    linear_combination (-(∑ i' : {i // i ≠ j}, B a i' * d i')) * hd⟩
  left_inv A := by
    obtain ⟨A, hA⟩ := A
    apply Subtype.ext
    ext a i
    simp only [Matrix.of_apply]
    split_ifs with h
    · subst h
      have hrow := congrFun hA a
      simp only [mulVec, dotProduct, Pi.zero_apply] at hrow
      rw [Fintype.sum_eq_add_sum_subtype_ne _ i] at hrow
      linear_combination (-(d i)) * hrow + A a i * hd
    · rfl
  right_inv B := by
    funext a i
    simp only [Matrix.of_apply, i.2, dite_false]

/-- **Binary inputs hashed by a uniform matrix form a two-universal family.** -/
theorem isTwoUniversal_binaryHash [Nonempty mm] :
    IsTwoUniversal (PMF.uniformOfFintype (Matrix rr mm R)) (binaryHash (R := R)) := by
  intro x x' hne
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  set d : mm → R := fun i => bitVal (x i) - bitVal (x' i)
  have hd : d j * d j = 1 := by
    simp only [d, bitVal]
    cases hx : x j <;> cases hx' : x' j <;> simp_all
  have hset : {A : Matrix rr mm R | binaryHash A x = binaryHash A x'} =
      {A | A *ᵥ d = 0} := by
    ext A
    simp only [Set.mem_ofPred_eq, binaryHash, d]
    rw [← sub_eq_zero, ← mulVec_sub]
    rfl
  rw [hset, PMF.toOuterMeasure_apply, tsum_fintype]
  have hsum : ∑ A : Matrix rr mm R, {A : Matrix rr mm R | A *ᵥ d = 0}.indicator
      (PMF.uniformOfFintype (Matrix rr mm R)) A =
      (Fintype.card {A : Matrix rr mm R // A *ᵥ d = 0} : ℝ≥0∞) *
        (Fintype.card (Matrix rr mm R) : ℝ≥0∞)⁻¹ := by
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, PMF.uniformOfFintype_apply]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      Fintype.card_subtype]
  have hcard : Fintype.card {A : Matrix rr mm R // A *ᵥ d = 0} * Fintype.card (rr → R) =
      Fintype.card (Matrix rr mm R) := by
    rw [Fintype.card_congr (annihEquiv d j hd)]
    have hM : Fintype.card (Matrix rr mm R) = Fintype.card R ^ (Fintype.card mm * Fintype.card rr) := by
      show Fintype.card (rr → mm → R) = _
      rw [Fintype.card_fun, Fintype.card_fun, ← pow_mul]
    have hj1 : Fintype.card {i // i ≠ j} = Fintype.card mm - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    rw [hM, Fintype.card_fun, Fintype.card_fun, Fintype.card_fun, hj1, ← pow_mul, ← pow_add]
    have hm : 1 ≤ Fintype.card mm := Fintype.card_pos
    congr 1
    rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ hm)]
  rw [hsum, ← hcard, Nat.cast_mul, ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
    (Or.inl (ENNReal.natCast_ne_top _)), ← mul_assoc]
  have hpos : (Fintype.card {A : Matrix rr mm R // A *ᵥ d = 0} : ℝ≥0∞) ≠ 0 := by
    have : 0 < Fintype.card {A : Matrix rr mm R // A *ᵥ d = 0} :=
      Fintype.card_pos_iff.mpr ⟨⟨0, by simp⟩⟩
    exact_mod_cast this.ne'
  rw [ENNReal.mul_inv_cancel hpos (ENNReal.natCast_ne_top _), one_mul]

end SigabaNeo.Lattices
