import CslibFrontier.Probability.UniversalHash
import Mathlib.Data.Matrix.Mul
import CslibFrontier.Probability.StatisticalDistance.CloseTo
import CslibFrontier.Probability.StatisticalDistance.Event
import Cslib.Probability.StatisticalDistance

/-!
# The leftover hash lemma for lattices

The leftover hash lemma (LHL) for the hash `x ↦ A · x` of binary inputs by a uniform matrix, over any
finite commutative ring `R`, for instance `ℤ_q` or `ℤ_q[X]/(X^N + 1)`:

* `isTwoUniversal_binaryHash`: the family is two-universal. Two distinct inputs `x, x' ∈ {0,1}^m`
  differ by `±1` at some coordinate `j`, a unit, so for each value of the other columns exactly one
  column `j` makes them collide. No structure of `R` is needed: for `R = ℤ_{2^K}[X]/(X^N + 1)` small
  polynomials need not be units, but `±1` always are.
* `closeTo_binaryHash`: **the LHL**: `(A, A · x)` with uniform `A ∈ R^{r×m}` and uniform
  `x ∈ {0,1}^m` is within `√(|R|^r · 2^{−m}) / 2` of `(A, u)` with uniform `u ∈ R^r`.
* `closeTo_of_dist`: statistical distance (cslib's `dist`) gives `CloseTo`.

The general statements, for any two-universal family, with min-entropy sources and with side
information, are cslib-frontier's (`Cslib.Probability.IsTwoUniversal.leftover_hash`,
`leftover_hash_of_isSource`, `leftover_hash_conditional_of_isSource`); this module instantiates them
for lattices. It is the statistical step of the simulated setup of BTVW17 §4.2
(`AdvancedEncryption/PE/Impl/DualUse`).
-/

namespace SigabaNeo.Lattices

open Cslib.Probability Matrix
open scoped Cslib.Probability.PMF
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

/-- Statistical distance gives closeness. -/
theorem closeTo_of_dist {α : Type} [Fintype α] {p q : PMF α} {ε : ℝ} (h : dist p q ≤ ε) :
    CloseTo p q (ENNReal.ofReal ε) := by
  intro E
  have h1 := Cslib.Probability.PMF.abs_toOuterMeasure_toReal_sub_le_dist p q E
  have hle : ∀ r : PMF α, r.toOuterMeasure E ≠ ⊤ := fun r =>
    ne_top_of_le_ne_top ENNReal.one_ne_top ((r.toOuterMeasure_mono (Set.subset_univ _)).trans
      (le_of_eq ((r.toOuterMeasure_apply_eq_one_iff Set.univ).mpr (Set.subset_univ _))))
  have hp := hle p
  have hq := hle q
  rw [← ENNReal.ofReal_toReal hp, ← ENNReal.ofReal_toReal hq,
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg (le_trans (abs_nonneg _) (h1.trans h))]
  apply ENNReal.ofReal_le_ofReal
  have := (abs_le.mp (h1.trans h)).2
  linarith

/-- **The leftover hash lemma for binary inputs**: `(A, A·x)` with uniform `A` and uniform binary
`x ∈ {0,1}^m` is within `√(|R|^r · 2^{-m}) / 2` of `(A, u)` with uniform `u`. -/
theorem closeTo_binaryHash {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    {rr mm : Type} [Fintype rr] [Fintype mm] [DecidableEq rr] [DecidableEq mm] [Nonempty mm] :
    CloseTo (seededHash (PMF.uniformOfFintype (Matrix rr mm R))
        (PMF.uniformOfFintype (mm → Bool)) (binaryHash (R := R)))
      ((PMF.uniformOfFintype (Matrix rr mm R)).bind fun A =>
        (PMF.uniformOfFintype (rr → R)).map (A, ·))
      (ENNReal.ofReal (Real.sqrt (Fintype.card (rr → R) * (2 ^ Fintype.card mm : ℝ)⁻¹) / 2)) := by
  apply closeTo_of_dist
  refine (isTwoUniversal_binaryHash (R := R) (rr := rr) (mm := mm)).leftover_hash_of_mass_le _
    fun x => ?_
  simp [PMF.uniformOfFintype_apply, Fintype.card_bool]

end SigabaNeo.Lattices
