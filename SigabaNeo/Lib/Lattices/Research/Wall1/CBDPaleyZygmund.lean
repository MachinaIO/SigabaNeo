module

public import SigabaNeo.Lib.Lattices.Research.Wall1.CBDQuadratic
import all SigabaNeo.Lib.Lattices.Research.Wall1.CBDTail
import Mathlib.Tactic

public section

namespace SigabaNeo.Wall1.CBDPaleyZygmund

open SampleDeletion CBDTail CBDQuadratic
open scoped BigOperators

private theorem tail_product {α : Type*} [Fintype α] (w X : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hmass : ∑ x, w x = 1) (t : ℝ) (ht : 0 ≤ t) (hu : t ≤ 1)
    (hm : 0 ≤ ∑ x, w x * X x) :
    let m := ∑ x, w x * X x
    (1-t)^2 * m^2 ≤ (∑ x with t*m < X x, w x) * ∑ x, w x * X x^2 := by
  intro m
  let s := Finset.univ.filter fun x ↦ t*m < X x
  have low : m ≤ t*m + ∑ x ∈ s, w x * X x := by
    rw [show t*m = ∑ x, w x * (t*m) by rw [← Finset.sum_mul, hmass, one_mul]]
    unfold s
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    split_ifs with h
    · have := mul_nonneg (hw x) (mul_nonneg ht hm)
      linarith
    · simpa using mul_le_mul_of_nonneg_left (le_of_not_gt h) (hw x)
  have hsq := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun x _ ↦ hw x)
    (fun x _ ↦ mul_nonneg (hw x) (sq_nonneg (X x)))
    (r := fun x ↦ w x * X x) (fun x _ ↦ by apply le_of_eq; ring)
  have hle : (1-t)*m ≤ ∑ x ∈ s, w x * X x := by linarith
  rw [← mul_pow]
  exact (pow_le_pow_left₀ (mul_nonneg (sub_nonneg.mpr hu) hm) hle 2).trans
    (hsq.trans (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
        (fun x _ _ ↦ mul_nonneg (hw x) (sq_nonneg _))) (Finset.sum_nonneg fun x _ ↦ hw x)))

theorem paley_zygmund {α : Type*} [Fintype α] (w X : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hmass : ∑ x, w x = 1) (hX : ∀ x, 0 ≤ X x) (t : ℝ) (ht : 0 ≤ t) (hu : t ≤ 1) :
    let m := ∑ x, w x * X x
    (1-t)^2 * m^2 / (∑ x, w x * X x^2) ≤ ∑ x with t*m < X x, w x := by
  intro m
  have h := Finset.sum_nonneg (s := Finset.univ) fun x _ ↦ mul_nonneg (hw x) (sq_nonneg (X x))
  rcases h.eq_or_lt with h | h
  · rw [← h, div_zero]
    exact Finset.sum_nonneg fun x _ ↦ hw x
  · exact (div_le_iff₀ h).mpr (tail_product w X hw hmass t ht hu
      (Finset.sum_nonneg fun x _ ↦ mul_nonneg (hw x) (hX x)))

variable {N : ℕ}

theorem projection_second_moment_le (Q : Matrix (Fin N) (Fin N) ℝ) (hs : Q.transpose = Q)
    (hp : Q*Q = Q) :
    ∑ w, jointWeight w * quadratic Q w ^ 2 ≤ (9/4)*Q.trace^2 + (9/2)*Q.trace := by
  have h := projection_variance_le Q hs hp
  have expand (w : Fin N → Digit 3) :
      jointWeight w * (quadratic Q w - (3/2)*Q.trace)^2 =
        jointWeight w * quadratic Q w^2 - (jointWeight w * quadratic Q w)*(3*Q.trace) +
        jointWeight w * ((3/2)*Q.trace)^2 := by ring
  simp only [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    quadratic_mean, joint_mass, one_mul] at h
  linarith

theorem projection_tail_lower (Q : Matrix (Fin N) (Fin N) ℝ) (hs : Q.transpose = Q)
    (hp : Q*Q = Q) (hd : 0 < Q.trace) :
    (1/25)*Q.trace/(Q.trace+2) ≤ ∑ w with (6/5)*Q.trace < quadratic Q w, jointWeight w := by
  have hw (w : Fin N → Digit 3) : 0 ≤ jointWeight w := by unfold jointWeight weight; positivity
  have h := tail_product jointWeight (quadratic Q) hw joint_mass (4/5) (by norm_num) (by norm_num)
    (by rw [quadratic_mean]; positivity)
  dsimp only at h
  rw [quadratic_mean, show (4/5:ℝ)*((3/2)*Q.trace) = (6/5)*Q.trace by ring] at h
  have hb := h.trans (mul_le_mul_of_nonneg_left (projection_second_moment_le Q hs hp)
    (Finset.sum_nonneg fun w _ ↦ hw w))
  apply (div_le_iff₀ (by linarith : 0 < Q.trace+2)).mpr
  apply le_of_mul_le_mul_right (a := Q.trace) _ hd
  nlinarith only [hb]

#print axioms paley_zygmund
#print axioms projection_second_moment_le
#print axioms projection_tail_lower

end SigabaNeo.Wall1.CBDPaleyZygmund
