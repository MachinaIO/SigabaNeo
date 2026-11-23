import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-! # No products of two large components below the truncation threshold

This file verifies the algebraic truncation used in Part 286. It applies to any
finite tail of powers, hence to the factorial-weighted exponential remainder.
It does not establish the probabilistic cumulant identity, numerical activity
bounds, or the full BKZ certificate.
-/

noncomputable section
namespace SigabaNeo.Wall1.LinearRemainder
open Finset PowerSeries

variable {R : Type*} [CommRing R]

/-- The coefficients strictly below a cutoff vanish. -/
def VanishesBelow (k : ℕ) (f : PowerSeries R) : Prop :=
  ∀ n, n < k → coeff n f = 0

/-- Multiplication adds lower support cutoffs. -/
theorem vanishesBelow_mul {k l : ℕ} {f g : PowerSeries R}
    (hf : VanishesBelow k f) (hg : VanishesBelow l g) :
    VanishesBelow (k + l) (f * g) := by
  intro n hn
  rw [coeff_mul]
  apply sum_eq_zero
  rintro ⟨i, j⟩ hij
  have he : i + j = n := mem_antidiagonal.mp hij
  by_cases hi : i < k
  · simp [hf i hi]
  · have hj : j < l := by omega
    simp [hg j hj]

/-- Multiplying by an unrestricted series preserves a lower support cutoff. -/
theorem vanishesBelow_mul_left (f : PowerSeries R) {k : ℕ} {g : PowerSeries R}
    (hg : VanishesBelow k g) : VanishesBelow k (f * g) := by
  simpa using vanishesBelow_mul (k := 0) (f := f) (by intro n hn; omega) hg

/-- Every power of exponent at least two begins at twice the support cutoff. -/
theorem vanishesBelow_pow_add_two {k : ℕ} {u : PowerSeries R}
    (hu : VanishesBelow k u) (r : ℕ) : VanishesBelow (k + k) (u ^ (r + 2)) := by
  rw [pow_add, pow_two]
  exact vanishesBelow_mul_left _ (vanishesBelow_mul hu hu)

/-- A finite arbitrary-coefficient tail starting at the square. -/
def higherPowers (terms : ℕ) (c : ℕ → R) (u : PowerSeries R) : PowerSeries R :=
  ∑ r ∈ range terms, C (c r) * u ^ (r + 2)

/-- A sum of higher powers still starts at twice the support cutoff. -/
theorem vanishesBelow_higherPowers {k : ℕ} {u : PowerSeries R}
    (hu : VanishesBelow k u) (terms : ℕ) (c : ℕ → R) :
    VanishesBelow (k + k) (higherPowers terms c u) := by
  intro n hn
  simp only [higherPowers, map_sum]
  apply sum_eq_zero
  intro r hr
  exact vanishesBelow_mul_left _ (vanishesBelow_pow_add_two hu r) n hn

/-- All mixtures with a fixed series are linear in the high-supported remainder. -/
theorem coeff_remainder_linear {k n : ℕ} {u : PowerSeries R}
    (hu : VanishesBelow k u) (hn : n < k + k)
    (e : PowerSeries R) (terms : ℕ) (c : ℕ → R) :
    coeff n (e * (u + higherPowers terms c u)) = coeff n (e * u) := by
  rw [mul_add, map_add]
  rw [vanishesBelow_mul_left e (vanishesBelow_higherPowers hu terms c) n hn, add_zero]

/-- Weighted truncation retains only the linear convolution with the unknown series. -/
theorem weighted_remainder_linear {k order : ℕ} {u : PowerSeries R}
    (hu : VanishesBelow k u) (horder : order < k + k)
    (e : PowerSeries R) (terms : ℕ) (c w : ℕ → R) :
    (∑ n ∈ range (order + 1), w n * coeff n (e * (u + higherPowers terms c u))) =
      ∑ n ∈ range (order + 1), w n *
        ∑ p ∈ antidiagonal n, coeff p.1 e * coeff p.2 u := by
  apply sum_congr rfl
  intro n hn
  have hn' : n < k + k := by have := mem_range.mp hn; omega
  rw [coeff_remainder_linear hu hn', coeff_mul]

/-- At order 24, components supported in degrees at least 14 have only linear contributions. -/
theorem weighted_remainder_24 {u : PowerSeries R} (hu : VanishesBelow 14 u)
    (e : PowerSeries R) (terms : ℕ) (c w : ℕ → R) :
    (∑ n ∈ range 25, w n * coeff n (e * (u + higherPowers terms c u))) =
      ∑ n ∈ range 25, w n *
        ∑ p ∈ antidiagonal n, coeff p.1 e * coeff p.2 u :=
  weighted_remainder_linear hu (by norm_num : 24 < 14 + 14) e terms c w

/-- Only the low prefix of the known multiplier can mix with a high-supported series. -/
theorem coeff_mul_eq_of_prefix {k order n : ℕ} {u e f : PowerSeries R}
    (hu : VanishesBelow k u) (hn : n ≤ order)
    (hef : ∀ i, i + k ≤ order → coeff i e = coeff i f) :
    coeff n (e * u) = coeff n (f * u) := by
  simp only [coeff_mul]
  apply sum_congr rfl
  rintro ⟨i, j⟩ hij
  have he : i + j = n := mem_antidiagonal.mp hij
  by_cases hj : j < k
  · simp [hu j hj]
  · rw [hef i (by omega)]

/-- Degrees above ten of the multiplier do not affect the order-24 residual. -/
theorem coeff_mul_prefix_24 {u e f : PowerSeries R}
    (hu : VanishesBelow 14 u) (hef : ∀ i, i ≤ 10 → coeff i e = coeff i f)
    {n : ℕ} (hn : n ≤ 24) : coeff n (e * u) = coeff n (f * u) :=
  coeff_mul_eq_of_prefix hu hn (fun i hi ↦ hef i (by omega))

/-- The nonconstant finite exponential sum, including powers one through `terms + 1`. -/
def exponentialRemainder (terms : ℕ) (u : PowerSeries ℝ) : PowerSeries ℝ :=
  ∑ r ∈ range (terms + 1), C ((Nat.factorial (r + 1) : ℝ)⁻¹) * u ^ (r + 1)

/-- The factorial sum has its linear term followed by a tail starting at the square. -/
theorem exponentialRemainder_eq (terms : ℕ) (u : PowerSeries ℝ) :
    exponentialRemainder terms u =
      u + higherPowers terms (fun r ↦ (Nat.factorial (r + 2) : ℝ)⁻¹) u := by
  simp [exponentialRemainder, sum_range_succ', higherPowers, add_comm,
    Nat.add_left_comm]

/-- The actual factorial-weighted finite exponential remainder is linear through degree 24. -/
theorem weighted_exponential_remainder_24 {u : PowerSeries ℝ}
    (hu : VanishesBelow 14 u) (e : PowerSeries ℝ) (terms : ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ range 25, w n * coeff n (e * exponentialRemainder terms u)) =
      ∑ n ∈ range 25, w n *
        ∑ p ∈ antidiagonal n, coeff p.1 e * coeff p.2 u := by
  rw [exponentialRemainder_eq]
  exact weighted_remainder_24 hu e terms _ w

end SigabaNeo.Wall1.LinearRemainder
