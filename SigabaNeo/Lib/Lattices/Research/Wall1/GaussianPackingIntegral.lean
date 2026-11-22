module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-! # Gaussian mass from polynomial ball counts

The indices may be the nonzero points of a lattice. Bounding every finite partial sum
avoids any a priori summability assumption on its theta series.
-/

public section
namespace SigabaNeo.Wall1

open MeasureTheory Set Real

/-- Integrate a counting bound in the squared-radius variable. -/
theorem gaussianMass_of_sublevel_count {ι : Type*} (energy : ι → ℝ)
    (he : ∀ i, 0 ≤ energy i) {A p : ℝ} (hp : 0 ≤ p)
    (count : ∀ (s : Finset ι) (t : ℝ), 0 < t →
      ((s.filter (fun i ↦ energy i < t)).card : ℝ) ≤ A * t ^ p) :
    Summable (fun i ↦ exp (-energy i)) ∧
      ∑' i, exp (-energy i) ≤ A * Gamma (1 + p) := by
  classical
  let f (i : ι) := (Ioi (energy i)).indicator (fun t : ℝ ↦ exp (-t))
  have hi i : Integrable (f i) := (integrable_indicator_iff measurableSet_Ioi).2
    (integrableOn_exp_neg_Ioi _)
  have ev i : (∫ t in Ioi (0 : ℝ), f i t) = exp (-energy i) := by
    rw [show (∫ t in Ioi (0 : ℝ), f i t) = _ from
      setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr (Ioi_subset_Ioi (he i)),
      integral_exp_neg_Ioi]
  have hΓ : 0 < 1 + p := by linarith
  have ig := Real.GammaIntegral_convergent hΓ
  have val := Real.Gamma_eq_integral hΓ
  rw [show 1 + p - 1 = p by ring] at ig val
  have finite (s : Finset ι) : ∑ i ∈ s, exp (-energy i) ≤ A * Gamma (1+p) := by
    simp_rw [← ev]
    rw [← integral_finsetSum _ (fun i _ ↦ (hi i).integrableOn), val, ← integral_const_mul]
    apply integral_mono_ae (integrable_finsetSum _ (fun i _ ↦ (hi i).integrableOn))
      (ig.const_mul A)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    have eq : ∑ i ∈ s, f i t = ((s.filter (fun i ↦ energy i < t)).card : ℝ) * exp (-t) := by
      simp [f, Set.indicator, ← Finset.sum_filter]
    rw [eq]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right (count s t ht) (exp_pos (-t)).le
  have hs := summable_of_sum_le (fun i ↦ (exp_pos (-energy i)).le) finite
  exact ⟨hs, hs.tsum_le_of_sum_le finite⟩

/-- The integration step in (3), with the packing estimate on nonzero points
expressed at radius squared `R`. The origin contributes one separately. -/
theorem gaussianPackingExcess {ι : Type*} (radiusSq : ι → ℝ) (hr : ∀ i, 0 ≤ radiusSq i)
    (d : ℕ) {u L : ℝ} (hu : 0 < u) (hL : 0 < L)
    (pack : ∀ (s : Finset ι) (R : ℝ), 0 < R →
      ((s.filter (fun i ↦ radiusSq i < R)).card : ℝ) ≤
        2 * ((d : ℝ) + 1)^2 * (2 * R / L^2) ^ ((d : ℝ)/2)) :
    ∑' i, exp (-(u * radiusSq i)) ≤
      2 * ((d : ℝ)+1)^2 * Gamma (1+(d : ℝ)/2) * (2 / (u*L^2)) ^ ((d : ℝ)/2) := by
  let p : ℝ := d/2
  let A := 2 * ((d : ℝ)+1)^2 * (2 / (u*L^2))^p
  have h := gaussianMass_of_sublevel_count (fun i ↦ u * radiusSq i)
    (fun i ↦ mul_nonneg hu.le (hr i)) (A := A) (p := p) (by dsimp [p]; positivity) (by
      intro s t ht
      have eq (i : ι) : u * radiusSq i < t ↔ radiusSq i < t/u := by
        rw [lt_div_iff₀ hu, mul_comm]
      simp_rw [eq]
      apply (pack s (t/u) (div_pos ht hu)).trans_eq
      dsimp only [A, p]
      rw [show 2 * (t/u) / L^2 = (2 / (u*L^2)) * t by ring,
        Real.mul_rpow (by positivity) ht.le]
      ring)
  exact h.2.trans_eq (by dsimp [A, p]; ring)

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.gaussianMass_of_sublevel_count
#print axioms SigabaNeo.Wall1.gaussianPackingExcess
