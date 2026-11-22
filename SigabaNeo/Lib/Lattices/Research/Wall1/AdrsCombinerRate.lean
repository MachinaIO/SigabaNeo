module

public import SigabaNeo.Lib.Lattices.Research.Wall1.AdrsSelected
public import SigabaNeo.Lib.Lattices.Research.Wall1.AdrsGaussianBins
import Mathlib.Tactic

/-! # Gaussian mass formula for the Poisson combiner's output intensity -/

@[expose] public section

noncomputable section

namespace SigabaNeo.Wall1.ADRS

open ProbabilityTheory MeasureTheory ZLattice
open scoped ENNReal NNReal

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
variable (L : Submodule ℤ E) (b : Module.Basis ι ℤ L) {r : ℕ} (e : (ι → ZMod 2) ≃ Fin r)
variable [FiniteDimensional ℝ E] [DiscreteTopology L] {s : ℝ} (hs : 0 < s)

theorem gaussianLabels_mass (c : ι → ZMod 2) :
    (gaussianLabels L b e hs (e c)).toReal =
      (∑' x : ParityFiber L b c, gaussianWeight s (x.val : E)) / gaussianMass L s 0 := by
  have h : gaussianLabels L b e hs =
      ((discreteGaussian L s hs 0).map (coefficientMod L b 2)).map e := by
    rw [PMF.map_comp]; rfl
  rw [h, Cslib.Probability.PMF.map_equiv_apply, e.symm_apply_apply]
  exact parityLabel_mass L b hs c

theorem gaussianLabels_collision :
    (collisionMass (gaussianLabels L b e hs)).toReal =
      (gaussianMass L (s/√2) 0 / gaussianMass L s 0)^2 := by
  classical
  rw [collisionMass, ENNReal.toReal_sum (fun c _ ↦ ENNReal.pow_ne_top (PMF.apply_ne_top _ _)),
    ← e.sum_comp]
  simp only [ENNReal.toReal_pow, gaussianLabels_mass]
  exact sum_sq_parityProbability L b hs

/-- I1 and the central-bin identity give the stated mass-ratio formula for Λ'. -/
theorem nextRate_gaussian (rate θ : ℝ≥0) (hr : 0 < rate) :
    (nextRate rate (gaussianLabels L b e hs) θ
      (rate * (gaussianLabels L b e hs (e 0)).toNNReal) : ℝ) =
      θ * rate * (gaussianMass L (s/√2) 0)^2 /
        (gaussianMass L s 0 * gaussianMass L (s/2) 0) := by
  simp only [nextRate, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_pow,
    ENNReal.coe_toNNReal_eq_toReal, gaussianLabels_collision, gaussianLabels_mass,
    zero_parityProbability L b hs]
  have h₀ := (gaussianMass_pos L s hs 0).ne'
  have h₂ := (gaussianMass_pos L (s/2) (by positivity) 0).ne'
  have hr' : (rate : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp [h₀,h₂,hr']

/-- I3 verifies the count-coupling upper envelope when A is the central bin intensity. -/
theorem le_central_bin_intensity [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L]
    (rate : ℝ≥0) (c : Fin r) :
    rate * (gaussianLabels L b e hs c).toNNReal ≤
      rate * (gaussianLabels L b e hs (e 0)).toNNReal := by
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply NNReal.coe_le_coe.mp
  obtain ⟨d,rfl⟩ := e.surjective c
  simp only [ENNReal.coe_toNNReal_eq_toReal, gaussianLabels_mass, zero_parityProbability L b hs]
  exact parityProbability_le L b hs d

end SigabaNeo.Wall1.ADRS

#print axioms SigabaNeo.Wall1.ADRS.nextRate_gaussian
#print axioms SigabaNeo.Wall1.ADRS.le_central_bin_intensity
