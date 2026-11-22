import SigabaNeo.Lib.Lattices.Research.Wall1.CBDTail
import SigabaNeo.Lib.Lattices.Research.Wall1.MarkedIntegerSection
import CslibFrontier.Foundations.Probability.Gaussian.Poisson
import Mathlib.Tactic

/-! # Fourier weights for a projected CBD plant -/

noncomputable section
namespace SigabaNeo.Wall1

open CBDTail SampleDeletion ProbabilityTheory ZLattice Complex
open scoped RealInnerProductSpace

private theorem digit_cexp (s : ℂ) :
    ∑ j : Digit 3, (weight j : ℂ) * Complex.exp (s * (centered j : ℂ)) =
      Complex.cosh (s / 2) ^ 6 := by
  have term (j : Digit 3) : Complex.exp (s * (centered j : ℂ)) =
      Complex.exp s ^ j.val * Complex.exp (-(3 * s)) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    simp [centered]
    ring
  have hc : Complex.cosh (s / 2) = (Complex.exp s + 1) * Complex.exp (-(s / 2)) / 2 := by
    rw [Complex.cosh, add_mul, ← Complex.exp_add, one_mul, show s + -(s / 2) = s / 2 by ring]
  simp_rw [term]
  rw [hc, div_pow, mul_pow, ← Complex.exp_nat_mul,
    show ((6 : ℕ) : ℂ) * -(s / 2) = -(3 * s) by push_cast; ring]
  change (∑ j : Fin 7, _) = _
  norm_num [Fin.sum_univ_succ, weight, mass, Nat.choose]
  ring

/-- The lattice Fourier convention uses the phase exp(2πi x). -/
theorem cbd_fourierChar {N : ℕ} (a : Fin N → ℝ) :
    ∑ x, (jointWeight x : ℂ) * (Real.fourierChar (projection a x) : ℂ) =
      ∏ i, (Real.cos (Real.pi * a i) : ℂ) ^ 6 := by
  let s (i : Fin N) : ℂ := ((2 * Real.pi * a i : ℝ) : ℂ) * I
  have eq x : (Real.fourierChar (projection a x) : ℂ) =
      ∏ i, Complex.exp (s i * (centered (x i) : ℂ)) := by
    rw [Real.fourierChar_apply, ← Complex.exp_sum]
    congr 1
    simp [projection, s, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hc i : Complex.cosh (s i / 2) = (Real.cos (Real.pi * a i) : ℂ) := by
    rw [show s i / 2 = ((Real.pi * a i : ℝ) : ℂ) * I by dsimp [s]; push_cast; ring,
      Complex.cosh_mul_I, Complex.ofReal_cos]
  simp_rw [eq, jointWeight, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (j : Digit 3) ↦ (weight j : ℂ) *
    Complex.exp (s i * (centered j : ℂ)))]
  simp_rw [digit_cexp, hc]

variable {N : ℕ}
abbrev PlantSpace (N : ℕ) := EuclideanSpace ℝ (Fin N)
def cbdVector (x : Fin N → Digit 3) : PlantSpace N :=
  WithLp.toLp 2 (fun i ↦ (centered (x i) : ℝ))

/-- Averaging the shifted Gaussian over the original plant produces a real, nonnegative
Fourier series. The center has the minus sign needed for the translate H + kPX. -/
theorem projectedCBD_gaussian_poisson (S : Submodule ℝ (PlantSpace N)) (H : Submodule ℤ S)
    [DiscreteTopology H] [IsZLattice ℝ H] {s : ℝ} (hs : 0 < s) (k : ℝ) :
    (∑ x, jointWeight x * gaussianMass H s (-(k • S.orthogonalProjectionOnto (cbdVector x)))) =
      s ^ Module.finrank ℝ S / covolume H * ∑' w : metricDual H,
        gaussianWeight (1/s) (w : S) * ∏ i, Real.cos (Real.pi * (k * w.val.val i)) ^ 6 := by
  let P (x : Fin N → Digit 3) := S.orthogonalProjectionOnto (cbdVector x)
  let G (w : metricDual H) := gaussianWeight (1/s) (w : S)
  let phase (x : Fin N → Digit 3) (w : metricDual H) : ℂ :=
    (Real.fourierChar (projection (fun i ↦ k * w.val.val i) x) : ℂ)
  have arg x (w : metricDual H) : -⟪-(k • P x), w.val⟫ =
      projection (fun i ↦ k * w.val.val i) x := by
    rw [inner_neg_left, neg_neg, real_inner_smul_left, real_inner_comm,
      S.inner_orthogonalProjectionOnto_eq_of_mem_left]
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, cbdVector, projection,
      Finset.mul_sum, mul_left_comm, mul_comm]
  let : DiscreteTopology (metricDual H) := discreteTopology_dualSubmodule H
  have sg : Summable G := by
    simpa [G] using summable_gaussianWeight (metricDual H) (1/s) (by positivity) 0
  have sp x : Summable (fun w ↦ (G w : ℂ) * phase x w) := by
    apply Summable.of_norm
    simpa [norm_mul, phase, abs_of_nonneg (gaussianWeight_pos _ _).le, G] using sg
  let A := s ^ Module.finrank ℝ S / covolume H
  have poisson x : (gaussianMass H s (-(k • P x)) : ℂ) =
      (A : ℂ) * ∑' w, (G w : ℂ) * phase x w := by
    rw [gaussianMass_eq_tsum_dual H s hs]
    simp only [A, Complex.ofReal_div, Complex.ofReal_pow, arg, G, phase]
  apply Complex.ofReal_injective
  change ((∑ x, jointWeight x * gaussianMass H s (-(k • P x)) : ℝ) : ℂ) =
    ((A * ∑' w : metricDual H, G w * ∏ i, Real.cos (Real.pi * (k * w.val.val i)) ^ 6 : ℝ) : ℂ)
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, poisson, Complex.ofReal_tsum,
    Complex.ofReal_prod, Complex.ofReal_pow, mul_left_comm (jointWeight _ : ℂ) (A : ℂ),
    ← Finset.mul_sum]
  congr 1
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun x _ ↦ (sp x).mul_left (jointWeight x : ℂ))]
  apply tsum_congr
  intro w
  simp_rw [mul_left_comm (jointWeight _ : ℂ) (G w : ℂ), ← Finset.mul_sum]
  simp only [phase, cbd_fourierChar]

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.cbd_fourierChar
#print axioms SigabaNeo.Wall1.projectedCBD_gaussian_poisson
