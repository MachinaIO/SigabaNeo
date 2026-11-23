import SigabaNeo.Lib.Lattices.Research.Wall1.RankTwoReducedWindow

/-! Change from the three Gram-Schmidt parameters to area and upper half-plane coordinates. -/
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Wall1.RankTwo

abbrev Triple := Fin 3 → ℝ

/-- The open coordinate range, for either (length, axial coordinate, residual length)
or (area, real part, height). -/
def positiveTriples : Set Triple := {p | 0 < p 0 ∧ 0 < p 2}

def areaChart (p : Triple) : Triple := ![p 0 * p 2, p 1 / p 0, p 2 / p 0]

private def inverseChart (q : Triple) : Triple :=
  let a := Real.sqrt (q 0 / q 2)
  ![a, a * q 1, a * q 2]

private theorem inverseChart_areaChart {p : Triple} (hp : p ∈ positiveTriples) :
    inverseChart (areaChart p) = p := by
  obtain ⟨ha,ht⟩ := hp
  have h : p 0 * p 2 / (p 2 / p 0) = p 0 ^ 2 := by field_simp
  ext k
  fin_cases k <;> simp [inverseChart, areaChart, h, Real.sqrt_sq ha.le] <;> field_simp

private theorem image_areaChart : areaChart '' positiveTriples = positiveTriples := by
  ext q
  constructor
  · rintro ⟨p,⟨ha,ht⟩,rfl⟩
    exact ⟨mul_pos ha ht, div_pos ht ha⟩
  · rintro ⟨hA,hy⟩
    let a := Real.sqrt (q 0 / q 2)
    have ha : 0 < a := Real.sqrt_pos.mpr (div_pos hA hy)
    have hs : a*a = q 0/q 2 := Real.mul_self_sqrt (div_pos hA hy).le
    refine ⟨inverseChart q, ⟨ha,mul_pos ha hy⟩, ?_⟩
    ext k
    fin_cases k
    · change a*(a*q 2) = q 0
      rw [← mul_assoc,hs,div_mul_cancel₀ _ hy.ne']
    · change a*q 1 / a = q 1
      field_simp
    · change a*q 2 / a = q 2
      field_simp

private abbrev proj (k : Fin 3) : Triple →L[ℝ] ℝ := ContinuousLinearMap.proj k

private def chartDerivative (p : Triple) : Triple →L[ℝ] Triple :=
  let d := (-(p 0 ^ 2)⁻¹) • proj 0
  ContinuousLinearMap.pi ![p 0 • proj 2 + p 2 • proj 0,
    p 1 • d + (p 0)⁻¹ • proj 1, p 2 • d + (p 0)⁻¹ • proj 2]

private theorem areaChart_deriv {p : Triple} (ha : p 0 ≠ 0) :
    HasFDerivAt areaChart (chartDerivative p) p := by
  have h (k : Fin 3) := hasFDerivAt_apply (𝕜 := ℝ) k p
  have hi := (hasDerivAt_inv ha).comp_hasFDerivAt p (h 0)
  apply hasFDerivAt_pi.mpr
  intro k; fin_cases k
  · exact (h 0).mul (h 2)
  · convert! (h 1).mul hi using 1
  · convert! (h 2).mul hi using 1

private theorem chartDerivative_det {p : Triple} (ha : p 0 ≠ 0) :
    (chartDerivative p).det = 2*p 2/(p 0)^2 := by
  change LinearMap.det (chartDerivative p).toLinearMap = _
  rw [← LinearMap.det_toMatrix', Matrix.det_fin_three]
  simp [LinearMap.toMatrix'_apply, chartDerivative, proj]
  field_simp
  ring

/-- Changing variables from triangular frame coordinates yields the area density
A^(d-1) and the hyperbolic density dy du / y², with Jacobian factor two. -/
theorem areaChart_weighted_integral (d : ℕ) (hd : 2 ≤ d) (F : Triple → ℝ≥0∞) :
    (∫⁻ q in positiveTriples, ENNReal.ofReal ((q 0)^(d-1) / (q 2)^2) * F q) =
      ∫⁻ p in positiveTriples, ENNReal.ofReal (2*(p 0)^(d-1)*(p 2)^(d-2)) * F (areaChart p) := by
  have hm : MeasurableSet positiveTriples :=
    (measurableSet_lt measurable_const (measurable_pi_apply 0)).inter
      (measurableSet_lt measurable_const (measurable_pi_apply 2))
  have inj : Set.InjOn areaChart positiveTriples := fun p hp q hq e ↦
    (inverseChart_areaChart hp).symm.trans ((congrArg inverseChart e).trans (inverseChart_areaChart hq))
  conv_lhs => rw [← image_areaChart]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hm
    (fun p hp ↦ (areaChart_deriv hp.1.ne').hasFDerivWithinAt) inj]
  apply setLIntegral_congr_fun hm
  intro p hp
  obtain ⟨ha,ht⟩ := hp
  change ENNReal.ofReal |(chartDerivative p).det| *
    (ENNReal.ofReal ((p 0*p 2)^(d-1)/(p 2/p 0)^2) * _) = _
  rw [chartDerivative_det ha.ne', abs_of_pos (by positivity), ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [mul_pow, show d-1 = (d-2)+1 by omega, pow_succ (p 2)]
  field_simp

end SigabaNeo.Wall1.RankTwo

#print axioms SigabaNeo.Wall1.RankTwo.areaChart_weighted_integral
