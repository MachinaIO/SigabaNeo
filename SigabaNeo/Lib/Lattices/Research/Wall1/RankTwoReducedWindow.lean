import SigabaNeo.Lib.Lattices.Research.Wall1.RankTwoMinimumBound

/-! The shortest-vector and hyperbolic integration steps of the planar shape window. -/
noncomputable section
open Matrix MeasureTheory SigabaNeo.Rogers
open scoped ENNReal InnerProductSpace
namespace SigabaNeo.Wall1.RankTwo

/-- The closed Gauss inequalities, with the shorter basis vector first. -/
def GaussReduced {d : ℕ} (x : Frames d) : Prop :=
  ‖x 0‖ ≤ ‖x 1‖ ∧ 2 * |⟪x 0,x 1⟫_ℝ| ≤ ‖x 0‖^2

private theorem coefficient_bound {s t : ℤ} (hn : s ≠ 0 ∨ t ≠ 0) :
    1 ≤ s^2 + t^2 - |s*t| := by
  have h : 2 * |s*t| ≤ s^2+t^2 := by
    rcases abs_cases (s*t) with ⟨he,_⟩ | ⟨he,_⟩ <;> rw [he] <;>
      nlinarith [sq_nonneg (s-t),sq_nonneg (s+t)]
  have hp : 0 < s^2 + t^2 := by
    rcases hn with hs | ht <;> positivity
  omega

/-- The first vector of a reduced basis realizes the first minimum. -/
theorem norm_first_le_of_reduced {d : ℕ} {x : Frames d} (hx : GaussReduced x) (s t : ℤ)
    (hn : s ≠ 0 ∨ t ≠ 0) : ‖x 0‖ ≤ ‖s • x 0 + t • x 1‖ := by
  let N := ‖x 0‖ ^ 2
  let M := ‖x 1‖ ^ 2
  let v := ⟪x 0,x 1⟫_ℝ
  have hNM : N ≤ M := pow_le_pow_left₀ (norm_nonneg _) hx.1 _
  have hc : (1 : ℝ) ≤ (s : ℝ)^2 + (t : ℝ)^2 - |(s : ℝ)*t| := by
    exact_mod_cast coefficient_bound hn
  have hv : -(|(s : ℝ)*t| *N) ≤ 2*(s:ℝ)*t*v := by
    calc
      _ ≤ -(|(s : ℝ)*t| *(2*|v|)) := by gcongr; exact hx.2
      _ = -|2*(s:ℝ)*t*v| := by simp [abs_mul]; ring
      _ ≤ _ := neg_abs_le _
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ, norm_add_sq_real,
    real_inner_smul_left, real_inner_smul_right, norm_smul, norm_smul,
    mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  change N ≤ (s:ℝ)^2*N + 2*((s:ℝ)*(t*v)) + (t:ℝ)^2*M
  nlinarith [mul_le_mul_of_nonneg_left hNM (sq_nonneg (t:ℝ)),
    mul_le_mul_of_nonneg_right hc (show 0 ≤ N from sq_nonneg _)]

/-- In reduced coordinates with height y = A/‖x₀‖² the window tests A ≤ a and A ≤ ℓ² y. -/
theorem planeWindow_iff_reduced {d : ℕ} {x : Frames d} (hx : GaussReduced x) (hA : 0 < area x)
    (hx₀ : 0 < ‖x 0‖) (a ℓ : ℝ) (hℓ : 0 < ℓ) :
    x ∈ planeWindow d a ℓ ↔ area x ≤ a ∧ area x ≤ ℓ^2 * (area x / ‖x 0‖^2) := by
  have he : area x ≤ ℓ^2 * (area x / ‖x 0‖^2) ↔ ‖x 0‖ ≤ ℓ := by
    rw [← mul_div_assoc,le_div_iff₀ (sq_pos_of_pos hx₀),mul_comm (ℓ^2),
      mul_le_mul_iff_right₀ hA, sq_le_sq₀ (norm_nonneg _) hℓ.le]
  rw [he]
  constructor
  · rintro ⟨ha,s,t,hpos,ht⟩
    have hn : s ≠ 0 ∨ t ≠ 0 := by
      by_contra! hz
      simp [hz.1,hz.2] at hpos
    exact ⟨ha,(norm_first_le_of_reduced hx s t hn).trans ht⟩
  · rintro ⟨ha,hl⟩
    exact ⟨ha,1,0,by simpa using hx₀,by simpa using hl⟩

/-- Integrating the hyperbolic density on the vertical fiber gives the reciprocal height. -/
theorem hyperbolic_vertical_tail {b : ℝ} (hb : 0 < b) :
    (∫⁻ y in Set.Ici b, ENNReal.ofReal ((y^2)⁻¹)) = ENNReal.ofReal b⁻¹ := by
  rw [← Measure.restrict_congr_set (Ioi_ae_eq_Ici (μ := volume) (a := b))]
  have he (y : ℝ) : (y^2)⁻¹ = y ^ (-2 : ℝ) := by
    rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg_natCast]
    norm_num
  simp_rw [he]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt (by norm_num) hb)
    (ae_restrict_mem measurableSet_Ioi |>.mono fun y hy ↦ Real.rpow_nonneg (hb.trans hy).le _),
    integral_Ioi_rpow_of_lt (by norm_num) hb]
  norm_num [Real.rpow_neg hb.le]

/-- The shape fraction is the normalized hyperbolic mass of the reduced domain cut by
the squared first-minimum test. Both the circular boundary and the cutoff are included. -/
theorem shapeFraction_eq_hyperbolic {A ℓ : ℝ} (hA : 0 < A) (hℓ : 0 < ℓ) :
    shapeFraction A ℓ = ENNReal.ofReal (3 / Real.pi) *
      ∫⁻ u in Set.Icc (-(1/2) : ℝ) (1/2),
        ∫⁻ y in {y : ℝ | 0 < y ∧ 1 ≤ u^2+y^2 ∧ A ≤ ℓ^2*y}, ENNReal.ofReal ((y^2)⁻¹) := by
  unfold shapeFraction
  congr 1
  apply setLIntegral_congr_fun measurableSet_Icc
  intro u hu
  let b := max (Real.sqrt (1-u^2)) (A/ℓ^2)
  have hb : 0 < b := lt_of_lt_of_le (div_pos hA (sq_pos_of_pos hℓ)) (le_max_right ..)
  have eqn : {y : ℝ | 0 < y ∧ 1 ≤ u^2+y^2 ∧ A ≤ ℓ^2*y} = Set.Ici b := by
    ext y
    change (_ ∧ _ ∧ _) ↔ max _ _ ≤ y
    rw [max_le_iff, div_le_iff₀ (sq_pos_of_pos hℓ), mul_comm y (ℓ^2)]
    constructor
    · rintro ⟨hy,hc,hl⟩
      exact ⟨(Real.sqrt_le_left hy.le).mpr (by linarith),hl⟩
    · rintro ⟨hc,hl⟩
      have hy : 0 < y := hb.trans_le (max_le hc ((div_le_iff₀ (sq_pos_of_pos hℓ)).mpr
        (by simpa only [mul_comm y] using hl)))
      exact ⟨hy,by linarith [(Real.sqrt_le_left hy.le).mp hc],hl⟩
  dsimp only
  rw [eqn, hyperbolic_vertical_tail hb]

end SigabaNeo.Wall1.RankTwo

#print axioms SigabaNeo.Wall1.RankTwo.norm_first_le_of_reduced
#print axioms SigabaNeo.Wall1.RankTwo.planeWindow_iff_reduced
#print axioms SigabaNeo.Wall1.RankTwo.shapeFraction_eq_hyperbolic
