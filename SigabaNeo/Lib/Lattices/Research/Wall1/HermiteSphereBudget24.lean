import SigabaNeo.Lib.Lattices.Research.Wall1.TerminalScale506

/-! Scalar conversion of the rank-24 spherical polynomial search winner.
The search and the signed-lens exclusions are in wall1_sphere24.py. -/
noncomputable section
namespace SigabaNeo.Wall1.HermiteSphereBudget24
open Real TerminalProjection.TerminalInterval

def threshold : ℚ := 1245798 / 10000000

/-- At degree three, q = q₀ + q₁ x and B = q₀+q₁. -/
def ratio : ℚ := 24*(1-threshold)*(25*threshold+2)/(1-24*threshold^2)

/-- The axial cutoff admits a log-volume gain of 412/1000 nats at this threshold. -/
def radiusSq : ℝ := exp (103/3000) / (2*(1-(threshold:ℝ)))

/-- The selected certificate's Hermite coefficient, equivalently the positive g
satisfying (π U g)^12 = 12! B, lies in an interval of width 2·10⁻⁸. -/
theorem coefficient_enclosure {g : ℝ} (hg : 0 ≤ g)
    (conversion : (π*radiusSq*g)^12 = Nat.factorial 12 * (ratio:ℝ)) :
    4.37200933 < g ∧ g < 4.37200935 := by
  let l : ℚ := 1.03492952574700338
  let u : ℚ := 1.03492952574700339
  have lo := exp_lower (103/3000) l (by decide +kernel) (by decide +kernel)
  have hi := exp_upper (103/3000) u (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have den : (0:ℝ) < 2*(1-(threshold:ℝ)) := by norm_num [threshold]
  have hl : (l:ℝ)/(2*(1-(threshold:ℝ))) ≤ radiusSq :=
    div_le_div_of_nonneg_right (by simpa [radiusSq] using lo) den.le
  have hu : radiusSq ≤ (u:ℝ)/(2*(1-(threshold:ℝ))) :=
    div_le_div_of_nonneg_right (by simpa [radiusSq] using hi) den.le
  have hR : 0 ≤ radiusSq := div_nonneg (exp_pos _).le den.le
  constructor
  · by_contra! hh
    have h := pow_le_pow_left₀ (mul_nonneg (mul_nonneg pi_pos.le hR) hg)
      (mul_le_mul (mul_le_mul pi_lt_d20.le hu hR (by norm_num)) hh hg (by positivity [hR.trans hu])) 12
    rw [conversion] at h
    norm_num [u,ratio,threshold] at h
  · by_contra! hh
    have hlow : 0 ≤ (l:ℝ)/(2*(1-(threshold:ℝ))) := by norm_num [l,threshold]
    have h := pow_le_pow_left₀
      (by positivity [hlow] :
        0 ≤ 3.14159265358979323846*((l:ℝ)/(2*(1-(threshold:ℝ))))*4.37200935)
      (mul_le_mul (mul_le_mul pi_gt_d20.le hl hlow pi_pos.le) hh (by norm_num) (mul_nonneg pi_pos.le hR)) 12
    rw [conversion] at h
    norm_num [l,ratio,threshold] at h

end SigabaNeo.Wall1.HermiteSphereBudget24

#print axioms SigabaNeo.Wall1.HermiteSphereBudget24.coefficient_enclosure
