import SigabaNeo.Lib.Lattices.Gaussian.Smooth

/-! Real inequalities used by the tails and smoothing bounds. -/

namespace SigabaNeo.Lattices

open SigabaNeo.Lattices
open scoped ENNReal

/-! ### Real inequalities -/

theorem ratio_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1 / 4) : (1 + r) / (1 - r) ≤ 1 + 3 * r := by
  rw [div_le_iff₀ (by linarith)]; nlinarith

theorem one_add_pow_le {x : ℝ} (h0 : 0 ≤ x) (m : ℕ) (h1 : x * m ≤ 1 / 2) :
    (1 + x) ^ m ≤ 1 + 2 * (x * m) := by
  have hp : (1 + x) ^ m ≤ Real.exp (x * m) := by
    rw [show x * (m : ℝ) = m * x by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) m
  have hm : 0 ≤ x * m := by positivity
  have he := Real.exp_bound_div_one_sub_of_interval hm (by linarith)
  have : 1 / (1 - x * m) ≤ 1 + 2 * (x * m) := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

theorem one_sub_exp_neg_ge {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) : c / 2 ≤ 1 - Real.exp (-c) := by
  have he := Real.add_one_le_exp c
  have hpos := Real.exp_pos c
  have hinv : Real.exp (-c) * Real.exp c = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-c)]

theorem exp_quarter_le_sqrt_pi : Real.exp (1 / 4) ≤ Real.sqrt Real.pi := by
  have h2 : Real.exp (1 / 2) ≤ 2 := by
    have := Real.exp_bound_div_one_sub_of_interval (x := 1 / 2) (by norm_num) (by norm_num)
    norm_num at this ⊢; linarith
  have hsq : Real.exp (1 / 4) ^ 2 = Real.exp (1 / 2) := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [← Real.sqrt_sq (Real.exp_pos (1 / 4)).le, hsq]
  exact Real.sqrt_le_sqrt (by linarith [Real.two_le_pi])

/-! ### `ℝ≥0∞` conversions -/

theorem geom_eq {R : ℝ} (h0 : 0 ≤ R) (h1 : R < 1) :
    (1 + ENNReal.ofReal R) * (1 - ENNReal.ofReal R)⁻¹ = ENNReal.ofReal ((1 + R) / (1 - R)) := by
  rw [div_eq_mul_inv, ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_inv_of_pos (by linarith),
    ENNReal.ofReal_sub _ h0, ENNReal.ofReal_add zero_le_one h0, ENNReal.ofReal_one]

theorem ennreal_256 : (256 : ℝ≥0∞) * ENNReal.ofReal (1 / 256) = 1 := by
  rw [show (256 : ℝ≥0∞) = ENNReal.ofReal 256 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

end SigabaNeo.Lattices
