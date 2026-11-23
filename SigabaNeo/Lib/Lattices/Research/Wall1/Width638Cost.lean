module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Static accounting for Part 238. All counts refer to the specified 768-bit word model. -/

@[expose] public section
namespace SigabaNeo.Wall1.CVP638

def initialMean : ℕ := 2^753
def sampleCount : ℕ := 2^754
def levels : ℕ := 36
def sampleWork : ℕ := 8192*638 + 32*127*511 + 64*638 + 512
def callWork : ℕ := 2^42 + sampleCount*sampleWork + 2*sampleCount*(64*638+128) +
  levels*(8*2^638+128) + 2^21
def totalWork : ℕ := 4*callWork + 2^24
def spaceWords : ℕ := 4*(638+10)*sampleCount + 2^640 + 2^30

theorem word_charges :
    sampleWork = 7344544 ∧ 23*(16*15+32)+16*15+64 ≤ 8192 ∧
    511*3328*(2^22-1)+3328 < 2^43 ∧ 638*(2^22-1)^2 < 2^54 ∧
    spaceWords < 2^766 ∧ 2^766 < (2:ℕ)^768 := by decide +kernel

/-- Clearing the denominator 40 in .825 gives small exact integer certificates. -/
theorem work_powers : callWork^40 < 2^31073 ∧ totalWork^40 < 2^31153 := by decide +kernel

private theorem from_power {w k : ℕ} (h : w^40 < 2^k) :
    (w : ℝ) < (2:ℝ)^((k:ℝ)/40) := by
  rw [div_eq_mul_inv, Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  apply (Real.lt_rpow_inv_iff_of_pos (by positivity) (by positivity) (by norm_num)).2
  change (w:ℝ)^((40:ℕ):ℝ) < (2:ℝ)^(k:ℝ)
  rw [Real.rpow_natCast, Real.rpow_natCast]
  exact_mod_cast h

theorem word_work :
    (callWork:ℝ) < (2:ℝ)^(776.825:ℝ) ∧ (totalWork:ℝ) < (2:ℝ)^(778.825:ℝ) := by
  constructor
  · convert from_power work_powers.1 using 2
    norm_num
  · convert from_power work_powers.2 using 2
    norm_num

/-- The audited scale squared after j variance halvings. -/
noncomputable def variance (j : ℕ) : ℝ := 647*3329^2*Real.log 1298 / Real.pi / 2^j

theorem inverse_temperature : 16 < Real.pi / variance levels / Real.log 2 := by
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h₁ : 0 < Real.log 1298 := Real.log_pos (by norm_num)
  have hlog : Real.log 1298 ≤ 11 * Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 1298) (by norm_num : (1298:ℝ) ≤ 2^11)
    simpa using h
  have h₂' : Real.log 2 ≤ 0.7 := by linarith [Real.log_two_lt_d9]
  have hprod := mul_le_mul (show Real.log 1298 ≤ 7.7 by linarith) h₂' h₂.le (by norm_num)
  unfold variance levels
  rw [lt_div_iff₀ h₂, lt_div_iff₀ (by positivity)]
  field_simp
  nlinarith [Real.pi_gt_d2, sq_nonneg (Real.pi-3.14)]

theorem terminal_factor : Real.exp (1276/65535) < 16/15 := by
  exact (Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)).trans_lt
    (by norm_num)

theorem poisson_miss : Real.exp (-120) < 1 / (2:ℝ)^172 := by
  rw [one_div, ← Real.exp_log (by positivity : (0:ℝ) < 2^172), ← Real.exp_neg,
    Real.exp_lt_exp, Real.log_pow]
  norm_num
  linarith [Real.log_two_lt_d9]

theorem population : initialMean / (2^638 * 8^35) = 1024 ∧
    initialMean / (2^638 * 8^levels) = 128 ∧ 128*(15:ℚ)/16 = 120 := by decide +kernel

def mismatch : ℚ := 36 * (2:ℚ)^753 * 8 * ((1/4)^1999 + (3/4)^3999)

theorem mismatch_lt : mismatch < 1/(2:ℚ)^830 := by decide +kernel
theorem overflow_lt : (3/4:ℚ)^2000 < 1/(2:ℚ)^800 := by decide +kernel

/-- Precision and probability charges for the 511 tail and 127 head coordinates. -/
theorem sampler_budget :
    15*64 = (960:ℕ) ∧ 1024+64 = (1088:ℕ) ∧
    1/(2:ℚ)^6683 + 511/(2:ℚ)^932 + 127/(2:ℚ)^948 < 1/(2:ℚ)^923 := by decide +kernel

theorem failure_budget :
    1/(2:ℚ)^830 + 1/(2:ℚ)^800 + 1/(2:ℚ)^172 + (2:ℚ)^754/(2:ℚ)^923 <
    1/(2:ℚ)^168 := by decide +kernel

/-- Rounding margin of the published twelve-place geometric probability bound. -/
theorem four_loss_margin :
    (6431620941/10^10:ℚ) < 643162094166/10^12 - 4/(2:ℚ)^168 := by decide +kernel

end SigabaNeo.Wall1.CVP638

#print axioms SigabaNeo.Wall1.CVP638.word_charges
#print axioms SigabaNeo.Wall1.CVP638.word_work
#print axioms SigabaNeo.Wall1.CVP638.inverse_temperature
#print axioms SigabaNeo.Wall1.CVP638.terminal_factor
#print axioms SigabaNeo.Wall1.CVP638.poisson_miss
#print axioms SigabaNeo.Wall1.CVP638.population
#print axioms SigabaNeo.Wall1.CVP638.mismatch_lt
#print axioms SigabaNeo.Wall1.CVP638.overflow_lt
#print axioms SigabaNeo.Wall1.CVP638.sampler_budget
#print axioms SigabaNeo.Wall1.CVP638.failure_budget
#print axioms SigabaNeo.Wall1.CVP638.four_loss_margin
