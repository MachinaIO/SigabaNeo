module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Gaussian prefactors at the audited width-506 model determinant -/

public section
noncomputable section
namespace SigabaNeo.Wall1.Model506
open Real

def t : ℝ := 505/1921
def width : ℝ := √(π/t)

/-- Logarithm of the geometric mean of the last 505 full-row GSA lengths.
The expression uses log(506/(2πe)) = log(506/(2π)) - 1. -/
def logG : ℝ := 511/1023 * log 3329 -
  518/1010 * (log (506/(2*π)) - 1 + log (π*506)/506)

/-- Covolume in the retained span. -/
def determinant : ℝ := exp (505*logG)

/-- Agreement with the note's expression G₀^505 in terms of the full-row GSA slope. -/
theorem determinant_eq_gsa :
    determinant = ((3329:ℝ)^(511/1023:ℝ) *
      exp ((505-1023:ℝ) * ((log (506/(2*π*exp 1)) + log (π*506)/506) /
        (2*(506-1)))))^505 := by
  rw [show (506:ℝ)/(2*π*exp 1) = (506/(2*π))/exp 1 by ring,
    log_div (by positivity) (exp_pos _).ne', log_exp, rpow_def_of_pos (by norm_num),
    ← exp_add, ← exp_nat_mul]
  unfold determinant logG
  congr 1; push_cast; ring

private theorem exp_lower_cert (x m : ℝ) (n : ℕ) (hx : 0 ≤ x) (hm : 0 ≤ m)
    (cert : m ≤ ∑ j ∈ Finset.range 15, x^j / j.factorial) :
    m^n ≤ exp (n*x) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ hm (cert.trans (sum_le_exp_of_nonneg hx _)) _

private theorem exp_upper_cert (x m : ℝ) (n : ℕ) (hx : 0 ≤ x) (hx' : x ≤ 1)
    (cert : (∑ j ∈ Finset.range 15, x^j / j.factorial) +
      x^15 * (15+1)/(Nat.factorial 15 * 15) ≤ m) : exp (n*x) ≤ m^n := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le ((Real.exp_bound' hx hx' (by decide : 0 < 15)).trans cert) _

private theorem commonLog : t*960.5 + 505/2 * log (π/t) - 505*logG ≤ -285.5500737 := by
  have a : 8.1104272375 ≤ log 3329 := by
    apply (le_log_iff_exp_le (by norm_num)).2
    have h := exp_upper_cert (8.1104272375/16) 1.660139611830 16 (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial_succ])
    norm_num at h ⊢
    linarith
  have b : log (506/(2*π)) ≤ 4.3886596030 := by
    apply (log_le_iff_le_exp (by positivity)).2
    have h := exp_lower_cert (4.3886596030/8) 1.730797786318 8 (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial_succ])
    norm_num at h ⊢
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [mul_nonneg (sub_nonneg.mpr h) Real.pi_pos.le, Real.pi_gt_d20]
  have c : log (π*506) ≤ 7.3712665553 := by
    apply (log_le_iff_le_exp (by positivity)).2
    have h := exp_lower_cert (7.3712665553/16) 1.585189818882 16 (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial_succ])
    norm_num at h ⊢
    linarith [Real.pi_lt_d20]
  have d : log (π/t) ≤ 2.4807726195 := by
    unfold t
    apply (log_le_iff_le_exp (by positivity)).2
    have h := exp_lower_cert (2.4807726195/4) 1.859287137538 4 (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial_succ])
    norm_num at h ⊢
    linarith [Real.pi_lt_d20]
  unfold logG t at *
  linarith

set_option exponentiation.threshold 1024 in
private theorem commonWeight :
    exp (t*960.5 + 505/2 * log (π/t) - 505*logG) ≤ 9.709094e-125 := by
  apply (exp_le_exp.mpr commonLog).trans
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (exp_pos _)]
  have h := exp_lower_cert (285.5500737/512) 1.74667675898 512 (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial_succ])
  norm_num at h ⊢
  linarith

private theorem heightPolynomial :
    ∑ k ∈ Finset.Icc (2:ℕ) 30, exp (-t*(k:ℝ)^2) ≤ 0.4596432 := by
  have hbase : exp (-t) ≤ 0.768831143 := by
    rw [exp_neg, inv_eq_one_div, div_le_iff₀ (exp_pos _)]
    have h := sum_le_exp_of_nonneg (by norm_num [t] : 0 ≤ t) 12
    norm_num [Finset.sum_range_succ, Nat.factorial_succ, t] at h ⊢
    linarith
  have hp : (∑ k ∈ Finset.Icc (2:ℕ) 30, (0.768831143:ℚ)^min (k^2) 100) ≤ 0.4596432 := by
    decide +kernel
  have cast := (Rat.cast_le (K := ℝ)).2 hp
  push_cast at cast
  apply le_trans _ cast
  apply Finset.sum_le_sum
  intro k _
  have e : exp (-t*(k:ℝ)^2) = exp (-t)^(k^2) := by
    rw [← exp_nat_mul]; push_cast; ring_nf
  rw [e]
  exact (pow_le_pow_left₀ (exp_pos _).le hbase _).trans
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (min_le_left _ _))

/-- Sum of all 29 zero-mode prefactors. -/
theorem sum_prefactors_lt :
    ∑ k ∈ Finset.Icc (2:ℕ) 30, exp (t*(960.5-(k:ℝ)^2)) * width^505 / determinant < 4.46272e-125 := by
  have hw : width^505 = exp (505/2 * log (π/t)) := by
    have pos : 0 < π/t := by unfold t; positivity
    rw [← exp_log (show 0 < width by exact Real.sqrt_pos.mpr pos), ← exp_nat_mul]
    unfold width
    rw [Real.log_sqrt pos.le]
    congr 1; push_cast; ring
  have each (k : ℕ) : exp (t*(960.5-(k:ℝ)^2)) * width^505 / determinant =
      exp (t*960.5 + 505/2 * log (π/t) - 505*logG) * exp (-t*(k:ℝ)^2) := by
    rw [hw, determinant, ← exp_add, ← exp_sub, ← exp_add]; congr 1; ring
  simp_rw [each, ← Finset.mul_sum]
  have bound := mul_le_mul commonWeight heightPolynomial
    (Finset.sum_nonneg fun _ _ ↦ (exp_pos _).le) (by norm_num)
  exact bound.trans_lt (by norm_num)

end SigabaNeo.Wall1.Model506
#print axioms SigabaNeo.Wall1.Model506.sum_prefactors_lt
#print axioms SigabaNeo.Wall1.Model506.determinant_eq_gsa
