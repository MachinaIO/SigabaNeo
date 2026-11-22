module

public import SigabaNeo.Lib.Lattices.Research.Wall1.FixedBlockChernoff
import all SigabaNeo.Lib.Lattices.Research.Wall1.FixedBlockChernoff
import Mathlib.Tactic

/-! # The projected CBD norm cap at horizontal rank 505 -/

public section
namespace SigabaNeo.Wall1.FinalBlock

/-- Rational Taylor lower bounds for two positive exponentials enclose the Chernoff formula. -/
theorem normChernoff_505_lt_with_slack : normChernoff 505 (1919/2) < 0.00047835099 := by
  have hlog : Real.log (19/15) ≤ 0.236388779 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).2
    apply le_trans _ (Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 0.236388779) 9)
    norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  have small : (2.6003493 : ℝ) ≤ Real.exp (7.6451666/8) := by
    apply le_trans _ (Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 7.6451666/8) 12)
    norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.6003493) small 8
  rw [← Real.exp_nat_mul] at hh
  norm_num at hh
  unfold normChernoff
  norm_num
  apply lt_of_le_of_lt (Real.exp_le_exp.mpr (show _ ≤ -(7.6451666 : ℝ) by linarith))
  rw [Real.exp_neg, inv_eq_one_div, div_lt_iff₀ (Real.exp_pos _)]
  norm_num
  linarith

theorem normChernoff_505_lt : normChernoff 505 (1919/2) < 0.000478351 :=
  normChernoff_505_lt_with_slack.trans (by norm_num)

/-- The probability of exceeding the cap, for any ambient dimension and rank-505 block. -/
theorem capTail_505_lt {N : ℕ} (B : FinalBlock N 505) : B.capTail (1919/2) < 0.000478351 :=
  (B.capTail_le_normChernoff (by decide) (by norm_num)).trans_lt normChernoff_505_lt

end SigabaNeo.Wall1.FinalBlock

#print axioms SigabaNeo.Wall1.FinalBlock.normChernoff_505_lt
#print axioms SigabaNeo.Wall1.FinalBlock.capTail_505_lt
