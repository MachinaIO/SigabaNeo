module

public import SigabaNeo.Lib.Lattices.Attacks.Primal.SampleDeletionPacked
import all SigabaNeo.Lib.Lattices.Attacks.Primal.SampleDeletionPacked
import Mathlib.Tactic

/-! Exact Part 236 arithmetic. The coefficients use the original CBD weights with
denominator 64 per coordinate. The conditional probabilities keep their full precision. -/

public section
namespace SigabaNeo.Wall1.Width638
open SigabaNeo.SampleDeletion Polynomial Finset

set_option maxRecDepth 16000
set_option exponentiation.threshold 12000000

@[expose] def H : ℕ := 3329^127
@[expose] def D : ℕ := H * 64^127
@[expose] def gap (j : ℕ) := H - (ballCount 638 j - 1)
@[expose] def credit (t : ℕ) :=
  ∑ j ∈ range (955-t), shell 3 127 j * gap (t+j)

/-- Degree 954-t of the reversed gap polynomial times the CBD error polynomial
is the (unnormalized) group success credit conditional on secret energy t. -/
private noncomputable def gaps : ℕ[X] :=
  ∑ k ∈ range 955, C (gap k) * X^(954-k)

@[expose] def fastDigit (w k : ℕ) := (w >>> (4608*k)) % base

private theorem fastDigit_eq (w k : ℕ) : fastDigit w k = w / base^k % base := by
  simp [fastDigit, base, Nat.shiftRight_eq_div_pow, pow_mul]

@[expose] def gapWord (balls : ℕ) := sumTo
  (fun k ↦ (H - (fastDigit balls k - 1)) * base^(954-k)) 955

@[expose] def productWord := gapWord (packedBall 638) * packedCBD 127

@[expose] def contribution (a g : ℕ) := a * (D^4 - (D-g)^4)

@[expose] def wordSum (secrets product : ℕ) := sumTo (fun t ↦
  contribution (fastDigit secrets t) (fastDigit product (954-t))) 955

@[expose] def gain := wordSum (packedCBD 511) productWord
@[expose] def denominator : ℕ := 64^511 * D^4

attribute [local irreducible] shell ballCount base H D packedBall packedCBD
  gap gapWord productWord gain denominator

private theorem eval_gaps : gaps.eval base = gapWord (packedBall 638) := by
  unfold gaps gapWord
  rw [sumTo_eq, eval_finsetSum]
  apply sum_congr rfl
  intro k hk
  rw [fastDigit_eq, ball_digit (by decide) (by have := mem_range.mp hk; omega)]
  simp [gap]

private theorem credit_coeff {t : ℕ} (ht : t ≤ 954) :
    (cbd 3 ^ 127 * gaps).coeff (954-t) = credit t := by
  unfold gaps
  rw [Finset.mul_sum, finsetSum_coeff, ← sum_range_add_sum_Ico _ (show t ≤ 955 by omega)]
  have term (k : ℕ) : (cbd 3 ^ 127 * (C (gap k) * X^(954-k))).coeff (954-t) =
      (if 954-k ≤ 954-t then shell 3 127 (954-t-(954-k)) * gap k else 0) := by
    rw [← mul_assoc, coeff_mul_X_pow']
    split <;> simp [cbd_coeff]
  simp_rw [term]
  rw [sum_eq_zero (s := range t) (fun k hk ↦ ite_eq_right (by have := mem_range.mp hk; omega)),
    zero_add, sum_Ico_eq_sum_range]
  unfold credit
  apply sum_congr rfl
  intro j hj
  have := mem_range.mp hj
  rw [ite_eq_left (by omega), show 954-t-(954-(t+j)) = j by omega]

theorem conditional_digit {t : ℕ} (ht : t ≤ 954) :
    productWord / base^(954-t) % base = credit t := by
  rw [← credit_coeff ht]
  apply packed_coeff _ _ _ 2001 (by omega)
  · rw [eval_mul, eval_pow, eval_cbd, show cbdWord 1 = 64 by decide]
    have le : gaps.eval 1 ≤ 955*H := by
      simp only [gaps, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one, gap]
      calc
        _ ≤ ∑ _k ∈ range 955, H := sum_le_sum fun k _ ↦ Nat.sub_le H (ballCount 638 k - 1)
        _ = _ := by simp
    exact (Nat.mul_le_mul_left _ le).trans_lt (by unfold H base; decide +kernel)
  · rw [eval_mul, eval_pow, eval_cbd, eval_gaps, mul_comm]
    unfold productWord packedCBD
    rw [Nat.powMod_def]
    exact (Nat.mod_modEq _ _).mul_left _

theorem gain_eq :
    gain = ∑ t ∈ range 955, shell 3 511 t * (D^4 - (D - credit t)^4) := by
  unfold gain wordSum
  rw [sumTo_eq]
  apply sum_congr rfl
  intro t ht
  have ht' := mem_range.mp ht
  simp only [fastDigit_eq]
  rw [cbd_digit (by decide) (by omega), conditional_digit (by omega)]
  rfl

end SigabaNeo.Wall1.Width638

#print axioms SigabaNeo.Wall1.Width638.gain_eq
