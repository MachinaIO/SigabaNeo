module

public import SigabaNeo.Lib.Lattices.Research.Wall1.GaussianConstantArgument
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

/-! # Executable constants for the eight recorded Gaussian tables -/

@[expose] public section

namespace SigabaNeo.Wall1.CDT
namespace FixedConstants

open Real Finset

/-- Magnitude of term `k` and signed Taylor sum through that term. Multiplication and
division are separately truncated, as in §3.3, K6. -/
def taylor (x : ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, 1)
  | k+1 =>
    let (p, s) := taylor x k
    let t := trunc 1088 (trunc 1088 (p*x) / (k+1:ℚ))
    (t, s + (-1)^(k+1) * t)

/-- The stored F-format value of the 36-term approximation. -/
def expApprox (x : ℚ) : ℚ := min 1 (trunc 1024 (taylor x 35).2)

private theorem taylor_error {x : ℚ} (hx₀ : 0 ≤ (x:ℝ)) (hx : (x:ℝ) ≤ 1/2^31) (n : ℕ) :
    |((taylor x n).1 : ℝ) - (x:ℝ)^n/n.factorial| ≤ 2.1 * ulp 1088 ∧
    |((taylor x n).2 : ℝ) - ∑ k ∈ range (n+1), (-1:ℝ)^k * ((x:ℝ)^k/k.factorial)| ≤
      n * (2.1 * ulp 1088) := by
  have hu := (ulp_pos 1088).le
  induction n with
  | zero => simp [taylor]; positivity
  | succ k ih =>
    obtain ⟨hp, hsum⟩ := ih
    let p := (taylor x k).1
    let m := trunc 1088 (p*x)
    have hm : |(m:ℝ)-(p:ℝ)*(x:ℝ)| ≤ ulp 1088 := by
      simpa only [m, Rat.cast_mul] using trunc_error 1088 (p*x)
    have hstep : |(p:ℝ)*(x:ℝ) - ((x:ℝ)^k/k.factorial)*(x:ℝ)| ≤ 0.1 * ulp 1088 := by
      rw [← sub_mul, abs_mul, abs_of_nonneg hx₀]
      exact (mul_le_mul hp hx hx₀ (by positivity)).trans (by linarith only [hu])
    have hd : 1 ≤ (k+1:ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hnext : |(m:ℝ)/(k+1:ℝ) - (x:ℝ)^(k+1)/(k+1).factorial| ≤ 1.1 * ulp 1088 := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ,
        show (x:ℝ)^k*x / ((k+1:ℝ)*k.factorial) =
          ((x:ℝ)^k/k.factorial*x)/(k+1:ℝ) by simp only [div_eq_mul_inv, mul_inv_rev]; ring, ← sub_div, abs_div,
        abs_of_pos (by positivity : 0 < (k+1:ℝ)), div_le_iff₀ (by positivity)]
      calc _ ≤ 1.1 * ulp 1088 := by linarith only [via hm hstep]
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hd
    have ht := trunc_error 1088 (m/(k+1:ℚ))
    push_cast at ht
    have he : |(trunc 1088 (m/(k+1:ℚ)) : ℝ) - (x:ℝ)^(k+1)/(k+1).factorial| ≤
        2.1 * ulp 1088 := by linarith only [via ht hnext]
    refine ⟨he, ?_⟩
    simp only [taylor, Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg, Rat.cast_one,
      sum_range_succ (n := k+1), Nat.cast_succ]
    rw [add_sub_add_comm, ← mul_sub]
    apply (abs_add_le ..).trans
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    linarith only [hsum, he]

private theorem alternating_exp_error {x : ℝ} (hx₀ : 0 ≤ x) (hx : x ≤ 1) (n : ℕ) :
    |(∑ k ∈ range n, (-1:ℝ)^k * (x^k/k.factorial)) - exp (-x)| ≤ x^n := by
  let f := fun k : ℕ ↦ x^k/k.factorial
  have hmono : Antitone f := antitone_nat_of_succ_le fun k ↦ by
    dsimp [f]
    apply div_le_div₀ (by positivity) (pow_le_pow_of_le_one hx₀ hx (by omega)) (by positivity)
    exact_mod_cast Nat.factorial_le (Nat.le_succ k)
  have he := alternating_series_error_bound f hmono (Real.summable_pow_div_factorial x) n
  have hs : HasSum (fun k : ℕ ↦ (-1:ℝ)^k * f k) (exp (-x)) := by
    rw [Real.exp_eq_exp_ℝ, ← neg_one_mul x]
    simpa only [f, mul_pow, mul_div_assoc] using NormedSpace.expSeries_div_hasSum_exp ((-1)*x)
  rw [hs.tsum_eq, abs_sub_comm] at he
  exact he.trans (div_le_self (by positivity) (by exact_mod_cast Nat.factorial_pos n))

private theorem exp_diff {a b : ℝ} (h : b ≤ a) (ha : a ≤ 0) : exp a - exp b ≤ a-b := by
  have hs : exp b = exp a * exp (b-a) := by rw [← exp_add]; ring_nf
  rw [hs, ← mul_one_sub]
  exact (mul_le_mul (exp_le_one_iff.mpr ha) (show 1-exp (b-a) ≤ a-b by
    linarith [add_one_le_exp (b-a)]) (by linarith [exp_le_one_iff.mpr (sub_nonpos.mpr h)])
    zero_le_one).trans_eq (one_mul _)

private theorem exp_neg_contract {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |exp (-x)-exp (-y)| ≤ |x-y| := by
  rcases le_total x y with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr (exp_le_exp.mpr (neg_le_neg h))),
      abs_of_nonpos (sub_nonpos.mpr h)]
    linarith only [exp_diff (neg_le_neg h) (neg_nonpos.mpr hx)]
  · rw [abs_of_nonpos (sub_nonpos.mpr (exp_le_exp.mpr (neg_le_neg h))),
      abs_of_nonneg (sub_nonneg.mpr h)]
    linarith only [exp_diff (neg_le_neg h) (neg_nonpos.mpr hy)]

set_option exponentiation.threshold 2048 in
private theorem rounded_error {x : ℚ} {y : ℝ} (hx₀ : 0 ≤ (x:ℝ)) (hx : (x:ℝ) ≤ 1/2^31)
    (hy : 0 ≤ y) (hxy : |(x:ℝ)-y| ≤ 4*ulp 1088) :
    |(trunc 1024 (taylor x 35).2:ℝ) - exp (-y)| ≤ ulp 1024 + 80*ulp 1088 := by
  have h₁ := (taylor_error hx₀ hx 35).2
  have h₂ := alternating_exp_error hx₀ (hx.trans (by norm_num)) 36
  have hrem : (x:ℝ)^36 ≤ ulp 1088 := by
    calc _ ≤ (1/(2:ℝ)^31)^36 := pow_le_pow_left₀ hx₀ hx _
      _ ≤ _ := by norm_num [ulp]
  have hp := via (via h₁ (h₂.trans hrem)) ((exp_neg_contract hx₀ hy).trans hxy)
  have hround := via (trunc_error 1024 (taylor x 35).2) hp
  norm_num only [Nat.cast_ofNat] at hround
  linarith only [hround, ulp_pos 1088]

set_option exponentiation.threshold 2048 in
theorem expApprox_unit {x : ℚ} (hx₀ : 0 ≤ (x:ℝ)) (hx : (x:ℝ) ≤ 1/2^31) :
    (expApprox x : ℝ) ∈ Set.Icc 0 1 := by
  have h := rounded_error hx₀ hx hx₀ (by simpa only [sub_self,abs_zero] using
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (ulp_pos 1088).le))
  have he : ulp 1024 + 80*ulp 1088 ≤ 1/2 := by norm_num [ulp]
  unfold expApprox
  push_cast
  exact ⟨le_min zero_le_one (by linarith only [(abs_le.mp h).1, add_one_le_exp (-(x:ℝ)), hx, he]),
    min_le_left ..⟩

set_option exponentiation.threshold 2048 in
/-- The exponential and rounding bound including a four-ulp uncertainty in the argument. -/
theorem expApprox_error {x : ℚ} {y : ℝ} (hx₀ : 0 ≤ (x:ℝ)) (hx : (x:ℝ) ≤ 1/2^31)
    (hy : 0 ≤ y) (hxy : |(x:ℝ)-y| ≤ 4*ulp 1088) :
    |(expApprox x:ℝ)-exp (-y)| ≤ 1/(2:ℝ)^1024 + 2^((6.4:ℝ)-1088) := by
  have hsmall := rounded_error hx₀ hx hy hxy
  have hu : exp (-y) ≤ 1 := exp_le_one_iff.mpr (neg_nonpos.mpr hy)
  have hclamp : |(expApprox x:ℝ)-exp (-y)| ≤ ulp 1024 + 80*ulp 1088 := by
    unfold expApprox
    push_cast
    rw [abs_le] at *
    constructor <;> simp only [le_sub_iff_add_le, sub_le_iff_le_add, le_min_iff, min_le_iff] <;>
      grind [ulp_pos 1024, ulp_pos 1088]
  have h80 : (80:ℝ) ≤ 2^(6.4:ℝ) := by
    apply (pow_le_pow_iff_left₀ (by norm_num) (by positivity) (by decide : 5 ≠ 0)).mp
    rw [← Real.rpow_mul_natCast (by norm_num)]
    norm_num
  apply hclamp.trans
  rw [Real.rpow_sub (by norm_num : (0:ℝ)<2), show (1088:ℝ) = ((1088:ℕ):ℝ) by norm_num,
    Real.rpow_natCast]
  apply add_le_add (le_refl _)
  simpa only [ulp, mul_one_div] using
    div_le_div_of_nonneg_right h80 (show (0:ℝ) ≤ 2^1088 by positivity)

end FixedConstants

open Real FixedConstants

/-- Both certified F-format constants at any recorded dimension and run index. -/
noncomputable def recordedGaussianConstants {d j : ℕ} (hd : d = 646 ∨ d = 647) (hj : j < 4) :
    GaussianConstants (recordedWidth d j) := by
  let l := lambdaApprox d j
  let y := π/(recordedWidth d j)^2
  obtain ⟨h₀, h₂, hl⟩ := lambdaApprox_spec hd hj
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hu := (ulp_pos 1088).le
  have hx : (l:ℝ) ≤ 1/2^31 := by linarith
  have htw₀ : (0:ℝ) ≤ ((2*l:ℚ):ℝ) := by push_cast; exact mul_nonneg (by norm_num) h₀
  have htw : ((2*l:ℚ):ℝ) ≤ 1/2^31 := by push_cast; exact h₂
  refine ⟨expApprox l, expApprox (2*l), expApprox_unit h₀ hx, expApprox_unit htw₀ htw, ?_, ?_⟩
  · apply expApprox_error h₀ hx hy
    linarith only [hl,hu]
  · rw [neg_mul]
    apply expApprox_error htw₀ htw (by positivity)
    push_cast
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith only [hl]

/-- Recorded-instance statistical distance with all table constants supplied by the rational routine. -/
theorem recorded_sdist_discGauss_le_computed {r t j : ℕ} (hd : r+t = 646 ∨ r+t = 647)
    (hj : j < 4) (M : Matrix (Fin r) (Fin t) ℤ) :
    let s := recordedWidth (r+t) j
    let e := recordedGaussianConstants hd hj
    let A := tableDraws 3329 (2^22-1) 960 1024 e.unit₁.1 e.unit₂.1
    sdist (A.output M) (discGauss s 3329 M) ≤
      (r+t:ℝ) * (1/(2:ℝ)^930) + sdist (kleinLaw s 3329 M) (discGauss s 3329 M) :=
  recorded_sdist_discGauss_le hd hj M (recordedGaussianConstants hd hj)

end SigabaNeo.Wall1.CDT

#print axioms SigabaNeo.Wall1.CDT.FixedConstants.expApprox_error
#print axioms SigabaNeo.Wall1.CDT.recordedGaussianConstants
#print axioms SigabaNeo.Wall1.CDT.recorded_sdist_discGauss_le_computed
