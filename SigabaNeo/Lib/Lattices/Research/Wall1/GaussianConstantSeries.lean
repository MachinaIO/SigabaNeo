module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! # Fixed-point Machin and logarithm series for the Gaussian table constants -/

@[expose] public section

namespace SigabaNeo.Wall1.CDT.FixedConstants

open Real Finset

/-- Round a rational down to a dyadic with `bits` fractional bits. -/
def trunc (bits : ℕ) (x : ℚ) : ℚ := (⌊x * 2 ^ bits⌋ : ℚ) / 2 ^ bits

noncomputable def ulp (bits : ℕ) : ℝ := 1 / 2 ^ bits

theorem ulp_pos (b : ℕ) : 0 < ulp b := by unfold ulp; positivity

theorem trunc_error (b : ℕ) (x : ℚ) : |(trunc b x : ℝ) - x| ≤ ulp b := by
  have hlo := Int.floor_le (x * 2 ^ b)
  have hhi := Int.lt_floor_add_one (x * 2 ^ b)
  have h : |trunc b x - x| ≤ 1 / (2 : ℚ)^b := by
    rw [abs_le]; unfold trunc
    constructor
    · rw [le_sub_iff_add_le, ← neg_div, le_div_iff₀ (by positivity)]
      rw [add_mul, div_mul_cancel₀ _ (by positivity)]
      linarith
    · rw [sub_le_iff_le_add, div_le_iff₀ (by positivity), add_mul,
        div_mul_cancel₀ _ (by positivity)]
      linarith
  simpa only [ulp, Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_pow,
    Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 h

/-- An error triangle with the middle value supplied explicitly. -/
theorem via {a b c e f : ℝ} (h : |a-b| ≤ e) (h' : |b-c| ≤ f) : |a-c| ≤ e+f :=
  (abs_sub_le a b c).trans (add_le_add h h')

/-- The next odd power and the partial sum of the first `n` rounded terms.
The sign is −1 for arctan and +1 for the logarithm. -/
def oddSeries (x sign : ℚ) : ℕ → ℚ × ℚ
  | 0 => (trunc 1088 x, 0)
  | k+1 =>
    let (p, s) := oddSeries x sign k
    (trunc 1088 (p * x^2), s + sign^k * trunc 1088 (p / (2*k+1 : ℕ)))

private theorem odd_error (x sign : ℚ) (hx : (x : ℝ)^2 ≤ 1/2) (hs : |(sign : ℝ)| = 1)
    (n : ℕ) :
    |((oddSeries x sign n).1 : ℝ) - (x : ℝ)^(2*n+1)| ≤ 2 * ulp 1088 ∧
    |((oddSeries x sign n).2 : ℝ) -
      ∑ k ∈ range n, (sign : ℝ)^k * ((x : ℝ)^(2*k+1) / (2*k+1))| ≤
      n * (2 * ulp 1088) := by
  have hu := (ulp_pos 1088).le
  induction n with
  | zero =>
    simp only [oddSeries, mul_zero, zero_add, pow_one, sum_range_zero, Rat.cast_zero,
      sub_zero, abs_zero, Nat.cast_zero, zero_mul, le_refl, and_true]
    linarith [trunc_error 1088 x]
  | succ k ih =>
    obtain ⟨hp, hsum⟩ := ih
    let p := (oddSeries x sign k).1
    let den := 2*k+1
    have hd : 1 ≤ (den : ℝ) := by exact_mod_cast (show 1 ≤ den by dsimp [den]; omega)
    have hm := trunc_error 1088 (p*x^2)
    push_cast at hm
    have hp' : |(p:ℝ)*(x:ℝ)^2 - (x:ℝ)^(2*k+1)*(x:ℝ)^2| ≤ ulp 1088 := by
      rw [← sub_mul, abs_mul, abs_of_nonneg (sq_nonneg (x:ℝ))]
      exact (mul_le_mul hp hx (sq_nonneg _) (by positivity)).trans_eq (by ring)
    have ht := trunc_error 1088 (p / den)
    push_cast at ht
    have hdiv : |(p:ℝ)/den - (x:ℝ)^(2*k+1)/den| ≤ ulp 1088 := by
      by_cases hk : k = 0
      · subst k
        simpa [p, den, oddSeries] using trunc_error 1088 x
      have hd₂ : (2:ℝ) ≤ den := by exact_mod_cast (show 2 ≤ den by dsimp [den]; omega)
      rw [← sub_div, abs_div, abs_of_pos (by linarith : (0:ℝ) < den),
        div_le_iff₀ (by linarith)]
      exact hp.trans (by linarith only [mul_le_mul_of_nonneg_right hd₂ hu])
    have ht' := via ht hdiv
    constructor
    · change |(trunc 1088 (p*x^2) : ℝ) - _| ≤ _
      rw [show 2*(k+1)+1 = (2*k+1)+2 by omega, pow_add]
      linarith [via hm hp']
    · simp only [oddSeries, Rat.cast_add, Rat.cast_mul, Rat.cast_pow, sum_range_succ]
      push_cast
      rw [add_sub_add_comm, ← mul_sub]
      have hsign : |(sign : ℝ)^k| = 1 := by simp [abs_pow, hs]
      apply (abs_add_le ..).trans
      rw [abs_mul, hsign, one_mul]
      dsimp [den] at ht'
      push_cast at ht'
      linarith

/-- The G-bit Machin approximation, with the two truncation orders of Lemma 5. -/
def piApprox : ℚ := 16 * (oddSeries (1/5) (-1) 234).2 - 4 * (oddSeries (1/239) (-1) 69).2

private theorem atan_error (x : ℚ) (hx₀ : 0 ≤ (x:ℝ)) (hx : (x:ℝ) < 1)
    (hx₂ : (x:ℝ)^2 ≤ 1/2) (n : ℕ) (htail : (x:ℝ)^(2*n+1) ≤ ulp 1088) :
    |((oddSeries x (-1) n).2 : ℝ) - arctan x| ≤ (2*n+1 : ℝ)*ulp 1088 := by
  let f := fun k : ℕ ↦ (x:ℝ)^(2*k+1)/(2*k+1)
  have hden (k : ℕ) : 1 ≤ (2*k+1 : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hf (k : ℕ) : f k ≤ (x:ℝ)^(2*k+1) :=
    div_le_self (by positivity) (hden k)
  have hmono : Antitone f := antitone_nat_of_succ_le fun k ↦ by
    dsimp [f]
    apply div_le_div₀ (by positivity) (pow_le_pow_of_le_one hx₀ hx.le (by omega)) (by positivity)
    push_cast; linarith
  have hsum : Summable f := (summable_geometric_of_lt_one hx₀ hx).of_nonneg_of_le
    (fun k ↦ by dsimp [f]; positivity)
    (fun k ↦ (hf k).trans (pow_le_pow_of_le_one hx₀ hx.le (by omega)))
  have hs := Real.hasSum_arctan (x := x) (by rw [Real.norm_eq_abs, abs_of_nonneg hx₀]; exact hx)
  have hts : HasSum (fun k : ℕ ↦ (-1:ℝ)^k * f k) (arctan x) := by
    simpa [f, mul_div_assoc] using hs
  have he := alternating_series_error_bound f hmono hsum n
  rw [hts.tsum_eq, abs_sub_comm] at he
  have ho := (odd_error x (-1) hx₂ (by norm_num) n).2
  push_cast at ho
  linarith [via ho (he.trans ((hf n).trans htail))]

set_option exponentiation.threshold 5000 in
theorem piApprox_error : |(piApprox : ℝ) - π| ≤ 8192 * ulp 1088 := by
  have h₅ := atan_error (1/5) (by norm_num) (by norm_num) (by norm_num) 234
    (by norm_num [ulp])
  have h₂ := atan_error (1/239) (by norm_num) (by norm_num) (by norm_num) 69
    (by norm_num [ulp])
  have hm := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Nat.cast_ofNat, one_div] at h₅ h₂
  unfold piApprox
  push_cast
  rw [abs_le] at *
  constructor <;> linarith [ulp_pos 1088]

/-- The G-bit logarithm via range reduction at 1024 and the atanh series. -/
def logArg (d : ℕ) : ℚ := ((2*d+4 : ℕ) - (1024:ℚ)) / ((2*d+4 : ℕ) + (1024:ℚ))
def logApprox (d : ℕ) : ℚ :=
  20 * (oddSeries (1/3) 1 343).2 + 2 * (oddSeries (logArg d) 1 177).2

private theorem logSeries_error (x : ℚ) (hx₀ : 0 ≤ (x:ℝ)) (hx : (x:ℝ) < 1)
    (hx₂ : (x:ℝ)^2 ≤ 1/2) (n : ℕ)
    (htail : (x:ℝ)^(2*n+1)/(1-(x:ℝ)^2) ≤ ulp 1088) :
    |((oddSeries x 1 n).2 : ℝ) - 1/2 * log ((1+x)/(1-x))| ≤ (2*n+1:ℝ)*ulp 1088 := by
  have h := Real.sum_range_sub_log_div_le (x := (x:ℝ)) (by rwa [abs_of_nonneg hx₀]) n
  rw [abs_sub_comm, abs_of_nonneg hx₀] at h
  have ho := (odd_error x 1 hx₂ (by norm_num) n).2
  simp only [Rat.cast_one, one_pow, one_mul] at ho
  linarith [via ho (h.trans htail)]

set_option exponentiation.threshold 5000 in
theorem logApprox_error {d : ℕ} (hd : d = 646 ∨ d = 647) :
    |(logApprox d : ℝ) - log (2*(d:ℝ)+4)| ≤ 14450 * ulp 1088 := by
  have h₃ := logSeries_error (1/3) (by norm_num) (by norm_num) (by norm_num) 343
    (by norm_num [ulp])
  have hd' := logSeries_error (logArg d)
    (by rcases hd with rfl | rfl <;> norm_num [logArg])
    (by rcases hd with rfl | rfl <;> norm_num [logArg])
    (by rcases hd with rfl | rfl <;> norm_num [logArg]) 177
    (by rcases hd with rfl | rfl <;> norm_num [logArg, ulp])
  have hid : (1+(logArg d:ℝ))/(1-(logArg d:ℝ)) = (2*(d:ℝ)+4)/1024 := by
    rcases hd with rfl | rfl <;> norm_num [logArg]
  rw [hid, log_div (by positivity) (by norm_num), show (1024:ℝ) = 2^10 by norm_num,
    Real.log_pow] at hd'
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Nat.cast_ofNat] at h₃ hd'
  unfold logApprox
  push_cast
  rw [abs_le] at *
  constructor <;> linarith [ulp_pos 1088]

end SigabaNeo.Wall1.CDT.FixedConstants

#print axioms SigabaNeo.Wall1.CDT.FixedConstants.piApprox_error
#print axioms SigabaNeo.Wall1.CDT.FixedConstants.logApprox_error
