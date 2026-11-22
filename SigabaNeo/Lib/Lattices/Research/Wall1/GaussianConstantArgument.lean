module

public import SigabaNeo.Lib.Lattices.Research.Wall1.GaussianConstantSeries
public import SigabaNeo.Lib.Lattices.Research.Wall1.GaussianCDTBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-! # The fixed-point argument of the exponential at the recorded widths -/

@[expose] public section

namespace SigabaNeo.Wall1.CDT.FixedConstants

open Real

/-- G-format numerator of the factor multiplying π² in run `j`. The two square
roots operate on scaled integers. Each division discards the fractional bits. -/
def factorNumerator (j : ℕ) : ℕ :=
  let S := 2^1088
  let a := Nat.sqrt (2*S^2)
  let b := Nat.sqrt (a*S)
  match j with
  | 0 => S
  | 1 => (a*b/S)/2
  | 2 => a/2
  | _ => b/2

def factorApprox (j : ℕ) : ℚ := (factorNumerator j : ℚ) / 2^1088
noncomputable def factorValue (j : ℕ) : ℝ := 1/(2:ℝ)^((j:ℝ)/4)

/-- Certify both sides of the fourth-root enclosure using integer arithmetic only. -/
private theorem factorCertificate {j : ℕ} (hj : j < 4) :
    let a := factorNumerator j
    4 ≤ a ∧ a ≤ 2^1088 ∧
      (a-4)^4 * 2^j ≤ (2^1088)^4 ∧ (2^1088)^4 ≤ (a+4)^4 * 2^j := by
  interval_cases j <;> decide +kernel

set_option exponentiation.threshold 2048 in
theorem factorApprox_error {j : ℕ} (hj : j < 4) :
    |(factorApprox j : ℝ) - factorValue j| ≤ 4 * ulp 1088 := by
  obtain ⟨ha, _, hl, hu⟩ := factorCertificate hj
  let a : ℝ := factorNumerator j
  let S : ℝ := 2^1088
  have hS : 0 < S := by dsimp [S]; positivity
  have ha' : 4 ≤ a := by simpa only [a,Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr ha
  have hl' : (a-4)^4 * 2^j ≤ S^4 := by
    simpa only [a,S,Nat.cast_mul,Nat.cast_pow,Nat.cast_sub ha,Nat.cast_ofNat] using
      (Nat.cast_le (α := ℝ)).mpr hl
  have hu' : S^4 ≤ (a+4)^4 * 2^j := by
    simpa only [a,S,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
      (Nat.cast_le (α := ℝ)).mpr hu
  have hp : (factorValue j)^4 = 1/(2:ℝ)^j := by
    rw [factorValue, div_pow, one_pow, ← Real.rpow_mul_natCast (by norm_num)]
    norm_num [Real.rpow_natCast]
  have hc : 0 ≤ factorValue j := by dsimp [factorValue]; positivity
  have hs₁ : (a-4)/S ≤ factorValue j := by
    apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ (a-4)/S) hc (by decide : 4 ≠ 0)).mp
    rw [div_pow, hp, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    exact hl'
  have hs₂ : factorValue j ≤ (a+4)/S := by
    apply (pow_le_pow_iff_left₀ hc (by positivity : 0 ≤ (a+4)/S) (by decide : 4 ≠ 0)).mp
    rw [div_pow, hp, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    exact hu'
  unfold factorApprox ulp
  push_cast
  change |a/S-factorValue j| ≤ 4*(1/S)
  rw [sub_div] at hs₁
  rw [abs_le, ← div_eq_mul_one_div 4 S]
  rw [add_div] at hs₂
  constructor <;> linarith only [hs₁, hs₂]

/-- K2 and K5 use one rounded square, one rounded product, and one rounded quotient. -/
def lambdaApprox (d j : ℕ) : ℚ :=
  trunc 1088 (trunc 1088 (trunc 1088 (piApprox^2) * factorApprox j) /
    ((d:ℚ)*3329^2*logApprox d))

private theorem width_identity (d j : ℕ) :
    π/(recordedWidth d j)^2 = π^2 * factorValue j /
      ((d:ℝ)*3329^2*log (2*(d:ℝ)+4)) := by
  have hlog : 0 ≤ log (2*(d:ℝ)+4) := log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) d])
  rw [recordedWidth, mul_pow, mul_pow, Real.sq_sqrt (by positivity), factorValue,
    ← Real.rpow_mul_natCast (by norm_num), show (j:ℝ)/8 * (2:ℕ) = j/4 by ring]
  field_simp

private theorem product_error {a b x y A Y e f : ℝ}
    (ha : |a| ≤ A) (hy : |y| ≤ Y) (hx : |a-x| ≤ e) (hb : |b-y| ≤ f) :
    |a*b-x*y| ≤ A*f+e*Y := by
  rw [show a*b-x*y = a*(b-y)+(a-x)*y by ring]
  apply (abs_add_le ..).trans
  simp only [abs_mul]
  exact add_le_add (mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha))
    (mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx))

attribute [local irreducible] piApprox trunc logApprox factorApprox

set_option maxHeartbeats 800000 in
set_option exponentiation.threshold 2048 in
/-- The computed λ is nonnegative, has room for the factor two in K6, and is within
two G-format units of the argument at the actual (transcendental) recorded width. -/
theorem lambdaApprox_spec {d j : ℕ} (hd : d = 646 ∨ d = 647) (hj : j < 4) :
    0 ≤ (lambdaApprox d j : ℝ) ∧ 2*(lambdaApprox d j : ℝ) ≤ 1/(2:ℝ)^31 ∧
      |(lambdaApprox d j : ℝ) - π/(recordedWidth d j)^2| ≤ 2*ulp 1088 := by
  let U := ulp 1088
  let D := (d:ℝ)*3329^2
  let L := log (2*(d:ℝ)+4)
  let B : ℝ := logApprox d
  let C := factorValue j
  let N := π^2*C
  let lam := N/(D*L)
  let p : ℝ := piApprox
  let P := trunc 1088 (piApprox^2)
  let A := trunc 1088 (P*factorApprox j)
  have hU : 0 < U := ulp_pos _
  have hUs : U ≤ 1/10^20 := by norm_num [U,ulp]
  have hD : 7100000000 ≤ D ∧ D ≤ 7300000000 := by rcases hd with rfl | rfl <;> norm_num [D]
  have hL : 7 ≤ L ∧ L ≤ 8 := by
    constructor
    · apply (le_log_iff_exp_le (by positivity)).mpr
      calc exp 7 = (exp 1)^7 := by rw [← exp_nat_mul]; norm_num
        _ ≤ (2.75:ℝ)^7 := by gcongr; linarith [exp_one_lt_d9]
        _ ≤ _ := by rcases hd with rfl | rfl <;> norm_num
    · apply (log_le_iff_le_exp (by positivity)).mpr
      calc _ ≤ (2.5:ℝ)^8 := by rcases hd with rfl | rfl <;> norm_num
        _ ≤ (exp 1)^8 := by gcongr; linarith [exp_one_gt_d9]
        _ = exp 8 := by rw [← exp_nat_mul]; norm_num
  have hC : 1/2 ≤ C ∧ C ≤ 1 := by
    have hj' : (j:ℝ) ≤ 3 := by exact_mod_cast (show j ≤ 3 by omega)
    have hpow : (2:ℝ)^((j:ℝ)/4) ≤ 2 := by
      calc _ ≤ (2:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = _ := Real.rpow_one _
    exact ⟨one_div_le_one_div_of_le (by positivity) hpow,
      one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1)
        (one_le_rpow (by norm_num) (by positivity)) |>.trans (by norm_num)⟩
  have hπ : π ≤ 3.2 := by linarith [Real.pi_lt_d2]
  have hN : 4 ≤ N ∧ N ≤ 10.24 := by
    have hs := mul_self_le_mul_self pi_pos.le hπ
    constructor
    · dsimp [N]; nlinarith [mul_le_mul (show 9 ≤ π^2 by nlinarith [pi_gt_three]) hC.1
          (by norm_num) (sq_nonneg π)]
    · dsimp [N]; nlinarith [mul_le_mul (show π^2 ≤ 10.24 by nlinarith) hC.2
          (by linarith : 0 ≤ C) (by norm_num : (0:ℝ) ≤ 10.24)]
  have hD₀ : 0 < D := by linarith
  have hL₀ : 0 < L := by linarith
  have hlam : 1/10^11 ≤ lam ∧ lam ≤ 1/4700000000 := by
    constructor
    · apply (le_div_iff₀ (mul_pos hD₀ hL₀)).mpr
      linarith [mul_le_mul hD.2 hL.2 hL₀.le (by norm_num : (0:ℝ) ≤ 7300000000)]
    · apply (div_le_iff₀ (mul_pos hD₀ hL₀)).mpr
      linarith [mul_le_mul hD.1 hL.1 (by norm_num) hD₀.le]
  have hB : |B-L| ≤ 14450*U := logApprox_error hd
  have hB₀ : 6 ≤ B := by linarith [(abs_le.mp hB).1]
  have hP : |p-π| ≤ 8192*U := piApprox_error
  have hp : |p| ≤ 4 := by rw [abs_le]; have := abs_le.mp hP; constructor <;> linarith [pi_pos]
  have hsq := product_error hp (show |π| ≤ 4 by rw [abs_of_pos pi_pos]; linarith) hP hP
  have hround : |(P:ℝ)-p*p| ≤ U := by
    change |(trunc 1088 (piApprox^2):ℝ)-(piApprox:ℝ)*(piApprox:ℝ)| ≤ _
    rw [← pow_two, ← Rat.cast_pow]; exact trunc_error ..
  have heP : |(P:ℝ)-π^2| ≤ 105000*U := by rw [pow_two]; linarith only [via hround hsq,hU]
  have hPa : |(P:ℝ)| ≤ 12 := by
    rw [abs_le]; have := abs_le.mp heP
    constructor <;> nlinarith [sq_nonneg π, mul_self_le_mul_self pi_pos.le hπ]
  have heC : |(factorApprox j:ℝ)-C| ≤ 4*U := factorApprox_error hj
  have hprod := product_error hPa (show |C| ≤ 1 by rw [abs_of_nonneg (by linarith)]; exact hC.2)
    heP heC
  have hroundA : |(A:ℝ)-(P:ℝ)*(factorApprox j:ℝ)| ≤ U := by
    simpa only [A, Rat.cast_mul] using trunc_error 1088 (P*factorApprox j)
  have heA : |(A:ℝ)-N| ≤ 106000*U := by dsimp only [N]; linarith only [via hroundA hprod,hU]
  have hlamD : lam*D ≤ 2 := by
    have h := mul_le_mul hlam.2 hD.2 hD₀.le (by norm_num)
    linarith
  have hi : lam*(D*L) = N := div_mul_cancel₀ _ (mul_pos hD₀ hL₀).ne'
  have he : |(A:ℝ)-lam*(D*B)| ≤ 152000*U := by
    rw [show (A:ℝ)-lam*(D*B) = ((A:ℝ)-N) + (lam*D)*(L-B) by rw [← hi]; ring]
    apply (abs_add_le ..).trans
    rw [abs_mul, abs_of_nonneg (mul_nonneg (by linarith only [hlam.1]) hD₀.le), abs_sub_comm L B]
    linarith [mul_le_mul hlamD hB (abs_nonneg _) (by norm_num)]
  have hDB : 152000 ≤ D*B := by linarith [mul_le_mul hD.1 hB₀ (by norm_num) hD₀.le]
  have hDB₀ : 0 < D*B := by linarith
  have hquot : |(A:ℝ)/(D*B)-lam| ≤ U := by
    rw [div_sub' hDB₀.ne', abs_div, abs_of_pos hDB₀, div_le_iff₀ hDB₀]
    rw [mul_comm (D*B)]
    exact he.trans (by linarith [mul_le_mul_of_nonneg_right hDB hU.le])
  have hr : |(lambdaApprox d j:ℝ)-(A:ℝ)/(D*B)| ≤ U := by
    have h := trunc_error 1088 (A/((d:ℚ)*3329^2*logApprox d))
    push_cast at h
    exact h
  have hfinal : |(lambdaApprox d j:ℝ)-lam| ≤ 2*U := by linarith only [via hr hquot]
  rw [width_identity d j]
  obtain ⟨hlo, hhi⟩ := abs_le.mp hfinal
  exact ⟨by linarith only [hlo,hUs,hlam.1], by linarith only [hhi,hUs,hlam.2], hfinal⟩

end SigabaNeo.Wall1.CDT.FixedConstants

#print axioms SigabaNeo.Wall1.CDT.FixedConstants.factorApprox_error
#print axioms SigabaNeo.Wall1.CDT.FixedConstants.lambdaApprox_spec
