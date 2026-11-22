module

public import SigabaNeo.Lib.Lattices.Research.Wall1.ThetaProfile
public import SigabaNeo.Lib.Lattices.Research.Wall1.GaussianSmoothing1D
import all SigabaNeo.Lib.Lattices.Research.Wall1.ThetaProfile
import all SigabaNeo.Lib.Lattices.Research.Wall1.GaussianSmoothing1D
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

/-! # Convexity of the logarithmic integer theta function -/

public section
namespace SigabaNeo.Wall1

open Real Set

private noncomputable def term (k : ℕ) (n : ℤ) (s : ℝ) := ((n : ℝ)^2)^k * exp (-s*(n : ℝ)^2)
private noncomputable def moment (k : ℕ) (s : ℝ) := ∑' n : ℤ, term k n s

private theorem term_nn (k : ℕ) (n : ℤ) (s : ℝ) : 0 ≤ term k n s := by
  unfold term; positivity

private theorem summable_moment (k : ℕ) {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℤ ↦ term k n s) := by
  let a := s/2
  have ha : 0 < a := half_pos hs
  apply Summable.of_nonneg_of_le (fun n ↦ term_nn k n s) _
    ((summable_int_gauss ha).mul_left ((k.factorial : ℝ)/a^k))
  intro n
  have h := pow_div_factorial_le_exp (a*(n : ℝ)^2) (mul_nonneg ha.le (sq_nonneg (n : ℝ))) k
  rw [mul_pow, div_le_iff₀ (by positivity)] at h
  have bound : ((n : ℝ)^2)^k ≤ (k.factorial : ℝ)/a^k * exp (a*(n : ℝ)^2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos ha k)]
    linarith
  apply (mul_le_mul_of_nonneg_right bound (exp_pos _).le).trans_eq
  rw [mul_assoc, ← exp_add, show a*(n : ℝ)^2 + -s*(n : ℝ)^2 = -a*(n : ℝ)^2 by dsimp [a]; ring]

private theorem moment_deriv (k : ℕ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (moment k) (-moment (k+1) s) s := by
  have hterm n y : HasDerivAt (term k n) (-term (k+1) n y) y := by
    unfold term
    have h := (((hasDerivAt_id y).neg.mul_const ((n : ℝ)^2)).exp).const_mul (((n : ℝ)^2)^k)
    convert h using 1
    · rfl
    change -(((n : ℝ)^2)^(k+1)*exp (-y*(n : ℝ)^2)) =
      ((n : ℝ)^2)^k * (exp (-y*(n : ℝ)^2) * (-1*(n : ℝ)^2))
    rw [pow_succ]; ring
  have mem : s ∈ Ioi (s/2) := by change s/2 < s; linarith
  have h := hasDerivAt_tsum_of_isPreconnected (summable_moment (k+1) (half_pos hs))
    isOpen_Ioi isPreconnected_Ioi (fun n y _ ↦ hterm n y) (by
      intro n y hy
      rw [norm_neg, Real.norm_of_nonneg (term_nn _ _ _)]
      unfold term
      gcongr
      exact (show s/2 < y from hy).le)
    mem (summable_moment k hs) mem
  change HasDerivAt (fun z ↦ ∑' n, term k n z) _ _
  rw [show -moment (k+1) s = ∑' n, -term (k+1) n s by rw [tsum_neg]; rfl]
  exact h

private theorem moment0 (s : ℝ) : moment 0 s = thetaFactor s := by simp [moment, term, thetaFactor]
private theorem moment_ge_one {s : ℝ} (hs : 0 < s) : 1 ≤ moment 0 s := by
  have h := (summable_moment 0 hs).sum_le_tsum ({0} : Finset ℤ) (fun n _ ↦ term_nn 0 n s)
  simpa [term, moment] using h
private theorem moment_pos {s : ℝ} (hs : 0 < s) : 0 < moment 0 s :=
  one_pos.trans_le (moment_ge_one hs)

set_option maxHeartbeats 1000000 in
private theorem small_moment {s : ℝ} (hs : π ≤ s) : moment 1 s ≤ 1/2 := by
  have hs3 := pi_gt_three.le.trans hs
  let f (n : ℕ) := term 1 ((n+1 : ℕ) : ℤ) s
  have hsum := summable_moment 1 (pi_pos.trans_le hs)
  have pos : Summable (fun n : ℕ ↦ term 1 (n : ℤ) s) := hsum.comp_injective Nat.cast_injective
  have neg : Summable (fun n : ℕ ↦ term 1 (-((n : ℤ)+1)) s) := hsum.comp_injective (show Function.Injective (fun n : ℕ ↦ -((n : ℤ)+1)) by
    intro i j h; simpa using h)
  have hpos : Summable f := pos.comp_injective Nat.succ_injective
  have negEq (n : ℕ) : term 1 (-((n : ℤ)+1)) s = f n := by
    simp only [term, f, Int.cast_neg, Int.cast_add, Int.cast_one, Int.cast_natCast, Nat.cast_add,
      Nat.cast_one, even_two.neg_pow]
  have split := tsum_of_nat_of_neg_add_one (f := fun n ↦ term 1 n s) pos neg
  rw [pos.tsum_eq_zero_add] at split
  simp_rw [negEq] at split
  change moment 1 s = (term 1 0 s + ∑' n, f n) + ∑' n, f n at split
  rw [split, show term 1 0 s = 0 by simp [term], zero_add]
  have row n : f n ≤ exp (-2*((n : ℝ)+1)^2) := by
    let z := ((n : ℝ)+1)^2
    change _ ≤ exp (-2*z)
    have hz : 0 ≤ z := sq_nonneg _
    have hh : z ≤ exp z := (by linarith [add_one_le_exp z] : z ≤ exp z)
    have eq : f n = z * exp (-s*z) := by simp [f, z, term]
    rw [eq]
    apply (mul_le_mul_of_nonneg_right hh (exp_pos _).le).trans
    rw [← exp_add, exp_le_exp]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs3) hz]
  have M := (hpos.tsum_le_tsum row (summable_tail (by norm_num : (0:ℝ)<2))).trans
    (tailSum_le (by norm_num : (0:ℝ)<2))
  have e2 : exp (-2) ≤ 1/5 := by
    rw [exp_neg, inv_le_comm₀ (exp_pos _) (by norm_num)]
    have h := sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 2) 3
    norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h ⊢
    exact h
  have e6 : exp (-3*2) ≤ 1/5 := (exp_le_exp.mpr (by norm_num)).trans e2
  have hd : 0 < 1-exp (-3*2) := sub_pos.mpr (e6.trans_lt (by norm_num))
  have hh : exp (-2)/(1-exp (-3*2)) ≤ 1/4 := (div_le_iff₀ hd).2 (by linarith only [e2, e6])
  linarith [M.trans hh]

private noncomputable def slope (x : ℝ) := -exp x * moment 1 (exp x) / moment 0 (exp x)
private noncomputable def curvature (x : ℝ) :=
  let s := exp x
  ((s^2*moment 2 s-s*moment 1 s)*moment 0 s - (s*moment 1 s)^2)/(moment 0 s)^2

private theorem slope_eq (x : ℝ) :
    HasDerivAt (fun y ↦ log (thetaFactor (exp y))) (slope x) x := by
  have h := ((moment_deriv 0 (exp_pos x)).comp x (hasDerivAt_exp x)).log (moment_pos (exp_pos x)).ne'
  simpa only [moment0, Function.comp_def, slope, neg_mul, mul_comm (exp x)] using h

private theorem curvature_eq (x : ℝ) : HasDerivAt slope (curvature x) x := by
  have h0 := (moment_deriv 0 (exp_pos x)).comp x (hasDerivAt_exp x)
  have h1 := (moment_deriv 1 (exp_pos x)).comp x (hasDerivAt_exp x)
  have h := (((hasDerivAt_exp x).neg.mul h1).div h0 (moment_pos (exp_pos x)).ne')
  convert h using 1
  · rfl
  unfold curvature
  simp only [Nat.reduceAdd, Function.comp_apply, Pi.mul_apply, Pi.neg_apply]
  ring

private theorem curvature_nonneg_right {x : ℝ} (hx : π ≤ exp x) : 0 ≤ curvature x := by
  let s := exp x
  let m := moment 1 s
  let Z := moment 0 s
  have hz : 1 ≤ Z := moment_ge_one (exp_pos x)
  have hm : 0 ≤ m := tsum_nonneg fun n ↦ term_nn 1 n s
  have h2 : m ≤ moment 2 s := by
    apply (summable_moment 1 (exp_pos x)).tsum_le_tsum _ (summable_moment 2 (exp_pos x))
    intro n
    apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
    have h : (0 : ℤ) ≤ n^2*(n^2-1) := by
      rcases eq_or_ne n 0 with h|h
      · simp [h]
      · have hn := sq_pos_of_ne_zero h
        exact mul_nonneg hn.le (by omega)
    have hh : (0 : ℝ) ≤ (n : ℝ)^2*((n : ℝ)^2-1) := by exact_mod_cast h
    nlinarith
  have hs : 3 ≤ s := pi_gt_three.le.trans hx
  have hm' : m ≤ 1/2 := small_moment hx
  unfold curvature
  apply div_nonneg _ (sq_nonneg _)
  change 0 ≤ (s^2*moment 2 s-s*m)*Z-(s*m)^2
  have a : s*m ≤ (s-1)*Z := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ s-1) (sub_nonneg.mpr hz),
      mul_le_mul_of_nonneg_left hm' (by linarith : 0 ≤ s)]
  nlinarith [mul_nonneg (mul_nonneg (sq_nonneg s) (sub_nonneg.mpr h2)) (by linarith : 0 ≤ Z),
    mul_nonneg (mul_nonneg (by linarith : 0 ≤ s) hm) (sub_nonneg.mpr a)]

/-- Reflection of the centered theta function, in the logarithmic argument. -/
theorem logTheta_reflection (x : ℝ) :
    log (thetaFactor (exp x)) = (log π-x)/2 + log (thetaFactor (exp (2*log π-x))) := by
  let a := sqrt (π/exp x)
  have ha : 0 < a := sqrt_pos.mpr (div_pos pi_pos (exp_pos x))
  have sq : a^2 = π/exp x := sq_sqrt (div_pos pi_pos (exp_pos x)).le
  have b : exp (2*log π-x) = π*(π/exp x) := by rw [exp_sub, two_mul, exp_add, exp_log pi_pos]; ring
  have eq : theta1 a 0 = thetaFactor (exp x) := by
    unfold theta1 thetaFactor
    apply tsum_congr; intro n
    rw [add_zero, sq]; congr 1; field_simp [pi_ne_zero, exp_ne_zero]
  have h := theta1_poisson ha 0
  rw [eq] at h
  simp only [mul_zero, cos_zero, mul_one, sq, neg_mul] at h
  have poweq : thetaFactor (exp x) = a * thetaFactor (exp (2*log π-x)) := by
    rw [b, h]; congr 1; apply tsum_congr; intro n; congr 1; ring
  rw [poweq, log_mul ha.ne' ((moment0 _ ▸ moment_pos (exp_pos _))).ne']
  congr 1
  rw [show log a = log (π/exp x)/2 from log_sqrt (by positivity), log_div pi_ne_zero
    (exp_ne_zero _), log_exp]

/-- Global convexity of `x ↦ log θ(exp x)`. -/
theorem logTheta_convex : ConvexOn ℝ Set.univ (fun x ↦ log (thetaFactor (exp x))) := by
  let R (x : ℝ) := 2*log π-x
  have refl x : slope x = -1/2 - slope (R x) := by
    have h := (((hasDerivAt_const x (log π)).sub (hasDerivAt_id x)).div_const 2).add
      ((slope_eq (R x)).comp x ((hasDerivAt_const x (2*log π)).sub (hasDerivAt_id x)))
    have h' := h.congr_of_eventuallyEq (Filter.Eventually.of_forall logTheta_reflection)
    simpa only [sub_eq_add_neg, zero_add, mul_neg, mul_one] using (slope_eq x).unique h'
  have curv x : curvature x = curvature (R x) := by
    have h := (hasDerivAt_const x (-1/2 : ℝ)).sub
      ((curvature_eq (R x)).comp x ((hasDerivAt_const x (2*log π)).sub (hasDerivAt_id x)))
    simpa using (curvature_eq x).unique (h.congr_of_eventuallyEq (Filter.Eventually.of_forall refl))
  apply convexOn_of_hasDerivWithinAt2_nonneg convex_univ
    (fun x _ ↦ (slope_eq x).continuousAt.continuousWithinAt)
    (fun x _ ↦ (slope_eq x).hasDerivWithinAt) (fun x _ ↦ (curvature_eq x).hasDerivWithinAt)
  intro x _
  by_cases hx : log π ≤ x
  · exact curvature_nonneg_right ((log_le_iff_le_exp pi_pos).mp hx)
  · rw [curv]
    apply curvature_nonneg_right
    exact (log_le_iff_le_exp pi_pos).mp (by dsimp [R]; linarith)

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.logTheta_reflection
#print axioms SigabaNeo.Wall1.logTheta_convex
