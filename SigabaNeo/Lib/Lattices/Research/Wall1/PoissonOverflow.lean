module

public import SigabaNeo.Lib.Lattices.Research.Wall1.AdrsPoisson
public import SigabaNeo.Lib.Lattices.Research.Wall1.Width638Cost
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! An exact Poisson input-size bound by comparison with the law at double intensity. -/

@[expose] public section
noncomputable section
namespace SigabaNeo.Wall1.CVP638

open SigabaNeo.Wall1.ADRS ProbabilityTheory MeasureTheory Real
open scoped ENNReal NNReal

/-- At counts above twice the mean, exponential tilting costs at most (e/4)^n. -/
theorem poisson_overflow (n : ℕ) :
    poissonMeasure (n:ℝ≥0) {k | 2*n < k} ≤ ENNReal.ofReal ((exp 1 / 4)^n) := by
  let K := 2*n+1
  have hset : {k | 2*n < k} = Set.Ici K := Set.ext fun _ ↦ by rfl
  rw [hset, ← ofReal_measureReal, ← poissonTail_eq]
  apply ENNReal.ofReal_le_ofReal
  let a : ℝ := n
  have hP : HasSum (poissonMass a) 1 := hasSum_one_poissonMeasure n
  have hQ : HasSum (poissonMass (2*a)) 1 := hasSum_one_poissonMeasure (2*n)
  have shifted {g : ℕ → ℝ} (hg : Summable g) : Summable (fun k ↦ g (K+k)) := by
    simpa only [Nat.add_comm K] using (summable_nat_add_iff K).2 hg
  have hcompare (k : ℕ) : poissonMass a (K+k) ≤ (exp 1 / 4)^n * poissonMass (2*a) (K+k) := by
    let j := K+k
    have h2 : (4:ℝ)^n ≤ 2^j := by
      rw [show (4:ℝ) = 2^2 by norm_num, ← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (by dsimp [j,K]; omega)
    have hid : poissonMass a j =
        (exp a / 2^j) * poissonMass (2*a) j := by
      unfold poissonMass
      rw [mul_pow, show exp (-a) = exp a * exp (-(2*a)) by rw [← exp_add]; congr 1; ring]
      field_simp
    rw [hid]
    apply mul_le_mul_of_nonneg_right _ (by unfold poissonMass a; positivity)
    rw [div_pow, ← exp_nat_mul, mul_one]
    exact div_le_div_of_nonneg_left (exp_pos _).le (by positivity) h2
  apply ((shifted hP.summable).tsum_le_tsum hcompare ((shifted hQ.summable).mul_left _)).trans
  rw [tsum_mul_left]
  have tail : (∑' k, poissonMass (2*a) (K+k)) ≤ 1 := by
    have hh := poissonTail_eq (2*(n:ℝ≥0)) K
    exact hh.le.trans measureReal_le_one
  simpa only [mul_one] using mul_le_mul_of_nonneg_left tail
    (show 0 ≤ (exp 1/4)^n by positivity)

theorem initial_poisson_overflow :
    poissonMeasure (initialMean:ℝ≥0) {n | sampleCount < n} ≤ ENNReal.ofReal (1/(2:ℝ)^800) := by
  have cap : sampleCount = 2*initialMean := by decide +kernel
  rw [cap]
  apply (poisson_overflow _).trans
  apply ENNReal.ofReal_le_ofReal
  have hn : 2000 ≤ initialMean := by decide +kernel
  apply (pow_le_pow_left₀ (by positivity) (show exp 1 / 4 ≤ 3/4 by linarith [exp_one_lt_three])
    initialMean).trans
  apply (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn).trans
  have q := (Rat.cast_lt (K := ℝ)).mpr overflow_lt
  push_cast at q
  exact q.le

end SigabaNeo.Wall1.CVP638

#print axioms SigabaNeo.Wall1.CVP638.poisson_overflow
#print axioms SigabaNeo.Wall1.CVP638.initial_poisson_overflow
