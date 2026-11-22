module

public import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Tactic

/-! # The Poisson likelihood ratio and tail estimates of Part 140, §4.3 -/

@[expose] public section

noncomputable section

namespace SigabaNeo.Wall1.ADRS

open Real ProbabilityTheory MeasureTheory
open scoped NNReal

/-- Poisson point mass, in real arithmetic. -/
def poissonMass (a : ℝ) (j : ℕ) := exp (-a) * a ^ j / j.factorial

theorem poissonMass_eq (a : ℝ≥0) (j : ℕ) :
    poissonMass a j = (poissonMeasure a).real {j} := (poissonMeasure_real_singleton ..).symm

/-- Point mass of the number of disjoint pairs available in a Poisson-sized bin. -/
def halfMass (a : ℝ) (j : ℕ) := poissonMass a (2*j) + poissonMass a (2*j+1)

theorem halfMass_eq (a : ℝ≥0) (j : ℕ) :
    halfMass a j = (poissonMeasure a).real {n : ℕ | n / 2 = j} := by
  have he : {n : ℕ | n / 2 = j} = {2*j} ∪ {2*j+1} := by ext n; simp; omega
  rw [he, measureReal_union (by simp : Disjoint ({2*j} : Set ℕ) {2*j+1})
    (measurableSet_singleton _)]
  simp only [halfMass, poissonMass_eq]

private theorem poissonMass_pos {a : ℝ} (ha : 0 < a) (n : ℕ) : 0 < poissonMass a n := by
  unfold poissonMass
  positivity

private theorem poissonMass_succ (a : ℝ) (j : ℕ) :
    poissonMass a (j+1) = poissonMass a j * a / (j+1) := by
  simp only [poissonMass, Nat.factorial_succ, pow_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

theorem halfMass_factor (a : ℝ) (j : ℕ) :
    halfMass a j = poissonMass a (2*j) * (1 + a / (2*j+1)) := by
  rw [halfMass, poissonMass_succ]
  push_cast
  ring

/-- Rⱼ in Lemma 4.3a, with b supplied explicitly. -/
def likelihoodRatio (a b : ℝ) (j : ℕ) := poissonMass b j / halfMass a j

theorem likelihoodRatio_step {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (j : ℕ) :
    likelihoodRatio a b (j+1) / likelihoodRatio a b j =
      (2*b/a^2) * (2*j+3) * (2*j+1+a) / (2*j+3+a) := by
  simp only [likelihoodRatio, halfMass_factor, show 2*(j+1) = (2*j+1)+1 by omega,
    poissonMass_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  have h₁ := poissonMass_pos ha (2*j)
  have h₂ := poissonMass_pos hb j
  field_simp
  ring

theorem likelihoodRatio_step_le {a A θ : ℝ} (ha : 0 < a) (hA : 0 < A) (hθ : 0 < θ) (j : ℕ) :
    likelihoodRatio a (θ*a^2/A) (j+1) / likelihoodRatio a (θ*a^2/A) j ≤
      2*θ*(2*j+3)/A := by
  rw [likelihoodRatio_step ha (by positivity)]
  field_simp
  nlinarith [mul_pos (mul_pos (sq_pos_of_pos ha) hθ) (show (0 : ℝ) < 2*j+3 by positivity)]

/-- The floor cutoff of §4.3 makes the likelihood ratio antitone throughout the retained range. -/
theorem likelihoodRatio_antitone {a A θ : ℝ} (ha : 0 < a) (haA : a ≤ A) (hθ : 0 < θ)
    {m : ℕ} (hm : m = ⌊A/(4*θ) - 1/2⌋₊) (hm₁ : 1 ≤ m) :
    AntitoneOn (likelihoodRatio a (θ*a^2/A)) (Set.Iic m) := by
  have hA := ha.trans_le haA
  have hfloor : (m : ℝ) ≤ A/(4*θ) - 1/2 := by
    have hn : 0 ≤ A/(4*θ) - 1/2 := by
      by_contra! hn
      rw [hm, Nat.floor_of_nonpos hn.le] at hm₁
      omega
    rw [hm]
    exact Nat.floor_le hn
  have hcut : 2*θ*(2*(m : ℝ)+1) ≤ A := by
    have h := (le_div_iff₀ (show 0 < 4*θ by positivity)).1
      (show (m : ℝ) + 1/2 ≤ A/(4*θ) by linarith)
    linarith
  apply antitoneOn_of_succ_le (Set.ordConnected_Iic)
  intro j _ _ hj
  have hj' : (j : ℝ) + 1 ≤ m := by exact_mod_cast (show j + 1 ≤ m from hj)
  have hpos : 0 < likelihoodRatio a (θ*a^2/A) j := by
    exact div_pos (poissonMass_pos (by positivity) _)
      (add_pos (poissonMass_pos ha _) (poissonMass_pos ha _))
  apply (div_le_one hpos).1
  refine (likelihoodRatio_step_le ha hA hθ j).trans ((div_le_one hA).2 ?_)
  nlinarith [mul_nonneg (sub_nonneg.mpr hj') hθ.le]

/-- Poisson upper tail starting at K, indexed by its excess over K. -/
def poissonTail (a : ℝ) (K : ℕ) := ∑' n : ℕ, poissonMass a (K+n)

theorem poissonTail_eq (a : ℝ≥0) (K : ℕ) :
    poissonTail a K = (poissonMeasure a).real (Set.Ici K) := by
  have he : (Set.Ici K : Set ℕ) = ⋃ n : ℕ, {K+n} := by
    ext i
    simp only [Set.mem_Ici, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · intro hi; exact ⟨i - K, by omega⟩
    · rintro ⟨n,rfl⟩; omega
  rw [he, measureReal_def, measure_iUnion]
  · simp only [poissonMeasure_singleton, poissonTail, poissonMass]
    rw [ENNReal.tsum_toReal_eq]
    · apply tsum_congr
      intro n
      exact (ENNReal.toReal_ofReal (by positivity)).symm
    · intro n; exact ENNReal.ofReal_ne_top
  · intro i j hij
    simpa using hij
  · exact fun _ ↦ measurableSet_singleton _

/-- P2, including K=0 and rate zero. -/
theorem poissonTail_le {a : ℝ} (ha : 0 ≤ a) (K : ℕ) :
    poissonTail a K ≤ a^K / K.factorial := by
  have hp : HasSum (poissonMass a) 1 := hasSum_one_poissonMeasure ⟨a, ha⟩
  have hb := hp.mul_left (a^K / K.factorial)
  rw [← mul_one (a^K / K.factorial), ← hb.tsum_eq]
  have htail : Summable (fun n ↦ poissonMass a (K+n)) := by
    simpa only [Nat.add_comm K] using (summable_nat_add_iff K).2 hp.summable
  apply Summable.tsum_le_tsum _ htail hb.summable
  intro n
  have hfac : (K.factorial : ℝ) * n.factorial ≤ (K+n).factorial := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add K n)
  dsimp [poissonMass]
  rw [pow_add]
  field_simp
  nlinarith only [mul_nonneg (show 0 ≤ a^K * a^n by positivity)
    (sub_nonneg.mpr hfac)]

/-- The unrelaxed finite-coset bound of Lemma 4.3b. K is n+1, so 2K-1 is 2n+1. -/
theorem sum_poissonTails_le {C : Type*} (T : Finset C) (a b : C → ℝ) {A θ : ℝ}
    (ha : ∀ c ∈ T, 0 ≤ a c) (hb : ∀ c ∈ T, 0 ≤ b c)
    (haA : ∀ c ∈ T, a c ≤ A) (hbA : ∀ c ∈ T, b c ≤ θ*A) (n : ℕ) :
    (∑ c ∈ T, (poissonTail (b c) (n+1) + poissonTail (a c) (2*n+2))) ≤
      (∑ c ∈ T, b c) * ((θ*A)^n / (n+1).factorial) +
      (∑ c ∈ T, a c) * (A^(2*n+1) / (2*n+2).factorial) := by
  rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
  apply add_le_add <;> apply Finset.sum_le_sum <;> intro c hc
  · refine (poissonTail_le (hb c hc) _).trans ?_
    rw [pow_succ, mul_div_assoc', mul_comm]
    gcongr
    exacts [hb c hc, hb c hc, hbA c hc]
  · refine (poissonTail_le (ha c hc) _).trans ?_
    rw [show 2*n+2 = (2*n+1)+1 by omega, pow_succ, mul_div_assoc', mul_comm]
    gcongr
    exacts [ha c hc, ha c hc, haA c hc]

/-- One exponential-series term bounds both factorial coefficients of §4.3b. -/
private theorem factorial_coefficient_le {u C d : ℝ} (hu : 0 ≤ u) (hC : 0 ≤ C) (hd : 0 ≤ d)
    (n : ℕ) (h : u ≤ C * (n + 1 + d)) :
    u^n / (n+1).factorial ≤ exp (1+d) * (C * exp 1)^n / (n+1) := by
  let x : ℝ := n + 1 + d
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have h₁ : u^n ≤ C^n * x^n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hu h _
  have h₂ := Real.pow_div_factorial_le_exp x hx (n+1)
  have h₃ : ((n : ℝ)+1) * (u^n / (n+1).factorial) ≤ C^n * exp x := by
    calc _ ≤ x * (C^n * x^n / (n+1).factorial) := by
           gcongr
           exact le_add_of_nonneg_right hd
         _ = C^n * (x^(n+1) / (n+1).factorial) := by rw [pow_succ]; ring
         _ ≤ _ := by gcongr
  apply (le_div_iff₀ (by positivity)).2
  have he : exp x = exp (1+d) * exp 1 ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    dsimp [x]; ring
  rw [he] at h₃
  rw [mul_pow]
  linarith

/-- The two explicit exponential coefficients g₁(K), g₂(K) in Lemma 4.3b, with K=n+1. -/
theorem poisson_tail_coefficients {A θ : ℝ} (hA : 0 ≤ A) (hθ : 0 ≤ θ) (n : ℕ)
    (hcut : A ≤ 4*θ*((n : ℝ)+1+1/2)) :
    (θ*A)^n / (n+1).factorial ≤ exp (3/2) * (4*exp 1*θ^2)^n / (n+1) ∧
    A^(2*n+1) / (2*n+2).factorial ≤ exp 2 * (2*exp 1*θ)^(2*n+1) / (2*n+2) := by
  constructor
  · have h := factorial_coefficient_le (u := θ*A) (C := 4*θ^2) (d := 1/2)
      (by positivity) (by positivity) (by norm_num) n (by nlinarith [mul_le_mul_of_nonneg_left hcut hθ])
    convert h using 1; ring_nf
  · have h := factorial_coefficient_le (u := A) (C := 2*θ) (d := 1) hA
      (by positivity) (by norm_num) (2*n+1) (by push_cast; linarith)
    convert h using 1; push_cast; ring_nf

/-- Combined finite-coset tail bound of Lemma 4.3b(3), with K=n+1. -/
theorem sum_poissonTails_explicit {C : Type*} (T : Finset C) (a b : C → ℝ) {A θ : ℝ}
    (hA : 0 ≤ A) (hθ : 0 ≤ θ) (ha : ∀ c ∈ T, 0 ≤ a c) (hb : ∀ c ∈ T, 0 ≤ b c)
    (haA : ∀ c ∈ T, a c ≤ A) (hbA : ∀ c ∈ T, b c ≤ θ*A) (n : ℕ)
    (hcut : A ≤ 4*θ*((n : ℝ)+1+1/2)) :
    (∑ c ∈ T, (poissonTail (b c) (n+1) + poissonTail (a c) (2*n+2))) ≤
      (∑ c ∈ T, b c) * (exp (3/2) * (4*exp 1*θ^2)^n / (n+1)) +
      (∑ c ∈ T, a c) * (exp 2 * (2*exp 1*θ)^(2*n+1) / (2*n+2)) := by
  apply (sum_poissonTails_le T a b ha hb haA hbA n).trans
  obtain ⟨h₁,h₂⟩ := poisson_tail_coefficients hA hθ n hcut
  exact add_le_add (mul_le_mul_of_nonneg_left h₁ (Finset.sum_nonneg hb))
    (mul_le_mul_of_nonneg_left h₂ (Finset.sum_nonneg ha))

end SigabaNeo.Wall1.ADRS

#print axioms SigabaNeo.Wall1.ADRS.poissonMass_eq
#print axioms SigabaNeo.Wall1.ADRS.halfMass_eq
#print axioms SigabaNeo.Wall1.ADRS.halfMass_factor
#print axioms SigabaNeo.Wall1.ADRS.likelihoodRatio_step
#print axioms SigabaNeo.Wall1.ADRS.likelihoodRatio_step_le
#print axioms SigabaNeo.Wall1.ADRS.likelihoodRatio_antitone
#print axioms SigabaNeo.Wall1.ADRS.poissonTail_le
#print axioms SigabaNeo.Wall1.ADRS.sum_poissonTails_le
#print axioms SigabaNeo.Wall1.ADRS.poissonTail_eq
#print axioms SigabaNeo.Wall1.ADRS.poisson_tail_coefficients
#print axioms SigabaNeo.Wall1.ADRS.sum_poissonTails_explicit
