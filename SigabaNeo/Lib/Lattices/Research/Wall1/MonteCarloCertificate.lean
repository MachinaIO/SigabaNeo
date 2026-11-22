module

public import SigabaNeo.Lib.Lattices.Research.Wall1.RestartReduction
public import SigabaNeo.Lib.Lattices.Research.Wall1.StatDistance
import Mathlib.Tactic

/-! # Plant-blind Monte Carlo certification (Part 136, Theorem 1)

The true plant is an independent factor of the transcript law. The transcript may contain
designs, reducer coins and all simulated plants. At fixed design and reducer coins, the same
failure predicate is tested on each of the independent copies of the plant. -/

@[expose] public section
noncomputable section

namespace SigabaNeo.Wall1.RestartCertificate

open Classical MultiBlock PlantBlindRestart

variable {H P D C : Type*} [Fintype H] [Fintype P] [Fintype C]

/-- Joint probability of any transcript statistic and any true-plant event factors. The
statistic can return the stopping decision together with the accepted design and its coins. -/
theorem plant_independent_statistic {S : Type*} (w : H → ℚ) (ρ : P → ℚ) (stat : H → S)
    (event : S → Prop) (E : P → Prop) :
    plantProb (fun h : H × P ↦ w h.1 * ρ h.2) (fun h ↦ event (stat h.1) ∧ E h.2) =
      plantProb w (fun h ↦ event (stat h)) * plantProb ρ E := by
  simp only [plantProb, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro h _
  by_cases hs : event (stat h) <;> by_cases hp : E p <;> simp [hs, hp]

/-- The full joint law of a selected transcript value and the true plant. A statistic with
values in `Option D` can record exhaustion as well as the accepted design. -/
theorem selected_design_law {S : Type*} (w : H → ℝ) (ρ : P → ℝ) (stat : H → S) (s : S) (p : P) :
    push (fun h : H × P ↦ (stat h.1, h.2)) (fun h ↦ w h.1 * ρ h.2) (s, p) =
      push stat w s * ρ p := by
  simp only [push, tsum_fintype, Fintype.sum_prod_type, Prod.mk.injEq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hs : stat h = s <;> simp [hs]

/-- Joint selected-trial failure is the integral of the fresh-plant risk against the selected
transcript law. This identity includes selectors that inspect the entire simulated history. -/
theorem selected_failure (w : H → ℚ) (ρ : P → ℚ) (accept : H → Prop) (design : H → D)
    (fail : D → P → Prop) :
    plantProb (fun h : H × P ↦ w h.1 * ρ h.2)
        (fun h ↦ accept h.1 ∧ fail (design h.1) h.2) =
      ∑ h, (if accept h then w h else 0) * plantProb ρ (fail (design h)) := by
  simp only [plantProb, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro p _
  by_cases ha : accept h <;> by_cases hf : fail (design h) p <;> simp [ha, hf]

/-- Conditional risk given acceptance is an average of the unmodified risks, with the
conditional distribution of the accepted design. -/
theorem conditional_selected_failure (w : H → ℚ) (ρ : P → ℚ) (accept : H → Prop)
    (design : H → D) (fail : D → P → Prop) (_h : 0 < plantProb w accept) :
    plantProb (fun h : H × P ↦ w h.1 * ρ h.2) (fun h ↦ accept h.1 ∧ fail (design h.1) h.2) /
        plantProb w accept =
      ∑ h, ((if accept h then w h else 0) / plantProb w accept) * plantProb ρ (fail (design h)) := by
  rw [selected_failure, Finset.sum_div]
  exact Finset.sum_congr rfl fun h _ ↦ by ring

/-- On every positive-mass fiber of the stopped design and coins, the decoder has exactly
the risk computed from a fresh plant at that output. -/
theorem conditional_fiber_risk (w : H → ℚ) (ρ : P → ℚ) (select : H → Option D)
    (fail : D → P → Prop) (d : D) (hd : 0 < plantProb w (fun h ↦ select h = some d)) :
    plantProb (fun h : H × P ↦ w h.1 * ρ h.2)
        (fun h ↦ select h.1 = some d ∧ fail d h.2) / plantProb w (fun h ↦ select h = some d) =
      plantProb ρ (fail d) := by
  rw [plant_independent_statistic w ρ select (· = some d) (fail d)]
  exact mul_div_cancel_left₀ _ hd.ne'

/-- Number of failed tests on the simulated plants. -/
def countFailures {M : ℕ} (F : P → Prop) (x : Fin M → P) : ℕ :=
  ∑ i, if F (x i) then 1 else 0

/-- Probability that the certificate accepts a fixed output. -/
def certAccept (ρ : P → ℚ) (F : P → Prop) (M k : ℕ) : ℚ :=
  expect ρ fun x : Fin M → P ↦ if countFailures F x ≤ k then 1 else 0

theorem product_mass (ρ : P → ℚ) (hρ : ∑ p, ρ p = 1) (M : ℕ) :
    ∑ x : Fin M → P, ∏ i, ρ (x i) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : Fin M) p ↦ ρ p), hρ, Finset.prod_const_one]

theorem certAccept_mem (ρ : P → ℚ) (hρ : ∑ p, ρ p = 1) (hρ0 : ∀ p, 0 ≤ ρ p)
    (F : P → Prop) (M k : ℕ) : certAccept ρ F M k ∈ Set.Icc 0 1 := by
  unfold certAccept expect
  dsimp only
  constructor
  · exact Finset.sum_nonneg fun x _ ↦ mul_nonneg (Finset.prod_nonneg fun i _ ↦ hρ0 (x i))
      (by split_ifs <;> norm_num)
  · apply LE.le.trans _ (product_mass ρ hρ M).le
    exact Finset.sum_le_sum fun x _ ↦ mul_le_of_le_one_right
      (Finset.prod_nonneg fun i _ ↦ hρ0 (x i)) (by split_ifs <;> norm_num)

/-- Exact probability generating function of the simulated count, the binomial PGF. -/
theorem count_pgf (ρ : P → ℚ) (hρ : ∑ p, ρ p = 1) (F : P → Prop) (M : ℕ) (z : ℚ) :
    expect ρ (fun x : Fin M → P ↦ z ^ countFailures F x) =
      (1 + plantProb ρ F * (z - 1)) ^ M := by
  have step : (∑ p, ρ p * z ^ (if F p then 1 else 0 : ℕ)) = 1 + plantProb ρ F * (z-1) := by
    rw [plantProb, Finset.sum_mul]
    conv_rhs => lhs; rw [← hρ]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    by_cases hp : F p
    · simp [hp]
      ring
    · simp [hp]
  simp only [expect, countFailures, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin M) p ↦ ρ p * z ^ (if F p then 1 else 0 : ℕ))]
  simp only [step, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Exponential Markov bound for an event in the simulated experiment. -/
private theorem chernoff (ρ : P → ℚ) (hρ : ∑ p, ρ p = 1) (hρ0 : ∀ p, 0 ≤ ρ p)
    (F : P → Prop) (M : ℕ) (E : (Fin M → P) → Prop) [DecidablePred E] {z c : ℚ} (hz : 0 ≤ z) (hc : 0 < c)
    (hE : ∀ x, E x → c ≤ z ^ countFailures F x) :
    expect ρ (fun x ↦ if E x then 1 else 0) ≤ (1 + plantProb ρ F * (z-1))^M / c := by
  apply (le_div_iff₀ hc).2
  rw [← count_pgf ρ hρ F M z, expect, Finset.sum_mul, expect]
  refine Finset.sum_le_sum fun x _ ↦ ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun i _ ↦ hρ0 (x i))
  by_cases hx : E x
  · simpa [hx] using hE x hx
  · simp [hx, pow_nonneg hz]

/-- Completeness at a good design. Every rational tilt above one gives a Chernoff bound
on false rejection at the integer threshold k+1. -/
theorem certificate_complete (ρ : P → ℚ) (hρ : ∑ p, ρ p = 1) (hρ0 : ∀ p, 0 ≤ ρ p)
    (F : P → Prop) (M k : ℕ) {θ z : ℚ} (hg : plantProb ρ F ≤ θ) (hz : 1 < z) :
    1 - (1 + θ * (z-1))^M / z^(k+1) ≤ certAccept ρ F M k := by
  have h := chernoff ρ hρ hρ0 F M (fun x ↦ k < countFailures F x)
    (z := z) (c := z^(k+1)) (by linarith) (by positivity)
    (fun x hx ↦ pow_le_pow_right₀ hz.le hx)
  have hp : 0 ≤ plantProb ρ F := Finset.sum_nonneg fun p _ ↦ mul_nonneg (hρ0 p)
    (by split_ifs <;> norm_num)
  have hbase : 0 ≤ 1 + plantProb ρ F * (z - 1) := by nlinarith
  have hle := pow_le_pow_left₀ hbase
    (show 1 + plantProb ρ F * (z-1) ≤ 1 + θ * (z-1) by nlinarith) M
  have hsum : certAccept ρ F M k +
      expect ρ (fun x : Fin M → P ↦ if k < countFailures F x then 1 else 0) = 1 := by
    apply Eq.trans _ (product_mass ρ hρ M)
    rw [certAccept, expect, expect, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ ↦ by
      by_cases hx : countFailures F x ≤ k
      · simp [hx, not_lt_of_ge hx]
      · simp [hx, lt_of_not_ge hx]
  have hrej := h.trans (div_le_div_of_nonneg_right hle (by positivity))
  exact (sub_le_iff_le_add).2 (hsum.symm.le.trans (add_le_add le_rfl hrej))

/-- False acceptance at a bad design. Tilts strictly between zero and one bound the lower tail. -/
theorem certificate_false_accept (ρ : P → ℚ) (hρ : ∑ p, ρ p = 1) (hρ0 : ∀ p, 0 ≤ ρ p)
    (F : P → Prop) (M k : ℕ) {θ z : ℚ} (hb : θ ≤ plantProb ρ F) (hz : 0 < z) (hz1 : z ≤ 1) :
    certAccept ρ F M k ≤ (1 + θ * (z-1))^M / z^k := by
  have h := chernoff ρ hρ hρ0 F M (fun x ↦ countFailures F x ≤ k) hz.le
    (pow_pos hz k) (fun x hx ↦ pow_le_pow_of_le_one hz.le hz1 hx)
  have hp : plantProb ρ F ≤ 1 := by
    rw [← hρ]
    exact Finset.sum_le_sum fun p _ ↦ mul_le_of_le_one_right (hρ0 p) (by split_ifs <;> norm_num)
  have hbase : 0 ≤ 1 + plantProb ρ F * (z - 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hz1)]
  exact h.trans (div_le_div_of_nonneg_right
    (pow_le_pow_left₀ hbase (by nlinarith : 1 + plantProb ρ F * (z-1) ≤ 1 + θ * (z-1)) M)
    (pow_nonneg hz.le k))

/-- Averaging completeness over reducer coins gives the one-sided guarantee on α(A). -/
theorem design_complete (v : C → ℚ) (hv : ∀ c, 0 ≤ v c) (ρ : P → ℚ)
    (hρ : ∑ p, ρ p = 1) (hρ0 : ∀ p, 0 ≤ ρ p) (F : C → P → Prop) (M k : ℕ)
    {θ z : ℚ} (hz : 1 < z) :
    (1 - (1 + θ * (z-1))^M / z^(k+1)) * plantProb v (fun c ↦ plantProb ρ (F c) ≤ θ) ≤
      ∑ c, v c * certAccept ρ (F c) M k := by
  rw [plantProb, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  by_cases h : plantProb ρ (F c) ≤ θ
  · simpa [h, mul_comm] using mul_le_mul_of_nonneg_left
      (certificate_complete ρ hρ hρ0 (F c) M k h hz) (hv c)
  · simpa [h] using mul_nonneg (hv c) (certAccept_mem ρ hρ hρ0 (F c) M k).1

end SigabaNeo.Wall1.RestartCertificate

#print axioms SigabaNeo.Wall1.RestartCertificate.plant_independent_statistic
#print axioms SigabaNeo.Wall1.RestartCertificate.selected_design_law
#print axioms SigabaNeo.Wall1.RestartCertificate.selected_failure
#print axioms SigabaNeo.Wall1.RestartCertificate.conditional_selected_failure
#print axioms SigabaNeo.Wall1.RestartCertificate.conditional_fiber_risk
#print axioms SigabaNeo.Wall1.RestartCertificate.count_pgf
#print axioms SigabaNeo.Wall1.RestartCertificate.certificate_complete
#print axioms SigabaNeo.Wall1.RestartCertificate.certificate_false_accept
#print axioms SigabaNeo.Wall1.RestartCertificate.design_complete
