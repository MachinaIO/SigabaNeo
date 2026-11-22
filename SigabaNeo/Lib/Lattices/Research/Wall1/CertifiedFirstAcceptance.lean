module

public import SigabaNeo.Lib.Lattices.Research.Wall1.MonteCarloCertificate
public import SigabaNeo.Lib.Lattices.Research.Wall1.SharedDesignExhaustion
import Mathlib.Tactic

/-! # Error of the first Monte Carlo acceptance (Part 136, Theorem 1(a))

Condition on the designs and reducer coins for all trials. Each trial receives its own block of
M fresh simulated plants. The decoder uses the single independent true plant. The outer
expectation permits arbitrary correlations among the designs and reducer coins. -/

@[expose] public section
noncomputable section
namespace SigabaNeo.Wall1.RestartCertificate

open Classical MultiBlock PlantBlindRestart

variable {P H : Type*} [Fintype P] [Fintype H] {T M : ℕ}

/-- The coordinates of the batch assigned to trial i. -/
def batch (i : Fin T) (j : Fin M) := (i,j)

private theorem batch_inj : Function.Injective
    (fun q : (Σ _ : Fin T, Fin M) ↦ batch q.1 q.2) := by
  rintro ⟨i,j⟩ ⟨i',j'⟩ h
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
  rfl

def passes (F : Fin T → P → Prop) (k : ℕ) (i : Fin T) (x : Fin M → P) :=
  countFailures (F i) x ≤ k

/-- Probability that trial i is reached, conditional on the designs and reducer coins. -/
def reach (ρ : P → ℚ) (F : Fin T → P → Prop) (M k : ℕ) (i : Fin T) :=
  ∏ j ∈ Finset.univ.filter (· < i), (1-certAccept ρ (F j) M k)

def noAcceptance (ρ : P → ℚ) (F : Fin T → P → Prop) (M k : ℕ) :=
  ∏ i, (1-certAccept ρ (F i) M k)

/-- Number of tests performed on a full vector of simulated plants, including the last test. -/
def testsRun (F : Fin T → P → Prop) (k : ℕ) (x : (Fin T × Fin M) → P) : ℚ :=
  ∑ i, if ∀ j < i, ¬ passes F k j (fun m ↦ x (j,m)) then 1 else 0

private theorem reject_eq (ρ : P → ℚ) (hρ : ∑ p, ρ p = 1)
    (F : Fin T → P → Prop) (M k : ℕ) (i : Fin T) :
    rejectProb ρ (passes (M := M) F k) i = 1 - certAccept ρ (F i) M k := by
  apply eq_sub_of_add_eq
  apply Eq.trans _ (product_mass ρ hρ M)
  rw [rejectProb, certAccept, expect, expect, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ ↦ by
    by_cases h : countFailures (F i) x ≤ k <;> simp [passes, h]

private theorem accept_eq (ρ : P → ℚ) (F : Fin T → P → Prop) (M k : ℕ) (i : Fin T) :
    acceptProb ρ (passes (M := M) F k) i = certAccept ρ (F i) M k := by
  unfold acceptProb certAccept passes
  congr 1
  funext x
  by_cases h : countFailures (F i) x ≤ k <;> simp [h]

private theorem accepted_risk (ρ : P → ℚ) (F : Fin T → P → Prop) (M k : ℕ) (i : Fin T) :
    acceptFail ρ ρ (passes (M := M) F k) (fun j p _ ↦ F j p) i =
      certAccept ρ (F i) M k * plantProb ρ (F i) := by
  rw [acceptFail, certAccept, expect, expect, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : countFailures (F i) x ≤ k <;> simp [passes,h]

/-- Exact exhaustion law for independent blocks, even before drawing the true plant. -/
theorem disjoint_exhaustion {Y I K : Type*} [Fintype Y] [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K] {r : K → ℕ} (b : ∀ i, Fin (r i) → I)
    (hb : Function.Injective (fun q : (Σ i, Fin (r i)) ↦ b q.1 q.2)) (w : Y → ℚ)
    (hw : ∑ y, w y = 1) (acc : ∀ i, (Fin (r i) → Y) → Prop) :
    expect w (fun x : I → Y ↦ if ∀ i, ¬ acc i (fun j ↦ x (b i j)) then 1 else 0) =
      ∏ i, expect w (fun x ↦ if ¬ acc i x then 1 else 0) := by
  have h := block_product b hb w hw (fun i x ↦ if ¬ acc i x then 1 else 0)
  convert h using 2
  funext x
  rw [Fintype.prod_boole]

theorem noAcceptance_eq (ρ : P → ℚ) (hρ : ∑ p, ρ p = 1) (F : Fin T → P → Prop) (M k : ℕ) :
    expect ρ (fun x : (Fin T × Fin M) → P ↦
      if ∀ i, ¬ passes F k i (fun j ↦ x (i,j)) then 1 else 0) = noAcceptance ρ F M k := by
  have h := disjoint_exhaustion batch batch_inj ρ hρ (passes (M := M) F k)
  change _ = ∏ i, rejectProb ρ (passes (M := M) F k) i at h
  simp_rw [reject_eq ρ hρ F M k] at h
  refine Eq.trans ?_ h
  congr 1
  funext x
  by_cases hx : ∀ i, ¬ passes F k i (fun j ↦ x (i,j)) <;> simp [batch, hx]

/-- Derivation of the tail-sum formula for the expected capped number of trials. -/
theorem expected_tests (ρ : P → ℚ) (hρ : ∑ p, ρ p = 1) (F : Fin T → P → Prop) (M k : ℕ) :
    expect ρ (testsRun (M := M) F k) = ∑ i, reach ρ F M k i := by
  have one : expect ρ (fun _ : Fin M → P ↦ (1:ℚ)) = 1 := by
    simpa [expect] using product_mass ρ hρ M
  have atTrial (i : Fin T) :
      expect ρ (fun x : (Fin T × Fin M) → P ↦
        if ∀ j < i, ¬ passes F k j (fun m ↦ x (j,m)) then 1 else 0) = reach ρ F M k i := by
    let G (j : Fin T) (y : Fin M → P) : ℚ :=
      if j < i then (if ¬ passes F k j y then 1 else 0) else 1
    have h := block_product batch batch_inj ρ hρ G
    have hleft (x : (Fin T × Fin M) → P) :
        (∏ j, G j (fun m ↦ x (batch j m))) =
          if ∀ j < i, ¬ passes F k j (fun m ↦ x (j,m)) then 1 else 0 := by
      unfold G
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_boole]
      simp only [batch, Finset.mem_filter, Finset.mem_univ, true_and]

    have hright (j : Fin T) : expect ρ (G j) = if j < i then 1-certAccept ρ (F j) M k else 1 := by
      by_cases hj : j < i
      · simpa [G, hj, rejectProb] using reject_eq ρ hρ F M k j
      · simpa [G, hj] using one
    simpa only [hleft, hright, Finset.prod_ite, Finset.prod_const_one, mul_one, reach] using h
  simp only [expect, testsRun, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ atTrial i

/-- Failure occurs on exhaustion, or on failure at the first passing index. -/
theorem first_failure_exact (ρ : P → ℚ) (hρ : ∑ p, ρ p = 1) (F : Fin T → P → Prop) (M k : ℕ) :
    failProb ρ ρ (passes (M := M) F k) (fun i p _ ↦ F i p) batch =
      noAcceptance ρ F M k +
        ∑ i, reach ρ F M k i * (certAccept ρ (F i) M k * plantProb ρ (F i)) := by
  simpa only [reach, noAcceptance, reject_eq ρ hρ, accepted_risk] using
    failProb_eq hρ hρ (passes (M := M) F k) (fun i p _ ↦ F i p) batch batch_inj

private theorem reach_mem (ρ : P → ℚ) (hρ : ∑ p, ρ p = 1) (hρ0 : ∀ p, 0 ≤ ρ p)
    (F : Fin T → P → Prop) (M k : ℕ) (i : Fin T) : reach ρ F M k i ∈ Set.Icc 0 1 := by
  have h j := certAccept_mem ρ hρ hρ0 (F j) M k
  exact ⟨Finset.prod_nonneg fun j _ ↦ sub_nonneg.mpr (h j).2,
    Finset.prod_le_one₀ (fun j _ ↦ sub_nonneg.mpr (h j).2) (fun j _ ↦ by linarith [(h j).1])⟩

/-- First-acceptance soundness for a fixed design and coin history, with any valid upper bound
B on false acceptance. The hypothesis is supplied by `certificate_false_accept`. -/
theorem first_failure_bound (ρ : P → ℚ) (hρ : ∑ p, ρ p = 1) (hρ0 : ∀ p, 0 ≤ ρ p)
    (F : Fin T → P → Prop) (M k : ℕ) {θ B : ℚ} (hθ : 0 ≤ θ) (hB : 0 ≤ B)
    (hbad : ∀ i, θ < plantProb ρ (F i) → certAccept ρ (F i) M k ≤ B) :
    failProb ρ ρ (passes (M := M) F k) (fun i p _ ↦ F i p) batch ≤
      noAcceptance ρ F M k + θ + B * expect ρ (testsRun (M := M) F k) := by
  have part := partition hρ (passes (M := M) F k) batch batch_inj
  simp only [reject_eq ρ hρ, accept_eq] at part
  change ∑ i, reach ρ F M k i * certAccept ρ (F i) M k = 1-noAcceptance ρ F M k at part
  have hnone : 0 ≤ noAcceptance ρ F M k :=
    Finset.prod_nonneg fun i _ ↦ sub_nonneg.mpr (certAccept_mem ρ hρ hρ0 (F i) M k).2
  have upper (i : Fin T) : certAccept ρ (F i) M k * plantProb ρ (F i) ≤
      θ * certAccept ρ (F i) M k + B := by
    have ha := (certAccept_mem ρ hρ hρ0 (F i) M k).1
    by_cases hi : plantProb ρ (F i) ≤ θ
    · nlinarith [mul_le_mul_of_nonneg_left hi ha]
    · have hf : plantProb ρ (F i) ≤ 1 := by
        apply LE.le.trans _ hρ.le
        exact Finset.sum_le_sum fun p _ ↦ mul_le_of_le_one_right (hρ0 p) (by split_ifs <;> norm_num)
      linarith [mul_le_of_le_one_right ha hf, hbad i (lt_of_not_ge hi), mul_nonneg hθ ha]
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦
    mul_le_mul_of_nonneg_left (upper i) (reach_mem ρ hρ hρ0 F M k i).1
  have algebra (i : Fin T) : reach ρ F M k i * (θ * certAccept ρ (F i) M k + B) =
      θ * (reach ρ F M k i * certAccept ρ (F i) M k) + B * reach ρ F M k i := by ring
  simp only [algebra, Finset.sum_add_distrib, ← Finset.mul_sum, part] at hs
  rw [first_failure_exact ρ hρ, expected_tests ρ hρ]
  linarith [mul_nonneg hθ hnone]

/-- Theorem 1(a), averaged over design/coin histories, with an explicit lower-tail Chernoff B.
The two conclusions give the expected-cost budget and its deterministic-cap relaxation. -/
theorem monteCarlo_restart_sound (w : H → ℚ) (hw : ∑ h, w h = 1) (hw0 : ∀ h, 0 ≤ w h)
    (ρ : P → ℚ) (hρ : ∑ p, ρ p = 1) (hρ0 : ∀ p, 0 ≤ ρ p) (F : H → Fin T → P → Prop)
    (M k : ℕ) {θ z : ℚ} (hθ : θ ∈ Set.Icc 0 1) (hz : 0 < z) (hz1 : z ≤ 1) :
    let B := (1 + θ*(z-1))^M / z^k
    let failure := ∑ h, w h * failProb ρ ρ (passes (M := M) (F h) k) (fun i p _ ↦ F h i p) batch
    let exhausted := ∑ h, w h * noAcceptance ρ (F h) M k
    let run := ∑ h, w h * expect ρ (testsRun (M := M) (F h) k)
    failure ≤ exhausted + θ + B*run ∧ exhausted + θ + B*run ≤ exhausted + θ + B*T := by
  intro B failure exhausted run
  have hbase : 0 ≤ 1 + θ*(z-1) := by nlinarith [mul_nonneg hθ.1 hz.le, hθ.2]
  have hB : 0 ≤ B := div_nonneg (pow_nonneg hbase _) (pow_nonneg hz.le _)
  constructor
  · have hbound (h : H) := first_failure_bound ρ hρ hρ0 (F h) M k hθ.1 hB
          (fun i hi ↦ certificate_false_accept ρ hρ hρ0 (F h i) M k hi.le hz hz1)
    have hs := Finset.sum_le_sum (s := Finset.univ) fun h _ ↦
      mul_le_mul_of_nonneg_left (hbound h) (hw0 h)
    have rearrange (h : H) : w h * (B * expect ρ (testsRun (M := M) (F h) k)) =
        B * (w h * expect ρ (testsRun (M := M) (F h) k)) := by ring
    simpa only [failure, exhausted, run, mul_add, rearrange, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, hw, one_mul] using hs
  · have hcap (h : H) : expect ρ (testsRun (M := M) (F h) k) ≤ T := by
      rw [expected_tests ρ hρ]
      simpa using Finset.sum_le_sum (s := Finset.univ) fun i _ ↦
        (reach_mem ρ hρ hρ0 (F h) M k i).2
    have hrun : run ≤ T := by
      have hs := Finset.sum_le_sum (s := Finset.univ) fun h _ ↦
        mul_le_mul_of_nonneg_left (hcap h) (hw0 h)
      simpa only [run, ← Finset.sum_mul, hw, one_mul] using hs
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hrun hB)

/-- One trial draws reducer coins and a fresh iid plant batch independently. -/
def trialWeight {C : Type*} (v : C → ℚ) (ρ : P → ℚ) (u : C × (Fin M → P)) : ℚ :=
  v u.1 * ∏ j, ρ (u.2 j)

/-- Shared-design exhaustion specialized to the actual Monte Carlo test. Its α is the
coin-average of the conditional certificate acceptance probabilities in `design_complete`. -/
theorem certified_shared_exhaustion {D C : Type*} [Fintype D] [Fintype C] (w : D → ℝ)
    (v : D → C → ℚ) (hv : ∀ a, ∑ c, v a c = 1) (ρ : P → ℚ) (hρ : ∑ p, ρ p = 1)
    (F : D → C → P → Prop) (M k T : ℕ) :
    (∑ a, w a * (expect (trialWeight (v a) ρ) (fun u : Fin T → C × (Fin M → P) ↦
      if ∀ i, ¬ countFailures (F a (u i).1) (u i).2 ≤ k then 1 else 0) : ℚ)) =
      exhaustion w (fun a ↦ ((∑ c, v a c * certAccept ρ (F a c) M k : ℚ) : ℝ)) T := by
  let acc (a : D) (u : C × (Fin M → P)) := countFailures (F a u.1) u.2 ≤ k
  have mass a : ∑ u : C × (Fin M → P), trialWeight (v a) ρ u = 1 := by
    simp only [Fintype.sum_prod_type, trialWeight, ← Finset.mul_sum, product_mass ρ hρ, mul_one, hv]
  have single a : plantProb (trialWeight (v a) ρ) (acc a) =
      ∑ c, v a c * certAccept ρ (F a c) M k := by
    simp only [plantProb, Fintype.sum_prod_type, trialWeight, acc, certAccept, expect, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases h : countFailures (F a c) x ≤ k <;> simp [h]
  have h := shared_exhaustion w (fun a ↦ trialWeight (v a) ρ) mass acc T
  simp only [single] at h
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  congr 3
  funext u
  by_cases he : ∀ i, ¬ countFailures (F a (u i).1) (u i).2 ≤ k <;> simp [acc, he]

end SigabaNeo.Wall1.RestartCertificate

#print axioms SigabaNeo.Wall1.RestartCertificate.disjoint_exhaustion
#print axioms SigabaNeo.Wall1.RestartCertificate.noAcceptance_eq
#print axioms SigabaNeo.Wall1.RestartCertificate.certified_shared_exhaustion
#print axioms SigabaNeo.Wall1.RestartCertificate.expected_tests
#print axioms SigabaNeo.Wall1.RestartCertificate.first_failure_exact
#print axioms SigabaNeo.Wall1.RestartCertificate.first_failure_bound
#print axioms SigabaNeo.Wall1.RestartCertificate.monteCarlo_restart_sound
