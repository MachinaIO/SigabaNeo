module

public import SigabaNeo.Lib.Lattices.Research.Wall1.PlantBlindRestart
public import SigabaNeo.Lib.Lattices.Research.Wall1.CBDPaleyZygmund
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Shared-design exhaustion (Part 136, Theorems 1(b), 2 and Proposition 7)

The coin type can include an entire vector of fresh simulated plants. Conditional on a design,
trials are independent. All design-level results allow arbitrary finite nonuniform laws. -/

@[expose] public section
noncomputable section

namespace SigabaNeo.Wall1.RestartCertificate

open Classical PlantBlindRestart MultiBlock Filter
open scoped Topology

variable {D C : Type*} [Fintype D] [Fintype C]

/-- The mixture of conditional probabilities of exhausting the trial budget. -/
def exhaustion (w α : D → ℝ) (T : ℕ) := ∑ a, w a * (1 - α a)^T

/-- Product rule for the event that all independent draws satisfy the same predicate. -/
theorem iid_all (v : C → ℚ) (pass : C → Prop) (T : ℕ) :
    expect v (fun x : Fin T → C ↦ if ∀ i, pass (x i) then 1 else 0) = (plantProb v pass)^T := by
  have e (x : Fin T → C) : (if ∀ i, pass (x i) then (1:ℚ) else 0) =
      ∏ i, if pass (x i) then 1 else 0 := by
    rw [Fintype.prod_boole]
    by_cases h : ∀ i, pass (x i) <;> simp [h]
  simp only [expect, e, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin T) c ↦ v c * (if pass c then 1 else 0))]
  simp only [plantProb, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Exact exhaustion probability derived from the event of rejecting every independent coin
draw. The conditional coin law may vary with the shared design. -/
theorem shared_exhaustion (w : D → ℝ) (v : D → C → ℚ) (hv : ∀ a, ∑ c, v a c = 1)
    (accept : D → C → Prop) (T : ℕ) :
    (∑ a, w a * (expect (v a) (fun x : Fin T → C ↦ if ∀ i, ¬ accept a (x i) then 1 else 0) : ℚ)) =
      exhaustion w (fun a ↦ (plantProb (v a) (accept a) : ℝ)) T := by
  unfold exhaustion
  apply Finset.sum_congr rfl
  intro a _
  have hc : plantProb (v a) (fun c ↦ ¬ accept a c) = 1 - plantProb (v a) (accept a) := by
    conv_rhs => lhs; rw [← hv a]
    rw [plantProb, plantProb, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ ↦ by by_cases h : accept a c <;> simp [h]
  have he : expect (v a) (fun x : Fin T → C ↦ if ∀ i, ¬ accept a (x i) then 1 else 0) =
      (1-plantProb (v a) (accept a))^T := by
    rw [← hc]
    convert iid_all (v a) (fun c ↦ ¬ accept a c) T using 2
    funext x
    by_cases h : ∀ i, ¬ accept a (x i) <;> simp [h]
  rw [he]
  push_cast
  rfl

/-- Two conditionally independent acceptances on the same design have joint probability E[α²]. -/
theorem two_acceptances (w : D → ℝ) (v : D → C → ℚ) (accept : D → C → Prop) :
    (∑ a, w a * (expect (v a) (fun x : Fin 2 → C ↦ if ∀ i, accept a (x i) then 1 else 0) : ℚ)) =
      ∑ a, w a * (plantProb (v a) (accept a) : ℝ)^2 := by
  simp only [iid_all, Rat.cast_pow]

variable {w α : D → ℝ}

theorem exhaustion_antitone (hw : ∀ a, 0 ≤ w a) (hα : ∀ a, α a ∈ Set.Icc 0 1) :
    Antitone (exhaustion w α) := by
  intro S T hST
  exact Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (sub_nonneg.mpr (hα a).2) (by linarith [(hα a).1]) hST) (hw a)

/-- A design-level completeness guarantee bounds exhaustion by the good-output surrogate
and, for at least one trial, by the bad-design mass plus certificate incompleteness. -/
theorem restart_reduction (hw : ∀ a, 0 ≤ w a) (hm : ∑ a, w a = 1)
    (hα : ∀ a, α a ∈ Set.Icc 0 1) {p : D → ℝ} (hp : ∀ a, p a ∈ Set.Icc 0 1)
    {ε : ℝ} (hε : ε ∈ Set.Icc 0 1) (hc : ∀ a, (1-ε)*p a ≤ α a) {T : ℕ} (hT : 1 ≤ T) :
    exhaustion w α T ≤ exhaustion w (fun a ↦ (1-ε)*p a) T ∧
      exhaustion w (fun a ↦ (1-ε)*p a) T ≤ (1 - ∑ a, w a * p a) + ε := by
  constructor
  · exact Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (sub_nonneg.mpr (hα a).2) (sub_le_sub_left (hc a) 1) T) (hw a)
  · have hb (a) : (1-ε)*p a ∈ Set.Icc (0:ℝ) 1 :=
      ⟨mul_nonneg (sub_nonneg.mpr hε.2) (hp a).1, (mul_le_of_le_one_left (hp a).1
        (by linarith [hε.1])).trans (hp a).2⟩
    apply (exhaustion_antitone hw hb hT).trans
    unfold exhaustion
    simp only [pow_one]
    calc _ ≤ ∑ a, (w a - w a * p a + w a * ε) := by
            exact Finset.sum_le_sum fun a _ ↦ by
              nlinarith [mul_nonneg (hw a) (mul_nonneg hε.1 (sub_nonneg.mpr (hp a).2))]
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hm, one_mul]

/-- The closed lower tail gives a lower bound and the open lower tail gives an upper bound. -/
theorem exhaustion_quantiles (hw : ∀ a, 0 ≤ w a) (hm : ∑ a, w a = 1)
    (hα : ∀ a, α a ∈ Set.Icc 0 1) {x : ℝ} (hx : x ∈ Set.Icc 0 1) (T : ℕ) :
    (∑ a with α a ≤ x, w a) * (1-x)^T ≤ exhaustion w α T ∧
      exhaustion w α T ≤ (∑ a with α a < x, w a) + (1-x)^T := by
  unfold exhaustion
  constructor
  · rw [Finset.sum_mul, Finset.sum_filter]
    refine Finset.sum_le_sum fun a _ ↦ ?_
    split_ifs with h
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sub_nonneg.mpr hx.2)
        (sub_le_sub_left h _) T) (hw a)
    · exact mul_nonneg (hw a) (pow_nonneg (sub_nonneg.mpr (hα a).2) T)
  · rw [show (1-x)^T = ∑ a, w a * (1-x)^T by rw [← Finset.sum_mul, hm, one_mul],
      Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun a _ ↦ ?_
    split_ifs with h
    · have hu := pow_le_one₀ (sub_nonneg.mpr (hα a).2) (by linarith [(hα a).1] : 1-α a ≤ 1) (n := T)
      linarith [mul_le_of_le_one_right (hw a) hu,
        mul_nonneg (hw a) (pow_nonneg (sub_nonneg.mpr hx.2) T)]
    · simpa using mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (sub_nonneg.mpr (hα a).2) (sub_le_sub_left (le_of_not_gt h) 1) T) (hw a)

theorem exhaustion_le_reciprocal (hw : ∀ a, 0 ≤ w a) (hα : ∀ a, α a ∈ Set.Icc 0 1) (T : ℕ) :
    exhaustion w α T ≤ ∑ a, w a * (1 / (1 + T * α a)) := by
  refine Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left ?_ (hw a)
  have ha := (hα a).1
  have hb := (hα a).2
  apply (le_div_iff₀ (by positivity)).2
  calc (1-α a)^T * (1+T*α a) ≤ (1-α a)^T * (1+α a)^T :=
        mul_le_mul_of_nonneg_left (one_add_mul_le_pow (by linarith) T) (pow_nonneg (by linarith) _)
    _ ≤ 1 := by
      rw [← mul_pow]
      exact pow_le_one₀ (mul_nonneg (by linarith) (by linarith)) (by nlinarith [sq_nonneg (α a)])

/-- Positive conditional acceptance is required for a finite reciprocal mean. -/
theorem exhaustion_inverse_mean (hw : ∀ a, 0 ≤ w a) (hα : ∀ a, 0 < α a) {T : ℕ} (hT : 0 < T) :
    (∑ a, w a * (1 / (1 + T * α a))) ≤ (∑ a, w a * (α a)⁻¹) / T := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro a _
  have hpos : 0 < (T : ℝ) * α a := mul_pos (by exact_mod_cast hT) (hα a)
  have h := one_div_le_one_div_of_le hpos (by linarith : (T:ℝ)*α a ≤ 1+T*α a)
  simpa [one_div, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_left h (hw a)

/-- Tail sum of the waiting time to first acceptance (the Las Vegas mean). -/
theorem exhaustion_hasSum (w : D → ℝ) (hα : ∀ a, 0 < α a ∧ α a ≤ 1) :
    HasSum (exhaustion w α) (∑ a, w a * (α a)⁻¹) := by
  apply hasSum_sum
  intro a _
  simpa using (hasSum_geometric_of_lt_one (sub_nonneg.mpr (hα a).2)
    (by linarith [(hα a).1] : 1-α a < 1)).mul_left (w a)

theorem exhaustion_jensen (hw : ∀ a, 0 ≤ w a) (hm : ∑ a, w a = 1) (hα : ∀ a, α a ≤ 1) (T : ℕ) :
    (1 - ∑ a, w a * α a)^T ≤ exhaustion w α T := by
  have h := (convexOn_pow (𝕜 := ℝ) T).map_sum_le (fun a _ ↦ hw a) hm
    (p := fun a ↦ 1-α a) (fun a _ ↦ sub_nonneg.mpr (hα a))
  simpa [smul_eq_mul, mul_sub, Finset.sum_sub_distrib, hm, exhaustion] using h

theorem exhaustion_zero_mass (hw : ∀ a, 0 ≤ w a) (hα : ∀ a, α a ≤ 1) (T : ℕ) :
    (∑ a with α a = 0, w a) ≤ exhaustion w α T := by
  rw [Finset.sum_filter, exhaustion]
  apply Finset.sum_le_sum
  intro a _
  split_ifs with h
  · simp [h]
  · exact mul_nonneg (hw a) (pow_nonneg (sub_nonneg.mpr (hα a)) _)

theorem exhaustion_limit (w : D → ℝ) (hα : ∀ a, α a ∈ Set.Icc 0 1) :
    Tendsto (exhaustion w α) atTop (𝓝 (∑ a with α a = 0, w a)) := by
  rw [Finset.sum_filter]
  apply tendsto_finsetSum
  intro a _
  by_cases h : α a = 0
  · simp [h]
  · have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr (hα a).2)
        (by linarith [lt_of_le_of_ne (hα a).1 (Ne.symm h)] : 1-α a < 1)
    simpa [h] using ht.const_mul (w a)

/-- With completeness strictly above zero, the surrogate exhaustion tends to the mass of
designs on which no reducer coin is good. -/
theorem surrogate_limit (w p : D → ℝ) (hp : ∀ a, p a ∈ Set.Icc 0 1)
    {ε : ℝ} (hε : ε ∈ Set.Ico 0 1) :
    Tendsto (exhaustion w (fun a ↦ (1-ε)*p a)) atTop (𝓝 (∑ a with p a = 0, w a)) := by
  have hc : 0 < 1-ε := sub_pos.mpr hε.2
  have hb (a) : (1-ε)*p a ∈ Set.Icc (0:ℝ) 1 := ⟨mul_nonneg hc.le (hp a).1,
    (mul_le_of_le_one_left (hp a).1 (by linarith [hε.1])).trans (hp a).2⟩
  simpa only [mul_eq_zero, hc.ne', false_or] using exhaustion_limit w hb

theorem exhaustion_binary (w : D → ℝ) (hm : ∑ a, w a = 1) (hα : ∀ a, α a = 0 ∨ α a = 1)
    {T : ℕ} (hT : 0 < T) : exhaustion w α T = 1 - ∑ a, w a * α a := by
  conv_rhs => lhs; rw [← hm]
  rw [exhaustion, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rcases hα a with h | h <;> simp [h, hT.ne']

/-- A two-percent closed lower tail and a one-percent exhaustion budget force this trial count. -/
theorem exhaustion_necessity (hw : ∀ a, 0 ≤ w a) (hm : ∑ a, w a = 1)
    (hα : ∀ a, α a ∈ Set.Icc 0 1) {x : ℝ} (hx : x ∈ Set.Ioo 0 1) {T : ℕ}
    (htail : 2/100 ≤ ∑ a with α a ≤ x, w a) (hex : exhaustion w α T ≤ 1/100) :
    Real.log 2 / (-Real.log (1-x)) ≤ T ∧
      Real.log 2 * (1-x) / x ≤ Real.log 2 / (-Real.log (1-x)) := by
  have h1 : 0 < 1-x := sub_pos.mpr hx.2
  have h2 := (exhaustion_quantiles hw hm hα ⟨hx.1.le,hx.2.le⟩ T).1.trans hex
  have hhalf : (1-x)^T ≤ (2:ℝ)⁻¹ := by
    linarith [mul_le_mul_of_nonneg_right htail (pow_nonneg h1.le T)]
  have hlog := Real.log_le_log (pow_pos h1 T) hhalf
  rw [Real.log_pow, Real.log_inv] at hlog
  have hn : 0 < -Real.log (1-x) := neg_pos.mpr (Real.log_neg h1 (by linarith [hx.1]))
  constructor
  · apply (div_le_iff₀ hn).2
    linarith
  · have h := Real.log_le_sub_one_of_pos (inv_pos.mpr h1)
    rw [Real.log_inv] at h
    have hl : -Real.log (1-x) * (1-x) ≤ x := by
      have hh := mul_le_mul_of_nonneg_right h h1.le
      rwa [sub_mul, inv_mul_cancel₀ h1.ne', one_mul, sub_sub_cancel] at hh
    apply (div_le_div_iff₀ hx.1 hn).2
    nlinarith [mul_le_mul_of_nonneg_left hl (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))]

/-- Design-level Paley–Zygmund for the probability of accepting one trial. -/
theorem design_paley_zygmund (hw : ∀ a, 0 ≤ w a) (hm : ∑ a, w a = 1)
    (hα : ∀ a, 0 ≤ α a) {θ : ℝ} (hθ : θ ∈ Set.Icc 0 1) :
    let μ := ∑ a, w a * α a
    (1-θ)^2 * μ^2 / (∑ a, w a * α a^2) ≤ ∑ a with θ*μ < α a, w a :=
  CBDPaleyZygmund.paley_zygmund w α hw hm hα θ hθ.1 hθ.2

/-- The variance is the excess joint rejection probability over independent designs. -/
theorem variance_eq_joint_reject (w α : D → ℝ) (hm : ∑ a, w a = 1) :
    let μ := ∑ a, w a * α a
    (∑ a, w a * (α a - μ)^2) = exhaustion w α 2 - (1-μ)^2 := by
  intro μ
  have expand (a) : w a * (α a - μ)^2 =
      w a*(1-α a)^2 + (w a*α a)*(2-2*μ) + w a*(μ^2-1) := by ring
  simp only [expand, Finset.sum_add_distrib, ← Finset.sum_mul, hm, one_mul, exhaustion]
  change _ + μ * _ + _ = _
  ring

/-- Chebyshev on the lower half-mean event, followed by the quantile upper bound. -/
theorem design_chebyshev (hw : ∀ a, 0 ≤ w a) (hm : ∑ a, w a = 1)
    (hα : ∀ a, α a ∈ Set.Icc 0 1) (hμ : 0 < ∑ a, w a * α a) (T : ℕ) :
    let μ := ∑ a, w a * α a
    exhaustion w α T ≤ 4 * (∑ a, w a * (α a - μ)^2) / μ^2 + (1-μ/2)^T := by
  intro μ
  have hu : μ ≤ 1 := hm ▸ Finset.sum_le_sum fun a _ ↦ mul_le_of_le_one_right (hw a) (hα a).2
  have hpos : 0 < μ := hμ
  apply (exhaustion_quantiles hw hm hα (x := μ/2) ⟨by positivity, by linarith⟩ T).2.trans
  refine add_le_add ?_ le_rfl
  apply (le_div_iff₀ (sq_pos_of_pos hpos)).2
  rw [Finset.sum_mul, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  split_ifs with h
  · have hl : μ^2 ≤ 4*(α a-μ)^2 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ μ-2*α a) (by linarith : 0 ≤ 3*μ-2*α a)]
    linarith [mul_le_mul_of_nonneg_left hl (hw a)]
  · exact mul_nonneg (by norm_num) (mul_nonneg (hw a) (sq_nonneg _))

end SigabaNeo.Wall1.RestartCertificate

#print axioms SigabaNeo.Wall1.RestartCertificate.iid_all
#print axioms SigabaNeo.Wall1.RestartCertificate.two_acceptances
#print axioms SigabaNeo.Wall1.RestartCertificate.shared_exhaustion
#print axioms SigabaNeo.Wall1.RestartCertificate.exhaustion_antitone
#print axioms SigabaNeo.Wall1.RestartCertificate.restart_reduction
#print axioms SigabaNeo.Wall1.RestartCertificate.exhaustion_quantiles
#print axioms SigabaNeo.Wall1.RestartCertificate.exhaustion_le_reciprocal
#print axioms SigabaNeo.Wall1.RestartCertificate.exhaustion_inverse_mean
#print axioms SigabaNeo.Wall1.RestartCertificate.exhaustion_hasSum
#print axioms SigabaNeo.Wall1.RestartCertificate.exhaustion_jensen
#print axioms SigabaNeo.Wall1.RestartCertificate.exhaustion_zero_mass
#print axioms SigabaNeo.Wall1.RestartCertificate.exhaustion_limit
#print axioms SigabaNeo.Wall1.RestartCertificate.surrogate_limit
#print axioms SigabaNeo.Wall1.RestartCertificate.exhaustion_binary
#print axioms SigabaNeo.Wall1.RestartCertificate.exhaustion_necessity
#print axioms SigabaNeo.Wall1.RestartCertificate.design_paley_zygmund
#print axioms SigabaNeo.Wall1.RestartCertificate.variance_eq_joint_reject
#print axioms SigabaNeo.Wall1.RestartCertificate.design_chebyshev
