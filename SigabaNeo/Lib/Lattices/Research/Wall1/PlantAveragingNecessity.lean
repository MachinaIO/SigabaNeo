module

public import SigabaNeo.Lib.Lattices.Research.Wall1.ConditionalReduction
import all SigabaNeo.Lib.Lattices.Research.Wall1.ConditionalReduction
import all SigabaNeo.Lib.Lattices.Research.Wall1.UniquenessProbability
import all SigabaNeo.Lib.Lattices.Research.Wall1.HeightZeroFloor
import Mathlib.Tactic

/-! Part 134 Theorem 2 (audit-corrected scope): plant averaging cannot replace a null-only
lower tail for the minimum of the final block.

For a plant-blind reducer (the final block is a function of the design, coins included in the
design), the failure probability of **all-heights uniqueness of the single final block** is at
least `Pr_A[λ₁(H_A)² ≤ μ − t] · t²/(v + t²)`, with `μ = 1 + (3/2)d` and `v = (9/2)d`.
Per the audit this lower-bounds uniqueness failure only, not recovery failure of decoders
that do not need uniqueness. The event `λ₁(H_A)² ≤ μ − t` is written as the existence of a
nonzero vector of the block's ℤ-span with squared norm at most `μ − t`; ties count as
failure. -/

public section

namespace SigabaNeo.Wall1

open SampleDeletion CBDTail CBDQuadratic InnerProductSpace Classical

variable {N d : ℕ}

/-- The final block has a nonzero lattice vector of squared norm at most `r2`
(that is, `λ₁(H)² ≤ r2`). -/
def FinalBlock.ShortVector (B : FinalBlock N d) (r2 : ℝ) : Prop :=
  ∃ h ∈ Submodule.span ℤ (Set.range B.basis), h ≠ (0 : B.V) ∧ ‖h‖ ^ 2 ≤ r2

/-- CBD(3) failure mass of all-heights uniqueness in the fiber over one fixed design. -/
noncomputable def FinalBlock.failure (B : FinalBlock N d) : ℝ :=
  ∑ w with ¬allHeightsUnique (horizontalLattice B.V B.basis) (projectedCBD B.Q w), jointWeight w

private theorem jointWeight_nonneg' (w : Fin N → Digit 3) : 0 ≤ jointWeight w := by
  unfold jointWeight weight
  positivity

/-- Fixed-block form: if `λ₁(H)² ≤ μ − t`, the projected CBD(3) plant breaks all-heights
uniqueness with probability at least `t²/(v + t²)` (lower Cantelli for the plant norm). -/
theorem FinalBlock.failure_lower (B : FinalBlock N d) {t : ℝ} (ht : 0 < t)
    (short : B.ShortVector (1 + (3/2)*(d : ℝ) - t)) :
    let v := (9/2)*(d : ℝ)
    t^2/(v+t^2) ≤ B.failure := by
  intro v
  obtain ⟨h, hh, hn, hle⟩ := short
  let m := (3/2)*(d : ℝ)
  -- every plant with `‖Q X‖² > m − t` breaks the height-zero test against `h`
  have cover : ∀ w, ¬ quadratic B.Q w ≤ m - t →
      ¬allHeightsUnique (horizontalLattice B.V B.basis) (projectedCBD B.Q w) := by
    intro w hq hu
    have zero := ((allHeightsUniquenessCriterion _ _).1 hu).1 h.val ⟨h, hh, rfl⟩
      (fun e ↦ hn (Subtype.ext e))
    rw [projectedCBD_norm_sq _ B.symmetric B.idempotent] at zero
    have : ‖h.val‖ = ‖h‖ := rfl
    rw [this] at zero
    have hq' := lt_of_not_ge hq
    dsimp [m] at hq'
    linarith
  have hc := quadratic_cantelli B.Q t ht
  simp only [B.trace_eq] at hc
  let var := ∑ w, jointWeight w * (quadratic B.Q w - m)^2
  have hv : 0 ≤ var := Finset.sum_nonneg fun w _ ↦ mul_nonneg (jointWeight_nonneg' _) (sq_nonneg _)
  have hv' : var ≤ v := by
    simpa [var, m, v, B.trace_eq] using projection_variance_le B.Q B.symmetric B.idempotent
  have low : (∑ w with quadratic B.Q w ≤ m - t, jointWeight w) ≤ v/(v+t^2) := by
    apply (show _ ≤ var/(var+t^2) from hc).trans
    apply (div_le_div_iff₀ (by positivity) (by dsimp [v]; positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hv' (sq_nonneg t)]
  have split := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun w ↦ quadratic B.Q w ≤ m - t) jointWeight
  rw [joint_mass] at split
  have mono : (∑ w with ¬ quadratic B.Q w ≤ m - t, jointWeight w) ≤ B.failure := by
    unfold FinalBlock.failure
    rw [Finset.sum_filter, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro w _
    by_cases hq : quadratic B.Q w ≤ m - t
    · simp only [hq, not_true_eq_false, ite_false]
      split <;> simp [jointWeight_nonneg']
    · simp [hq, cover w hq]
  have hvt : 0 < v + t^2 := by dsimp [v]; positivity
  have eq : t^2/(v+t^2) + v/(v+t^2) = 1 := by
    rw [← add_div, add_comm (t^2), div_self hvt.ne']
  linarith

/-- **Part 134 Theorem 2 (weighted design law).** Let `ρ` be any probability law on a finite
design space `D` (coins included), and let a plant-blind reducer return the final block `R A`.
With the CBD(3) plant independent of the design,

`Pr[all-heights uniqueness fails] ≥ Pr_A[λ₁(H_A)² ≤ μ − t] · t²/(v + t²)`. -/
theorem plantAveraging_lower {D : Type*} [Fintype D] (ρ : D → ℝ) (hρ : ∀ A, 0 ≤ ρ A)
    (R : D → FinalBlock N d) {t : ℝ} (ht : 0 < t) :
    let μ := 1 + (3/2)*(d : ℝ)
    let v := (9/2)*(d : ℝ)
    (∑ A with (R A).ShortVector (μ - t), ρ A) * (t^2/(v+t^2)) ≤ ∑ A, ρ A * (R A).failure := by
  intro μ v
  have fpos A : 0 ≤ (R A).failure :=
    Finset.sum_nonneg fun w _ ↦ jointWeight_nonneg' w
  rw [Finset.sum_mul, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro A _
  split
  · rename_i hs
    exact mul_le_mul_of_nonneg_left ((R A).failure_lower ht hs) (hρ A)
  · exact mul_nonneg (hρ A) (fpos A)

/-- **Part 134 Theorem 2 (uniform finite design, as in `conditionalReduction`).** -/
theorem plantAveraging_lower_uniform {D : Type*} [Fintype D] [Nonempty D]
    (R : D → FinalBlock N d) {t : ℝ} (ht : 0 < t) :
    let μ := 1 + (3/2)*(d : ℝ)
    let v := (9/2)*(d : ℝ)
    ((Finset.univ.filter fun A ↦ (R A).ShortVector (μ - t)).card : ℝ) / Fintype.card D *
        (t^2/(v+t^2)) ≤
      (∑ A, (R A).failure) / Fintype.card D := by
  intro μ v
  have hcard : (0 : ℝ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  have h : (∑ A with (R A).ShortVector (μ - t), (1 / Fintype.card D : ℝ)) * (t^2/(v+t^2)) ≤
      ∑ A, (1 / Fintype.card D : ℝ) * (R A).failure :=
    plantAveraging_lower (fun _ ↦ (1 / Fintype.card D : ℝ)) (fun _ ↦ by positivity) R ht
  rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at h
  calc _ = _ := by ring
    _ ≤ _ := h
    _ = _ := by ring

/-- Failure and success masses are complementary in each design fiber. -/
theorem FinalBlock.failure_add_success (B : FinalBlock N d) : B.failure + B.success = 1 := by
  unfold FinalBlock.failure FinalBlock.success
  rw [add_comm, Finset.sum_filter_add_sum_filter_not, joint_mass]

/-- Consequence: a reducer whose design-averaged uniqueness success is at least `1 − θ` must
have `Pr_A[λ₁(H_A)² ≤ μ − t] ≤ θ·(v + t²)/t²` for every `t > 0`. -/
theorem plantAveraging_tail_necessary {D : Type*} [Fintype D] [Nonempty D]
    (R : D → FinalBlock N d) {t θ : ℝ} (ht : 0 < t)
    (success : 1 - θ ≤ (∑ A, (R A).success) / Fintype.card D) :
    let μ := 1 + (3/2)*(d : ℝ)
    let v := (9/2)*(d : ℝ)
    ((Finset.univ.filter fun A ↦ (R A).ShortVector (μ - t)).card : ℝ) / Fintype.card D ≤
      θ * ((v + t^2)/t^2) := by
  intro μ v
  have hcard : (0 : ℝ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  have h := plantAveraging_lower_uniform R ht
  have fail : (∑ A, (R A).failure) / Fintype.card D ≤ θ := by
    have e : (∑ A, (R A).failure) = Fintype.card D - ∑ A, (R A).success := by
      rw [Finset.sum_congr rfl (fun A _ ↦ eq_sub_of_add_eq (R A).failure_add_success),
        Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [e, sub_div, div_self hcard.ne']
    linarith
  have hv : 0 < v + t^2 := by dsimp [v]; positivity
  have hq : 0 < t^2/(v+t^2) := by positivity
  calc _ = (((Finset.univ.filter fun A ↦ (R A).ShortVector (μ - t)).card : ℝ) / Fintype.card D *
        (t^2/(v+t^2))) * ((v+t^2)/t^2) := by field_simp
    _ ≤ θ * ((v+t^2)/t^2) := by
        apply mul_le_mul_of_nonneg_right (h.trans fail) (by positivity)

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.FinalBlock.failure_lower
#print axioms SigabaNeo.Wall1.plantAveraging_lower
#print axioms SigabaNeo.Wall1.plantAveraging_lower_uniform
#print axioms SigabaNeo.Wall1.plantAveraging_tail_necessary
