module

public import SigabaNeo.Lib.Lattices.Research.Wall1.FixedBlockChernoff
import all SigabaNeo.Lib.Lattices.Research.Wall1.FixedBlockCount
import all SigabaNeo.Lib.Lattices.Research.Wall1.ConditionalReduction
import all SigabaNeo.Lib.Lattices.Research.Wall1.UniquenessProbability
import Mathlib.Tactic

/-! # Exact capped competitor score (Part 181) -/

public section
namespace SigabaNeo.Wall1.FinalBlock

open Classical SampleDeletion CBDTail CBDQuadratic
variable {N d : ℕ} (B : FinalBlock N d)

/-- Nonzero horizontal points whose augmented squared length at height `k` is at most
the plant's squared length. The final squared comparison also handles empty sections. -/
noncomputable def scoreSection (y : EuclideanSpace ℝ (Fin N)) (k : ℕ) : Finset B.V :=
  (B.ballSection ((k : ℝ) • y) (√(1 + ‖y‖^2))).filter fun h ↦
    h ≠ 0 ∧ ‖h.val + (k : ℝ) • y‖^2 + (k : ℝ)^2 ≤ 1 + ‖y‖^2

theorem mem_scoreSection {y : EuclideanSpace ℝ (Fin N)} {k : ℕ} {h : B.V} :
    h ∈ B.scoreSection y k ↔ h ∈ Submodule.span ℤ (Set.range B.basis) ∧ h ≠ 0 ∧
      ‖h.val + (k : ℝ) • y‖^2 + (k : ℝ)^2 ≤ 1 + ‖y‖^2 := by
  simp only [scoreSection, Finset.mem_filter, ballSection, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  · exact fun ⟨⟨hm, _⟩, hn, hit⟩ ↦ ⟨hm, hn, hit⟩
  · rintro ⟨hm, hn, hit⟩
    exact ⟨⟨hm, Real.le_sqrt_of_sq_le (by linarith [sq_nonneg (k : ℝ)])⟩, hn, hit⟩

/-- Total number of competing nonzero horizontal terms for a plant within the energy cap. -/
noncomputable def cappedCount (a : ℝ) (y : EuclideanSpace ℝ (Fin N)) : ℕ :=
  if ‖y‖^2 ≤ a then
    ∑ k ∈ Finset.Iic ⌊√(1 + a)⌋₊, (B.scoreSection y k).card
  else 0

/-- The expectation under the full CBD(3) law, with zero contribution off the cap. -/
noncomputable def score (a : ℝ) : ℝ :=
  ∑ w : Plant N, jointWeight w * (B.cappedCount a (projectedCBD B.Q w) : ℝ)

/-- Each capped failure contributes at least one point, including equality in a length test. -/
theorem cappedCount_pos_of_failure {a : ℝ} {y : EuclideanSpace ℝ (Fin N)} (cap : ‖y‖^2 ≤ a)
    (fail : ¬ allHeightsUnique (horizontalLattice B.V B.basis) y) : 0 < B.cappedCount a y := by
  by_contra! empty
  apply fail
  apply (allHeightsUniquenessCriterion _ _).2
  have absent (k : ℕ) (h : B.V) (hm : h ∈ Submodule.span ℤ (Set.range B.basis)) (hn : h ≠ 0)
      (hit : ‖h.val + (k : ℝ) • y‖^2 + (k : ℝ)^2 ≤ 1 + ‖y‖^2) : False := by
    have mem : k ∈ Finset.Iic ⌊√(1 + a)⌋₊ := Finset.mem_Iic.mpr
      ((Nat.le_floor_iff (Real.sqrt_nonneg _)).2
        (Real.le_sqrt_of_sq_le (by linarith [sq_nonneg ‖h.val + (k : ℝ) • y‖])))
    have pos := Finset.card_pos.mpr ⟨h, B.mem_scoreSection.mpr ⟨hm, hn, hit⟩⟩
    rw [cappedCount, ite_eq_left cap] at empty
    exact (not_lt_of_ge empty) (pos.trans_le
      (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (B.scoreSection y j).card) mem))
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨h, hm, rfl⟩ hn
    apply lt_of_not_ge
    intro hit
    exact absent 0 h hm (fun eq ↦ hn (by simp [eq])) (by simpa [add_comm] using hit)
  · rintro _ ⟨h, hm, rfl⟩ hn
    apply lt_of_not_ge
    intro hit
    apply absent 1 h hm (fun eq ↦ hn (by simp [eq]))
    simpa [add_comm] using hit
  · intro k hk _
    lift k to ℕ using (by omega)
    rintro _ ⟨h, hm, rfl⟩
    apply lt_of_not_ge
    intro hit
    change ‖h.val + (k : ℤ) • y‖^2 ≤ ‖y‖^2 + 1 - ((k : ℤ) : ℝ)^2 at hit
    have hit' : ‖h.val + (k : ℝ) • y‖^2 + (k : ℝ)^2 ≤ ‖y‖^2 + 1 := by
      rw [Nat.cast_smul_eq_nsmul ℝ]
      rw [Int.cast_natCast, natCast_zsmul] at hit
      linarith
    have hn := (highHit _ _ _ (by exact_mod_cast hk) hit').1
    exact absent k h hm (fun eq ↦ hn (by simp [eq])) (by linarith)

/-- The off-cap mass is charged once; the score covers every capped Part 94 failure. -/
theorem failure_le_capTail_add_score (a : ℝ) : 1 - B.success ≤ B.capTail a + B.score a := by
  apply sub_le_iff_le_add.mpr
  rw [← joint_mass (N := N)]
  simp only [success, capTail, cbdMass, score, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun w _ ↦ ?_
  let y := projectedCBD B.Q w
  change jointWeight w ≤ ((if a < ‖y‖^2 then jointWeight w else 0) +
    jointWeight w * (B.cappedCount a y : ℝ)) +
    (if allHeightsUnique (horizontalLattice B.V B.basis) y then jointWeight w else 0)
  have nonneg := mul_nonneg (weightNonneg w) (Nat.cast_nonneg (B.cappedCount a y) (α := ℝ))
  by_cases ht : a < ‖y‖^2 <;> by_cases hu : allHeightsUnique (horizontalLattice B.V B.basis) y
  · simp [ht, hu]; linarith [weightNonneg w]
  · simpa [ht, hu] using nonneg
  · simpa [ht, hu] using nonneg
  · simp only [ht, hu, ite_false, zero_add, add_zero]
    exact le_mul_of_one_le_right (weightNonneg _) (by
      exact_mod_cast B.cappedCount_pos_of_failure (le_of_not_gt ht) hu)

/-- A score allowance and the explicit Chernoff tail suffice in the upper-tail regime. -/
theorem failure_le_normChernoff_add_budget {a σ : ℝ} (hd : 0 < d) (ha : 3 * (d : ℝ) / 2 < a)
    (hs : B.score a ≤ σ) : 1 - B.success ≤ normChernoff d a + σ :=
  (B.failure_le_capTail_add_score a).trans (add_le_add (B.capTail_le_normChernoff hd ha) hs)

end SigabaNeo.Wall1.FinalBlock

#print axioms SigabaNeo.Wall1.FinalBlock.mem_scoreSection
#print axioms SigabaNeo.Wall1.FinalBlock.cappedCount_pos_of_failure
#print axioms SigabaNeo.Wall1.FinalBlock.failure_le_capTail_add_score
#print axioms SigabaNeo.Wall1.FinalBlock.failure_le_normChernoff_add_budget
