module

public import SigabaNeo.Lib.Lattices.Research.Wall1.UniquenessProfile
import all SigabaNeo.Lib.Lattices.Research.Wall1.ConditionalReduction
import all SigabaNeo.Lib.Lattices.Research.Wall1.UniquenessProbability
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Tactic

/-! # Fixed-block CBD counts (Part 175, formula (1))

All probabilities are in one fixed design fiber. The cap charge is the exact CBD
mass of exceeding the cap. The higher-height counts average over the original law.
-/

public section
namespace SigabaNeo.Wall1.FinalBlock

open SampleDeletion CBDTail CBDQuadratic Classical
variable {N d : ℕ} (B : FinalBlock N d)

abbrev Plant (N : ℕ) := Fin N → Digit 3

noncomputable def cbdMass (P : Plant N → Prop) : ℝ := ∑ w with P w, jointWeight w

private theorem mass_mono {P R : Plant N → Prop} (h : ∀ w, P w → R w) :
    cbdMass P ≤ cbdMass R := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.monotone_filter_right _ fun w _ ↦ h w
  · exact fun w _ _ ↦ weightNonneg w

private theorem mass_le_one (P : Plant N → Prop) : cbdMass P ≤ 1 := by
  simpa [cbdMass, joint_mass] using mass_mono (P := P) (R := fun _ ↦ True) (by simp)

private noncomputable abbrev H := Submodule.span ℤ (Set.range B.basis)

/-- A minimum floor on the embedded horizontal lattice. -/
def MinFloor (L : ℝ) : Prop := ∀ h ∈ H B, h ≠ (0 : B.V) → L ≤ ‖h‖

/-- The finite closed-ball section includes the origin whenever it qualifies. -/
noncomputable def ballSection (v : EuclideanSpace ℝ (Fin N)) (r : ℝ) : Finset B.V :=
  Set.Finite.toFinset (s := {h : B.V | h ∈ H B ∧ ‖h.val + v‖ ≤ r}) (by
    apply (ZSpan.setFinite_inter B.basis (Metric.isBounded_closedBall (x := (0 : B.V))
      (r := r + ‖v‖))).subset
    rintro h ⟨hm, hh⟩
    refine ⟨Metric.mem_closedBall.mpr ?_, hm⟩
    rw [dist_zero_right]
    calc ‖h.val‖ = ‖h.val + v - v‖ := by rw [add_sub_cancel_right]
         _ ≤ ‖h.val + v‖ + ‖v‖ := norm_sub_le _ _
         _ ≤ _ := by linarith)

/-- Exact expected number of lattice points in the shifted closed ball. -/
noncomputable def ballMoment (a : ℝ) (k : ℕ) : ℝ :=
  ∑ w : Plant N, jointWeight w *
    ((B.ballSection ((k : ℝ) • projectedCBD B.Q w) (√(1 + a - (k : ℝ)^2))).card : ℝ)

noncomputable def capTail (a : ℝ) : ℝ :=
  cbdMass fun w ↦ a < ‖projectedCBD B.Q w‖^2

private noncomputable def vector (c : Fin d → ℤ) : B.V := ∑ i, (c i : ℝ) • B.basis i

/-- The full primal Gaussian sum with its origin removed, in basis coordinates. -/
noncomputable def oneTheta : ℝ :=
  (∑' c, Real.exp (-(1/12 : ℝ) * ‖B.vector c‖^2)) - 1

private theorem mass_one_le :
    cbdMass (fun w ↦ ∃ h ∈ H B, h ≠ (0 : B.V) ∧
      ‖projectedCBD B.Q w + h.val‖^2 ≤ ‖projectedCBD B.Q w‖^2) ≤ B.oneTheta := by
  let A := Finset.univ.filter fun w ↦ ∃ h ∈ H B, h ≠ (0 : B.V) ∧
    ‖projectedCBD B.Q w + h.val‖^2 ≤ ‖projectedCBD B.Q w‖^2
  have witness w (hw : w ∈ A) : ∃ c, c ≠ 0 ∧
      ‖projectedCBD B.Q w + (B.vector c).val‖^2 ≤ ‖projectedCBD B.Q w‖^2 := by
    obtain ⟨h, hh, hn, hit⟩ := (Finset.mem_filter.mp hw).2
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hh
    have eq : B.vector c = h := by simpa [vector, Int.cast_smul_eq_zsmul] using hc
    exact ⟨c, fun hz ↦ hn (by simp [← eq, hz, vector]), eq.symm ▸ hit⟩
  let pick w := if hw : w ∈ A then (witness w hw).choose else 0
  have spec w (hw : w ∈ A) := (witness w hw).choose_spec
  let S := A.image pick
  have h0 : 0 ∉ S := by
    rintro hz
    obtain ⟨w, hw, eq⟩ := Finset.mem_image.mp hz
    exact (spec w hw).1 (by simpa [pick, hw] using eq)
  let f (c : Fin d → ℤ) := Real.exp (-(1/12 : ℝ) * ‖B.vector c‖^2)
  have mass : ∑ w ∈ A, jointWeight w ≤ ∑ c ∈ S, f c := by
    rw [← Finset.sum_fiberwise_of_maps_to (fun w hw ↦ Finset.mem_image_of_mem pick hw)]
    refine Finset.sum_le_sum fun c _ ↦ ?_
    have single := heightOneVector B.Q B.symmetric (B.vector c).val (B.fixed _)
    apply le_trans _ (single.trans_eq ?_)
    swap
    · congr 1
      change -‖B.vector c‖^2/12 = -(1/12 : ℝ) * ‖B.vector c‖^2
      ring
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun w _ _ ↦ weightNonneg w)
    intro w hw
    obtain ⟨ha, hc⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa [← hc, pick, ha] using (spec w ha).2⟩
  have summ : Summable f := (latticeThetaProfile B.basis (s := 1/12) (by norm_num)).1
  have total := summ.sum_le_tsum (insert 0 S) (fun c _ ↦ (Real.exp_pos _).le)
  change (∑ c ∈ insert 0 S, f c) ≤ ∑' c, f c at total
  rw [Finset.sum_insert h0, show f 0 = 1 by simp [f, vector]] at total
  change (∑ w ∈ A, jointWeight w) ≤ (∑' c, f c) - 1
  linarith

noncomputable def oneCharge (a L : ℝ) : ℝ :=
  if 2 * √a < L then 0 else min 1 B.oneTheta

noncomputable def highCharge (a L : ℝ) (k : ℕ) : ℝ :=
  if (k : ℝ) * √a + √(1 + a - (k : ℝ)^2) < L then 0 else min 1 (B.ballMoment a k)

/-- Formula (1), using the certified minimum floor and the exact norm-tail mass. -/
noncomputable def countError (a L : ℝ) : ℝ :=
  if √(1 + a) < L then min 1 (B.capTail a + B.oneCharge a L +
    ∑ k ∈ Finset.Icc 2 ⌊√(1 + a)⌋₊, B.highCharge a L k) else 1

private def oneEvent (a : ℝ) (w : Plant N) : Prop :=
  let y := projectedCBD B.Q w
  ‖y‖^2 ≤ a ∧ ∃ h ∈ H B, h ≠ (0 : B.V) ∧ ‖y + h.val‖^2 ≤ ‖y‖^2

private def highEvent (a : ℝ) (k : ℕ) (w : Plant N) : Prop :=
  let y := projectedCBD B.Q w
  ‖y‖^2 ≤ a ∧ ∃ h ∈ H B, h ≠ (0 : B.V) ∧
    ‖h.val + (k : ℝ) • y‖ ≤ √(1 + a - (k : ℝ)^2)

private theorem mass_oneEvent_le {a L : ℝ} (floor : B.MinFloor L) :
    cbdMass (B.oneEvent a) ≤ B.oneCharge a L := by
  unfold oneCharge
  split_ifs with exc
  · have empty w : ¬ B.oneEvent a w := by
      rintro ⟨cap, h, hh, hn, hit⟩
      let y := projectedCBD B.Q w
      have hy : ‖y‖ ≤ √a := Real.le_sqrt_of_sq_le cap
      have hhit : ‖y + h.val‖ ≤ ‖y‖ := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hit
      have tr := norm_sub_le (y + h.val) y
      rw [add_sub_cancel_left] at tr
      exact (floor h hh hn).not_gt (by change ‖h.val‖ < L; linarith)
    simp [cbdMass, empty]
  · exact le_min (mass_le_one _) ((mass_mono fun _ hw ↦ hw.2).trans B.mass_one_le)

private theorem mass_highEvent_le {a L : ℝ} (floor : B.MinFloor L) (k : ℕ) :
    cbdMass (B.highEvent a k) ≤ B.highCharge a L k := by
  unfold highCharge
  split_ifs with exc
  · have empty w : ¬ B.highEvent a k w := by
      rintro ⟨cap, h, hh, hn, hit⟩
      let y := projectedCBD B.Q w
      have hy : ‖y‖ ≤ √a := Real.le_sqrt_of_sq_le cap
      have tr := norm_sub_le (h.val + (k : ℝ) • y) ((k : ℝ) • y)
      rw [add_sub_cancel_right, norm_smul, Real.norm_natCast] at tr
      apply (floor h hh hn).not_gt
      change ‖h.val‖ < L
      linarith [mul_le_mul_of_nonneg_left hy k.cast_nonneg]
    simp [cbdMass, empty]
  · refine le_min (mass_le_one _) ?_
    unfold cbdMass ballMoment
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun w _ ↦ ?_
    split_ifs with hw
    · obtain ⟨_, h, hh, _, hit⟩ := hw
      have mem : h ∈ B.ballSection ((k : ℝ) • projectedCBD B.Q w) (√(1+a-(k:ℝ)^2)) :=
        by simpa [ballSection] using And.intro hh hit
      exact le_mul_of_one_le_right (weightNonneg w)
        (by exact_mod_cast Finset.card_pos.mpr ⟨h, mem⟩)
    · exact mul_nonneg (weightNonneg _) (Nat.cast_nonneg _)

/-- Failure of any Part 94 test, counting ties, has mass bounded by (1). -/
theorem failure_le_countError {a L : ℝ} (floor : B.MinFloor L) :
    1 - B.success ≤ B.countError a L := by
  have trivialBound : 1 - B.success ≤ 1 := by
    have : 0 ≤ B.success := Finset.sum_nonneg fun w _ ↦ weightNonneg w
    linarith
  unfold countError
  split_ifs with strict
  · refine le_min trivialBound ?_
    let S := Finset.Icc 2 ⌊√(1+a)⌋₊
    let U w := allHeightsUnique (horizontalLattice B.V B.basis) (projectedCBD B.Q w)
    let T w := a < ‖projectedCBD B.Q w‖^2
    have cover w (cap : ¬T w) (one : ¬B.oneEvent a w) (high : ∀ k ∈ S, ¬B.highEvent a k w) :
        U w := by
      have hc : ‖projectedCBD B.Q w‖^2 ≤ a := le_of_not_gt cap
      apply (allHeightsUniquenessCriterion _ _).2
      refine ⟨?_, ?_, ?_⟩
      · rintro _ ⟨h, hh, rfl⟩ hn
        have hl := floor h hh (fun eq ↦ hn (by simp [eq]))
        change _ < ‖h‖^2
        have hsq := sq_lt_sq' (by linarith [Real.sqrt_nonneg (1+a)] : -‖h‖ < √(1+a))
          (strict.trans_le hl)
        nlinarith [Real.sq_sqrt (by linarith [sq_nonneg ‖projectedCBD B.Q w‖] : 0 ≤ 1+a)]
      · rintro _ ⟨h, hh, rfl⟩ hn
        by_contra! hit
        exact one ⟨hc, h, hh, fun eq ↦ hn (by simp [eq]), by simpa [add_comm] using hit⟩
      · intro k hk hcap
        lift k to ℕ using (by omega)
        rintro _ ⟨h, hh, rfl⟩
        by_contra! hit
        push_cast at hcap hit
        have hk' : 2 ≤ k := by omega
        have mem : k ∈ S := Finset.mem_Icc.mpr ⟨hk', (Nat.le_floor_iff (Real.sqrt_nonneg _)).2
          (Real.le_sqrt_of_sq_le (by linarith))⟩
        have hit' : ‖h.val + (k : ℝ) • projectedCBD B.Q w‖^2 + (k : ℝ)^2 ≤
            ‖projectedCBD B.Q w‖^2 + 1 := by
          rw [Nat.cast_smul_eq_nsmul ℝ]
          change ‖h.val + (k : ℤ) • projectedCBD B.Q w‖^2 ≤ _ at hit
          simp only [natCast_zsmul] at hit
          linarith
        have hn := (highHit _ _ _ (by exact_mod_cast hk') hit').1
        exact high k mem ⟨hc, h, hh, fun eq ↦ hn (by simp [eq]),
          Real.le_sqrt_of_sq_le (by linarith)⟩
    have total : 1 ≤ cbdMass U + cbdMass T + cbdMass (B.oneEvent a) +
        ∑ k ∈ S, cbdMass (B.highEvent a k) := by
      rw [← joint_mass (N := N)]
      simp only [cbdMass, Finset.sum_filter]
      rw [Finset.sum_comm (s := S)]
      simp only [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun w _ ↦ ?_
      have pos (P : Prop) [Decidable P] : 0 ≤ (if P then jointWeight w else 0) := by
        split <;> simp [weightNonneg]
      have nonneg := Finset.sum_nonneg (s := S) (fun k _ ↦ pos (B.highEvent a k w))
      by_cases hu : U w
      · simp [hu]; linarith [pos (T w), pos (B.oneEvent a w)]
      by_cases ht : T w
      · simp [hu, ht]; linarith [pos (B.oneEvent a w)]
      by_cases ho : B.oneEvent a w
      · simp [hu, ht, ho, nonneg]
      obtain ⟨k, hk, hit⟩ : ∃ k ∈ S, B.highEvent a k w := by
        by_contra! no; exact hu (cover w ht ho no)
      simpa [hu, ht, ho, hit] using Finset.single_le_sum (fun j _ ↦ pos (B.highEvent a j w)) hk
    have high := Finset.sum_le_sum (s := S) fun k _ ↦ B.mass_highEvent_le floor (a := a) k
    change 1 - cbdMass U ≤ cbdMass T + _ + ∑ k ∈ S, _
    linarith [B.mass_oneEvent_le floor (a := a)]
  · exact trivialBound

end SigabaNeo.Wall1.FinalBlock

#print axioms SigabaNeo.Wall1.FinalBlock.failure_le_countError
