module

public import CslibFrontier.Probability.StatisticalDistance.Coupling

/-! A one-draw coupling from the unmatched mass of two discrete laws on any type. -/

public section

namespace SigabaNeo.Wall1

open Cslib.Probability
open scoped ENNReal

/-- Match the common mass on the diagonal, then pair the two remainders independently.
The disagreement probability equals the one-sided excess, including on infinite types. -/
theorem exists_coupling_of_excess {α : Type*} (P Q : PMF α) :
    ∃ J : PMF (α × α), J.map Prod.fst = P ∧ J.map Prod.snd = Q ∧
      J.toOuterMeasure {z | z.1 ≠ z.2} = ∑' a, (P a - Q a) := by
  classical
  let common (a : α) := min (P a) (Q a)
  let left (a : α) := P a - Q a
  let right (a : α) := Q a - P a
  let excess := ∑' a, left a
  have splitP (a) : left a + common a = P a := tsub_add_min
  have splitQ (a) : right a + common a = Q a := by
    simpa only [right, common, min_comm (P a)] using tsub_add_min (a := Q a) (b := P a)
  have finiteExcess : excess ≠ ⊤ :=
    ne_top_of_le_ne_top P.tsum_coe_ne_top (tsum_le_tsum fun _ ↦ tsub_le_self)
  have balance : ∑' a, right a = excess := PMF.tsum_tsub_comm Q P
  have cancel (x : ℝ≥0∞) (hz : excess = 0 → x = 0) : x * excess * excess⁻¹ = x := by
    by_cases h : excess = 0
    · simp [hz h]
    · rw [mul_assoc, ENNReal.mul_inv_cancel h finiteExcess, mul_one]
  let residual (a b : α) := left a * right b * excess⁻¹
  have rowResidual (a) : ∑' b, residual a b = left a := by
    simp only [residual, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, balance]
    exact cancel _ fun h ↦ tsum_eq_zero_iff.mp h a
  have colResidual (b) : ∑' a, residual a b = right b := by
    simp only [residual, ENNReal.tsum_mul_right]
    change excess * right b * excess⁻¹ = right b
    rw [mul_comm excess]
    exact cancel _ fun h ↦ tsum_eq_zero_iff.mp (balance.trans h) b
  have diagResidual (a) : residual a a = 0 := by
    rcases le_total (P a) (Q a) with h | h
    · simp [residual, left, tsub_eq_zero_of_le h]
    · simp [residual, right, tsub_eq_zero_of_le h]
  let w (z : α × α) := residual z.1 z.2 + if z.1 = z.2 then common z.1 else 0
  have row (a) : ∑' b, w (a,b) = P a := by simp [w, tsum_add, rowResidual, splitP]
  have col (b) : ∑' a, w (a,b) = Q b := by simp [w, tsum_add, colResidual, splitQ]
  let J : PMF (α × α) := ⟨w, CompleteLattice.summable.hasSum_iff.mpr (by
    rw [tsum_prod', show (fun a ↦ ∑' b, w (a,b)) = P from funext row, P.tsum_coe])⟩
  refine ⟨J, ?_, ?_, ?_⟩
  · ext a
    rw [PMF.map_apply, tsum_prod', tsum_eq_single a]
    · simp only [ite_true, eq_self]
      exact row a
    · intro x hx
      simp [Ne.symm hx]
  · ext b
    rw [PMF.map_apply, tsum_prod', tsum_comm, tsum_eq_single b]
    · simp only [ite_true, eq_self]
      exact col b
    · intro x hx
      simp [Ne.symm hx]
  · have indicator (z : α × α) :
        Set.indicator {z : α × α | z.1 ≠ z.2} J z = residual z.1 z.2 := by
      rcases z with ⟨a,b⟩
      by_cases h : a = b
      · subst b
        simp [diagResidual]
      · rw [Set.indicator_of_mem h]
        change w (a,b) = residual a b
        simp [w, h]
    simp only [PMF.toOuterMeasure_apply, indicator, tsum_prod', rowResidual, left]

/-- A mismatch budget is equivalent to the scalar bound on unmatched mass.
The outcome type can be infinite. -/
theorem coupledWithin_iff_excess_le {α : Type} (P Q : PMF α) (ε : ℝ≥0∞) :
    PMF.CoupledWithin P Q ε ↔ ∑' a, (P a - Q a) ≤ ε := by
  constructor
  · intro h
    exact closeTo_iff_tsum_tsub_le.mp h.toOuterMeasure_le
  · intro h
    obtain ⟨J, hP, hQ, hJ⟩ := exists_coupling_of_excess P Q
    exact ⟨J, hP, hQ, hJ.le.trans h⟩

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.exists_coupling_of_excess
#print axioms SigabaNeo.Wall1.coupledWithin_iff_excess_le
