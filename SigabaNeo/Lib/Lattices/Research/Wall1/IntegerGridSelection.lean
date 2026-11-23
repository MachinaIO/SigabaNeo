module

public import SigabaNeo.Lib.Lattices.Research.Wall1.IntegerGridCoordinates

/-! Pulling an optional Euclidean minimizer back to an integer submodule. -/

public section
noncomputable section

namespace SigabaNeo.Wall1.IntegerGrid

open SigabaNeo.LLL SigabaNeo.SampleDeletion
open scoped ENNReal

variable {d : ℕ} (S : Submodule ℤ (Fin d → ℤ))

/-- The zero fallback and each successful pullback belong to the submodule by construction. -/
def pullbackSelection : Option (S.map intVec) → S
  | some x => (realization S).symm x
  | none => 0

/-- Any selected Euclidean minimizer gives an integer minimizer, including in case of ties. -/
theorem pullbackSelection_minimal (t : Fin d → ℤ) {o : Option (S.map intVec)}
    (h : ∃ x, o = some x ∧ ∀ y : S.map intVec,
      ‖(x : EuclideanSpace ℝ (Fin d)) - intVec t‖ ≤ ‖(y : EuclideanSpace ℝ (Fin d)) - intVec t‖)
    (z : S) : normSq ((pullbackSelection S o).val - t) ≤ normSq (z.val - t) := by
  obtain ⟨x, rfl, hx⟩ := h
  exact minimizes_normSq_of_closest S t x hx z

/-- The probability of a nonminimal integer answer is bounded by the probability that the
selector fails to return a Euclidean minimizer. -/
theorem pullbackSelection_failure_le {Ω : Type*} (P : PMF Ω) (t : Fin d → ℤ)
    (select : Ω → Option (S.map intVec)) :
    P.toOuterMeasure {ω | ¬ ∀ z : S,
      normSq ((pullbackSelection S (select ω)).val - t) ≤ normSq (z.val - t)} ≤
    P.toOuterMeasure {ω | ¬ ∃ x, select ω = some x ∧ ∀ y : S.map intVec,
      ‖(x : EuclideanSpace ℝ (Fin d)) - intVec t‖ ≤
        ‖(y : EuclideanSpace ℝ (Fin d)) - intVec t‖} := by
  exact P.toOuterMeasure.mono fun _ hbad hmin ↦ hbad (pullbackSelection_minimal S t hmin)

end SigabaNeo.Wall1.IntegerGrid

#print axioms SigabaNeo.Wall1.IntegerGrid.pullbackSelection
#print axioms SigabaNeo.Wall1.IntegerGrid.pullbackSelection_minimal
#print axioms SigabaNeo.Wall1.IntegerGrid.pullbackSelection_failure_le
