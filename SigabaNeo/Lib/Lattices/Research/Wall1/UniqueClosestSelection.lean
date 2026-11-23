module

public import SigabaNeo.Lib.Lattices.Research.Wall1.Width638Geometry
public import SigabaNeo.Lib.Lattices.Research.Wall1.OneDrawCoupling
import all SigabaNeo.Lib.Lattices.Research.Wall1.Width638Geometry
import Mathlib.Tactic

public section
namespace SigabaNeo.Wall1.Width638

open QaryMembership SigabaNeo.SampleDeletion

/-- At a good target, every successful selection gives the plant, pointwise in the seed. -/
theorem selected_of_not_bad {r n q : ℕ} [Fact q.Prime] {Ω : Type*}
    (p : Grid r n) (A : Design r n q) (hg : ¬ Bad p A)
    (select : Ω → Option (Grid r n)) (ω : Ω)
    (hs : ∃ x, select ω = some x ∧ output A x = output A p ∧
      ∀ w, output A w = output A p → normSq x ≤ normSq w) :
    select ω = some p := by
  obtain ⟨x, hx, feasible, minimal⟩ := hs
  have eq : x = p := by
    by_contra h
    exact hg ⟨x, h, minimal p rfl, feasible⟩
  exact hx.trans (congrArg some eq)

/-- In the lattice 2ℤ, two exact selectors can disagree on the first accepted answer
even when a later target has the origin as its unique closest point. All answers pass
validation in this example. A lattice point with coordinate k has ambient position 2k. -/
theorem exists_disagreeing_first_closest :
    ∃ t a b : Fin 4 → ℤ,
      (∀ i k, |2 * a i - t i| ≤ |2 * k - t i|) ∧
      (∀ i k, |2 * b i - t i| ≤ |2 * k - t i|) ∧
      (∃ i, ∀ k : ℤ, k ≠ 0 → |t i| < |2 * k - t i|) ∧
      (List.finRange 4).findSome? (fun i ↦ some (a i)) = some 0 ∧
      (List.finRange 4).findSome? (fun i ↦ some (b i)) = some 1 := by
  let t (i : Fin 4) : ℤ := if i = 0 then 1 else 0
  have odd_dist (k : ℤ) : 1 ≤ |2 * k - 1| := by
    have h : 2 * k - 1 ≠ 0 := by omega
    exact Int.add_one_le_iff.mpr (abs_pos.mpr h)
  refine ⟨t, fun _ ↦ 0, t, ?_, ?_, ⟨1, ?_⟩, rfl, rfl⟩
  · intro i k
    by_cases h : i = 0 <;> simp [t, h, odd_dist]
  · intro i k
    by_cases h : i = 0 <;> simp [t, h, odd_dist]
  · intro k hk
    simp [t, hk]

end SigabaNeo.Wall1.Width638

namespace SigabaNeo.Wall1

open Cslib.Probability

/-- The one-draw coupling budget, conditional on the sampler's stated excess-mass bound. -/
theorem oneDrawCoupling_of_samplerTV {α : Type} (P Q : PMF α)
    (samplerTV : ∑' x, (P x - Q x) ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 923)) :
    PMF.CoupledWithin P Q (ENNReal.ofReal (1 / (2 : ℝ) ^ 923)) :=
  (coupledWithin_iff_excess_le P Q _).2 samplerTV

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.Width638.selected_of_not_bad
#print axioms SigabaNeo.Wall1.Width638.exists_disagreeing_first_closest
#print axioms SigabaNeo.Wall1.oneDrawCoupling_of_samplerTV
