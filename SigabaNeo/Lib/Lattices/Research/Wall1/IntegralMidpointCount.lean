module

public import SigabaNeo.Lib.Lattices.Attacks.Primal.SampleDeletionBall
import all SigabaNeo.Lib.Lattices.Attacks.Primal.SampleDeletionBall
import Mathlib.Tactic

/-! The integral midpoint counting argument of ADS, Lemma 5.1, for affine sets.
The anchor and the other point may both lie strictly above the minimum. -/

@[expose] public section
namespace SigabaNeo.Wall1.CVP638

open SigabaNeo.SampleDeletion

variable {ι : Type*} [Fintype ι]

/-- The signed parallelogram identity in the integer coordinates used by `ballCount`. -/
theorem integral_midpoint_energy (x h : ι → ℤ) :
    normSq x + normSq (fun i ↦ x i + 2*h i) =
    2 * normSq (fun i ↦ x i + h i) + 2 * normSq h := by
  unfold normSq
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  zify
  simp only [sq_abs]
  ring

/-- If a parity fiber S admits integral half-differences and its midpoints have energy
at least D, its portion up through energy D+k embeds in the integer k-ball. -/
theorem parity_slice_card_le (S : Set (ι → ℤ)) (D k : ℕ)
    (midpoints : ∀ x ∈ S, ∀ y ∈ S, ∃ h : ι → ℤ,
      (∀ i, y i = x i + 2*h i) ∧ D ≤ normSq (fun i ↦ x i + h i)) :
    Nat.card {y : ι → ℤ // y ∈ S ∧ normSq y ≤ D+k} ≤ ballCount (Fintype.card ι) k := by
  classical
  let B := {y : ι → ℤ // y ∈ S ∧ normSq y ≤ D+k}
  by_cases hn : Nonempty B
  · obtain ⟨x⟩ := hn
    choose diff hdiff hlower using fun y : B ↦ midpoints x.val x.property.1 y.val y.property.1
    have hball (y : B) : normSq (diff y) ≤ k := by
      have he := integral_midpoint_energy x.val (diff y)
      rw [← funext (hdiff y)] at he
      have hx := x.property.2
      have hy := y.property.2
      have hm := hlower y
      omega
    let embed (y : B) : Points ι k := ⟨diff y, hball y⟩
    rw [← card_points ι k]
    apply Nat.card_le_card_of_injective embed
    intro y z h
    have e : diff y = diff z := congrArg Subtype.val h
    exact Subtype.ext (funext fun i ↦ by rw [hdiff y i, hdiff z i, e])
  · have : IsEmpty B := not_nonempty_iff.mp hn
    change Nat.card B ≤ _
    simp

/-- Membership in a minimizing set suffices even if different list orders select
different minimizers. -/
theorem minimum_of_hit {V : Type*} {energy : V → ℕ} {D : ℕ} (globalLower : ∀ v, D ≤ energy v)
    {items : Multiset V} {best : V} (least : ∀ v ∈ items, energy best ≤ energy v)
    (hit : ∃ v ∈ items, energy v = D) : energy best = D := by
  obtain ⟨v,hv,rfl⟩ := hit
  exact le_antisymm (least _ hv) (globalLower best)

end SigabaNeo.Wall1.CVP638

#print axioms SigabaNeo.Wall1.CVP638.integral_midpoint_energy
#print axioms SigabaNeo.Wall1.CVP638.parity_slice_card_le
#print axioms SigabaNeo.Wall1.CVP638.minimum_of_hit
