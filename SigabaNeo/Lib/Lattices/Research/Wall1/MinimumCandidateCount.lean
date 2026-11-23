module

public import SigabaNeo.Lib.Lattices.Research.Wall1.ClosestSelectionEvents
import all SigabaNeo.Lib.Lattices.Research.Wall1.ClosestSelectionEvents
import all SigabaNeo.Lib.Lattices.Attacks.Primal.SampleDeletionBall
import Mathlib.Tactic

/-! Finite first moments for decoded minima of integer point sets. -/

public section
noncomputable section
namespace SigabaNeo.Wall1.SelectorUniform
open SigabaNeo.SampleDeletion Finset
open scoped Classical

variable {ι α : Type*} [Fintype ι] {k : ℕ}

/-- Feasible points other than the reference point in its closed residual ball. -/
def competitors (F : (ι → ℤ) → Prop) (p : ι → ℤ) : Finset (ι → ℤ) :=
  letI : Finite (Points ι (normSq p)) := pointsFinite _ _
  ((Set.finite_range (fun z : Points ι (normSq p) ↦ z.val)).subset
    (show {x | F x ∧ x ≠ p ∧ normSq x ≤ normSq p} ⊆ _ from
      fun x hx ↦ ⟨⟨x, hx.2.2⟩, rfl⟩)).toFinset

@[simp] theorem mem_competitors {F : (ι → ℤ) → Prop} {p x : ι → ℤ} :
    x ∈ competitors F p ↔ F x ∧ x ≠ p ∧ normSq x ≤ normSq p :=
  Set.Finite.mem_toFinset _

/-- Multiple minima and repeated answers across blocks count only once on the left. -/
theorem wrong_minimum_card_le (F : Fin k → (ι → ℤ) → Prop)
    (decode : Fin k → (ι → ℤ) → Option α) (p : Fin k → ι → ℤ) (truth : α)
    (hp : ∀ i, F i (p i)) (hd : ∀ i, decode i (p i) = some truth) :
    (wrong (fun i ↦ minimumOptions (F i) (decode i)) truth).card ≤
      ∑ i, (competitors (F i) (p i)).card := by
  let answers i := ((competitors (F i) (p i)).image (decode i)).eraseNone
  have cover : wrong (fun i ↦ minimumOptions (F i) (decode i)) truth ⊆ univ.biUnion answers := by
    intro a ha
    obtain ⟨hne, i, hi⟩ := mem_wrong.mp ha
    obtain ⟨x, hx, he⟩ := mem_minimumOptions.mp hi
    refine mem_biUnion.mpr ⟨i, mem_univ _, mem_eraseNone.mpr (mem_image.mpr ⟨x, ?_, he⟩)⟩
    refine mem_competitors.mpr ⟨hx.1, ?_, hx.2 _ (hp i)⟩
    rintro rfl
    exact hne (Option.some.inj (he.symm.trans (hd i)))
  exact (card_le_card cover).trans (card_biUnion_le.trans
    (sum_le_sum fun i _ ↦ (card_eraseNone_le _).trans card_image_le))

/-- Weighted cardinality bound for arbitrary dependence among blocks. When the weights
sum to one, the two sides are respectively an expectation and a sum of expectations. -/
theorem expected_wrong_minimum_card_le {Ω : Type*} [Fintype Ω]
    (w : Ω → ℚ) (hw : ∀ ω, 0 ≤ w ω) (F : Ω → Fin k → (ι → ℤ) → Prop)
    (decode : Ω → Fin k → (ι → ℤ) → Option α) (p : Ω → Fin k → ι → ℤ) (truth : Ω → α)
    (hp : ∀ ω i, F ω i (p ω i)) (hd : ∀ ω i, decode ω i (p ω i) = some (truth ω)) :
    (∑ ω, w ω * (wrong (fun i ↦ minimumOptions (F ω i) (decode ω i)) (truth ω)).card) ≤
      ∑ i, ∑ ω, w ω * (competitors (F ω i) (p ω i)).card := by
  rw [sum_comm]
  apply sum_le_sum
  intro ω _
  rw [← mul_sum]
  apply mul_le_mul_of_nonneg_left _ (hw ω)
  exact_mod_cast wrong_minimum_card_le (F ω) (decode ω) (p ω) (truth ω) (hp ω) (hd ω)

end SigabaNeo.Wall1.SelectorUniform

#print axioms SigabaNeo.Wall1.SelectorUniform.wrong_minimum_card_le
#print axioms SigabaNeo.Wall1.SelectorUniform.expected_wrong_minimum_card_le
