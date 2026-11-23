module

public import SigabaNeo.Lib.Lattices.Research.Wall1.Width638Geometry
import all SigabaNeo.Lib.Lattices.Research.Wall1.QaryMembership
import all SigabaNeo.Lib.Lattices.Attacks.Primal.SampleDeletionBall
import all SigabaNeo.Lib.Lattices.Research.Wall1.Width638Geometry
import Mathlib.Tactic

/-! Expected-count form of the translated-ball bound. Summed over all designs, the
number of nonplanted closed-ball points sharing the plant's output is at most
`(ballCount - 1) * #designs / q^r`. This is the first moment behind `translated_ball`. -/

public section
namespace SigabaNeo.Wall1.Width638
open QaryMembership SigabaNeo.SampleDeletion Finset Matrix

variable {r n q : ℕ} [Fact q.Prime]

/-- Nonplanted points of the closed ball of radius `normSq p` with the plant's output. -/
noncomputable def competitors (p : Grid r n) (A : Design r n q) : Finset (Grid r n) := by
  classical
  exact (Fintype.ofFinite (Points (Fin r ⊕ Fin n) (normSq p))).elems.image Subtype.val |>.filter
    fun w ↦ w ≠ p ∧ output A w = output A p

theorem expected_competitors (p : Grid r n) (hq : 4 * normSq p < q^2) :
    (∑ A : Design r n q, (competitors p A).card) * q^r ≤
      (ballCount (r+n) (normSq p) - 1) * Fintype.card (Design r n q) := by
  classical
  let P := Points (Fin r ⊕ Fin n) (normSq p)
  let inst : Fintype P := Fintype.ofFinite P
  let p₀ : P := ⟨p, le_rfl⟩
  let S := (univ : Finset P).erase p₀
  let event (w : P) := designs (fun A : Design r n q ↦ output A w.val = output A p)
  have card_comp (A : Design r n q) :
      (competitors p A).card = (S.filter fun w ↦ output A w.val = output A p).card := by
    unfold competitors
    rw [show (Fintype.ofFinite P).elems = (univ : Finset P) from rfl]
    rw [filter_image, card_image_of_injective _ Subtype.val_injective]
    congr 1
    ext w
    simp only [S, mem_filter, mem_univ, true_and, mem_erase]
    constructor
    · rintro ⟨hne, he⟩
      exact ⟨⟨fun e ↦ hne (congrArg Subtype.val e), trivial⟩, he⟩
    · rintro ⟨⟨hne, -⟩, he⟩
      exact ⟨fun e ↦ hne (Subtype.ext e), he⟩
  have swap : ∑ A : Design r n q, (competitors p A).card = ∑ w ∈ S, (event w).card := by
    simp_rw [card_comp, card_filter]
    rw [sum_comm]
    refine sum_congr rfl fun w _ ↦ ?_
    rw [← card_filter]
    congr 1
    ext A
    simp [event, designs]
  have count : S.card = ballCount (r+n) (normSq p) - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, ← Nat.card_eq_fintype_card]
    change Nat.card (Points (Fin r ⊕ Fin n) _) - 1 = _
    rw [card_points]
    simp
  calc
    _ = ∑ w ∈ S, (event w).card * q^r := by rw [swap, sum_mul]
    _ ≤ ∑ _w ∈ S, Fintype.card (Design r n q) := sum_le_sum fun w hw ↦
      competitor_count w.val p (fun e ↦ (mem_erase.mp hw).1 (Subtype.ext e)) w.property hq
    _ = _ := by simp [count]

end SigabaNeo.Wall1.Width638

#print axioms SigabaNeo.Wall1.Width638.expected_competitors
