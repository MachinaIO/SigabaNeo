module

public import SigabaNeo.Lib.Lattices.Research.Wall1.SelectedSlide

@[expose] public section

namespace SigabaNeo.Wall1

/-- The four fair bits have second moment one and fourth moment five halves. -/
theorem cbd2_bit_moments :
    let x := fun (b : Fin 4 → Bool) ↦ (∑ j, if b j then (1 : ℚ) else 0) - 2
    (∑ b, x b) = 0 ∧ (∑ b, x b ^ 2) = 16 ∧
      (∑ b, x b ^ 3) = 0 ∧ (∑ b, x b ^ 4) = 40 := by
  decide +kernel

theorem projector_sum_squares {N : ℕ} (P : Matrix (Fin N) (Fin N) ℝ)
    (hs : P.transpose = P) (hp : P * P = P) :
    (∑ i, ∑ j, P i j ^ 2) = P.trace := by
  calc
    _ = (P * P.transpose).trace := by simp [Matrix.trace, Matrix.mul_apply, pow_two]
    _ = _ := by rw [hs, hp]

theorem mass_abs_tail {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ)
    (v t : ℝ) (ht : 0 < t) (hv : (∑ a, f a ^ 2) ≤ Fintype.card α * v) :
    mass (fun a ↦ t ≤ |f a|) ≤ v / t ^ 2 := by
  classical
  let S := Finset.univ.filter (fun a ↦ t ≤ |f a|)
  have bound : (S.card : ℝ) * t ^ 2 ≤ ∑ a, f a ^ 2 := calc
    _ = ∑ _a ∈ S, t ^ 2 := by simp
    _ ≤ ∑ a ∈ S, f a ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      have h := (Finset.mem_filter.mp ha).2
      calc
        _ ≤ |f a| ^ 2 := pow_le_pow_left₀ ht.le h _
        _ = _ := sq_abs _
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ ↦ sq_nonneg (f a))
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  change (S.card : ℝ) / Fintype.card α ≤ _
  rw [div_le_div_iff₀ hc (sq_pos_of_pos ht)]
  simpa [mul_comm] using bound.trans hv

end SigabaNeo.Wall1
