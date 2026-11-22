module

public import SigabaNeo.Lib.Lattices.Research.Wall1.StatDistance

/-! # Event probabilities after randomized postprocessing of a sampler -/

@[expose] public section

namespace SigabaNeo.Wall1

variable {α β : Type*}

/-- Keeping both the input and the output of a common probability kernel preserves the
statistical distance of the input laws. -/
theorem sdist_joint_same_kernel {P Q : α → ℝ} (hP : Summable P) (hQ : Summable Q)
    {K : α → β → ℝ} (hK0 : ∀ a b, 0 ≤ K a b) (hK : ∀ a, HasSum (K a) 1) :
    sdist (fun p : α × β ↦ P p.1 * K p.1 p.2) (fun p ↦ Q p.1 * K p.1 p.2) = sdist P Q := by
  have hfiber (a : α) :
      HasSum (fun b ↦ |P a * K a b - Q a * K a b|) |P a - Q a| := by
    simpa only [← sub_mul, abs_mul, abs_of_nonneg (hK0 a _), mul_one] using
      (hK a).mul_left |P a - Q a|
  have hjoint := hasSum_prod_of_nonneg (F := fun p : α × β ↦ |P p.1 * K p.1 p.2 -
    Q p.1 * K p.1 p.2|) (fun _ ↦ abs_nonneg _) hfiber (summable_abs_sub hP hQ).hasSum
  unfold sdist
  rw [hjoint.tsum_eq]

/-- A lower bound for an event of an ideal sequential sampler transfers to an approximate
sampler after shared randomized postprocessing. The event may inspect the full sample history
as well as the postprocessor's output. -/
theorem seqLaw_postprocess_event_lower {k l : (m : ℕ) → (Fin m → α) → α → ℝ}
    (hk0 : ∀ m x a, 0 ≤ k m x a) (hk : ∀ m x, HasSum (k m x) 1)
    (hl0 : ∀ m x a, 0 ≤ l m x a) (hl : ∀ m x, HasSum (l m x) 1)
    {ε : ℕ → ℝ} (hε : ∀ m x, sdist (k m x) (l m x) ≤ ε m) (n : ℕ)
    {K : (Fin n → α) → β → ℝ} (hK0 : ∀ x b, 0 ≤ K x b) (hK : ∀ x, HasSum (K x) 1)
    (E : (Fin n → α) × β → Prop) [DecidablePred E] {p : ℝ}
    (hideal : p ≤ ∑' z, if E z then seqLaw k n z.1 * K z.1 z.2 else 0) :
    p - ∑ m ∈ Finset.range n, ε m ≤ ∑' z, if E z then seqLaw l n z.1 * K z.1 z.2 else 0 := by
  have hP := seqLaw_hasSum hk0 hk n
  have hQ := seqLaw_hasSum hl0 hl n
  have htransfer := prob_le_prob_add_sdist
    (P := fun z : (Fin n → α) × β ↦ seqLaw k n z.1 * K z.1 z.2)
    (Q := fun z ↦ seqLaw l n z.1 * K z.1 z.2)
    (fun z ↦ mul_nonneg (seqLaw_nonneg hk0 n z.1) (hK0 z.1 z.2))
    (hasSum_bind (seqLaw_nonneg hk0 n) hP hK0 hK)
    (fun z ↦ mul_nonneg (seqLaw_nonneg hl0 n z.1) (hK0 z.1 z.2))
    (hasSum_bind (seqLaw_nonneg hl0 n) hQ hK0 hK) E
  rw [sdist_joint_same_kernel hP.summable hQ.summable hK0 hK] at htransfer
  exact sub_le_iff_le_add.mpr
    (hideal.trans (htransfer.trans (add_le_add le_rfl (sdist_seqLaw_le hk0 hk hl0 hl hε n))))

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.sdist_joint_same_kernel
#print axioms SigabaNeo.Wall1.seqLaw_postprocess_event_lower
