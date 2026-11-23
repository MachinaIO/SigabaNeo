import SigabaNeo.Lib.Lattices.Research.Wall1.SelectedCollisionCertificate
import Mathlib.Data.Nat.Choose.Sum

/-! # Nonnegative weighted Bonferroni bounds for selected histories

The finite intersection sums retain every selection event. The theorem does not
evaluate these intersections under the concrete BKZ input law.
-/

noncomputable section
namespace SigabaNeo.Wall1.SelectedBonferroni
open Finset
open SigabaNeo.Wall1.SelectedCollisionCertificate
open scoped Classical

/-- Even truncation of the absence indicator for `n` present forbidden events. -/
def evenTruncation (n k : ℕ) : ℚ :=
  ∑ j ∈ range (2 * k + 1), (-1 : ℚ) ^ j * n.choose j

/-- The truncated indicator is one when no forbidden event occurs. -/
theorem evenTruncation_zero (k : ℕ) : evenTruncation 0 k = 1 := by
  rw [evenTruncation, sum_eq_single 0]
  · simp
  · intro j hj hj0
    rw [Nat.choose_eq_zero_of_lt (by omega : 0 < j)]
    simp
  · simp

/-- With at least one hit, the even alternating sum is a nonnegative binomial coefficient. -/
theorem evenTruncation_succ (n k : ℕ) :
    evenTruncation (n + 1) k = (n.choose (2 * k) : ℚ) := by
  have h := Int.alternating_sum_range_choose_eq_choose (n := n) (m := 2 * k)
  have hs : (-1 : ℤ) ^ (2 * k) = 1 := by simp [pow_mul]
  rw [hs, one_mul] at h
  dsimp [evenTruncation]
  exact_mod_cast h

/-- Pointwise domination of the exact absence indicator, at every even cutoff. -/
theorem absence_le_evenTruncation (n k : ℕ) :
    (if n = 0 then (1 : ℚ) else 0) ≤ evenTruncation n k := by
  cases n with
  | zero => simp [evenTruncation_zero]
  | succ n => simp [evenTruncation_succ]

/-- The weighted absence bound needs nonnegativity, not independence. -/
theorem weighted_absence_bound {Ω ι : Type*} (samples : Finset Ω)
    (hits : Ω → Finset ι) (weight : Ω → ℚ) (k : ℕ)
    (hweight : ∀ ω ∈ samples, 0 ≤ weight ω) :
    (∑ ω ∈ samples.filter (fun ω ↦ hits ω = ∅), weight ω) ≤
      ∑ ω ∈ samples, weight ω * evenTruncation (hits ω).card k := by
  rw [sum_filter]
  apply sum_le_sum
  intro ω hω
  have h := mul_le_mul_of_nonneg_left
    (absence_le_evenTruncation (hits ω).card k) (hweight ω hω)
  simpa only [card_eq_zero, mul_ite, mul_one, mul_zero] using h

/-- Counting present `j`-fold intersections is exactly a binomial coefficient. -/
theorem choose_eq_intersection_sum {ι : Type*} (B H : Finset ι) (hHB : H ⊆ B) (j : ℕ) :
    (H.card.choose j : ℚ) =
      ∑ T ∈ B.powersetCard j, if T ⊆ H then (1 : ℚ) else 0 := by
  have he : (B.powersetCard j).filter (fun T ↦ T ⊆ H) = H.powersetCard j := by
    ext T
    simp only [mem_filter, mem_powersetCard]
    constructor
    · intro h
      exact ⟨h.2, h.1.2⟩
    · intro h
      exact ⟨⟨h.1.trans hHB, h.2⟩, h.1⟩
  rw [← card_powersetCard, ← he]
  simp

/-- Reordering the hit-count expression yields the actual intersection sums. -/
theorem weighted_intersection_expansion {Ω ι : Type*} (samples : Finset Ω)
    (B : Finset ι) (hits : Ω → Finset ι) (weight : Ω → ℚ) (k : ℕ)
    (hB : ∀ ω ∈ samples, hits ω ⊆ B) :
    (∑ ω ∈ samples, weight ω * evenTruncation (hits ω).card k) =
      ∑ j ∈ range (2 * k + 1), (-1 : ℚ) ^ j *
        ∑ T ∈ B.powersetCard j,
          ∑ ω ∈ samples.filter (fun ω ↦ T ⊆ hits ω), weight ω := by
  calc
    _ = ∑ ω ∈ samples, ∑ j ∈ range (2 * k + 1),
        ∑ T ∈ B.powersetCard j,
          weight ω * ((-1 : ℚ) ^ j * if T ⊆ hits ω then 1 else 0) := by
      apply sum_congr rfl
      intro ω hω
      simp only [evenTruncation, mul_sum]
      apply sum_congr rfl
      intro j hj
      rw [choose_eq_intersection_sum B (hits ω) (hB ω hω) j]
      simp only [mul_sum]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro j hj
      rw [sum_comm, mul_sum]
      apply sum_congr rfl
      intro T hT
      simp [sum_filter, mul_sum, mul_ite, mul_comm]

/-- Every even truncation of nonnegative weighted intersection sums is an upper bound. -/
theorem weighted_bonferroni {Ω ι : Type*} (samples : Finset Ω)
    (B : Finset ι) (hits : Ω → Finset ι) (weight : Ω → ℚ) (k : ℕ)
    (hB : ∀ ω ∈ samples, hits ω ⊆ B)
    (hweight : ∀ ω ∈ samples, 0 ≤ weight ω) :
    (∑ ω ∈ samples.filter (fun ω ↦ hits ω = ∅), weight ω) ≤
      ∑ j ∈ range (2 * k + 1), (-1 : ℚ) ^ j *
        ∑ T ∈ B.powersetCard j,
          ∑ ω ∈ samples.filter (fun ω ↦ T ⊆ hits ω), weight ω := by
  rw [← weighted_intersection_expansion samples B hits weight k hB]
  exact weighted_absence_bound samples hits weight k hweight

/-- The parity tail certificate combined with even-order selection intersections. -/
theorem selected_parity_tail {Ω ι : Type*} (samples : Finset Ω)
    (B : Finset ι) (hits : Ω → Finset ι) (J : Ω → ℤ) (k : ℕ)
    {a T : ℤ} (ha : a + 2 ≤ T)
    (hB : ∀ ω ∈ samples, hits ω ⊆ B)
    (hparity : ∀ ω ∈ samples, J ω % 2 ≠ a % 2) :
    ((samples.filter fun ω ↦ hits ω = ∅ ∧ T ≤ J ω).card : ℚ) ≤
      (∑ j ∈ range (2 * k + 1), (-1 : ℚ) ^ j *
        ∑ S ∈ B.powersetCard j,
          ∑ ω ∈ samples.filter (fun ω ↦ S ⊆ hits ω), parityPolynomial a (J ω)) /
        parityPolynomial a T := by
  apply (le_div_iff₀ (polynomial_threshold_pos ha)).2
  have htail := selected_tail_count (samples.filter fun ω ↦ hits ω = ∅) J
    (a := a) (T := T) (by omega) (fun ω hω ↦ hparity ω (mem_filter.mp hω).1)
  have hsum := weighted_bonferroni samples B hits (fun ω ↦ parityPolynomial a (J ω)) k
    hB (fun ω hω ↦ polynomial_nonneg (hparity ω hω))
  apply le_trans ?_ hsum
  simpa only [filter_filter] using htail

end SigabaNeo.Wall1.SelectedBonferroni

#print axioms SigabaNeo.Wall1.SelectedBonferroni.evenTruncation_zero
#print axioms SigabaNeo.Wall1.SelectedBonferroni.evenTruncation_succ
#print axioms SigabaNeo.Wall1.SelectedBonferroni.absence_le_evenTruncation
#print axioms SigabaNeo.Wall1.SelectedBonferroni.weighted_absence_bound
#print axioms SigabaNeo.Wall1.SelectedBonferroni.choose_eq_intersection_sum
#print axioms SigabaNeo.Wall1.SelectedBonferroni.weighted_intersection_expansion
#print axioms SigabaNeo.Wall1.SelectedBonferroni.weighted_bonferroni
#print axioms SigabaNeo.Wall1.SelectedBonferroni.selected_parity_tail
