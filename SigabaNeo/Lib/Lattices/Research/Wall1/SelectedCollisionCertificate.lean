import SigabaNeo.Lib.Lattices.Research.Wall1.CosetOccupancy

/-! # Integer collision certificates on selected finite samples

These results justify the parity polynomial and the tail-count transfer in Part 268.
The selected subset is arbitrary: independence or a uniform conditional flag law is
not assumed. Evaluating its polynomial sum for the actual BKZ history remains open.
-/

noncomputable section
namespace SigabaNeo.Wall1.SelectedCollisionCertificate
open Finset
open scoped Classical

/-- Squaring each occupancy preserves the parity of their total. -/
theorem occupancy_parity {α : Type*} (s : Finset α) (n : α → ℕ) :
    (∑ c ∈ s, n c ^ 2) % 2 = (∑ c ∈ s, n c) % 2 := by
  rw [sum_nat_mod s 2 (fun c ↦ n c ^ 2), sum_nat_mod s 2 n]
  congr 1
  apply sum_congr rfl
  intro c hc
  have h : n c % 2 = 0 ∨ n c % 2 = 1 := by omega
  rcases h with h | h <;> simp [Nat.pow_mod, h]

/-- Parity of the existing coset-occupancy collision statistic. -/
theorem collision_count_parity {α : Type*} [Fintype α] (n : α → ℕ) :
    CosetOccupancy.collisionCount n % 2 = (∑ c, n c) % 2 := by
  simpa [CosetOccupancy.collisionCount] using occupancy_parity (univ : Finset α) n

/-- The nonnegative-on-one-parity polynomial, evaluated in the rationals. -/
def parityPolynomial (a j : ℤ) : ℚ := ((j : ℚ) - a) ^ 2 - 1

/-- Distinct integers are separated by at least one, making this polynomial nonnegative. -/
theorem polynomial_nonneg_of_ne {a j : ℤ} (h : j ≠ a) :
    0 ≤ parityPolynomial a j := by
  have hgap : j ≤ a - 1 ∨ a + 1 ≤ j := by omega
  rcases hgap with hgap | hgap
  · have hq : (j : ℚ) ≤ (a : ℚ) - 1 := by exact_mod_cast hgap
    dsimp [parityPolynomial]
    nlinarith [sq_nonneg ((a : ℚ) - j - 1)]
  · have hq : (a : ℚ) + 1 ≤ j := by exact_mod_cast hgap
    dsimp [parityPolynomial]
    nlinarith [sq_nonneg ((j : ℚ) - a - 1)]

/-- Opposite parities exclude the sole integer where the polynomial is negative. -/
theorem polynomial_nonneg {a j : ℤ} (h : j % 2 ≠ a % 2) :
    0 ≤ parityPolynomial a j :=
  polynomial_nonneg_of_ne (by intro he; exact h (congrArg (· % 2) he))

/-- Monotonicity on the upper side of the center. -/
theorem polynomial_tail_mono {a T j : ℤ} (ha : a ≤ T) (hj : T ≤ j) :
    parityPolynomial a T ≤ parityPolynomial a j := by
  have ha' : (a : ℚ) ≤ T := by exact_mod_cast ha
  have hj' : (T : ℚ) ≤ j := by exact_mod_cast hj
  dsimp [parityPolynomial]
  nlinarith [sq_nonneg ((j : ℚ) - T)]

/-- A threshold two integer units past the center has strictly positive denominator. -/
theorem polynomial_threshold_pos {a T : ℤ} (h : a + 2 ≤ T) :
    0 < parityPolynomial a T := by
  have hq : (a : ℚ) + 2 ≤ T := by exact_mod_cast h
  dsimp [parityPolynomial]
  nlinarith [sq_nonneg ((T : ℚ) - a - 2)]

/-- A pointwise certificate summed over an arbitrary selected subset. -/
theorem selected_tail_count {Ω : Type*} (selected : Finset Ω) (J : Ω → ℤ)
    {a T : ℤ} (ha : a ≤ T)
    (hparity : ∀ ω ∈ selected, J ω % 2 ≠ a % 2) :
    ((selected.filter fun ω ↦ T ≤ J ω).card : ℚ) * parityPolynomial a T ≤
      ∑ ω ∈ selected, parityPolynomial a (J ω) := by
  calc
    _ = ∑ ω ∈ selected.filter (fun ω ↦ T ≤ J ω), parityPolynomial a T := by simp
    _ ≤ ∑ ω ∈ selected.filter (fun ω ↦ T ≤ J ω), parityPolynomial a (J ω) := by
      apply sum_le_sum
      intro ω hω
      exact polynomial_tail_mono ha (mem_filter.mp hω).2
    _ ≤ ∑ ω ∈ selected, parityPolynomial a (J ω) := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro ω hω hnot
      exact polynomial_nonneg (hparity ω hω)

/-- The rational tail-count bound, retaining the selection in the numerator. -/
theorem selected_tail_count_le_div {Ω : Type*} (selected : Finset Ω) (J : Ω → ℤ)
    {a T : ℤ} (ha : a + 2 ≤ T)
    (hparity : ∀ ω ∈ selected, J ω % 2 ≠ a % 2) :
    ((selected.filter fun ω ↦ T ≤ J ω).card : ℚ) ≤
      (∑ ω ∈ selected, parityPolynomial a (J ω)) / parityPolynomial a T := by
  apply (le_div_iff₀ (polynomial_threshold_pos ha)).2
  exact selected_tail_count selected J (by omega) hparity

/-- Application to occupancy counts, with history-dependent finite label types. -/
theorem selected_occupancy_tail {Ω : Type*} {α : Ω → Type*}
    [∀ ω, Fintype (α ω)] (selected : Finset Ω) (n : ∀ ω, α ω → ℕ)
    {a T : ℤ} (ha : a + 2 ≤ T)
    (hparity : ∀ ω ∈ selected, ((∑ c, n ω c : ℕ) : ℤ) % 2 ≠ a % 2) :
    ((selected.filter fun ω ↦ T ≤ (CosetOccupancy.collisionCount (n ω) : ℤ)).card : ℚ) ≤
      (∑ ω ∈ selected, parityPolynomial a (CosetOccupancy.collisionCount (n ω))) /
        parityPolynomial a T := by
  apply selected_tail_count_le_div selected
    (fun ω ↦ (CosetOccupancy.collisionCount (n ω) : ℤ)) ha
  intro ω hω
  have hp : (CosetOccupancy.collisionCount (n ω) : ℤ) % 2 =
      ((∑ c, n ω c : ℕ) : ℤ) % 2 := by
    exact_mod_cast collision_count_parity (n ω)
  rw [hp]
  exact hparity ω hω

end SigabaNeo.Wall1.SelectedCollisionCertificate

#print axioms SigabaNeo.Wall1.SelectedCollisionCertificate.occupancy_parity
#print axioms SigabaNeo.Wall1.SelectedCollisionCertificate.collision_count_parity
#print axioms SigabaNeo.Wall1.SelectedCollisionCertificate.polynomial_nonneg
#print axioms SigabaNeo.Wall1.SelectedCollisionCertificate.polynomial_tail_mono
#print axioms SigabaNeo.Wall1.SelectedCollisionCertificate.polynomial_threshold_pos
#print axioms SigabaNeo.Wall1.SelectedCollisionCertificate.selected_tail_count
#print axioms SigabaNeo.Wall1.SelectedCollisionCertificate.selected_tail_count_le_div
#print axioms SigabaNeo.Wall1.SelectedCollisionCertificate.selected_occupancy_tail
