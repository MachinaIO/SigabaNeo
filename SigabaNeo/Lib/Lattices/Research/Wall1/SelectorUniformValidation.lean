module

public import Mathlib.Data.Finset.Option
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-! Finite validation on independent holdout data, simultaneously for all tie choices. -/

public section
noncomputable section
namespace SigabaNeo.Wall1.SelectorUniform
open Finset
open scoped Classical

variable {α D V : Type*} {k : ℕ}

/-- Distinct wrong candidates across all blocks. A failed decode contributes no candidate. -/
def wrong (options : Fin k → Finset (Option α)) (truth : α) : Finset α :=
  ((univ.biUnion options).eraseNone).erase truth

theorem mem_wrong {options : Fin k → Finset (Option α)} {truth a : α} :
    a ∈ wrong options truth ↔ a ≠ truth ∧ ∃ i, some a ∈ options i := by
  simp [wrong]

/-- The ordered validation rule applied to one choice in each block. -/
def first (choose : Fin k → Option α) (accept : α → Bool) : Option α :=
  (List.finRange k).findSome? fun i ↦ (choose i).filter accept

/-- This event only depends on the candidate sets, the truth and the validation data. -/
def credited (options : Fin k → Finset (Option α)) (truth : α) (accept : α → Bool) : Prop :=
  (∃ i, options i = {some truth}) ∧ ∀ a ∈ wrong options truth, accept a = false

/-- The same credited input works for every selection, even one made after seeing validation. -/
theorem first_of_credited {options : Fin k → Finset (Option α)} {truth : α}
    {accept : α → Bool} (h : credited options truth accept) (ht : accept truth = true)
    (choose : Fin k → Option α) (hc : ∀ i, choose i ∈ options i) : first choose accept = some truth := by
  obtain ⟨⟨i, hi⟩, reject⟩ := h
  have hsome : first choose accept ≠ none := by
    intro hn
    have hz := List.findSome?_eq_none_iff.mp hn i (List.mem_finRange i)
    have hx : choose i = some truth := mem_singleton.mp (hi ▸ hc i)
    simp [hx, ht] at hz
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hsome
  obtain ⟨j, _, hj⟩ := List.exists_of_findSome?_eq_some (show
    (List.finRange k).findSome? (fun i ↦ (choose i).filter accept) = some a from ha)
  obtain ⟨he, hv⟩ := Option.filter_eq_some_iff.mp hj
  by_contra hf
  have ne : a ≠ truth := fun eq ↦ hf (eq ▸ ha)
  have hr := reject a (mem_wrong.mpr ⟨ne, j, he ▸ hc j⟩)
  simp_all

/-- Finite event mass under nonnegative rational weights. -/
def mass {X : Type*} [Fintype X] (p : X → ℚ) (E : X → Prop) : ℚ :=
  ∑ x, if E x then p x else 0

private theorem mass_mono {X : Type*} [Fintype X] (p : X → ℚ) (hp : ∀ x, 0 ≤ p x)
    {E F : X → Prop} (h : ∀ x, E x → F x) : mass p E ≤ mass p F := by
  unfold mass
  exact sum_le_sum fun x _ ↦ by by_cases he : E x <;> by_cases hf : F x <;> simp_all

/-- Union bound for a finite candidate set, conditional on the block data. -/
theorem any_accept_le [Fintype V] (p : V → ℚ) (hp : ∀ v, 0 ≤ p v) (C : Finset α)
    (accept : V → α → Bool) (ε : ℚ) (bound : ∀ a ∈ C, mass p (fun v ↦ accept v a) ≤ ε) :
    mass p (fun v ↦ ∃ a ∈ C, accept v a = true) ≤ C.card * ε := by
  classical
  calc
    _ ≤ ∑ v, ∑ a ∈ C, if accept v a then p v else 0 := by
      apply sum_le_sum
      intro v _
      split_ifs with h
      · obtain ⟨a, ha, hv⟩ := h
        exact (show p v = (if accept v a then p v else 0) by simp [hv]).le.trans
          (single_le_sum (f := fun a ↦ if accept v a then p v else 0)
            (fun a _ ↦ by split <;> simp_all) ha)
      · exact sum_nonneg fun a _ ↦ by split <;> simp_all
    _ = ∑ a ∈ C, mass p (fun v ↦ accept v a) := by
      rw [sum_comm]
      refine sum_congr rfl fun a _ ↦ sum_congr rfl fun v _ ↦ ?_
      by_cases h : accept v a = true <;> simp [h]
    _ ≤ ∑ _a ∈ C, ε := sum_le_sum bound
    _ = _ := by simp

/-- Complementary mass of the selector-independent credit under the product law. -/
theorem uncredited_mass_le [Fintype D] [Fintype V]
    (p : D → ℚ) (q : V → ℚ) (hp : ∀ d, 0 ≤ p d) (hq : ∀ v, 0 ≤ q v) (total : ∑ v, q v = 1)
    (options : D → Fin k → Finset (Option α)) (truth : D → α) (accept : D → V → α → Bool)
    (ε : ℚ) (hε : 0 ≤ ε)
    (bound : ∀ d a, a ∈ wrong (options d) (truth d) → mass q (fun v ↦ accept d v a) ≤ ε) :
    (∑ d, p d * mass q (fun v ↦ ¬ credited (options d) (truth d) (accept d v))) ≤
      mass p (fun d ↦ ∀ i, options d i ≠ {some (truth d)}) +
      (∑ d, p d * (wrong (options d) (truth d)).card) * ε := by
  rw [mass, sum_mul, ← sum_add_distrib]
  apply sum_le_sum
  intro d _
  by_cases good : ∃ i, options d i = {some (truth d)}
  · have hn : ¬ ∀ i, options d i ≠ {some (truth d)} := by simpa using good
    rw [ite_eq_right hn, zero_add, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (hp d)
    refine (mass_mono q hq ?_).trans (any_accept_le q hq _ (accept d) ε (bound d))
    intro v hf
    by_contra! hall
    exact hf ⟨good, fun a ha ↦ by simpa using hall a ha⟩
  · have hn : ∀ i, options d i ≠ {some (truth d)} := by simpa using good
    rw [ite_eq_left hn]
    have one : mass q (fun v ↦ ¬ credited (options d) (truth d) (accept d v)) ≤ 1 := by
      rw [← total]
      apply sum_le_sum
      intro v _
      split <;> simp_all
    exact (mul_le_of_le_one_right (hp d) one).trans
      (le_add_of_nonneg_right (mul_nonneg (mul_nonneg (hp d) (Nat.cast_nonneg _)) hε))

/-- Under the product law, failure for *any* selector costs at most the all-bad probability
plus the expected number of distinct wrong candidates times the one-candidate holdout bound. -/
theorem any_selection_failure_le [Fintype D] [Fintype V]
    (p : D → ℚ) (q : V → ℚ) (hp : ∀ d, 0 ≤ p d) (hq : ∀ v, 0 ≤ q v) (total : ∑ v, q v = 1)
    (options : D → Fin k → Finset (Option α)) (truth : D → α) (accept : D → V → α → Bool)
    (ht : ∀ d v, accept d v (truth d) = true) (ε : ℚ) (hε : 0 ≤ ε)
    (bound : ∀ d a, a ∈ wrong (options d) (truth d) → mass q (fun v ↦ accept d v a) ≤ ε) :
    (∑ d, p d * mass q (fun v ↦ ∃ choose : Fin k → Option α,
      (∀ i, choose i ∈ options d i) ∧ first choose (accept d v) ≠ some (truth d))) ≤
      mass p (fun d ↦ ∀ i, options d i ≠ {some (truth d)}) +
      (∑ d, p d * (wrong (options d) (truth d)).card) * ε := by
  refine le_trans (sum_le_sum fun d _ ↦ mul_le_mul_of_nonneg_left (mass_mono q hq ?_) (hp d))
    (uncredited_mass_le p q hp hq total options truth accept ε hε bound)
  rintro v ⟨choose, hc, hf⟩ hcredit
  exact hf (first_of_credited hcredit (ht d v) choose hc)

end SigabaNeo.Wall1.SelectorUniform
#print axioms SigabaNeo.Wall1.SelectorUniform.first_of_credited
#print axioms SigabaNeo.Wall1.SelectorUniform.uncredited_mass_le
#print axioms SigabaNeo.Wall1.SelectorUniform.any_selection_failure_le
