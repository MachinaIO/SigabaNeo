import SigabaNeoStd.Lattices.Estimator.Model
import SigabaNeoStd.Lattices.Estimator.Bound.FxLemmas

/-!
# Invariants of loops, and lower bounds on costs

`CostGe k c`: the cost `c` is infinite or at least `k`. The searches of the attack models only
ever return a value they computed, so a lower bound on every candidate is a lower bound on the
result; `forIn_inv` is the invariant principle used for that, and `floorBits_ge` turns lower bounds
on every attack into a lower bound on `floorBits`.
-/

namespace SigabaNeo.Lattices.Estimator

open Fx

/-- `c` is infinite or at least `k`. -/
def CostGe (k : Fx) (c : Cost) : Prop := ∀ x, c = some x → k ≤ x

/-- The decidable form of `CostGe`. -/
def costGeB (k : Fx) (c : Cost) : Bool := c.all (k ≤ ·)

theorem costGe_iff {k : Fx} {c : Cost} : CostGe k c ↔ costGeB k c = true := by
  cases c <;> simp [CostGe, costGeB]

@[simp] theorem costGe_none (k : Fx) : CostGe k none := by simp [CostGe]

@[simp] theorem costGe_some {k x : Fx} : CostGe k (some x) ↔ k ≤ x := by simp [CostGe]

theorem CostGe.mono {k k' : Fx} {c : Cost} (h : CostGe k c) (hk : k' ≤ k) : CostGe k' c :=
  fun x hx => hk.trans (h x hx)

theorem CostGe.min {k : Fx} {a b : Cost} (ha : CostGe k a) (hb : CostGe k b) :
    CostGe k (Cost.min a b) := by
  cases a <;> cases b <;> simp_all [Cost.min, CostGe]

theorem CostGe.bind {k : Fx} {a : Option α} {f : α → Cost} (h : ∀ x, a = some x → CostGe k (f x)) :
    CostGe k (a.bind f) := by
  cases a <;> simp_all [CostGe]

/-- The invariant principle for `for` loops over a list in `Id`. -/
theorem list_forIn_inv {α β : Type} (l : List α) (b : β) (f : α → β → Id (ForInStep β))
    (I : β → Prop) (h0 : I b) (hf : ∀ a ∈ l, ∀ s, I s → I (f a s).run.value) :
    I (forIn l b f) := by
  induction l generalizing b with
  | nil => exact h0
  | cons a l ih =>
    rw [List.forIn_cons]
    have h1 := hf a (List.mem_cons_self ..) b h0
    generalize f a b = st at h1 ⊢
    cases st with
    | done s => exact h1
    | yield s => exact ih s h1 fun a' ha' => hf a' (List.mem_cons_of_mem _ ha')

/-- The invariant principle for `for` loops over a range in `Id`. -/
theorem forIn_inv {β : Type} (r : Std.Legacy.Range) (b : β) (f : ℕ → β → Id (ForInStep β))
    (I : β → Prop) (h0 : I b) (hf : ∀ a ∈ List.range' r.start r.size r.step, ∀ s, I s →
      I (f a s).run.value) : I (forIn r b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact list_forIn_inv _ b f I h0 hf

/-- A lower bound on every attack is a lower bound on `floorBits`. -/
theorem floorBits_ge {as : List AttackModel} {p : LWEParams} {kb : ℕ}
    (h : ∀ a ∈ as, CostGe ((kb : ℤ) * ONE) (a.cost p)) (hf : kb ≤ fallbackBits) :
    kb ≤ floorBits as p := by
  unfold floorBits
  split
  · rename_i c hc
    obtain ⟨a, ha, hac⟩ := minCost_attained hc
    have h1 : (kb : ℤ) * ONE ≤ c := h a ha c hac
    have h2 : (kb : ℤ) ≤ Fx.floor c := by
      unfold Fx.floor
      rw [Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt ONE_pos)]
      exact (Int.le_ediv_iff_mul_le ONE_pos).mpr h1
    omega
  · exact hf

theorem kb_le_fallbackBits {kb : ℕ} (h : kb ≤ 4673) : kb ≤ fallbackBits := by
  have : fallbackBits = 4673 := by decide +kernel
  omega

end SigabaNeo.Lattices.Estimator
