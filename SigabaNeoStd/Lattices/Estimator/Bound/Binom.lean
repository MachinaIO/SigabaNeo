import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# A tail bound for guessing a dense secret

`z` coordinates of a secret with `h` nonzero entries among `n` are guessed with at most `w` nonzero
values. The number of `z`-subsets meeting the support in at most `w` places,
`Σ_{w' ≤ w} C(h,w') C(n−h,z−w')`, is at most `C(n,z) · 2^z / 4^{z−w}` when at least three
quarters of the entries are nonzero (`hit_mul_le`): a union bound over the `z − w` coordinates
that must be zero.
-/

namespace SigabaNeo.Lattices.Estimator.Binom

open Finset

/-- `C(n−h, r) 4^r ≤ C(n, r)` when `4 (n − h) ≤ n`. -/
theorem choose_sub_mul_pow_le {n h : ℕ} (hn : 4 * (n - h) ≤ n) :
    ∀ r, (n - h).choose r * 4 ^ r ≤ n.choose r := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
    have e1 := Nat.choose_succ_right_eq (n - h) r
    have e2 := Nat.choose_succ_right_eq n r
    have h1 : 4 * (n - h - r) ≤ n - r := by omega
    have : (n - h).choose (r + 1) * 4 ^ (r + 1) * (r + 1) ≤ n.choose (r + 1) * (r + 1) := by
      calc (n - h).choose (r + 1) * 4 ^ (r + 1) * (r + 1)
          = (n - h).choose (r + 1) * (r + 1) * 4 ^ r * 4 := by ring
        _ = (n - h).choose r * (n - h - r) * 4 ^ r * 4 := by rw [e1]
        _ = (n - h).choose r * 4 ^ r * (4 * (n - h - r)) := by ring
        _ ≤ n.choose r * (n - r) := Nat.mul_le_mul ih h1
        _ = n.choose (r + 1) * (r + 1) := e2.symm
    exact Nat.le_of_mul_le_mul_right this (Nat.succ_pos r)

/-- One term of the hit count, shifted to `w`. -/
theorem choose_le_mul {N z w w' : ℕ} (hw : w' ≤ w) (hwz : w ≤ z) :
    N.choose (z - w') ≤ N.choose (z - w) * (N - (z - w)).choose (w - w') := by
  have := Nat.choose_mul (n := N) (k := z - w') (s := z - w) (by omega)
  have hk : z - w' - (z - w) = w - w' := by omega
  rw [hk] at this
  have hpos : 1 ≤ (z - w').choose (z - w) := Nat.choose_pos (by omega)
  calc N.choose (z - w') ≤ N.choose (z - w') * (z - w').choose (z - w) := Nat.le_mul_of_pos_right _ hpos
    _ = _ := this

/-- The hit count is at most `C(n−h, z−w) C(n−z+w, w)`. -/
theorem hit_le {n h z w lo : ℕ} (hw : w ≤ z) (hz : z ≤ n) (hhn : h ≤ n) :
    ∑ w' ∈ Ico lo (w + 1), h.choose w' * (n - h).choose (z - w') ≤
      (n - h).choose (z - w) * (n - z + w).choose w := by
  by_cases hc : z - w ≤ n - h
  · calc ∑ w' ∈ Ico lo (w + 1), h.choose w' * (n - h).choose (z - w')
        ≤ ∑ w' ∈ Ico lo (w + 1), h.choose w' *
            ((n - h).choose (z - w) * (n - h - (z - w)).choose (w - w')) := by
          apply sum_le_sum; intro w' hw'
          rw [mem_Ico] at hw'
          exact Nat.mul_le_mul_left _ (choose_le_mul (by omega) hw)
      _ ≤ ∑ w' ∈ range (w + 1), h.choose w' *
            ((n - h).choose (z - w) * (n - h - (z - w)).choose (w - w')) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro x hx; rw [mem_Ico] at hx; rw [mem_range]; omega
          · intros; positivity
      _ = (n - h).choose (z - w) * ∑ w' ∈ range (w + 1), h.choose w' * (n - h - (z - w)).choose (w - w') := by
          rw [mul_sum]; apply sum_congr rfl; intros; ring
      _ = (n - h).choose (z - w) * (n - z + w).choose w := by
          congr 1
          have := Nat.add_choose_eq h (n - h - (z - w)) w
          rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at this
          rw [show h + (n - h - (z - w)) = n - z + w by omega] at this
          rw [this]
  · have : ∀ w' ∈ Ico lo (w + 1), h.choose w' * (n - h).choose (z - w') = 0 := by
      intro w' hw'; rw [mem_Ico] at hw'
      rw [Nat.choose_eq_zero_of_lt (n := n - h) (k := z - w') (by omega), mul_zero]
    rw [sum_eq_zero this]; exact Nat.zero_le _

/-- **The tail bound**: `hit · 4^{z−w} ≤ C(n,z) · 2^z`. -/
theorem hit_mul_le {n h z w lo : ℕ} (hw : w ≤ z) (hz : z ≤ n) (hhn : h ≤ n)
    (h4 : 4 * (n - h) ≤ n) :
    (∑ w' ∈ Ico lo (w + 1), h.choose w' * (n - h).choose (z - w')) * 4 ^ (z - w) ≤
      n.choose z * 2 ^ z := by
  have h1 := hit_le (lo := lo) hw hz hhn
  have h2 := choose_sub_mul_pow_le h4 (z - w)
  have h3 := Nat.choose_mul (n := n) (k := z) (s := z - w) (by omega)
  rw [show z - (z - w) = w by omega, show n - (z - w) = n - z + w by omega] at h3
  have h4' := Nat.choose_le_two_pow z (z - w)
  calc (∑ w' ∈ Ico lo (w + 1), h.choose w' * (n - h).choose (z - w')) * 4 ^ (z - w)
      ≤ (n - h).choose (z - w) * (n - z + w).choose w * 4 ^ (z - w) := Nat.mul_le_mul_right _ h1
    _ = (n - h).choose (z - w) * 4 ^ (z - w) * (n - z + w).choose w := by ring
    _ ≤ n.choose (z - w) * (n - z + w).choose w := Nat.mul_le_mul_right _ h2
    _ = n.choose z * z.choose (z - w) := h3.symm
    _ ≤ n.choose z * 2 ^ z := Nat.mul_le_mul_left _ h4'

theorem hit_pos {n h z lo : ℕ} (hz : z ≤ n) (hhn : h ≤ n) (hlo : lo = h - (n - z)) {w : ℕ}
    (hw1 : lo ≤ w) :
    0 < ∑ w' ∈ Ico lo (w + 1), h.choose w' * (n - h).choose (z - w') := by
  apply lt_of_lt_of_le _ (single_le_sum (f := fun w' => h.choose w' * (n - h).choose (z - w'))
    (fun _ _ => Nat.zero_le _) (mem_Ico.mpr ⟨le_rfl, by omega⟩))
  apply Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))

theorem log2_mul_two_pow {x : ℕ} (hx : 0 < x) (k : ℕ) : Nat.log2 (x * 2 ^ k) = Nat.log2 x + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, Nat.log2_eq_log_two, Nat.log_mul_base (by norm_num)
      (by positivity), ← Nat.log2_eq_log_two, ih]; ring

end SigabaNeo.Lattices.Estimator.Binom
