import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic

/-! A finite rational majorant for all nontrivial scalars in the field of order 3329. -/
namespace SigabaNeo.Wall1.RawScalarWeights

-- Pack the 109 rounded-up rational weights in base 2048. Expanding this literal once
-- gives constant-time lookup during the kernel's enumeration of the scalar rows.
local macro "rawWeightTable%" : term => do
  let packed := (List.range 109).foldr (fun k acc ↦
    (1024 * 15^k + 16^k - 1) / 16^k + 2048 * acc) 0
  return Lean.Syntax.mkNumLit (toString packed)

/-- Majorant for 1024 times the k-th power of 15/16. The last bucket covers the tail. -/
def bucket (k : ℕ) : ℕ := (rawWeightTable% >>> (11 * min k 108)) % 2048

private theorem weight_spec : ∀ k : Fin 109,
    1024 * 15^k.val ≤ bucket k.val * 16^k.val := by decide +kernel

theorem pow_le_bucket (k : ℕ) : (15/16 : ℝ)^k ≤ bucket k / 1024 := by
  let t := min k 108
  have h := weight_spec ⟨t, by dsimp [t]; omega⟩
  change 1024 * 15^t ≤ bucket t * 16^t at h
  have he : bucket t = bucket k := by simp [bucket,t]
  rw [he] at h
  calc
    _ ≤ (15/16 : ℝ)^t := pow_le_pow_of_le_one (by norm_num) (by norm_num) (min_le_left ..)
    _ ≤ _ := by
      rw [div_pow]
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
      rw [mul_comm ((15:ℝ)^t)]
      exact_mod_cast h

def magnitude (x : ℕ) : ℕ := min x (3329-x)

def entry (a x : ℕ) : ℕ :=
  bucket ((magnitude x ^ 2 + magnitude ((a*x)%3329) ^ 2) / 3072)

private def rowSum (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => rowSum a n + entry a n

private lemma prefix_sum (a n : ℕ) : rowSum a n = ∑ x ∈ Finset.range n, entry a x := by
  induction n with
  | zero => simp [rowSum]
  | succ n ih => simp [rowSum,ih,Finset.sum_range_succ]

/-- Positive half of a scalar row. The endpoints are treated separately. -/
def smallRow (a : ℕ) := rowSum a 577

lemma entry_field (a : ZMod 3329) (x : ZMod 3329) :
    entry a.val x.val = bucket ((x.valMinAbs.natAbs^2 + (a*x).valMinAbs.natAbs^2)/3072) := by
  simp [entry,magnitude,ZMod.valMinAbs_natAbs_eq_min,ZMod.val_mul]

private lemma entry_reflect (a : ZMod 3329) (x : ℕ) (hx : x < 1664) :
    entry a.val (1665+x) = entry a.val (1664-x) := by
  let y := (1664-x : ℕ)
  have hy : y < 3329 := by dsimp [y]; omega
  have hp : 1665+x < 3329 := by omega
  have he : ((1665+x:ℕ):ZMod 3329) = -(y:ZMod 3329) := by
    apply eq_neg_of_add_eq_zero_left
    rw [← Nat.cast_add,show 1665+x+y=3329 by dsimp [y]; omega]
    decide +kernel
  change entry a.val (1665+x) = entry a.val y
  rw [← ZMod.val_natCast_of_lt hp, ← ZMod.val_natCast_of_lt hy, entry_field, entry_field,he,
    mul_neg,ZMod.natAbs_valMinAbs_neg,ZMod.natAbs_valMinAbs_neg]

/-- Total one-coordinate interpolation weights for a nontrivial scalar, scaled by 1024. -/
theorem field_row_le (a : ZMod 3329) (ha : a ≠ 0) (h1 : a ≠ 1) (hm : a ≠ -1)
    (row_bound : ∀ b, 2 ≤ b → b < 3328 → smallRow b ≤ 93700) :
    ∑ x : ZMod 3329, entry a.val x.val ≤ 190*1024 := by
  have lo : 2 ≤ a.val := by
    by_contra! h
    rcases (by omega : a.val = 0 ∨ a.val = 1) with h | h
    · exact ha ((ZMod.val_injective _ ) (by simpa using h))
    · exact h1 (ZMod.val_injective _ (h.trans (by decide +kernel)))
  have hi : a.val < 3328 := by
    have w := a.val_lt
    by_contra! h
    exact hm (ZMod.val_injective _ (by rw [ZMod.val_neg_one]; omega))
  have small := row_bound a.val lo hi
  change rowSum a.val 577 ≤ 93700 at small
  rw [prefix_sum] at small
  have half : ∑ x ∈ Finset.range 1665, entry a.val x ≤ 93700+1088 := by
    rw [show 1665=577+1088 by decide, Finset.sum_range_add]
    apply Nat.add_le_add small
    have ht (x : ℕ) (hx : x < 1088) : entry a.val (577+x) = 1 := by
      have d : magnitude (577+x) = 577+x := by unfold magnitude; omega
      have h : 108 ≤ ((magnitude (577+x))^2 + magnitude (a.val*(577+x)%3329)^2)/3072 := by
        rw [d,Nat.le_div_iff_mul_le (by decide)]
        nlinarith [Nat.zero_le (magnitude (a.val*(577+x)%3329)^2)]
      change bucket _ = 1
      unfold bucket
      rw [min_eq_right h]
      decide +kernel
    simp only [Finset.sum_congr rfl (fun x hx ↦ ht x (Finset.mem_range.mp hx))]
    simp
  have rest : ∑ x ∈ Finset.range 1664, entry a.val (1665+x) ≤
      ∑ x ∈ Finset.range 1665, entry a.val x := by
    let f (x : ℕ) := 1664-x
    have inj : Set.InjOn f (Finset.range 1664 : Finset ℕ) := by
      intro i hi j hj h
      have hi := Finset.mem_range.mp hi
      have hj := Finset.mem_range.mp hj
      dsimp [f] at h
      omega
    rw [Finset.sum_congr rfl (fun x hx ↦ entry_reflect a x (Finset.mem_range.mp hx))]
    change ∑ x ∈ Finset.range 1664, entry a.val (f x) ≤ _
    rw [← Finset.sum_image (f := entry a.val) inj]
    apply Finset.sum_le_sum_of_subset
    intro x hx
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (by dsimp [f]; omega)
  rw [← (ZMod.finEquiv 3329).toEquiv.sum_comp]
  change ∑ x : Fin 3329, entry a.val x.val ≤ _
  rw [Fin.sum_univ_eq_sum_range]
  change ∑ i ∈ Finset.range (1665+1664), entry a.val i ≤ _
  rw [Finset.sum_range_add]
  omega

#print axioms field_row_le

end SigabaNeo.Wall1.RawScalarWeights
