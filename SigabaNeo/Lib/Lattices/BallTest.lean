import SigabaNeo.Lib.Lattices.Homomorphic.BinaryDigits
import SigabaNeo.Lib.Lattices.Homomorphic.Norm

/-!
# Testing membership in a ball by binary digits

For `x ∈ ℤ_q` and a radius `r` with `2r < 2^B` and `2^{B+1} ≤ q`:
**`zabs_le_iff_val`**: `|x| ≤ r ⟺ val(x + r) < 2^B ∧ val(r − x) < 2^B`. On `ℤ_q[X]/(X^N + 1)` with
`q ≤ 2^K` and `R` the element with every coefficient `r`: **`cnorm_le_iff_digits`**:
`‖v‖ ≤ r ⟺` every binary digit `i ∈ [B, K)` of `v + R` and of `R − v` is `0`. A machine checks
the digits by summing them (`binaryDigit` has coefficients `0`/`1`).
-/

namespace SigabaNeo.Lattices

open Cslib

variable {q : ℕ} [NeZero q]

theorem val_intCast_of_nonneg {z : ℤ} (h0 : 0 ≤ z) (hq : z < q) : ((z : ZMod q)).val = z.toNat := by
  have : (z : ZMod q) = ((z.toNat : ℕ) : ZMod q) := by
    rw [← Int.toNat_of_nonneg h0]; simp
  rw [this, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

/-- **The ball by two values**: `|x| ≤ r ⟺ val(x + r) < 2^B ∧ val(r − x) < 2^B`. -/
theorem zabs_le_iff_val (B r : ℕ) (hr : 2 * r < 2 ^ B) (hq : 2 ^ (B + 1) ≤ q) (x : ZMod q) :
    zabs x ≤ r ↔ (x + r).val < 2 ^ B ∧ ((r : ZMod q) - x).val < 2 ^ B := by
  have hpow : (2 : ℕ) ^ (B + 1) = 2 * 2 ^ B := by rw [pow_succ]; ring
  constructor
  · intro h
    have hx : x = ((x.valMinAbs : ℤ) : ZMod q) := (ZMod.coe_valMinAbs x).symm
    have he : x.valMinAbs.natAbs ≤ r := h
    have h1 : (x + r : ZMod q) = ((x.valMinAbs + r : ℤ) : ZMod q) := by
      conv_lhs => rw [hx]
      push_cast; ring
    have h2 : ((r : ZMod q) - x) = ((r - x.valMinAbs : ℤ) : ZMod q) := by
      conv_lhs => rw [hx]
      push_cast; ring
    rw [h1, h2, val_intCast_of_nonneg (by omega) (by push_cast; omega),
      val_intCast_of_nonneg (by omega) (by push_cast; omega)]
    omega
  · rintro ⟨ha, hb⟩
    set a := (x + r : ZMod q).val
    set b := ((r : ZMod q) - x).val
    have hsum : ((x + r) + ((r : ZMod q) - x)) = ((2 * r : ℕ) : ZMod q) := by push_cast; ring
    have hab : a + b = 2 * r := by
      have h := congrArg ZMod.val hsum
      rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)] at h
      exact h
    have hx : x = (((a : ℤ) - r : ℤ) : ZMod q) := by
      have : (x + r : ZMod q) = ((a : ℕ) : ZMod q) := (ZMod.natCast_zmod_val _).symm
      push_cast
      rw [← this]; ring
    rw [hx]
    refine (zabs_intCast_le _).trans ?_
    omega

theorem val_lt_iff_testBit {K B n : ℕ} (hn : n < 2 ^ K) :
    n < 2 ^ B ↔ ∀ i, B ≤ i → i < K → n.testBit i = false := by
  constructor
  · intro h i hi _
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hi))
  · intro h
    have e : n = n % 2 ^ B := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_mod_two_pow]
      by_cases hi : i < B
      · simp [hi]
      · simp only [hi, decide_false, Bool.false_and]
        by_cases hk : i < K
        · exact h i (by omega) hk
        · exact Nat.testBit_lt_two_pow
            (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [e]; exact Nat.mod_lt _ (by positivity)

variable {N : ℕ}

/-- The element with every coefficient `r`. -/
def allC (N : ℕ) (r : ZMod q) : Negacyclic (ZMod q) N := Negacyclic.ofCoeffs fun _ => r

theorem binaryDigit_eq_zero_iff (hq : 2 ≤ q) (a : Negacyclic (ZMod q) N) (i : ℕ) :
    binaryDigit a i = 0 ↔ ∀ j, (a.coeffs j).val.testBit i = false := by
  have h10 : (1 : ZMod q) ≠ 0 := by
    intro h
    have := congrArg ZMod.val h
    rw [ZMod.val_one'' (by omega), ZMod.val_zero] at this
    exact absurd this (by norm_num)
  constructor
  · intro h j
    have := congrArg (fun x => Negacyclic.coeffs x j) h
    simp only [coeffs_binaryDigit, Negacyclic.coeffs_zero, Pi.zero_apply] at this
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    rw [if_pos hc] at this
    exact h10 this
  · intro h
    apply Negacyclic.coeffs_injective
    funext j
    simp [coeffs_binaryDigit, h j]

/-- **The ball by binary digits**: `‖v‖ ≤ r` iff the digits `i ∈ [B, K)` of `v + R` and `R − v`
vanish (`R = allC r`). -/
theorem cnorm_le_iff_digits {K : ℕ} (hqK : q ≤ 2 ^ K) (B r : ℕ) (hr : 2 * r < 2 ^ B)
    (hq : 2 ^ (B + 1) ≤ q) (v : Negacyclic (ZMod q) N) :
    cnorm v ≤ r ↔ ∀ i, B ≤ i → i < K → binaryDigit (v + allC N (r : ZMod q)) i = 0 ∧
      binaryDigit (allC N (r : ZMod q) - v) i = 0 := by
  have hq2 : 2 ≤ q := le_trans (by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (B + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)) hq
  have hlt : ∀ x : ZMod q, x.val < 2 ^ K := fun x => lt_of_lt_of_le (ZMod.val_lt x) hqK
  rw [cnorm_le_iff]
  simp only [binaryDigit_eq_zero_iff hq2, Negacyclic.coeffs_add, Negacyclic.coeffs_sub, Pi.add_apply,
    Pi.sub_apply, allC, Negacyclic.coeffs_ofCoeffs]
  constructor
  · intro h i hi hiK
    refine ⟨fun j => ?_, fun j => ?_⟩
    · exact ((val_lt_iff_testBit (hlt _)).mp ((zabs_le_iff_val B r hr hq _).mp (h j)).1) i hi hiK
    · exact ((val_lt_iff_testBit (hlt _)).mp ((zabs_le_iff_val B r hr hq _).mp (h j)).2) i hi hiK
  · intro h j
    rw [zabs_le_iff_val B r hr hq]
    exact ⟨(val_lt_iff_testBit (hlt _)).mpr fun i hi hiK => (h i hi hiK).1 j,
      (val_lt_iff_testBit (hlt _)).mpr fun i hi hiK => (h i hi hiK).2 j⟩

/-- **A sum of digits vanishes iff every digit does**, when there are fewer than `q` of them. -/
theorem sum_binaryDigit_eq_zero_iff {ι : Type*} (s : Finset ι) (a : ι → Negacyclic (ZMod q) N)
    (i : ι → ℕ) (hs : s.card < q) :
    ∑ t ∈ s, binaryDigit (a t) (i t) = 0 ↔ ∀ t ∈ s, binaryDigit (a t) (i t) = 0 := by
  constructor
  · intro h t ht
    apply Negacyclic.coeffs_injective
    funext j
    have hj := congrArg (fun x => Negacyclic.coeffs x j) h
    simp only [Negacyclic.coeffs_sum, Finset.sum_apply, coeffs_binaryDigit,
      Negacyclic.coeffs_zero, Pi.zero_apply] at hj
    -- the coefficient sum as a natural number
    have hn : (∑ t ∈ s, if ((a t).coeffs j).val.testBit (i t) then 1 else 0 : ℕ) = 0 := by
      have hc : ((∑ t ∈ s, if ((a t).coeffs j).val.testBit (i t) then 1 else 0 : ℕ) : ZMod q) = 0 := by
        rw [← hj]; push_cast; rfl
      rw [ZMod.natCast_eq_zero_iff] at hc
      have hle : (∑ t ∈ s, if ((a t).coeffs j).val.testBit (i t) then 1 else 0 : ℕ) ≤ s.card := by
        calc _ ≤ ∑ _t ∈ s, 1 := Finset.sum_le_sum fun t _ => by split_ifs <;> simp
          _ = s.card := by simp
      exact Nat.eq_zero_of_dvd_of_lt hc (by omega)
    have ht0 := (Finset.sum_eq_zero_iff.mp hn) t ht
    simp only [coeffs_binaryDigit, Negacyclic.coeffs_zero, Pi.zero_apply]
    by_cases hb : ((a t).coeffs j).val.testBit (i t) = true
    · rw [if_pos hb] at ht0; exact absurd ht0 one_ne_zero
    · rw [if_neg hb]
  · intro h
    exact Finset.sum_eq_zero h

end SigabaNeo.Lattices
