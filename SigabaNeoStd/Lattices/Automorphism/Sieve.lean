import SigabaNeoStd.Lattices.Automorphism.Interface
import SigabaNeoStd.Lattices.Automorphism.Ring

/-!
# The coefficient sieve (Lemma 7 of ePrint 2026/2539)

For `W = 2^b` dividing `n`, the indices `hIdx n W j = 1 + j · 2n/W` (`j < W`) are odd, and summing
`σ_k` over them keeps exactly the monomials whose exponent is divisible by `W`, multiplied by `W`.

* `sum_pow_two_pow_mul`: in any commutative ring, if `z^(2^b) = −1` then
  `Σ_{j < 2^(b+1)} z^(p j) = 2^(b+1)` if `2^(b+1) ∣ p`, `0` otherwise.
* `sum_pow_hIdx_mul`: in any commutative ring, for `x^n = −1`,
  `Σ_{j<W} x^(hIdx n W j · p) = W · x^p` if `W ∣ p`, `0` otherwise.
* `odd_hIdx`, `sieve_aut` (**Lemma 7** on monomials of `Negacyclic R n`), and `sum_aut_hIdx`
  (Lemma 7 for every element: `Σ_j σ_{hIdx j}(a) = W · Σ_{W ∣ i} a_i X^i`).
-/

namespace SigabaNeo.Lattices

open Cslib Finset

section Generic

variable {S : Type*} [CommRing S]

theorem sum_range_two_pow_succ (f : ℕ → S) (b : ℕ) :
    ∑ j ∈ range (2 ^ (b + 1)), f j = ∑ j ∈ range (2 ^ b), (f j + f (2 ^ b + j)) := by
  rw [pow_succ, mul_two, Finset.sum_range_add, Finset.sum_add_distrib]

/-- Sums of powers of a root `z` with `z^(2^b) = −1`. -/
theorem sum_pow_two_pow_mul (b : ℕ) :
    ∀ (z : S) (p : ℕ), z ^ (2 ^ b) = -1 →
      ∑ j ∈ range (2 ^ (b + 1)), z ^ (p * j) =
        if 2 ^ (b + 1) ∣ p then ((2 ^ (b + 1) : ℕ) : S) else 0 := by
  induction b with
  | zero =>
    intro z p hz
    rw [pow_zero, pow_one] at hz
    subst hz
    simp only [zero_add, pow_one, Finset.sum_range_succ, Finset.sum_range_zero, mul_zero,
      pow_zero, mul_one, zero_add]
    rcases Nat.even_or_odd p with hp | hp
    · rw [hp.neg_one_pow, if_pos (even_iff_two_dvd.mp hp)]; norm_num
    · rw [hp.neg_one_pow, if_neg (Nat.not_even_iff_odd.mpr hp ∘ even_iff_two_dvd.mpr)]; ring
  | succ b ih =>
    intro z p hz
    have hsplit : ∑ j ∈ range (2 ^ (b + 1 + 1)), z ^ (p * j) =
        (1 + z ^ (p * 2 ^ (b + 1))) * ∑ j ∈ range (2 ^ (b + 1)), z ^ (p * j) := by
      rw [sum_range_two_pow_succ, add_mul, one_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← pow_add, mul_add]
    rw [hsplit]
    rcases Nat.even_or_odd p with ⟨p', rfl⟩ | hp
    · -- `p = 2 p'`: reduce to `z^2`
      have hf : z ^ ((p' + p') * 2 ^ (b + 1)) = 1 := by
        rw [show (p' + p') * 2 ^ (b + 1) = 2 ^ (b + 1) * (2 * p') by ring, pow_mul, hz, pow_mul]
        norm_num
      rw [hf]
      have hz2 : (z ^ 2) ^ (2 ^ b) = -1 := by rw [← pow_mul, ← pow_succ']; exact hz
      have hsum : ∑ j ∈ range (2 ^ (b + 1)), z ^ ((p' + p') * j) =
          ∑ j ∈ range (2 ^ (b + 1)), (z ^ 2) ^ (p' * j) :=
        Finset.sum_congr rfl fun j _ => by rw [← pow_mul]; ring_nf
      rw [hsum, ih (z ^ 2) p' hz2]
      have hdvd : 2 ^ (b + 1 + 1) ∣ p' + p' ↔ 2 ^ (b + 1) ∣ p' := by
        rw [← two_mul, pow_succ, mul_comm _ 2]
        exact Nat.mul_dvd_mul_iff_left (by norm_num)
      by_cases h : 2 ^ (b + 1) ∣ p'
      · rw [if_pos h, if_pos (hdvd.mpr h)]; push_cast; ring
      · rw [if_neg h, if_neg (fun h' => h (hdvd.mp h'))]; ring
    · have hodd : z ^ (p * 2 ^ (b + 1)) = -1 := by rw [mul_comm, pow_mul, hz, hp.neg_one_pow]
      have hnd : ¬ 2 ^ (b + 1 + 1) ∣ p := fun h =>
        (Nat.not_even_iff_odd.mpr hp) (even_iff_two_dvd.mpr ((Dvd.intro_left _ rfl).trans h))
      rw [hodd, if_neg hnd]; ring

/-- `2n/W = 2 (n/W)` is even, so `hIdx n W j = 1 + j · 2n/W` is odd. -/
theorem odd_hIdx {n W : ℕ} (hW : W ∣ n) (j : ℕ) : Odd (hIdx n W j) := by
  obtain ⟨t, rfl⟩ := hW
  rcases Nat.eq_zero_or_pos W with rfl | hW0
  · simp [hIdx]
  have : 2 * (W * t) / W = 2 * t := by
    rw [mul_left_comm, Nat.mul_div_cancel_left _ hW0]
  exact ⟨j * t, by rw [hIdx, this]; ring⟩

/-- **The sieve in any commutative ring** with `x^n = −1`, for `W = 2^b ∣ n`. -/
theorem sum_pow_hIdx_mul {n b : ℕ} (x : S) (hx : x ^ n = -1) (hW : 2 ^ b ∣ n) (p : ℕ) :
    ∑ j ∈ range (2 ^ b), x ^ (hIdx n (2 ^ b) j * p) =
      if 2 ^ b ∣ p then ((2 ^ b : ℕ) : S) * x ^ p else 0 := by
  rcases b with _ | b
  · simp [hIdx]
  obtain ⟨t, rfl⟩ := hW
  have hm : 2 * (2 ^ (b + 1) * t) / 2 ^ (b + 1) = 2 * t := by
    rw [mul_left_comm, Nat.mul_div_cancel_left _ (by positivity)]
  have hz : (x ^ (2 * t)) ^ (2 ^ b) = -1 := by
    rw [← pow_mul, ← hx]; congr 1; ring
  have hs : ∀ j, x ^ (hIdx (2 ^ (b + 1) * t) (2 ^ (b + 1)) j * p) =
      x ^ p * (x ^ (2 * t)) ^ (p * j) := fun j => by
    rw [hIdx, hm, ← pow_mul, ← pow_add]; congr 1; ring
  simp only [hs]
  rw [← Finset.mul_sum, sum_pow_two_pow_mul b _ p hz]
  split_ifs <;> ring

end Generic

variable {R : Type*} [CommRing R] {n b : ℕ}

/-- **Lemma 7** (on monomials): `Σ_{j<W} σ_{1 + j·2n/W}(X^p) = W X^p` if `W ∣ p`, `0` otherwise,
for `W = 2^b ∣ n`. -/
theorem sieve_aut (hW : 2 ^ b ∣ n) (p : ℕ) :
    ∑ j ∈ range (2 ^ b), aut n (hIdx n (2 ^ b) j) ((monoX n : Negacyclic R n) ^ p) =
      if 2 ^ b ∣ p then ((2 ^ b : ℕ) : Negacyclic R n) * monoX n ^ p else 0 := by
  rw [← sum_pow_hIdx_mul (monoX n) monoX_pow_n hW p]
  exact Finset.sum_congr rfl fun j _ => aut_monoX_pow (odd_hIdx hW j) p

/-- **Lemma 7**: `Σ_{j<W} σ_{1 + j·2n/W}(a) = W · Σ_{W ∣ i} a_i X^i`, for `W = 2^b ∣ n`. -/
theorem sum_aut_hIdx (hW : 2 ^ b ∣ n) (a : Negacyclic R n) :
    ∑ j ∈ range (2 ^ b), aut n (hIdx n (2 ^ b) j) a =
      ((2 ^ b : ℕ) : Negacyclic R n) *
        ∑ i : Fin n, if 2 ^ b ∣ (i : ℕ) then a.coeffs i • (monoX n) ^ (i : ℕ) else 0 := by
  conv_lhs => rw [eq_sum_monoX a]
  simp only [aut_sum, aut_smul]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.smul_sum, sieve_aut hW]
  split_ifs <;> simp

end SigabaNeo.Lattices
