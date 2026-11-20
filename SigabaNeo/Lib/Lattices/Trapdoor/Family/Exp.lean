import SigabaNeo.Lib.Lattices.Trapdoor.Family.Pi

/-!
# Trapdoor sampler: bracketing `e^y` with natural numbers

For `y = yN / yD ≥ 0`, an exponent count `E ≥ y` and `N ≥ 1` terms, the Taylor sum
`s = Σ_{i<N} (y/E)^i / i!` is `sNum / sDen` with natural numerator and denominator (`s_eq`), and

  `s^E ≤ e^y ≤ (s + 2/N!)^E`  (`exp_ge_pow`, `exp_le_pow`).

A Bernoulli trial accepting `u < 2^T` when `u · a < 2^T · b` succeeds for exactly
`⌈2^T b / a⌉` values of `u` when `b ≤ a` (`card_accept`).
-/

namespace SigabaNeo.Lattices.Trapdoor.Family

open Real Finset

/-- The numerator of `Σ_{i<N} (yN/(E yD))^i / i!` over `(E yD)^{N−1} (N−1)!`. -/
def sNum (yN yD E N : ℕ) : ℕ :=
  ∑ i ∈ range N, yN ^ i * (E * yD) ^ (N - 1 - i) * ((N - 1).factorial / i.factorial)

def sDen (yD E N : ℕ) : ℕ := (E * yD) ^ (N - 1) * (N - 1).factorial

theorem sDen_pos {yD E N : ℕ} (hyD : 0 < yD) (hE : 0 < E) : 0 < sDen yD E N := by
  unfold sDen; positivity

theorem s_eq (yN yD E N : ℕ) (hyD : 0 < yD) (hE : 0 < E) :
    (sNum yN yD E N : ℝ) / sDen yD E N =
      ∑ i ∈ range N, ((yN : ℝ) / (E * yD)) ^ i / i.factorial := by
  have hD : (0 : ℝ) < sDen yD E N := by exact_mod_cast sDen_pos hyD hE
  rw [div_eq_iff hD.ne', Finset.sum_mul]
  unfold sNum sDen
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ N - 1 := by have := Finset.mem_range.mp hi; omega
  have hdvd : i.factorial ∣ (N - 1).factorial := Nat.factorial_dvd_factorial hi'
  rw [Nat.cast_div hdvd (by positivity)]
  have hEy : (0 : ℝ) < E * yD := by positivity
  have hpow : ((E : ℝ) * yD) ^ (N - 1) = ((E : ℝ) * yD) ^ (N - 1 - i) * ((E : ℝ) * yD) ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi']
  rw [hpow, div_pow]
  field_simp

theorem exp_ge_pow (yN yD E N : ℕ) (hyD : 0 < yD) (hE : 0 < E) :
    ((sNum yN yD E N : ℝ) / sDen yD E N) ^ E ≤ Real.exp ((yN : ℝ) / yD) := by
  rw [s_eq yN yD E N hyD hE]
  have h1 := Real.sum_le_exp_of_nonneg (x := (yN : ℝ) / (E * yD)) (by positivity) N
  have h0 : 0 ≤ ∑ i ∈ range N, ((yN : ℝ) / (E * yD)) ^ i / i.factorial :=
    Finset.sum_nonneg fun i _ => by positivity
  calc (∑ i ∈ range N, ((yN : ℝ) / (E * yD)) ^ i / i.factorial) ^ E
      ≤ Real.exp ((yN : ℝ) / (E * yD)) ^ E := pow_le_pow_left₀ h0 h1 E
    _ = Real.exp ((yN : ℝ) / yD) := by
        rw [← Real.exp_nat_mul]; congr 1; field_simp

theorem exp_le_pow (yN yD E N : ℕ) (hyD : 0 < yD) (hE : 0 < E) (hN : 0 < N)
    (hy : yN ≤ E * yD) :
    Real.exp ((yN : ℝ) / yD) ≤ ((sNum yN yD E N : ℝ) / sDen yD E N + 2 / N.factorial) ^ E := by
  rw [s_eq yN yD E N hyD hE]
  set x := (yN : ℝ) / (E * yD)
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    rw [div_le_one (by positivity)]; exact_mod_cast hy
  have hb := Real.exp_bound' hx0 hx1 hN
  have hr : x ^ N * (N + 1) / (N.factorial * N) ≤ 2 / N.factorial := by
    have hxN : x ^ N ≤ 1 := pow_le_one₀ hx0 hx1
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hf : (0 : ℝ) < N.factorial := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hxN (by positivity : (0 : ℝ) ≤ (N + 1) * N.factorial)]
  calc Real.exp ((yN : ℝ) / yD) = Real.exp x ^ E := by
        rw [← Real.exp_nat_mul]; congr 1; simp only [x]; field_simp
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le (hb.trans (by linarith)) E

theorem lt_ceil_iff (u a X : ℕ) (ha : 0 < a) : u < (X + a - 1) / a ↔ u * a < X := by
  rw [← Nat.add_one_le_iff, Nat.le_div_iff_mul_le ha, add_mul, one_mul]
  omega

/-- The accepted `u`: `u < 2^T` with `u · a < 2^T · b`. -/
theorem card_accept (T a b : ℕ) (ha : 0 < a) (hb : b ≤ a) :
    ((range (2 ^ T)).filter fun u => u * a < 2 ^ T * b).card = (2 ^ T * b + a - 1) / a := by
  have hX : 2 ^ T * b ≤ 2 ^ T * a := Nat.mul_le_mul_left _ hb
  have hc : (2 ^ T * b + a - 1) / a ≤ 2 ^ T := by
    rw [Nat.div_le_iff_le_mul_add_pred ha]
    rw [mul_comm a]; omega
  have hset : (range (2 ^ T)).filter (fun u => u * a < 2 ^ T * b) =
      range ((2 ^ T * b + a - 1) / a) := by
    ext u
    simp only [mem_filter, mem_range, lt_ceil_iff u a _ ha]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h
      refine ⟨?_, h⟩
      exact ((lt_ceil_iff u a _ ha).mpr h).trans_le hc
  rw [hset, card_range]

end SigabaNeo.Lattices.Trapdoor.Family
