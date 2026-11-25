import SigabaNeoStd.Lattices.Algo.MatWords

/-!
# Negacyclic multiplication by Horner's rule in `X⁻¹`

The product `a * b` in `R_q = ℤ_{2^K}[X]/(X^N + 1)` is computed from the coefficients of `b` in
increasing order, without reversing any word: with `ρ e = X⁻¹ e` (the coefficients shifted down by
one, the first one negated to the top, `rhoR`) and `bⱼ · a` the scalar multiple (`scR`),

  `e₀ = 0`, `e_{m+1} = ρ e_m + b_m · a`, and `a * b = -ρ e_N` (`neg_rhoR_eR`).

The proof is on coefficients: `e_m` has the closed form `coefOf_eR` (a sum over `j < m` of
`b_j` times a coefficient of `a`, negated past the top), compared with the schoolbook sum
`coeffs_mul_eq_sum`.
-/

namespace SigabaNeo.Lattices.Algo

open Cslib

variable {N K : ℕ}

theorem coefOf_add (x y : Rq N K) (i : ℕ) : coefOf (x + y) i = coefOf x i + coefOf y i := by
  unfold coefOf; split_ifs <;> simp

theorem coefOf_neg (x : Rq N K) (i : ℕ) : coefOf (-x) i = -coefOf x i := by
  unfold coefOf; split_ifs <;> simp

theorem coefOf_zero (i : ℕ) : coefOf (0 : Rq N K) i = 0 := by
  unfold coefOf; split_ifs <;> simp

theorem ext_coefOf {x y : Rq N K} (h : ∀ i < N, coefOf x i = coefOf y i) : x = y := by
  apply Negacyclic.coeffs_injective
  funext i
  have := h i.val i.isLt
  simpa [coefOf, i.isLt] using this

/-- `X⁻¹ e`: the coefficients shifted down, the first one negated to the top. -/
def rhoR (e : Rq N K) : Rq N K :=
  Negacyclic.ofCoeffs fun i => if i.val + 1 < N then coefOf e (i.val + 1) else -coefOf e 0

/-- The scalar multiple `r · a`, coefficient by coefficient. -/
def scR (r : ZMod (2 ^ K)) (a : Rq N K) : Rq N K := Negacyclic.ofCoeffs fun i => a.coeffs i * r

theorem coefOf_rhoR (e : Rq N K) {i : ℕ} (hi : i < N) :
    coefOf (rhoR e) i = if i + 1 < N then coefOf e (i + 1) else -coefOf e 0 := by
  simp [coefOf, rhoR, hi]

theorem coefOf_scR (r : ZMod (2 ^ K)) (a : Rq N K) {i : ℕ} (hi : i < N) :
    coefOf (scR r a) i = coefOf a i * r := by
  simp [coefOf, scR, hi]

/-- The accumulator of Horner's rule in `X⁻¹`. -/
def eR (a b : Rq N K) : ℕ → Rq N K
  | 0 => 0
  | m + 1 => rhoR (eR a b m) + scR (coefOf b m) a

/-- The coefficient `t` of `a`, negated once past the top. -/
def sig (a : Rq N K) (t : ℕ) : ZMod (2 ^ K) := if t < N then coefOf a t else -coefOf a (t - N)

theorem coefOf_eR (a b : Rq N K) :
    ∀ m, m ≤ N → ∀ i < N,
      coefOf (eR a b m) i = ∑ j ∈ Finset.range m, coefOf b j * sig a (i + m - (j + 1))
  | 0, _, i, _ => by simp [eR, coefOf_zero]
  | m + 1, hm, i, hi => by
    rw [eR, coefOf_add, coefOf_rhoR _ hi, coefOf_scR _ _ hi, Finset.sum_range_succ]
    have hsi : sig a (i + (m + 1) - (m + 1)) = coefOf a i := by simp [sig, hi]
    rw [hsi, mul_comm (coefOf b m)]
    congr 1
    split_ifs with h
    · rw [coefOf_eR a b m (by omega) (i + 1) h]
      refine Finset.sum_congr rfl fun j hj => ?_
      congr 2; omega
    · rw [coefOf_eR a b m (by omega) 0 (by omega), ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj := Finset.mem_range.mp hj
      have hiN : i = N - 1 := by omega
      simp only [sig, zero_add, ← mul_neg]
      congr 1
      split_ifs <;> first | omega | (congr 2; omega)

/-- **Horner's rule in `X⁻¹`** computes the product. -/
theorem neg_rhoR_eR (a b : Rq N K) : -rhoR (eR a b N) = a * b := by
  apply ext_coefOf
  intro i hi
  have hab : coefOf (a * b) i = (a * b).coeffs ⟨i, hi⟩ := by simp [coefOf, hi]
  rw [coefOf_neg, coefOf_rhoR _ hi, hab, coeffs_mul_eq_sum a b i hi]
  split_ifs with h
  · rw [coefOf_eR a b N le_rfl (i + 1) h, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj := Finset.mem_range.mp hj
    simp only [negaTerm, sig]
    rw [show i + 1 + N - (j + 1) = N + i - j by omega]
    split_ifs <;> first | omega | (rw [show N + i - j - N = i - j by omega]; ring) | ring
  · rw [coefOf_eR a b N le_rfl 0 (by omega), neg_neg]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj := Finset.mem_range.mp hj
    simp only [negaTerm, sig, zero_add]
    split_ifs <;> first | omega | (rw [show i - j = N - (j + 1) by omega]; ring)

end SigabaNeo.Lattices.Algo
