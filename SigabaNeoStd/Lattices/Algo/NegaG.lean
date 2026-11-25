import SigabaNeoStd.Lattices.Algo.RingWords
import SigabaNeoStd.Lattices.Automorphism.Coeffs

/-!
# Negacyclic arithmetic over any commutative ring, on coefficients

The identities behind the ring programs, for `Negacyclic R N` with any commutative ring `R` (the
programs of `SigabaNeoStd.Lattices.ProgAlgo.Mersenne` use `R = ZMod (2^K − 1)`):

* `coefG a i`: the coefficient `i` of `a`, `0` past the last one; `coeffs_mul_eq_sumG`: the
  schoolbook sum of a product.
* `rhoG e = X⁻¹ e` (the coefficients shifted down by one, the first one negated to the top);
  `rhoG_eq_mul`: `rhoG e = xInvG * e` with `xInvG = −X^{N−1}`; `xInvG_pow_two_mul`: `X^{−2N} = 1`.
* **Horner's rule in `X⁻¹`**: `eG a b`, `e₀ = 0`, `e_{m+1} = X⁻¹ e_m + b_m · a`, and
  `-rhoG (eG a b N) = a * b` (`neg_rhoG_eG`).
* `extG e t`: the coefficient of `X^t` of `e` read `2N`-periodically (`X^N = −1`), so that
  `extG (rhoG^[j] e) t = extG e (t + j)` (`extG_rhoG_iter`).
* **The automorphism by rotations**: `eA a k`, `e₀ = 0`, `e_{j+1} = X^{−k} (e_j + a_j)`; then
  `rhoG^[k N] (eA a k N) = aut N k a` (`rhoG_iter_eA`), for every `k` (`aut` from
  `SigabaNeoStd.Lattices.Automorphism.Coeffs`).
-/

namespace SigabaNeo.Lattices.Algo

open Cslib

namespace NegaG

variable {R : Type} [CommRing R] {N : ℕ}

theorem mIfT {α : Sort*} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a :=
  ite_eq_left_of_eq_true _ _ (eq_true h)

theorem mIfF {α : Sort*} {c : Prop} [Decidable c] (h : ¬c) (a b : α) : (if c then a else b) = b :=
  ite_eq_right_of_eq_false _ _ (eq_false h)

/-! ### Coefficients -/

/-- The coefficient `i` of a ring element, and `0` past the last one. -/
def coefG (a : Negacyclic R N) (i : ℕ) : R := if h : i < N then a.coeffs ⟨i, h⟩ else 0

theorem coefG_add (x y : Negacyclic R N) (i : ℕ) : coefG (x + y) i = coefG x i + coefG y i := by
  unfold coefG; split_ifs <;> simp

theorem coefG_neg (x : Negacyclic R N) (i : ℕ) : coefG (-x) i = -coefG x i := by
  unfold coefG; split_ifs <;> simp

theorem coefG_sub (x y : Negacyclic R N) (i : ℕ) : coefG (x - y) i = coefG x i - coefG y i := by
  unfold coefG; split_ifs <;> simp

theorem coefG_zero (i : ℕ) : coefG (0 : Negacyclic R N) i = 0 := by
  unfold coefG; split_ifs <;> simp

theorem coefG_ofCoeffs (f : Fin N → R) {i : ℕ} (hi : i < N) :
    coefG (Negacyclic.ofCoeffs f) i = f ⟨i, hi⟩ := by
  simp [coefG, hi]

theorem coefG_of_lt (a : Negacyclic R N) {i : ℕ} (hi : i < N) : coefG a i = a.coeffs ⟨i, hi⟩ := by
  simp [coefG, hi]

theorem coefG_val (a : Negacyclic R N) (i : Fin N) : coefG a i.val = a.coeffs i := by
  simp [coefG, i.isLt]

theorem ext_coefG {x y : Negacyclic R N} (h : ∀ i < N, coefG x i = coefG y i) : x = y := by
  apply Negacyclic.coeffs_injective
  funext i
  rw [← coefG_val, ← coefG_val, h i.val i.isLt]

/-- The coefficients of a product, as the schoolbook sum. -/
theorem coeffs_mul_eq_sumG (a b : Negacyclic R N) (i : ℕ) (hi : i < N) :
    (a * b).coeffs ⟨i, hi⟩ = ∑ j ∈ Finset.range N, negaTerm N (coefG a) (coefG b) i j := by
  rw [Negacyclic.coeffs_mul, negacyclicMul, Matrix.mulVec, dotProduct,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [rotMatrix, Matrix.of_apply, negaTerm, coefG]
  have hj := j.isLt
  split_ifs with h1 h2 h3 <;> first | omega | simp_all

/-! ### Multiplication by `X⁻¹` -/

/-- `X⁻¹ e`: the coefficients shifted down, the first one negated to the top. -/
def rhoG (e : Negacyclic R N) : Negacyclic R N :=
  Negacyclic.ofCoeffs fun i => if i.val + 1 < N then coefG e (i.val + 1) else -coefG e 0

theorem coefG_rhoG (e : Negacyclic R N) {i : ℕ} (hi : i < N) :
    coefG (rhoG e) i = if i + 1 < N then coefG e (i + 1) else -coefG e 0 := by
  simp [coefG, rhoG, hi]

/-- `X⁻¹ = −X^{N−1}`. -/
def xInvG (R : Type) [CommRing R] (N : ℕ) : Negacyclic R N :=
  Negacyclic.ofCoeffs fun i => if i.val + 1 = N then -1 else 0

/-- **`rhoG` is the multiplication by `X⁻¹`.** -/
theorem rhoG_eq_mul (e : Negacyclic R N) : rhoG e = xInvG R N * e := by
  apply ext_coefG
  intro i hi
  have hab : coefG (xInvG R N * e) i = (xInvG R N * e).coeffs ⟨i, hi⟩ := by simp [coefG, hi]
  rw [coefG_rhoG e hi, hab, coeffs_mul_eq_sumG _ _ i hi]
  have hx : ∀ t, coefG (xInvG R N) t = if t + 1 = N then -1 else 0 := by
    intro t
    unfold coefG xInvG
    split_ifs <;> first | omega | simp_all
  split_ifs with h
  · rw [Finset.sum_eq_single (i + 1)]
    · simp only [negaTerm, hx]
      rw [mIfF (by omega), mIfT (by omega)]; ring
    · intro j hjr hj
      have := Finset.mem_range.mp hjr
      simp only [negaTerm, hx]
      split_ifs <;> first | omega | simp
    · intro hj; exact absurd (Finset.mem_range.mpr h) hj
  · rw [Finset.sum_eq_single 0]
    · simp only [negaTerm, hx]
      rw [mIfT (by omega), mIfT (by omega)]; ring
    · intro j hjr hj
      have := Finset.mem_range.mp hjr
      simp only [negaTerm, hx]
      split_ifs <;> first | omega | simp
    · intro hj; exact absurd (Finset.mem_range.mpr (by omega)) hj

/-! ### Horner's rule in `X⁻¹` -/

/-- The scalar multiple `r · a`, coefficient by coefficient. -/
def scG (r : R) (a : Negacyclic R N) : Negacyclic R N := Negacyclic.ofCoeffs fun i => a.coeffs i * r

theorem coefG_scG (r : R) (a : Negacyclic R N) (i : ℕ) : coefG (scG r a) i = coefG a i * r := by
  unfold coefG scG; split_ifs <;> simp

/-- The accumulator of Horner's rule in `X⁻¹`. -/
def eG (a b : Negacyclic R N) : ℕ → Negacyclic R N
  | 0 => 0
  | m + 1 => rhoG (eG a b m) + scG (coefG b m) a

/-- The coefficient `t` of `a`, negated once past the top. -/
def sigG (a : Negacyclic R N) (t : ℕ) : R := if t < N then coefG a t else -coefG a (t - N)

theorem coefG_eG (a b : Negacyclic R N) :
    ∀ m, m ≤ N → ∀ i < N,
      coefG (eG a b m) i = ∑ j ∈ Finset.range m, coefG b j * sigG a (i + m - (j + 1))
  | 0, _, i, _ => by simp [eG, coefG_zero]
  | m + 1, hm, i, hi => by
    rw [eG, coefG_add, coefG_rhoG _ hi, coefG_scG, Finset.sum_range_succ]
    have hsi : sigG a (i + (m + 1) - (m + 1)) = coefG a i := by simp [sigG, hi]
    rw [hsi, mul_comm (coefG b m)]
    congr 1
    split_ifs with h
    · rw [coefG_eG a b m (by omega) (i + 1) h]
      refine Finset.sum_congr rfl fun j hj => ?_
      congr 2; omega
    · rw [coefG_eG a b m (by omega) 0 (by omega), ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj := Finset.mem_range.mp hj
      simp only [sigG, zero_add, ← mul_neg]
      congr 1
      split_ifs <;> first | omega | (congr 2; omega)

/-- **Horner's rule in `X⁻¹`** computes the product. -/
theorem neg_rhoG_eG (a b : Negacyclic R N) : -rhoG (eG a b N) = a * b := by
  apply ext_coefG
  intro i hi
  have hab : coefG (a * b) i = (a * b).coeffs ⟨i, hi⟩ := by simp [coefG, hi]
  rw [coefG_neg, coefG_rhoG _ hi, hab, coeffs_mul_eq_sumG a b i hi]
  split_ifs with h
  · rw [coefG_eG a b N le_rfl (i + 1) h, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj := Finset.mem_range.mp hj
    simp only [negaTerm, sigG]
    rw [show i + 1 + N - (j + 1) = N + i - j by omega]
    split_ifs <;> first | omega | (rw [show N + i - j - N = i - j by omega]; ring) | ring
  · rw [coefG_eG a b N le_rfl 0 (by omega), neg_neg]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj := Finset.mem_range.mp hj
    simp only [negaTerm, sigG, zero_add]
    split_ifs <;> first | omega | (rw [show i - j = N - (j + 1) by omega]; ring)

/-! ### Periodic coefficients -/

/-- The coefficient of `X^t` in `e`, with `X^N = −1`: period `2N`. -/
def extG (e : Negacyclic R N) (t : ℕ) : R :=
  if t % (2 * N) < N then coefG e (t % (2 * N)) else -coefG e (t % (2 * N) - N)

theorem extG_add (x y : Negacyclic R N) (t : ℕ) : extG (x + y) t = extG x t + extG y t := by
  unfold extG; split_ifs <;> simp [coefG_add]; ring

theorem extG_of_lt (e : Negacyclic R N) {i : ℕ} (hi : i < N) : extG e i = coefG e i := by
  have : i % (2 * N) = i := Nat.mod_eq_of_lt (by omega)
  simp [extG, this, hi]

theorem succ_mod_two_mul {N : ℕ} (hN : 0 < N) (t : ℕ) :
    (t + 1) % (2 * N) = if t % (2 * N) + 1 < 2 * N then t % (2 * N) + 1 else 0 := by
  rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < 2 * N by omega)]
  have := Nat.mod_lt t (show 0 < 2 * N by omega)
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [show t % (2 * N) + 1 = 2 * N by omega, Nat.mod_self]

/-- **`X⁻¹` shifts the periodic coefficients.** -/
theorem extG_rhoG (hN : 0 < N) (e : Negacyclic R N) (t : ℕ) :
    extG (rhoG e) t = extG e (t + 1) := by
  have hu := Nat.mod_lt t (show 0 < 2 * N by omega)
  have hs := succ_mod_two_mul hN t
  unfold extG
  rw [hs]
  generalize t % (2 * N) = u at hu ⊢
  by_cases h2 : u + 1 < 2 * N
  · rw [mIfT h2]
    by_cases h1 : u < N
    · rw [mIfT h1, coefG_rhoG e h1]
      by_cases h3 : u + 1 < N
      · rw [mIfT h3, mIfT h3]
      · rw [mIfF h3, mIfF h3,
          show u + 1 - N = 0 by omega]
    · rw [mIfF h1,
        mIfF (show ¬ (u + 1 < N) by omega),
        coefG_rhoG e (by omega), mIfT (show u - N + 1 < N by omega),
        show u - N + 1 = u + 1 - N by omega]
  · rw [mIfF h2, mIfF (show ¬ u < N by omega),
      mIfT hN, coefG_rhoG e (by omega),
      mIfF (show ¬ (u - N + 1 < N) by omega), neg_neg]

theorem extG_rhoG_iter (hN : 0 < N) (e : Negacyclic R N) :
    ∀ (j t : ℕ), extG (rhoG^[j] e) t = extG e (t + j)
  | 0, t => rfl
  | j + 1, t => by
    rw [Function.iterate_succ_apply', extG_rhoG hN, extG_rhoG_iter hN e j,
      show t + 1 + j = t + (j + 1) by omega]

theorem coefG_rhoG_iter (hN : 0 < N) (e : Negacyclic R N) (j : ℕ) {i : ℕ} (hi : i < N) :
    coefG (rhoG^[j] e) i = extG e (i + j) := by
  rw [← extG_of_lt _ hi, extG_rhoG_iter hN]

theorem extG_add_two_mul (e : Negacyclic R N) (t : ℕ) : extG e (t + 2 * N) = extG e t := by
  simp [extG, Nat.add_mod_right]

/-- **`X^{−2N} = 1`.** -/
theorem rhoG_iter_two_mul (hN : 0 < N) (e : Negacyclic R N) : rhoG^[2 * N] e = e := by
  apply ext_coefG
  intro i hi
  rw [coefG_rhoG_iter hN e _ hi, extG_add_two_mul, extG_of_lt _ hi]

theorem rhoG_iter_eq_mul (e : Negacyclic R N) : ∀ j, rhoG^[j] e = xInvG R N ^ j * e
  | 0 => by simp
  | j + 1 => by
    rw [Function.iterate_succ_apply', rhoG_iter_eq_mul e j, rhoG_eq_mul, pow_succ', mul_assoc]

theorem xInvG_pow_two_mul (hN : 0 < N) : xInvG R N ^ (2 * N) = 1 := by
  have := rhoG_iter_two_mul hN (1 : Negacyclic R N)
  rwa [rhoG_iter_eq_mul, mul_one] at this

/-! ### The automorphism by rotations -/

/-- The constant `r` (coefficient `0`). -/
def single0 (r : R) : Negacyclic R N := Negacyclic.ofCoeffs fun i => if i.val = 0 then r else 0

/-- `extG` of the constant `1`: `1` at the multiples of `2N`, `−1` at the odd multiples of `N`. -/
def dG (N : ℕ) (u : ℕ) : R :=
  if u % (2 * N) = 0 then 1 else if u % (2 * N) = N then -1 else 0

theorem extG_single0 (hN : 0 < N) (r : R) (t : ℕ) :
    extG (single0 (N := N) r) t = r * dG N t := by
  have hu := Nat.mod_lt t (show 0 < 2 * N by omega)
  unfold extG dG single0 coefG
  generalize t % (2 * N) = u at hu ⊢
  have h3 : u - N = 0 ↔ u ≤ N := by omega
  by_cases h1 : u < N
  · have h2 : u ≠ N := by omega
    by_cases h0 : u = 0 <;> simp_all
  · have h0 : u ≠ 0 := by omega
    have h2 : u - N < N := by omega
    by_cases h4 : u = N
    · simp_all
    · have h5 : ¬ u ≤ N := by omega
      simp_all

/-- The accumulator of `σ_k` by rotations: `e_{j+1} = X^{−k} (e_j + a_j)`. -/
def eA (a : Negacyclic R N) (k : ℕ) : ℕ → Negacyclic R N
  | 0 => 0
  | j + 1 => rhoG^[k] (eA a k j + single0 (coefG a j))

theorem extG_zero (t : ℕ) : extG (0 : Negacyclic R N) t = 0 := by
  simp [extG, coefG_zero]

theorem extG_eA (hN : 0 < N) (a : Negacyclic R N) (k : ℕ) :
    ∀ (j t : ℕ), extG (eA a k j) t =
      ∑ j' ∈ Finset.range j, coefG a j' * dG N (t + k * (j - j'))
  | 0, t => by simp [eA, extG_zero]
  | j + 1, t => by
    rw [eA, extG_rhoG_iter hN, extG_add, extG_eA hN a k j, extG_single0 hN,
      Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl fun j' hj' => ?_
      have hj' := Finset.mem_range.mp hj'
      congr 2
      rw [show j + 1 - j' = (j - j') + 1 by omega, Nat.mul_succ]; ring
    · simp

/-- The sign pattern of `σ_k`: `dG N (i + 2kN − kj)` is `1` if `kj ≡ i`, `−1` if `kj ≡ i + N`
modulo `2N`. -/
theorem dG_aut (hN : 0 < N) {i j : ℕ} (hi : i < N) (hj : j < N) (k : ℕ) :
    dG (R := R) N (i + k * N + k * (N - j)) =
      (if (k * j) % (2 * N) = i then 1 else 0) - (if (k * j) % (2 * N) = i + N then 1 else 0) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hi' : i % (2 * N) = i := Nat.mod_eq_of_lt (by omega)
    simp only [zero_mul, add_zero, Nat.zero_mod, dG, hi']
    by_cases h0 : i = 0
    · subst h0; simp [show (0 = N) = False by simp; omega]
    · rw [mIfF h0, mIfF (by omega),
        mIfF (by omega), mIfF (by omega)]
      simp
  set q := k * j / (2 * N)
  set v := k * j % (2 * N)
  have hv : v < 2 * N := Nat.mod_lt _ (by omega)
  have hkj : 2 * N * q + v = k * j := Nat.div_add_mod _ _
  have hq : q < k := by
    apply Nat.div_lt_of_lt_mul
    have : k * j < k * N := Nat.mul_lt_mul_of_pos_left hj hk
    nlinarith
  have heq : i + k * N + k * (N - j) = (i + 2 * N - v) + 2 * N * (k - q - 1) := by
    have h1 : k * (N - j) = k * N - k * j := Nat.mul_sub k N j
    have h2 : k * j ≤ k * N := Nat.mul_le_mul_left k hj.le
    have h3 : 2 * N * (k - q - 1) = 2 * N * k - 2 * N * q - 2 * N := by
      rw [Nat.mul_sub, Nat.mul_sub, Nat.mul_one]
    have h4 : 2 * N * q + 2 * N ≤ 2 * N * k := by
      have := Nat.mul_le_mul_left (2 * N) (show q + 1 ≤ k by omega); nlinarith
    have h5 : 2 * N * k = 2 * (k * N) := by ring
    omega
  have hmod : (i + k * N + k * (N - j)) % (2 * N) = (i + 2 * N - v) % (2 * N) := by
    rw [heq, Nat.add_mul_mod_self_left]
  unfold dG
  rw [hmod]
  by_cases h1 : v = i
  · rw [mIfT (show (i + 2 * N - v) % (2 * N) = 0 by
      rw [show i + 2 * N - v = 2 * N by omega, Nat.mod_self]), mIfT h1, mIfF (by omega)]
    simp
  · by_cases h2 : v = i + N
    · rw [show i + 2 * N - v = N by omega, Nat.mod_eq_of_lt (by omega), mIfF (by omega),
        mIfT rfl, mIfF h1, mIfT h2]
      simp
    · rw [mIfF h1, mIfF h2]
      have hne0 : (i + 2 * N - v) % (2 * N) ≠ 0 := by
        intro h0
        rcases lt_or_ge (i + 2 * N - v) (2 * N) with h | h
        · rw [Nat.mod_eq_of_lt h] at h0; omega
        · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)] at h0; omega
      have hneN : (i + 2 * N - v) % (2 * N) ≠ N := by
        intro h0
        rcases lt_or_ge (i + 2 * N - v) (2 * N) with h | h
        · rw [Nat.mod_eq_of_lt h] at h0; omega
        · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)] at h0; omega
      rw [mIfF hne0, mIfF hneN]; simp

/-- **`σ_k` by rotations**: after the `N` rounds, `X^{−kN}` turns the accumulator into `σ_k(a)`. -/
theorem rhoG_iter_eA (hN : 0 < N) (a : Negacyclic R N) (k : ℕ) :
    rhoG^[k * N] (eA a k N) = SigabaNeo.Lattices.aut N k a := by
  apply ext_coefG
  intro i hi
  rw [coefG_rhoG_iter hN _ _ hi, extG_eA hN, SigabaNeo.Lattices.aut, coefG_ofCoeffs _ hi,
    SigabaNeo.Lattices.autCoeffs, ← Fin.sum_univ_eq_sum_range (fun j' => coefG a j' * _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dG_aut hN hi j.isLt, coefG_val]
  simp only [mul_sub, mul_ite, mul_one, mul_zero]
