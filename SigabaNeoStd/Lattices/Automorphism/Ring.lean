import SigabaNeoStd.Lattices.Automorphism.Coeffs
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring

/-!
# `σ_k` is a ring endomorphism of `R[X]/(X^n + 1)`

Over a commutative ring `R`, on `Negacyclic R n`:

* `monoX n`, the monomial `X`; `mono n p` the signed unit vector of `X^p` (`monoX_pow`:
  `monoX n ^ p = mono n p`), with `coeffs_monoX_pow`: `X^p` is `±1` at position `p mod n`, with sign
  `(−1)^(p / n)`; `monoX_pow_n : X^n = −1`, `monoX_pow_two_n : X^{2n} = 1`;
  `mul_monoX`: multiplication by `X` is the negacyclic shift.
* `eq_sum_monoX`: `a = Σ_j a_j X^j`; `aut_eq_sum`: `σ_k(a) = Σ_j a_j X^{k j}`.
* `autLin n k`: `σ_k` is `R`-linear (every `k`); `aut_monoX_pow`: `σ_k(X^p) = X^{k p}` for odd `k`.
* `autHom n k hk : Negacyclic R n →+* Negacyclic R n` for odd `k` (any `n`, `n = 0` included).
* `aut_one`, `aut_aut` (`σ_k ∘ σ_{k'} = σ_{k k'}` for odd `k`), `aut_add_two_n` (period `2n` in
  `k`), `aut_monoX` (`σ_k(X) = X^k`).
-/

namespace SigabaNeo.Lattices

open Cslib Finset

variable {R : Type*} [CommRing R] {n : ℕ}

omit [CommRing R] in
theorem Negacyclic.eq_of_zero (a b : Negacyclic R 0) : a = b :=
  Negacyclic.ext (funext fun i => i.elim0)

/-- The coefficients of `X^p` in `R[X]/(X^n+1)`: `1` at `p mod 2n` if `< n`, `−1` at
`p mod 2n − n` otherwise. -/
def monoCoeffs (n p : ℕ) : Fin n → R := fun i =>
  (if p % (2 * n) = i then 1 else 0) - (if p % (2 * n) = i + n then 1 else 0)

/-- The signed monomial `X^p` (as a coefficient vector). -/
def mono (n p : ℕ) : Negacyclic R n := Negacyclic.ofCoeffs (monoCoeffs n p)

/-- The monomial `X`. -/
def monoX (n : ℕ) : Negacyclic R n := mono n 1

@[simp] theorem coeffs_mono (p : ℕ) : (mono n p : Negacyclic R n).coeffs = monoCoeffs n p := rfl

/-- Multiplication by `X` is the negacyclic shift. -/
theorem mul_monoX (hn : 0 < n) (a : Negacyclic R n) (i : Fin n) :
    (a * monoX n).coeffs i =
      if h : 0 < (i : ℕ) then a.coeffs ⟨i - 1, by omega⟩ else -a.coeffs ⟨n - 1, by omega⟩ := by
  rw [Negacyclic.coeffs_mul, negacyclicMul, Matrix.mulVec, dotProduct]
  have h1 : 1 % (2 * n) = 1 := Nat.mod_eq_of_lt (by omega)
  rcases Nat.lt_or_ge 1 n with h2 | h2
  · rw [Finset.sum_eq_single (⟨1, h2⟩ : Fin n)]
    · simp only [monoX, coeffs_mono, monoCoeffs, h1, rotMatrix, Matrix.of_apply]
      by_cases hi : 0 < (i : ℕ)
      · have hi' : (1 : ℕ) ≤ i := hi
        simp [hi, hi', hn.ne']
      · have hi' : ¬ (1 : ℕ) ≤ i := by omega
        have hi0 : (i : ℕ) = 0 := by omega
        simp only [hi, hi', dite_false]
        simp only [hi0, add_zero]
        simp only [left_eq_add, hn.ne', ite_false, ite_true, sub_zero, mul_one]
    · intro j _ hj
      have hj' : (j : ℕ) ≠ 1 := fun h => hj (Fin.ext h)
      simp only [monoX, coeffs_mono, monoCoeffs, h1]
      rw [if_neg (Ne.symm hj'), if_neg (by omega)]
      simp
    · simp
  · have hn1 : n = 1 := by omega
    subst hn1
    have hi : (i : ℕ) = 0 := by omega
    rw [Fin.sum_univ_one]
    simp only [monoX, coeffs_mono, monoCoeffs, rotMatrix, Matrix.of_apply]
    have : (0 : Fin 1) = i := Fin.ext (by simp)
    subst this
    simp

theorem mono_succ (hn : 0 < n) (p : ℕ) :
    (mono n p : Negacyclic R n) * monoX n = mono n (p + 1) := by
  ext i
  rw [mul_monoX hn]
  have hr := Nat.mod_lt p (show 0 < 2 * n by omega)
  have h1 : 1 % (2 * n) = 1 := Nat.mod_eq_of_lt (by omega)
  have hs : (p + 1) % (2 * n) =
      if 2 * n ≤ p % (2 * n) + 1 then p % (2 * n) + 1 - 2 * n else p % (2 * n) + 1 := by
    rw [Nat.add_mod_eq_ite, h1]
  have hi := i.isLt
  simp only [coeffs_mono, monoCoeffs, hs]
  generalize p % (2 * n) = r at hr ⊢
  split_ifs <;> first | (exfalso; omega) | ring1

theorem mono_zero : (mono n 0 : Negacyclic R n) = 1 := by
  ext i
  have hi := i.isLt
  simp only [coeffs_mono, monoCoeffs, Nat.zero_mod, Negacyclic.coeffs_one]
  have h1 : ¬ (0 = (i : ℕ) + n) := by omega
  simp only [h1, ite_false, sub_zero]
  by_cases h : (i : ℕ) = 0
  · simp [h]
  · simp [h, Ne.symm h]

theorem monoX_pow (p : ℕ) : (monoX n : Negacyclic R n) ^ p = mono n p := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Negacyclic.eq_of_zero _ _
  induction p with
  | zero => rw [pow_zero, mono_zero]
  | succ p ih => rw [pow_succ, ih, mono_succ hn]

/-- The coefficients of `X^p`: `(−1)^(p / n)` at position `p mod n`, `0` elsewhere. -/
theorem coeffs_monoX_pow (p : ℕ) (i : Fin n) :
    ((monoX n : Negacyclic R n) ^ p).coeffs i =
      if (i : ℕ) = p % n then (if p / n % 2 = 0 then 1 else -1) else 0 := by
  rw [monoX_pow, coeffs_mono, monoCoeffs, mul_comm 2 n, Nat.mod_mul]
  have hi := i.isLt
  have hr := Nat.mod_lt p (show 0 < n by omega)
  have h2 := Nat.mod_lt (p / n) (show 0 < 2 by omega)
  generalize p % n = r at hr ⊢
  generalize p / n % 2 = s at h2 ⊢
  rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl <;> split_ifs <;> first | (exfalso; omega) | ring1

/-- `X^j` for `j < n` is the unit vector at `j`. -/
theorem coeffs_monoX_pow_of_lt {j : ℕ} (hj : j < n) (i : Fin n) :
    ((monoX n : Negacyclic R n) ^ j).coeffs i = if (i : ℕ) = j then 1 else 0 := by
  rw [coeffs_monoX_pow, Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]
  simp

theorem monoX_pow_n : (monoX n : Negacyclic R n) ^ n = -1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Negacyclic.eq_of_zero _ _
  ext i
  rw [coeffs_monoX_pow, Nat.mod_self, Nat.div_self hn]
  simp only [Negacyclic.coeffs_neg, Pi.neg_apply, Negacyclic.coeffs_one]
  split_ifs <;> simp_all

theorem monoX_pow_two_n : (monoX n : Negacyclic R n) ^ (2 * n) = 1 := by
  rw [mul_comm, pow_mul, monoX_pow_n]; simp

/-- `X^p = (−1)^(p / n) X^(p mod n)`. -/
theorem monoX_pow_eq (p : ℕ) :
    (monoX n : Negacyclic R n) ^ p = ((-1 : R) ^ (p / n)) • monoX n ^ (p % n) := by
  conv_lhs => rw [← Nat.mod_add_div p n, pow_add, pow_mul, monoX_pow_n]
  rw [Algebra.smul_def, mul_comm]
  simp

/-- Every element is `Σ_j a_j X^j`. -/
theorem eq_sum_monoX (a : Negacyclic R n) :
    a = ∑ j : Fin n, a.coeffs j • (monoX n : Negacyclic R n) ^ (j : ℕ) := by
  ext i
  rw [Negacyclic.coeffs_sum, Finset.sum_apply, Finset.sum_eq_single i]
  · rw [Negacyclic.coeffs_smul, Pi.smul_apply, coeffs_monoX_pow_of_lt i.isLt]; simp
  · intro j _ hj
    rw [Negacyclic.coeffs_smul, Pi.smul_apply, coeffs_monoX_pow_of_lt j.isLt,
      if_neg (fun h => hj (Fin.ext h.symm))]
    simp
  · simp

/-- `σ_k(a) = Σ_j a_j X^{k j}`. -/
theorem aut_eq_sum (k : ℕ) (a : Negacyclic R n) :
    aut n k a = ∑ j : Fin n, a.coeffs j • (monoX n : Negacyclic R n) ^ (k * j) := by
  ext i
  simp only [aut, autCoeffs, Negacyclic.coeffs_ofCoeffs, Negacyclic.coeffs_sum, Finset.sum_apply,
    Negacyclic.coeffs_smul, Pi.smul_apply, monoX_pow, coeffs_mono, monoCoeffs, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- `σ_k` as an `R`-linear map (every `k`). -/
def autLin (n k : ℕ) : Negacyclic R n →ₗ[R] Negacyclic R n where
  toFun := aut n k
  map_add' a b := by
    simp only [aut_eq_sum, Negacyclic.coeffs_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r a := by
    simp only [aut_eq_sum, Negacyclic.coeffs_smul, Pi.smul_apply, smul_eq_mul, mul_smul,
      RingHom.id_apply, Finset.smul_sum]

@[simp] theorem autLin_apply (k : ℕ) (a : Negacyclic R n) : autLin n k a = aut n k a := rfl

theorem aut_add (k : ℕ) (a b : Negacyclic R n) : aut n k (a + b) = aut n k a + aut n k b :=
  (autLin n k).map_add a b

theorem aut_smul (k : ℕ) (r : R) (a : Negacyclic R n) : aut n k (r • a) = r • aut n k a :=
  (autLin n k).map_smul r a

theorem aut_neg (k : ℕ) (a : Negacyclic R n) : aut n k (-a) = -aut n k a :=
  (autLin n k).map_neg a

theorem aut_sum (k : ℕ) {ι : Type*} (s : Finset ι) (f : ι → Negacyclic R n) :
    aut n k (∑ i ∈ s, f i) = ∑ i ∈ s, aut n k (f i) :=
  map_sum (autLin n k) f s

/-- `σ_k(X^j) = X^{k j}` for `j < n` (every `k`). -/
theorem aut_monoX_pow_of_lt (k : ℕ) {j : ℕ} (hj : j < n) :
    aut n k ((monoX n : Negacyclic R n) ^ j) = monoX n ^ (k * j) := by
  rw [aut_eq_sum, Finset.sum_eq_single ⟨j, hj⟩]
  · rw [coeffs_monoX_pow_of_lt hj]; simp
  · intro i _ hi
    rw [coeffs_monoX_pow_of_lt hj, if_neg (fun h => hi (Fin.ext h)), zero_smul]
  · simp

/-- `σ_k(X^p) = X^{k p}` for odd `k`. -/
theorem aut_monoX_pow {k : ℕ} (hk : Odd k) (p : ℕ) :
    aut n k ((monoX n : Negacyclic R n) ^ p) = monoX n ^ (k * p) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Negacyclic.eq_of_zero _ _
  rw [monoX_pow_eq p, aut_smul, aut_monoX_pow_of_lt k (Nat.mod_lt p hn)]
  have h : k * p = k * (p % n) + n * (k * (p / n)) := by
    conv_lhs => rw [← Nat.mod_add_div p n]
    ring
  rw [h, pow_add, pow_mul (monoX n) n, monoX_pow_n, pow_mul (-1 : Negacyclic R n) k, hk.neg_one_pow,
    Algebra.smul_def, mul_comm]
  simp

/-- `σ_k(X) = X^k` for odd `k`. -/
theorem aut_monoX {k : ℕ} (hk : Odd k) :
    aut n k (monoX n : Negacyclic R n) = monoX n ^ k := by
  simpa using aut_monoX_pow (R := R) (n := n) hk 1

theorem aut_one_eq (k : ℕ) : aut n k (1 : Negacyclic R n) = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Negacyclic.eq_of_zero _ _
  have := aut_monoX_pow_of_lt (R := R) k hn
  simpa using this

theorem aut_mul {k : ℕ} (hk : Odd k) (a b : Negacyclic R n) :
    aut n k (a * b) = aut n k a * aut n k b := by
  conv_lhs => rw [eq_sum_monoX a, eq_sum_monoX b, Finset.sum_mul_sum, aut_sum]
  rw [aut_eq_sum, aut_eq_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [aut_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_smul_comm, aut_smul, ← pow_add, aut_monoX_pow hk, smul_mul_smul_comm, ← pow_add,
    mul_add]

/-- `σ_k` as a ring endomorphism, for odd `k`. -/
def autHom (n k : ℕ) (hk : Odd k) : Negacyclic R n →+* Negacyclic R n where
  toFun := aut n k
  map_one' := aut_one_eq k
  map_mul' := aut_mul hk
  map_zero' := (autLin n k).map_zero
  map_add' := aut_add k

@[simp] theorem autHom_apply (k : ℕ) (hk : Odd k) (a : Negacyclic R n) :
    autHom n k hk a = aut n k a := rfl

/-- `σ_1 = id`. -/
theorem aut_one (a : Negacyclic R n) : aut n 1 a = a := by
  rw [aut_eq_sum]; conv_rhs => rw [eq_sum_monoX a]
  simp

/-- `σ_k ∘ σ_{k'} = σ_{k k'}` for odd `k`. -/
theorem aut_aut {k : ℕ} (hk : Odd k) (k' : ℕ) (a : Negacyclic R n) :
    aut n k (aut n k' a) = aut n (k * k') a := by
  rw [aut_eq_sum k' a, aut_sum, aut_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [aut_smul, aut_monoX_pow hk, mul_assoc]

/-- `σ_k` depends on `k` modulo `2n`. -/
theorem aut_add_two_n (k : ℕ) (a : Negacyclic R n) : aut n (k + 2 * n) a = aut n k a := by
  have h : ∀ j : ℕ, (k + 2 * n) * j % (2 * n) = k * j % (2 * n) := fun j => by
    rw [add_mul, Nat.add_mul_mod_self_left]
  unfold aut autCoeffs
  simp only [h]

theorem aut_mod_two_n (k : ℕ) (a : Negacyclic R n) : aut n (k % (2 * n)) a = aut n k a := by
  conv_rhs => rw [← Nat.mod_add_div k (2 * n)]
  generalize k / (2 * n) = m
  induction m with
  | zero => simp
  | succ m ih => rw [mul_add, mul_one, ← add_assoc, aut_add_two_n, ih]

theorem autHom_comp {k k' : ℕ} (hk : Odd k) (hk' : Odd k') :
    (autHom (R := R) n k hk).comp (autHom n k' hk') = autHom n (k * k') (hk.mul hk') :=
  RingHom.ext fun a => aut_aut hk k' a

theorem autHom_one : autHom (R := R) n 1 odd_one = RingHom.id _ :=
  RingHom.ext aut_one

end SigabaNeo.Lattices
