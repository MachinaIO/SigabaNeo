import SigabaNeo.Lib.Lattices.Automorphism.Interface
import SigabaNeo.Lib.Lattices.Automorphism.Coeffs
import SigabaNeo.Lib.Lattices.Homomorphic.NoiseBound

/-!
# `σ_k` permutes coefficients up to sign

For `k` coprime to `n` (for instance `k` odd and `n` a power of two, `coprime_pow_two`, or `k` an
index `1 + j · 2n/W` of the sieve with `W = 2^b ∣ n`, `coprime_hIdx`), the coefficient `a_j` of `a`
lands at position `autPos n k j = k j mod n` of `σ_k(a)`, with the sign `autSign n k j =
(−1)^(⌊k j / n⌋)` (`autCoeffs_autPos`), and `j ↦ k j mod n` is a permutation of `Fin n`
(`autPerm`). Main results:

* `autCoeffs_signedPerm`: `autCoeffs n k` is a signed permutation of the coefficients.
* `sum_comp_autCoeffs`, `sup_comp_autCoeffs`: every even coefficientwise sum / supremum is
  invariant.
* Over `ℤ_q` with the centered absolute value `zabs`: `cnorm_aut` (the `ℓ_∞` norm `cnorm` of
  `SigabaNeo.Lattices.Homomorphic.Norm` is invariant), `sum_zabs_aut` (the `ℓ₁` norm is invariant),
  and `rnorm_map_aut` (the row norm `rnorm` of the noise analysis is invariant under `σ_k` applied
  entrywise).
-/

namespace SigabaNeo.Lattices

open Cslib Finset

section Perm

variable {n k : ℕ}

/-- The position `k j mod n` of the coefficient `a_j` in `σ_k(a)`. -/
def autPos (n k : ℕ) (j : Fin n) : Fin n := ⟨(k * j) % n, Nat.mod_lt _ (by have := j.isLt; omega)⟩

/-- The sign `(−1)^(⌊k j / n⌋)` of the coefficient `a_j` in `σ_k(a)`. -/
def autSign {R : Type*} [Ring R] (n k j : ℕ) : R := if k * j / n % 2 = 0 then 1 else -1

theorem autSign_eq {R : Type*} [Ring R] (n k j : ℕ) :
    (autSign n k j : R) = 1 ∨ (autSign n k j : R) = -1 := by
  unfold autSign; split_ifs <;> simp

theorem autPos_injective (hk : k.Coprime n) : Function.Injective (autPos n k) := by
  intro j j' h
  have h' : k * (j : ℕ) ≡ k * j' [MOD n] := congrArg Fin.val h
  have := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hk) h'
  exact Fin.ext (by simpa [Nat.ModEq, Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt j'.isLt] using this)

/-- `j ↦ k j mod n` as a permutation of `Fin n`, for `k` coprime to `n`. -/
noncomputable def autPerm (hk : k.Coprime n) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (autPos_injective hk))

@[simp] theorem autPerm_apply (hk : k.Coprime n) (j : Fin n) : autPerm hk j = autPos n k j := rfl

variable {R : Type*} [Ring R]

/-- The coefficient `a_j` lands at `k j mod n` with sign `(−1)^(⌊k j / n⌋)`. -/
theorem autCoeffs_autPos (hk : k.Coprime n) (a : Fin n → R) (j : Fin n) :
    autCoeffs n k a (autPos n k j) = autSign n k j * a j := by
  have hn : 0 < n := by have := j.isLt; omega
  have hmod : ∀ x : ℕ, x % (2 * n) = x % n + n * (x / n % 2) := fun x => by
    rw [mul_comm 2 n, Nat.mod_mul]
  unfold autCoeffs
  rw [Finset.sum_eq_single j]
  · simp only [autPos, autSign, hmod]
    have := Nat.mod_lt (k * j / n) (show 0 < 2 by omega)
    rcases (by omega : k * j / n % 2 = 0 ∨ k * j / n % 2 = 1) with h | h <;> simp [h, hn.ne']
  · intro j' _ hj'
    have hne : (k * j' : ℕ) % n ≠ (k * j) % n := fun h =>
      hj' (autPos_injective hk (Fin.ext (by simpa [autPos] using h)))
    have h2 := Nat.mod_lt (k * j' / n) (show 0 < 2 by omega)
    have hlt := Nat.mod_lt (k * j' : ℕ) hn
    have hlt' := Nat.mod_lt (k * j : ℕ) hn
    have hc1 : ¬ (k * (j' : ℕ) % (2 * n) = (k * j) % n) := by
      rw [hmod]
      rcases (by omega : k * j' / n % 2 = 0 ∨ k * j' / n % 2 = 1) with h | h <;> rw [h] <;> omega
    have hc2 : ¬ (k * (j' : ℕ) % (2 * n) = (k * j) % n + n) := by
      rw [hmod]
      rcases (by omega : k * j' / n % 2 = 0 ∨ k * j' / n % 2 = 1) with h | h <;> rw [h] <;> omega
    simp only [autPos]
    simp only [hc1, hc2, ite_false, sub_zero]
  · simp

/-- **`σ_k` is a signed permutation of the coefficients** (`k` coprime to `n`). -/
theorem autCoeffs_signedPerm (hk : k.Coprime n) :
    ∃ π : Equiv.Perm (Fin n), ∃ ε : Fin n → R, (∀ j, ε j = 1 ∨ ε j = -1) ∧
      ∀ (a : Fin n → R) (j : Fin n), autCoeffs n k a (π j) = ε j * a j :=
  ⟨autPerm hk, fun j => autSign n k j, fun j => autSign_eq n k j,
    fun a j => autCoeffs_autPos hk a j⟩

theorem comp_autCoeffs_autPos {M : Type*} (f : R → M) (hf : ∀ x, f (-x) = f x) (hk : k.Coprime n)
    (a : Fin n → R) (j : Fin n) : f (autCoeffs n k a (autPos n k j)) = f (a j) := by
  rw [autCoeffs_autPos hk]
  rcases autSign_eq (R := R) n k j with h | h <;> rw [h] <;> simp [hf]

/-- Every even coefficientwise sum (e.g. an `ℓ₁` norm) is invariant under `σ_k`. -/
theorem sum_comp_autCoeffs {M : Type*} [AddCommMonoid M] (f : R → M) (hf : ∀ x, f (-x) = f x)
    (hk : k.Coprime n) (a : Fin n → R) :
    ∑ i, f (autCoeffs n k a i) = ∑ j, f (a j) := by
  rw [← Equiv.sum_comp (autPerm hk)]
  exact Finset.sum_congr rfl fun j _ => comp_autCoeffs_autPos f hf hk a j

/-- Every even coefficientwise supremum (e.g. an `ℓ_∞` norm) is invariant under `σ_k`. -/
theorem sup_comp_autCoeffs {M : Type*} [SemilatticeSup M] [OrderBot M] (f : R → M)
    (hf : ∀ x, f (-x) = f x) (hk : k.Coprime n) (a : Fin n → R) :
    Finset.univ.sup (fun i => f (autCoeffs n k a i)) = Finset.univ.sup (fun j => f (a j)) := by
  apply le_antisymm
  · refine Finset.sup_le fun i _ => ?_
    obtain ⟨j, rfl⟩ := (autPerm hk).surjective i
    rw [autPerm_apply, comp_autCoeffs_autPos f hf hk]
    exact Finset.le_sup (f := fun j => f (a j)) (Finset.mem_univ j)
  · refine Finset.sup_le fun j _ => ?_
    rw [← comp_autCoeffs_autPos f hf hk a j]
    exact Finset.le_sup (f := fun i => f (autCoeffs n k a i)) (Finset.mem_univ _)

end Perm

section Coprime

/-- An odd `k` is coprime to every power of two. -/
theorem coprime_pow_two {k : ℕ} (hk : Odd k) (e : ℕ) : k.Coprime (2 ^ e) :=
  Nat.Coprime.pow_right e (Nat.coprime_two_right.mpr hk)

/-- `1 + j · 2n/W` is coprime to `n` when `W = 2^b` divides `n`. -/
theorem coprime_hIdx {n b : ℕ} (hW : 2 ^ b ∣ n) (j : ℕ) : (hIdx n (2 ^ b) j).Coprime n := by
  obtain ⟨m, rfl⟩ := hW
  have hm : 2 * (2 ^ b * m) / 2 ^ b = 2 * m := by
    rw [mul_left_comm, Nat.mul_div_cancel_left _ (by positivity)]
  unfold hIdx
  rw [hm]
  refine Nat.Coprime.mul_right (coprime_pow_two ?_ b) ?_
  · exact ⟨j * m, by ring⟩
  · rw [show j * (2 * m) = (2 * j) * m by ring, Nat.coprime_add_mul_right_left]
    exact Nat.coprime_one_left m

end Coprime

section Norm

variable {q n k : ℕ}

/-- **`σ_k` preserves the `ℓ_∞` norm** of `ℤ_q[X]/(X^n + 1)` (`k` coprime to `n`). -/
theorem cnorm_aut (hk : k.Coprime n) (a : Negacyclic (ZMod q) n) : cnorm (aut n k a) = cnorm a :=
  sup_comp_autCoeffs zabs zabs_neg hk a.coeffs

/-- **`σ_k` preserves the `ℓ₁` norm** of `ℤ_q[X]/(X^n + 1)` (`k` coprime to `n`). -/
theorem sum_zabs_aut (hk : k.Coprime n) (a : Negacyclic (ZMod q) n) :
    ∑ i, zabs ((aut n k a).coeffs i) = ∑ i, zabs (a.coeffs i) :=
  sum_comp_autCoeffs zabs zabs_neg hk a.coeffs

/-- `σ_k` applied entrywise preserves the row norm `rnorm` (`k` coprime to `n`). -/
theorem rnorm_map_aut {W : Type*} [Fintype W] (hk : k.Coprime n)
    (e : Matrix (Fin 1) W (Negacyclic (ZMod q) n)) : rnorm (e.map (aut n k)) = rnorm e := by
  simp only [rnorm, Matrix.map_apply, cnorm_aut hk]

end Norm

end SigabaNeo.Lattices
