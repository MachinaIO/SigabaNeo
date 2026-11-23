import SigabaNeo.Lib.Lattices.Automorphism.Sieve
import Mathlib.Data.ZMod.Units

/-!
# `R[X]/(X^n + 1)` as an `ExpRing`

* `autσ n k`: `σ_k` for every `k` (`autHom` for odd `k`, the identity for even `k`, so that the
  family is `2n`-periodic in `k`).
* `expRingOf n b w …`: `Negacyclic R n` is an `ExpRing` with `X = monoX n`, `W = 2^b` (`2^b ∣ n`,
  `2^b < n`) and `W⁻¹ = w` for any `w` with `2^b w = 1` in `R`.
* `expRing q n b hq …`: over `ZMod q` for odd `q`, with `W⁻¹` the inverse of the unit `2^b`.
* `expRingMersenne K n b …`: over `ZMod (2^K − 1)` with the explicit `W⁻¹ = 2^(K−b)` (`b ≤ K`).
-/

namespace SigabaNeo.Lattices

open Cslib

variable {R : Type*} [CommRing R]

/-- `σ_k` for every `k`: the ring endomorphism `aut n k` for odd `k`, the identity otherwise. -/
noncomputable def autσ (n k : ℕ) : Negacyclic R n →+* Negacyclic R n :=
  if hk : Odd k then autHom n k hk else RingHom.id _

theorem autσ_of_odd {n k : ℕ} (hk : Odd k) (a : Negacyclic R n) : autσ n k a = aut n k a := by
  simp [autσ, hk]

theorem autσ_period (n k : ℕ) : (autσ (R := R) n (k + 2 * n)) = autσ n k := by
  have hiff : Odd (k + 2 * n) ↔ Odd k := by
    rw [Nat.odd_add]; simp
  by_cases hk : Odd k
  · ext a : 1
    rw [autσ_of_odd hk, autσ_of_odd (hiff.mpr hk), aut_add_two_n]
  · simp [autσ, hk, mt hiff.mp hk]

/-- `Negacyclic R n` with `X`, `W = 2^b` and a given inverse `w` of `2^b`. -/
noncomputable def expRingOf (n b : ℕ) (w : R) (hw : (2 : R) ^ b * w = 1) (hn : 0 < n)
    (hW : 2 ^ b ∣ n) (hlt : 2 ^ b < n) : ExpRing (Negacyclic R n) where
  n := n
  W := 2 ^ b
  X := monoX n
  σ := autσ n
  Winv := algebraMap R _ w
  n_pos := hn
  W_pos := by positivity
  W_dvd := hW
  W_lt := hlt
  W_mul_Winv := by
    rw [← map_natCast (algebraMap R (Negacyclic R n)), ← map_mul, Nat.cast_pow, Nat.cast_ofNat,
      hw, map_one]
  X_pow_n := monoX_pow_n
  σ_X k hk := by rw [autσ_of_odd hk, aut_monoX hk]
  σ_one := RingHom.ext fun a => by rw [autσ_of_odd odd_one, aut_one, RingHom.id_apply]
  σ_comp k k' hk hk' := RingHom.ext fun a => by
    rw [RingHom.comp_apply, autσ_of_odd hk, autσ_of_odd hk', autσ_of_odd (hk.mul hk'), aut_aut hk]
  σ_period k := autσ_period n k
  sieve p := by
    rw [← sieve_aut hW p]
    exact Finset.sum_congr rfl fun j _ => autσ_of_odd (odd_hIdx hW j) _

@[simp] theorem expRingOf_n (n b : ℕ) (w : R) (hw) (hn) (hW) (hlt) :
    (expRingOf n b w hw hn hW hlt).n = n := rfl
@[simp] theorem expRingOf_W (n b : ℕ) (w : R) (hw) (hn) (hW) (hlt) :
    (expRingOf n b w hw hn hW hlt).W = 2 ^ b := rfl
@[simp] theorem expRingOf_X (n b : ℕ) (w : R) (hw) (hn) (hW) (hlt) :
    (expRingOf n b w hw hn hW hlt).X = monoX n := rfl
@[simp] theorem expRingOf_σ (n b : ℕ) (w : R) (hw) (hn) (hW) (hlt) :
    (expRingOf n b w hw hn hW hlt).σ = autσ n := rfl
@[simp] theorem expRingOf_Winv (n b : ℕ) (w : R) (hw) (hn) (hW) (hlt) :
    (expRingOf n b w hw hn hW hlt).Winv = algebraMap R _ w := rfl

/-- `2^b` is a unit of `ZMod q` for odd `q`. -/
def twoPowUnit (q b : ℕ) (hq : Odd q) : (ZMod q)ˣ :=
  ZMod.unitOfCoprime (2 ^ b) (Nat.Coprime.pow_left b (Nat.coprime_two_left.mpr hq))

theorem two_pow_mul_twoPowUnit_inv (q b : ℕ) (hq : Odd q) :
    (2 : ZMod q) ^ b * ((twoPowUnit q b hq)⁻¹ : (ZMod q)ˣ) = 1 := by
  have h : ((twoPowUnit q b hq : (ZMod q)ˣ) : ZMod q) = 2 ^ b := by
    simp [twoPowUnit, ZMod.coe_unitOfCoprime]
  rw [← h, Units.mul_inv]

/-- **The instance over `ℤ_q[X]/(X^n + 1)`**, `q` odd, `W = 2^b ∣ n`, `W < n`. -/
noncomputable def expRing (q n b : ℕ) (hq : Odd q) (hn : 0 < n) (hW : 2 ^ b ∣ n)
    (hlt : 2 ^ b < n) : ExpRing (Negacyclic (ZMod q) n) :=
  expRingOf n b (((twoPowUnit q b hq)⁻¹ : (ZMod q)ˣ) : ZMod q) (two_pow_mul_twoPowUnit_inv q b hq)
    hn hW hlt

/-- In `ZMod (2^K − 1)`, `2^K = 1`. -/
theorem two_pow_eq_one_mersenne (K : ℕ) : (2 : ZMod (2 ^ K - 1)) ^ K = 1 := by
  have h : (2 : ZMod (2 ^ K - 1)) ^ K = ((2 ^ K - 1 + 1 : ℕ) : ZMod (2 ^ K - 1)) := by
    rw [Nat.sub_add_cancel Nat.one_le_two_pow]; push_cast; rfl
  rw [h, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]

theorem two_pow_mul_two_pow_sub_mersenne {K b : ℕ} (hb : b ≤ K) :
    (2 : ZMod (2 ^ K - 1)) ^ b * 2 ^ (K - b) = 1 := by
  rw [← pow_add, Nat.add_sub_cancel' hb, two_pow_eq_one_mersenne]

/-- **The instance over `ℤ_q[X]/(X^n + 1)` for `q = 2^K − 1`**, with `W⁻¹ = 2^(K−b)`. -/
noncomputable def expRingMersenne (K n b : ℕ) (hb : b ≤ K) (hn : 0 < n) (hW : 2 ^ b ∣ n)
    (hlt : 2 ^ b < n) : ExpRing (Negacyclic (ZMod (2 ^ K - 1)) n) :=
  expRingOf n b ((2 : ZMod (2 ^ K - 1)) ^ (K - b)) (two_pow_mul_two_pow_sub_mersenne hb) hn hW hlt

end SigabaNeo.Lattices
