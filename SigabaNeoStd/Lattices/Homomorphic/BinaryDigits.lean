import SigabaNeoStd.Lattices.Gadget
import SigabaNeoStd.Lattices.Homomorphic.Eval
import CslibFrontier.Foundations.Algebra.Negacyclic

/-!
# Binary gadget digits of `ℤ_q[X]/(X^N + 1)`

The gadget digits of cslib-frontier's negacyclic ring `Cslib.Negacyclic (ZMod q) N` (the ring of
`ModuleLWE` and `RingLWE`): `gᵢ = 2^i`, and `dᵢ(a)` is the element whose coefficients are the
`i`-th binary digits of those of `a`, so it has `0/1` coefficients (`coeffs_binaryDigit`) and
`∑ᵢ 2^i dᵢ(a) = a` when `q ≤ 2^k` (`binaryDigits`). On each coefficient this is the decomposition
`gadgetInv` of `SigabaNeoStd.Lattices.Gadget` (`sum_testBit_pow`).

`coeffBits` decomposes a matrix over `ℤ_q[X]/(X^N + 1)` into the bits of the coefficients of its
entries: the bit `(a, c, i, j)` is the `i`-th binary digit of the `j`-th coefficient of the entry
`(a, c)`, with the matrix `2^i X^j` at `(a, c)` (`MatrixBits`).
-/

namespace SigabaNeo.Lattices

open Cslib

variable {N q : ℕ}

/-- The element whose coefficients are the `i`-th binary digits of those of `a`. -/
def binaryDigit (a : Negacyclic (ZMod q) N) (i : ℕ) : Negacyclic (ZMod q) N :=
  Negacyclic.ofCoeffs fun j => if (a.coeffs j).val.testBit i then 1 else 0

theorem coeffs_binaryDigit (a : Negacyclic (ZMod q) N) (i : ℕ) (j : Fin N) :
    (binaryDigit a i).coeffs j = if (a.coeffs j).val.testBit i then 1 else 0 := rfl

/-- The binary gadget digits of `ℤ_q[X]/(X^N + 1)`, for `q ≤ 2^k`. -/
def binaryDigits (N q k : ℕ) [NeZero q] (hk : q ≤ 2 ^ k) :
    GadgetDigits (Negacyclic (ZMod q) N) k where
  g i := algebraMap (ZMod q) _ (2 ^ (i : ℕ))
  d a i := binaryDigit a i
  recompose a := by
    ext j
    simp only [← Algebra.smul_def, Negacyclic.coeffs_sum, Negacyclic.coeffs_smul,
      Finset.sum_apply, Pi.smul_apply, coeffs_binaryDigit, smul_eq_mul]
    have h := congrArg (fun m : ℕ => (m : ZMod q)) (sum_testBit_pow (a.coeffs j).val k)
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_zero] at h
    rw [Nat.mod_eq_of_lt ((ZMod.val_lt _).trans_le hk), ZMod.natCast_zmod_val] at h
    conv_rhs => rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp

/-- The monomial `2^i X^j`. -/
def monomial (N q : ℕ) (i : ℕ) (j : Fin N) : Negacyclic (ZMod q) N :=
  Negacyclic.ofCoeffs (Pi.single j (2 ^ i))

/-- The bits of the coefficients of the entries of a matrix over `ℤ_q[X]/(X^N + 1)`, for
`q ≤ 2^k`. -/
def coeffBits (N q k : ℕ) [NeZero q] (hk : q ≤ 2 ^ k) (r W : Type) [Fintype r] [Fintype W]
    [DecidableEq r] [DecidableEq W] : MatrixBits (Negacyclic (ZMod q) N) r W where
  Index := r × W × Fin k × Fin N
  bits Y b :=
    algebraMap (ZMod q) _ (if ((Y b.1 b.2.1).coeffs b.2.2.2).val.testBit b.2.2.1 then 1 else 0)
  V b := Matrix.of fun a c => if a = b.1 ∧ c = b.2.1 then monomial N q b.2.2.1 b.2.2.2 else 0
  recompose Y := by
    ext a c j
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
      Fintype.sum_prod_type, mul_ite, mul_zero]
    rw [Fintype.sum_eq_single a (fun x hx => by simp [Ne.symm hx]),
      Fintype.sum_eq_single c (fun x hx => by simp [Ne.symm hx])]
    simp only [true_and, ite_true, ← Algebra.smul_def, Negacyclic.coeffs_sum, Finset.sum_apply,
      Negacyclic.coeffs_smul, Pi.smul_apply, monomial, smul_eq_mul, Pi.single_apply, mul_ite,
      mul_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have h := congrArg (fun m : ℕ => (m : ZMod q)) (sum_testBit_pow ((Y a c).coeffs j).val k)
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_zero] at h
    rw [Nat.mod_eq_of_lt ((ZMod.val_lt _).trans_le hk), ZMod.natCast_zmod_val] at h
    conv_rhs => rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp

end SigabaNeo.Lattices
