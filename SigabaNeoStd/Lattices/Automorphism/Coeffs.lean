import CslibFrontier.Foundations.Algebra.Negacyclic
import Mathlib.Algebra.BigOperators.Fin

/-!
# The automorphism `σ_k` of `R[X]/(X^n + 1)` on coefficients

`autCoeffs n k a`: the coefficients of `σ_k(Σ_j a_j X^j) = Σ_j a_j X^{k j}`, reducing `X^{k j}` with
`X^n = −1`: the coefficient `a_j` lands at position `k j mod 2n` if that is `< n`, and with a minus
sign at position `k j mod 2n − n` otherwise. `aut n k` is the map on `Negacyclic R n`.

This is the definition shared by the circular Ring-LWE assumption
(`SigabaNeo.Lattices.CircularRingLWE`) and the ring automorphism of
`SigabaNeoStd.Lattices.Automorphism` (which proves that `aut n k` is a ring automorphism for odd
`k` and instantiates `ExpRing`).
-/

namespace SigabaNeo.Lattices

open Cslib

variable {R : Type*} [Ring R]

/-- The coefficients of `σ_k(a)`: `a_j` goes to `k j mod 2n` (minus sign when that is `≥ n`). -/
def autCoeffs (n k : ℕ) (a : Fin n → R) : Fin n → R := fun i =>
  ∑ j : Fin n, ((if (k * j) % (2 * n) = i then a j else 0) -
    (if (k * j) % (2 * n) = i + n then a j else 0))

/-- `σ_k` on `Negacyclic R n`. -/
def aut (n k : ℕ) (a : Negacyclic R n) : Negacyclic R n :=
  Negacyclic.ofCoeffs (autCoeffs n k a.coeffs)

end SigabaNeo.Lattices
