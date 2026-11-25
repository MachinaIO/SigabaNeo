import Mathlib.Data.ZMod.ValMinAbs
import CslibFrontier.Foundations.Algebra.Negacyclic

/-!
# Threshold decoding of a bit

A bit `M` is encoded in `ℤ_q` as `M · ⌊q/2⌋` (`encodeBit`) and decoded by the centered
representative `c` of what is received: `true` iff `4|c| ≥ q` (`decodeZMod`). Decoding is exact
under any error `e` with `4|e| + 2 < q` (`decodeZMod_encodeBit_add`), `|e|` the centered
representative.

In `ℤ_q[X]/(X^N + 1)` (cslib-frontier's `Cslib.Negacyclic`) the bit is the constant polynomial
`M · ⌊q/2⌋` and decoding reads the constant coefficient (`decodeBit`, `decodeBit_encodeBit_add`),
whatever the other coefficients of the error.
-/

namespace SigabaNeo.Lattices

open Cslib

variable {q : ℕ}

/-- The encoding `M · ⌊q/2⌋` of a bit in `ℤ_q`. -/
def encodeBit (q : ℕ) (M : Bool) : ZMod q := if M then ((q / 2 : ℕ) : ZMod q) else 0

/-- Decoding in `ℤ_q`: `true` iff the centered representative `c` has `4|c| ≥ q`. -/
def decodeZMod (q : ℕ) (c : ZMod q) : Bool := decide ((q : ℤ) ≤ 4 * |c.valMinAbs|)

/-- **Exact decoding.** `M · ⌊q/2⌋ + e` decodes to `M` when `4|e| + 2 < q`. -/
theorem decodeZMod_encodeBit_add [NeZero q] (M : Bool) (e : ZMod q)
    (he : 4 * |e.valMinAbs| + 2 < q) : decodeZMod q (encodeBit q M + e) = M := by
  set v := e.valMinAbs with hv
  have hv1 := neg_abs_le v
  have hv2 := le_abs_self v
  cases M with
  | false =>
    simp only [encodeBit, Bool.false_eq_true, ite_false, zero_add, decodeZMod,
      decide_eq_false_iff_not, not_le]
    linarith
  | true =>
    simp only [encodeBit, ite_true, decodeZMod, decide_eq_true_eq]
    set h : ℤ := ((q / 2 : ℕ) : ℤ) with hh
    have hq1 : 2 * h ≤ q := by rw [hh]; exact_mod_cast Nat.mul_div_le q 2
    have hq2 : (q : ℤ) ≤ 2 * h + 1 := by rw [hh]; norm_cast; omega
    have hcast : ((q / 2 : ℕ) : ZMod q) + e = ((h + v : ℤ) : ZMod q) := by
      rw [Int.cast_add, hv, ZMod.coe_valMinAbs, hh, Int.cast_natCast]
    rw [hcast]
    by_cases hw : (h + v) * 2 ≤ q
    · have hmin : ((h + v : ℤ) : ZMod q).valMinAbs = h + v :=
        (ZMod.valMinAbs_spec _ _).2 ⟨rfl, by linarith, hw⟩
      rw [hmin, abs_of_nonneg (by linarith)]
      linarith
    · have hmin : ((h + v : ℤ) : ZMod q).valMinAbs = h + v - q := by
        refine (ZMod.valMinAbs_spec _ _).2 ⟨?_, ?_, ?_⟩
        · rw [Int.cast_sub, Int.cast_natCast, ZMod.natCast_self, sub_zero]
        · linarith
        · linarith
      rw [hmin, abs_of_nonpos (by linarith)]
      linarith

variable {N : ℕ}

/-- Decoding in `ℤ_q[X]/(X^N + 1)`: the constant coefficient. -/
def decodeBit (hN : 0 < N) (v : Negacyclic (ZMod q) N) : Bool :=
  decodeZMod q (v.coeffs ⟨0, hN⟩)

/-- **Exact decoding in the ring.** The constant polynomial `M · ⌊q/2⌋` plus an error `e` decodes
to `M` when the constant coefficient `e₀` of `e` has `4|e₀| + 2 < q`. -/
theorem decodeBit_encodeBit_add [NeZero q] (hN : 0 < N) (M : Bool) (e : Negacyclic (ZMod q) N)
    (he : 4 * |(e.coeffs ⟨0, hN⟩).valMinAbs| + 2 < q) :
    decodeBit hN (algebraMap (ZMod q) _ (encodeBit q M) + e) = M := by
  unfold decodeBit
  simp only [Negacyclic.coeffs_add, Pi.add_apply, Negacyclic.coeffs_algebraMap, ite_true]
  exact decodeZMod_encodeBit_add M _ he

end SigabaNeo.Lattices
