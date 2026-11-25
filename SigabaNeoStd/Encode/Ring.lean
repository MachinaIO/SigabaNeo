import SigabaNeoStd.Encode.Enum
import CslibFrontier.Foundations.Algebra.Negacyclic
import Mathlib.Data.ZMod.Basic

/-!
# Fixed-length encodings of residues and ring elements

* `FixedEnc.comap`: an encoding through an injective map.
* `zmodEnc K`: a residue modulo `2^K` as its `K` bits, least significant first.
* `ringEnc N K`: an element of `ℤ_{2^K}[X]/(X^N + 1)` as its `N` coefficients, in order.
-/

namespace SigabaNeo.Encode

open Cslib

/-- An encoding through an injective map. -/
def FixedEnc.comap {α β : Type} {n : ℕ} (e : FixedEnc β n) (f : α → β) (hf : Function.Injective f) :
    FixedEnc α n where
  enc a := e.enc (f a)
  inj a b h := hf (e.inj h)
  length a := e.length (f a)

/-- **Residues modulo `2^K`**: the `K` bits of the representative, least significant first. -/
def zmodEnc (K : ℕ) : FixedEnc (ZMod (2 ^ K)) K where
  enc x := (List.finRange K).map fun (i : Fin K) => x.val.testBit i.val
  inj x y h := by
    have hb : ∀ i < K, x.val.testBit i = y.val.testBit i := fun i hi =>
      List.map_inj_left.mp h (⟨i, hi⟩ : Fin K) (List.mem_finRange _)
    have hx : x.val < 2 ^ K := ZMod.val_lt x
    have hy : y.val < 2 ^ K := ZMod.val_lt y
    apply ZMod.val_injective
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < K
    · exact hb i hi
    · have hK : K ≤ i := Nat.le_of_not_lt hi
      rw [Nat.testBit_lt_two_pow (hx.trans_le (Nat.pow_le_pow_right (by norm_num) hK)),
        Nat.testBit_lt_two_pow (hy.trans_le (Nat.pow_le_pow_right (by norm_num) hK))]
  length x := by simp

/-- **Ring elements**: their coefficients in order. -/
def ringEnc (N K : ℕ) : FixedEnc (Negacyclic (ZMod (2 ^ K)) N) (N * K) := by
  have e := (FixedEnc.fun (α := Fin N) (zmodEnc K)).comap Negacyclic.coeffs
    Negacyclic.coeffsEquiv.injective
  simpa [Enum.list] using e

end SigabaNeo.Encode
