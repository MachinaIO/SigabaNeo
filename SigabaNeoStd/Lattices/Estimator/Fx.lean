import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Choose.Basic

/-!
# Fixed-point arithmetic for the attack models

A number `x` is the integer `⌊x · 2^P⌋`; every division rounds down. `python/lwemodel/fx.py`
computes the same integers. Costs are `log₂` values, `none` meaning infinite (`Cost`).
-/

namespace SigabaNeo.Lattices.Estimator

/-- A fixed-point number. -/
abbrev Fx := ℤ

namespace Fx

def P : ℕ := 48
def ONE : ℤ := 2 ^ P
/-- Working precision of `log2Nat`. -/
def K : ℕ := 2 * P

def LN2 : ℤ := 195103586505167
def LOG2E : ℤ := 406082553034799
def PI : ℤ := 884279719003555
def E : ℤ := 765128314358509
def SQRT2PI : ℤ := 705553135224032

def ofInt (k : ℤ) : Fx := k * ONE
def ofRat (a b : ℤ) : Fx := Int.fdiv (a * ONE) b
def mul (a b : Fx) : Fx := Int.fdiv (a * b) ONE
def div (a b : Fx) : Fx := Int.fdiv (a * ONE) b
def floor (a : Fx) : ℤ := Int.fdiv a ONE
def ceil (a : Fx) : ℤ := -Int.fdiv (-a) ONE
/-- Floor division by an integer. -/
def idiv (a : Fx) (k : ℤ) : Fx := Int.fdiv a k

/-- `log₂ v` for a positive integer `v`, rounded down, by repeated squaring. -/
def log2Nat (v : ℕ) : Fx :=
  let e := Nat.log2 v
  let m0 := (v <<< K) >>> e
  let r := (List.range P).foldl (fun (acc : ℕ × ℕ) _ =>
    let m := (acc.1 * acc.1) >>> K
    if 2 ^ (K + 1) ≤ m then (m >>> 1, 2 * acc.2 + 1) else (m, 2 * acc.2)) (m0, 0)
  (e : ℤ) * ONE + r.2

/-- `log₂ x` for a positive fixed-point `x`. -/
def log2 (x : Fx) : Fx := log2Nat x.toNat - (P : ℤ) * ONE

def ln (x : Fx) : Fx := mul (log2 x) LN2

/-- Taylor sum of `e^t`, `t ∈ [0, ln 2)`. -/
def expTaylor (t : Fx) : (fuel i : ℕ) → (s term : Fx) → Fx
  | 0, _, s, _ => s
  | fuel + 1, i, s, term =>
    let term := Int.fdiv (mul term t) i
    if term = 0 then s else expTaylor t fuel (i + 1) (s + term) term

/-- `2^y`. -/
def exp2 (y : Fx) : Fx :=
  let k := Int.fdiv y ONE
  let f := y - k * ONE
  let s := expTaylor (mul f LN2) 63 1 ONE ONE
  if 0 ≤ k then s * 2 ^ k.toNat else Int.fdiv s (2 ^ (-k).toNat)

def exp (x : Fx) : Fx := exp2 (mul x LOG2E)

def sqrt (x : Fx) : Fx := (Nat.sqrt ((max 0 x) * ONE).toNat : ℤ)

/-- `x^y` for `x > 0`. -/
def pow (x y : Fx) : Fx := exp2 (mul y (log2 x))

/-- `log₂ (2^a + 2^b)`. -/
def log2Add (a b : Fx) : Fx := max a b + log2 (ONE + exp2 (min a b - max a b))

end Fx

/-- A cost: its `log₂` (fixed point), or `none` for infinity. -/
abbrev Cost := Option Fx

namespace Cost

def min : Cost → Cost → Cost
  | none, b => b
  | a, none => a
  | some a, some b => some (Min.min a b)

def add : Cost → Cost → Cost
  | some a, some b => some (Fx.log2Add a b)
  | _, _ => none

/-- `a ≤ b` with `none = ∞`. -/
def le : Cost → Cost → Prop
  | _, none => True
  | none, some _ => False
  | some a, some b => a ≤ b

instance : DecidableRel le := fun a b => by
  cases a <;> cases b <;> unfold le <;> infer_instance

end Cost

end SigabaNeo.Lattices.Estimator
