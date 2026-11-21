import SigabaNeo.Lib.Lattices.Estimator.Params
import SigabaNeo.Lib.Lattices.Estimator.Reduction

/-!
# Primal uSVP attack

`primal_usvp` of the estimator with the GSA shape model (`PrimalUSVP.cost_gsa`): the 2016 estimate
[ADPS16, AGVW17] for the embedding of the (normal-form) instance with the Bai–Galbraith scaling
of a small secret. The estimator's local search over `β ∈ [40, max_beta)` is an exhaustive scan
here, so the result is at most the estimator's. `python/lwemodel/usvp.py` is the mirror.

**Heuristics.** The geometric series assumption, and the 2016 estimate for when BKZ-`β` finds the
unique shortest vector.
-/

namespace SigabaNeo.Lattices.Estimator

namespace Usvp

open Fx

def maxBeta : ℕ := 1754

def log2Xi (p : LWEParams) : Fx :=
  if p.Xs.stddev < p.Xe.stddev then log2 p.Xe.stddev - log2 p.Xs.stddev else 0

/-- Smallest `d ∈ [n, m]` satisfying the uSVP condition, or `none`. -/
def solveForD (p : LWEParams) (m : Option ℕ) (β : ℕ) (x log2tau l2xi l2q : Fx) : Option ℕ :=
  let se2 := mul p.Xe.stddev p.Xe.stddev
  let C := idiv (log2 (se2 * ((β : ℤ) - 1) + mul (exp2 log2tau) (exp2 log2tau))) 2
  let a := -x
  let b := x * (2 * (β : ℤ) - 1) + l2q - C
  let c := log2tau + p.n * l2xi - ((p.n : ℤ) + 1) * l2q
  let n := p.n
  if 0 ≤ mul a (ofInt (n * n)) + b * n + c then some n
  else
    let disc := mul b b - 4 * mul a c
    if disc < 0 then none
    else
      let d1 := div (-b + sqrt disc) (2 * a)
      if ofInt n ≤ d1 then
        let dd := (ceil d1).toNat
        some (match m with | none => dd | some m => Min.min m dd)
      else none

/-- `PrimalUSVP.cost_gsa`. -/
def costGsa (β : ℕ) (p : LWEParams) (m : Option ℕ) : Cost :=
  let x := Reduction.log2Delta β
  let l2xi := log2Xi p
  let log2tau := log2 p.Xe.stddev
  let l2q := log2 (ofInt p.q)
  match solveForD p m β x log2tau l2xi l2q with
  | none => none
  | some d =>
    let d := if d < β then β else d
    let below : Bool := match m with | none => true | some m => decide (d < m)
    let d := if d = β ∧ below = true then d + 1 else d
    let se2 := mul p.Xe.stddev p.Xe.stddev
    let lhs := idiv (log2 (se2 * ((β : ℤ) - 1) + mul p.Xe.stddev p.Xe.stddev)) 2
    let rhs := x * (2 * (β : ℤ) - d - 1) + idiv (log2tau + l2xi * p.n + l2q * ((d : ℤ) - p.n - 1)) d
    if rhs < lhs then none else some (Reduction.matzovBits β d)

/-- `primal_usvp` (GSA). -/
def cost (params : LWEParams) : Cost :=
  let p := params.normalize
  let m := if p.Xs.stddev ≤ p.Xe.stddev then p.m.map (· + p.n) else p.m
  let mb := match m with | none => maxBeta | some m => Max.max (Min.min maxBeta m) 45
  (List.range' 40 (mb - 40)).foldl (fun best β => Cost.min best (costGsa β p m)) none

end Usvp

end SigabaNeo.Lattices.Estimator
