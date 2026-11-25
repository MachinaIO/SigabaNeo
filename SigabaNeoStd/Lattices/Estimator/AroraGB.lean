import SigabaNeoStd.Lattices.Estimator.NumMisc

/-! Arora–Ge semi-regular Hilbert series, Gaussian tail heuristic and multiplicative
guess_composition (gb.py and lwe_guess.py). A negative coefficient gives dreg. -/
namespace SigabaNeo.Lattices.Estimator.AroraGB
open Fx NumMisc

def gb (n d m s : Nat) : Cost := Id.run do
  let mut err := Array.replicate (min d (2*n)) (0 : Int)
  let mut sec := Array.replicate (min s (2*n)) (0 : Int)
  let mut sum : Int := 0
  let mut a : Int := 1
  for k in [1:2*n] do
    sum := sum+a
    err := err.modify ((k-1)%d) (·+a)
    let mut v := n*sum - (m : Int)*d*err[k%d]!
    if s > 0 then
      sec := sec.modify ((k-1)%s) (·+a)
      v := v - (n : Int)*s*sec[k%s]!
    a := v/k
    if a < 0 then return some (2 * log2Nat ((n+k).choose k))
  return none

def samples (c : Fx) : Nat :=
  let neglog := log2 (mul c SQRT2PI) - ONE + mul (mul c c) LOG2E / 2
  let l := ln (ofRat 99 100)
  if neglog ≥ 257*ONE then 2^31
  else if neglog > 25*ONE then (floor (mul (-l) (exp2 neglog))).toNat
  else (floor (div l (ln (ONE-exp2 (-neglog))))).toNat

def single (params : LWEParams) : Cost := Id.run do
  let p := params.normalize
  let s := if p.Xs.stddev > p.Xe.stddev then 0 else match p.Xs.kind with
    | .gauss v => (2*ceil (3*v)+1).toNat
    | _ => (floor (width p.Xs)).toNat
  let mut best : Cost := none
  match p.Xe.kind with
  | .gauss _ => pure ()
  | _ =>
    let d := (floor (width p.Xe)).toNat
    if d < 2*p.n || s > 0 then
      let bound := p.n ^ min d (2*p.n)
      best := gb p.n d (min bound (p.m.getD bound)) s
  if p.Xe.isGaussianLike && p.Xe.stddev > 0 then
    let mut g : Cost := none
    let mut stuck := 0
    for t in [(ceil p.Xe.stddev).toNat:p.n] do
      let m := samples (div (ofInt t) p.Xe.stddev)
      if !p.mGe m then break
      if m ≤ p.n && s == 0 then continue
      if let some v := gb p.n (2*t+1) m s then
        if g.all (v < ·) then
          g := some v
          stuck := 0
        else
          stuck := stuck+1
          if stuck == 5 then break
    best := Cost.min best g
  return best

def penalty (p : LWEParams) (z base : Nat) : Fx := Id.run do
  if !p.Xs.isSparse then return (z : Int)*log2Nat base
  let h := p.Xs.hammingWeight.toNat
  let mut space := 0
  let mut hits := 0
  let mut best := 0
  let count := match p.Xs.kind with
    | .gauss _ => min 1 (min h z)
    | _ => min h z
  for j in [:count] do
    space := space + z.choose j * (base-1)^j
    hits := hits + h.choose j * (p.n-h).choose (z-j)
    if hits > 0 then
      let v := log2Nat space + repeatBits (log2Nat hits - log2Nat (p.n.choose z))
      if best != 0 && v ≥ best then break
      best := v
  return best

def cost (params : LWEParams) : Cost := do
  let p := params.normalize
  let gaussian := match p.Xs.kind with
    | .gauss _ => true
    | _ => false
  -- The dense wrapper has an empty search interval for an infinite guessing base.
  guard (!gaussian || p.Xs.isSparse)
  let base := if gaussian then 2 else (floor (width p.Xs)).toNat
  let logbase := log2Nat base
  let stop ← if p.Xs.isSparse then pure (p.n-40) else do
    let baseline ← single p
    pure (min p.n (baseline/logbase).toNat)
  if logbase == 0 then return ← single p
  let candidate := fun z ↦ do
    if gaussian then guard (z ≤ p.n-p.Xs.hammingWeight.toNat)
    let v ← single (LWEParams.mk' (p.n-z) p.q p.Xs p.Xe p.m)
    return v + penalty p z base
  -- Preserve the wrapper's immediate infinity on an infeasible subproblem.
  let result ← search 0 stop candidate (fun a b ↦ b.isSome && (a.isNone || decide (Cost.le a b)))
  result
end SigabaNeo.Lattices.Estimator.AroraGB
