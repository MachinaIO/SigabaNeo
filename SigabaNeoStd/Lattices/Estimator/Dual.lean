import SigabaNeoStd.Lattices.Estimator.NumDual

/-! Micciancio-Regev dual attack using EJK sample selection, Gaussian distinguishing advantage
and GJ21 sampling. Scan all integer block sizes in the estimator interval. -/
namespace SigabaNeo.Lattices.Estimator.Dual
open Fx Reduction NumDual

def candidate (p : LWEParams) (xs c : Fx) (b : ℕ) : Cost := do
  let h := log2Delta b
  let opt := max 1 ((ceil (sqrt (div (p.n*c) h))).toNat - p.n)
  let m := min opt (p.m.getD opt)
  let d := m + p.n
  let sigma := rhoBits b (2*b) + xs + d*h - m*c/d
  if sigma > 4*ONE - log2 SQRT2PI then none else
    let a := mul (mul (4*mul PI PI) LOG2E) (exp2 (2*sigma))
    if a > 2150*ONE then none else
      let numerator := 2*ln (ofInt 50)
      let count ← if a < -2*log2 (ofRat 99 100) then some 0 else if a < 24*ONE then
        some (log2Nat (ceil (div numerator (-(ln (ONE-exp2 (-a)))))).toNat)
        else
          let prec := min 2048 (max 53 (2*ceil (a/2)))
          let units := floor (exp2 (ofInt prec-a) + ONE/2)
          if units == 0 then none else some (log2 numerator + ofInt prec - log2Nat units.toNat)
      return log2Add (← shortBits b d count) count

/-- The dual attack, given `lq = log₂ q` and whether `q = 0`. -/
def costQ (lq : Fx) (qZero : Bool) (p : LWEParams) : Cost := Id.run do
  let p := p.normalize
  if p.Xs.isSparse || p.Xs.stddev ≤ 0 || p.Xe.stddev ≤ 0 || p.n == 0 || qZero then return none
  let xs := log2 p.Xs.stddev
  let c := xs + lq - log2 p.Xe.stddev
  let mut best : Cost := none
  for b in [40:max 48 (min maxBeta (p.m.getD maxBeta))] do
    best := Cost.min best (candidate p xs c b)
  return best

/-- The dual attack. The modulus enters only through `log₂ q` and `q = 0`. -/
def cost (p : LWEParams) : Cost := costQ (log2Nat p.q) (p.q == 0) p

end SigabaNeo.Lattices.Estimator.Dual
