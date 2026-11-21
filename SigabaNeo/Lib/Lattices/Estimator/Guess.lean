import SigabaNeo.Lib.Lattices.Estimator.NumMisc

/-! Classical exhaustive search and analytical MITM from estimator/lwe_guess.py.
Both target 99% success and report infinity when the sample budget is insufficient. -/
namespace SigabaNeo.Lattices.Estimator.Guess
open Fx NumMisc

def exhaustiveCost (params : LWEParams) : Cost := do
  let p := params.normalize
  let prob := Fx.sqrt (ofRat 99 100)
  let size ← match p.Xs.kind with
    | .gauss _ => do
      guard ((p.n : Int) * log2 (tail p.Xs) ≥ log2 prob)
      pure ((p.n : Int) * log2 (width p.Xs))
    | _ => pure (log2Nat (ceil (prob * floor (width p.Xs) ^ p.n)).toNat)
  let s := mul PI p.Xe.stddev / p.q
  let exponent := 4 * mul s s
  guard (exponent ≤ 10000 * LN2)
  let m := 8 * mul (exp exponent) (mul size LN2 - ln (-(ln prob)))
  let bits := ONE + size + log2 m
  guard (p.mGe (ceil m).toNat && bits ≤ 10000 * ONE)
  return bits

def mitmCost (params : LWEParams) : Cost := do
  let p := params.normalize
  let err := width p.Xe
  let sec := width p.Xs
  guard (err < ofInt p.q)
  let den := 2 * ONE - err / p.q
  let k := (floor (div (ofInt p.n) den + ONE/2)).toNat
  let mut prob := (p.n : Int) * log2 (tail p.Xs)
  let mut t := (k : Int) * log2 sec
  if p.Xs.isSparse then
    let h := p.Xs.hammingWeight.toNat
    guard (h > 0)
    let j := h*k/p.n
    prob := prob + log2Nat (k.choose j * (p.n-k).choose (h-j)) - log2Nat (p.n.choose h)
    t := div (h * (log2Nat p.n - log2Nat h + log2 (sec-ONE) + LOG2E)) den
    t := t - (log2Nat h / 2 + div (h*h*LOG2E) (2*p.n*mul den den))
  let m := if t > 0 then max 1 (floor (t + log2 t + ONE/2)) else 1
  guard (p.mGe m.toNat)
  return ofInt m + repeatBits (prob + m * log2 (tail p.Xe))
end SigabaNeo.Lattices.Estimator.Guess
