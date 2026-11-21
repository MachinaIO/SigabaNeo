import SigabaNeo.Lib.Lattices.Estimator.Reduction
import SigabaNeo.Lib.Lattices.Estimator.Params

/-! GJ21.short_vectors with the MATZOV sieve fit, progressive BKZ overhead and batch rounding. -/
namespace SigabaNeo.Lattices.Estimator.NumDual
open Fx Reduction

def sieveDim (b d : ℕ) : ℕ :=
  let s := b - (floor (d4f b)).toNat
  if b < d then min d (s + (floor (div (log2Nat (d-b) + log2C) NN_A)).toNat) else s

def rhoBits (b d : ℕ) : Fx :=
  let s := sieveDim b d
  log2 (ofRat 4 3) / 2 + ((s : ℤ)-1) * (log2Delta s - log2Delta b)

def shortBits (b d : ℕ) (count : Fx) : Cost := do
  if count == 0 then return matzovBits b d
  let s := sieveDim b d
  let batch := floor (exp2 (ofRat 2075 10000 * s))
  if count > log2Nat batch.toNat + 1000*ONE then none else
    let runs := max 1 ((ceil (exp2 count) + batch - 1) / batch)
    return log2Nat runs.toNat + log2Add (matzovBits b d) (log2C + NN_A*s + NN_B)

end SigabaNeo.Lattices.Estimator.NumDual
