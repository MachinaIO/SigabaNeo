import SigabaNeo.Lib.Lattices.Estimator.Fx

/-!
# Lattice reduction cost

`estimator/reduction.py`: the root-Hermite factor `δ(β)`, Ducas' dimensions for free and the
default cost model `RC.MATZOV` (classical list-decoding sieve, fitted to [AGPS20] with the
[MATZOV22] improvement; `CheNgu12` enumeration below `β = 20`). Costs are `log₂` values.
`python/lwemodel/reduction.py` is the mirror.

**Heuristics.** The sieve cost is a numerical fit (not a theorem), the number of SVP calls of
progressive BKZ is the [Kyber20] rule `C · (d − β)`, and the dimensions for free are [Duc18].
-/

namespace SigabaNeo.Lattices.Estimator

namespace Reduction

open Fx

def NN_A : Fx := ofRat 29613500308205365 (10 ^ 17)
def NN_B : Fx := ofRat 20387885985467914 (10 ^ 15)
def CN_A : Fx := ofRat 270188776350190 (10 ^ 15)
def CN_B : Fx := ofRat 10192050451318417 (10 ^ 16)
def CN_C : Fx := ofRat 1610253135200765 (10 ^ 14)

def log2TwoPiE : Fx := log2 (mul (2 * PI) E)
def log2Pi : Fx := log2 PI
def ln43 : Fx := ln (ofRat 4 3)

/-- `log₂ δ(β)` (`ReductionCost._delta` at an integer `β`). -/
def log2Delta (β : ℕ) : Fx :=
  if β < 5 then log2 (ofRat 102190 (10 ^ 5))
  else if β < 10 then log2 (ofRat 101862 (10 ^ 5))
  else if β < 15 then log2 (ofRat 101616 (10 ^ 5))
  else if β < 20 then log2 (ofRat 101485 (10 ^ 5))
  else if β < 25 then log2 (ofRat 101420 (10 ^ 5))
  else if β < 28 then log2 (ofRat 101342 (10 ^ 5))
  else if β < 40 then log2 (ofRat 101331 (10 ^ 5))
  else if β = 40 then log2 (ofRat 101295 (10 ^ 5))
  else
    let lb := log2 (ofInt β)
    let t := lb - log2TwoPiE + idiv (log2Pi + lb) β
    idiv t (2 * ((β : ℤ) - 1))

/-- `β ln(4/3) / ln(β/(2πe))`, at least `0`. -/
def d4f (β : ℕ) : Fx :=
  let den := log2 (ofInt β) - log2TwoPiE
  if den ≤ 0 then 0 else max 0 (div (β * ln43) (mul den LN2))

/-- `log₂ C`, `C = 1/(1 − 2^{−a})`: the overhead of progressive sieving. -/
def log2C : Fx := log2 (div ONE (ONE - exp2 (-NN_A)))

def lllBits (d : ℕ) : Fx := 3 * log2 (ofInt d)

def svpRepeatBits (β d : ℕ) : Fx := if β < d then log2 (ofInt (8 * d)) else 0

/-- `log₂ RC.MATZOV(β, d)`. -/
def matzovBits (β d : ℕ) : Fx :=
  if β < 20 then
    let lnb := ln (ofInt β)
    let c := mul (CN_A * β) lnb - CN_B * β + CN_C + log2 (ofInt 100)
    log2Add (lllBits d) (svpRepeatBits β d + c)
  else
    let β' := ofInt β - d4f β
    let svp := log2C + log2 (ofInt (max ((d : ℤ) - β) 1))
    let gate := log2C + mul NN_A β' + NN_B
    log2Add (lllBits d) (svp + gate)

end Reduction

end SigabaNeo.Lattices.Estimator
