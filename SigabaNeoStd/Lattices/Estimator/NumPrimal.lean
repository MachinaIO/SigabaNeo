import SigabaNeoStd.Lattices.Estimator.Usvp

/-! Numeric approximations for PrimalHybrid's GSA projection, Babai and MITM probabilities.
The log product uses midpoint blocks in log-length space and the first finite-sphere correction
to the normal coordinate law. The ball volume uses a shifted Stirling expansion. -/

namespace SigabaNeo.Lattices.Estimator.NumPrimal
open Fx

def erf (x : Fx) : Fx :=
  if x ≥ 8*ONE then ONE else
  let t := div ONE (ONE + mul (ofRat 3275911 (10^7)) x)
  let a := [1061405429,-1453152027,1421413741,-284496736,254829592].foldl
    (fun a c ↦ mul (a + ofRat c (10^9)) t) 0
  ONE - mul a (exp (-mul x x))

def threshold (k : ℕ) : Fx := Id.run do
  let n := k+1
  let mut x := ofInt n / 2
  let mut acc := 0
  for _ in [:8] do
    if x < 8*ONE then
      x := x + ONE
      acc := acc + log2 x
  let corr := div ONE (12*x) - div ONE (360*mul x (mul x x))
  let gamma := mul (x+ONE/2) (log2 x) - mul x LOG2E + log2 SQRT2PI + mul corr LOG2E - acc
  return ((log2 PI + log2Nat n)*(n : ℤ)/2 - gamma)/(k : ℤ)

def repetitions (lp : Fx) : Fx :=
  if lp ≥ log2 (ofRat 99 100) then 0
  else if lp < -20*ONE then log2 (ln (100*ONE)) - lp
  else log2Nat (ceil (div (-(ln (100*ONE))) (ln (ONE-exp2 lp)))).toNat

/-- The block width of `profile`: about `1/16` in log-length. -/
def strideOf (step : Fx) : ℕ := max 1 (ONE/(16*step)).toNat

def profile (k : ℕ) (first step : Fx) (mitm : Bool) : Fx := Id.run do
  let stride := strideOf step
  let mut total := 0
  for j in [:(k+stride-1)/stride] do
    let i := j*stride
    let w := min (k-i) stride
    let l := first-step*(i : ℤ)-step*((w-1 : ℕ) : ℤ)/2
    if l < (if mitm then 48 else 4)*ONE then
      let x := exp2 l
      let v := if mitm then
        let y := mul x (ofRat 707106781 (10^9))
        if y ≥ 8*ONE then ONE - div ONE (mul y (sqrt PI))
        else if y < ONE/1024 then div y (sqrt PI)
        else erf y - div (ONE-exp (-mul y y)) (mul y (sqrt PI))
      else
        let t := x/2
        let t2 := mul t t
        if t2 ≥ ofInt k || t ≥ 9*ONE then ONE else
          let phi := div (exp ((-t2)/2)) SQRT2PI
          erf (div t (sqrt (2*ONE))) + mul (mul t (t2-3*ONE)) phi/(2*(k : ℤ))
      total := total + (w : ℤ)*log2 (max 1 (min ONE v))
  return total

/-- Reduce an eight-interval grid to the neighborhood of its best point until stride one. -/
def minimize (lo hi : ℕ) (f : ℕ → Cost) : ℕ × Cost := Id.run do
  let mut left := lo
  let mut right := hi
  let mut best := hi
  let mut value : Cost := none
  for _ in [:hi.log2+3] do
    if left > right then break
    let stride := max 1 ((right-left+7)/8)
    for i in right :: (List.range ((right-left+stride-1)/stride)).map (fun j ↦ left+j*stride) do
      if let some v := f i then
        if value.all (v < ·) then
          best := i
          value := some v
    if stride == 1 then break
    left := max lo (best-stride)
    right := min hi (best+stride)
  return (best,value)

/-- The upstream local_minimum iterator uses jumps and one-step probes on a scaled grid. -/
def localMinimum (start stop precision : ℕ) (f : ℕ → Cost) : ℕ × Cost := Id.run do
  let mut left := (start+precision-1)/precision
  let mut right := stop/precision-1
  let mut i := right
  let mut dir : ℤ := -1
  let mut best := i*precision
  let mut value : Cost := none
  let mut seen : List ℕ := []
  for _ in [:stop+1] do
    if i*precision < start || i ≥ stop/precision || seen.contains i then break
    seen := i :: seen
    let v := f (i*precision)
    if value.isNone || v.any (fun x ↦ value.all (x ≤ ·)) then
      best := i*precision
      value := v
      if dir.natAbs == 2 then
        dir := -1
        i := i-1
      else if dir == -1 then
        right := i
        dir := -2
        i := (left+right+1)/2
      else
        left := i
        dir := 2
        i := (left+right)/2
    else if dir == -1 then
      dir := 1
      i := i+2
    else if dir == 1 then break
    else if dir == -2 then
      left := i
      i := (left+right+1)/2
    else
      right := i
      i := (left+right)/2
  if precision > 1 then
    for j in [max start (best-precision):min stop (best+precision)] do
      let v := f j
      if value.isNone || v.any (fun x ↦ value.all (x ≤ ·)) then
        best := j
        value := v
  return (best,value)

end SigabaNeo.Lattices.Estimator.NumPrimal
