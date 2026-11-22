import SigabaNeo.Lib.Lattices.Estimator.NumDual

/-! MATZOV.Nf and Theorem 7.6: Gaussian bias, entropy approximation, FFT and table costs.
Search block sizes by the estimator's local_minimum and use its early-abort grids (stride ten
for enumeration and FFT dimensions, unit stride for the FFT modulus). -/
namespace SigabaNeo.Lattices.Estimator.DualHybrid
open Fx Reduction NumDual

def localMin (f : ℕ → Cost) (stop : ℕ) : Cost := Id.run do
  let mut lo := 40
  let mut hi := stop-1
  let mut x := hi
  let mut dir : Int := -1
  let mut seen : List Nat := []
  let mut best : Cost := none
  for _ in [:stop] do
    if x < 40 || x ≥ stop || seen.contains x then break
    seen := x :: seen
    let v := f x
    if Cost.le v best then
      best := v
      if dir.natAbs != 1 then
        dir := -1
        x := x-1
      else if dir == -1 then
        dir := -2
        hi := x
        x := (lo+hi+1)/2
      else
        dir := 2
        lo := x
        x := (lo+hi)/2
    else if dir == -1 then
      dir := 1
      x := x+2
    else if dir == 1 then break
    else if dir == -2 then
      lo := x
      x := (lo+hi+1)/2
    else
      hi := x
      x := (lo+hi)/2
  return best

def candidate (d k t : ℕ) (base extra fft coeff enumCost : Fx) (b : ℕ) : Cost := do
  let v := base + (log2Nat b - log2TwoPiE)/2 + ((d : ℤ)-b)*log2Delta b
  if v > 10*ONE then none else
    let count := mul (4*mul PI PI) (mul LOG2E (exp2 (2*v))) + extra
    let red ← shortBits b d count
    let table := log2Nat 640 + count
    let guess := coeff + k*enumCost + (if t == 0 then table else log2Add table fft)
    return log2Add red guess

/-- `α = (π s)²` of the secret's standard deviation `s`. -/
def alphaOf (s : Fx) : Fx := mul (mul PI s) (mul PI s)

/-- `e^{−2α}` (`0` when it underflows). -/
def minusOf (s : Fx) : Fx := if alphaOf s > 17*ONE then 0 else exp (-2*alphaOf s)

/-- `tanh α`. -/
def tanhOf (s : Fx) : Fx := div (ONE-minusOf s) (ONE+minusOf s)

/-- The entropy term of one guessed coordinate. -/
def hOf (s : Fx) : Fx := LOG2E/2 + log2 SQRT2PI + log2 s - log2 (tanhOf s)

/-- The enumeration cost per guessed coordinate. -/
def enumCostOf (s : Fx) : Fx :=
  ONE - LOG2E/2 + mul (8*mul (mul (alphaOf s) (minusOf s)) (tanhOf s)) LOG2E + hOf s

/-- The coefficient of the guessing cost. -/
def coeffOf (s : Fx) : Fx :=
  let u := div ONE (2*mul s s)
  let den := if mul s s == 0 || u > 34*ONE then ONE else ONE-exp (-u)
  if den == 0 then ONE + 2*log2 s else -(log2 den)

def cost (params : LWEParams) : Cost := Id.run do
  let p := params.normalize
  let s := p.Xs.stddev
  let e := p.Xe.stddev
  if p.n == 0 || p.q ≤ 2 || s ≤ 0 || e ≤ 0 then return none
  let ls := log2 s
  let le := log2 e
  let lq := log2Nat p.q
  let alpha := alphaOf s
  if tanhOf s == 0 then return none
  let h := hOf s
  let enumCost := enumCostOf s
  let coeff := coeffOf s
  let mut best : Cost := none
  for modulus in [2:p.q] do
    let lp := log2Nat modulus
    let mut be : Cost := none
    let mut te := 0
    for k in [0:p.n:10] do
      let mut bt : Cost := none
      let mut tt := 0
      for t in [0:p.n-k:10] do
        let lat := p.n-k-t
        let d := lat+p.n
        let base := (p.n*le + lat*(ls+lq))/d-lq + log2 (ofRat 4 3)/2
        let extra := mul (t*alpha/(3*modulus*modulus : ℤ)) LOG2E + log2 (k*h+mul (t*lp) LN2+LN2)
        let fft := 10*ONE + log2Nat t + (t+1 : ℕ)*lp
        let stop := max 41 (min maxBeta ((p.m.map (fun m ↦ m-k-t)).getD maxBeta))
        let val := localMin (candidate d k t base extra fft coeff enumCost) stop
        if ¬Cost.le val bt then break
        bt := val
        tt := t
      if ¬Cost.le bt be then break
      be := bt
      te := tt
    if ¬Cost.le be best then break
    best := be
    if modulus > 2 && te == 0 then break
  return best

end SigabaNeo.Lattices.Estimator.DualHybrid
