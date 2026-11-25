import SigabaNeoStd.Lattices.Estimator.NumMisc

/-! Coded-BKW (estimator/lwe_bkw.py), including sample amplification. Test dimension
uses Brent interpolation followed by an integer scan. Erf uses the A&S five-term approximation. -/
namespace SigabaNeo.Lattices.Estimator.Bkw
open Fx NumMisc

def erf (x : Fx) : Fx :=
  if x ≥ 7*ONE then ONE else
  let t := div ONE (ONE+mul (ofRat 3275911 (10^7)) x)
  let a := ([1061405429,-1453152027,1421413741,-284496736,254829592] : List Int).foldl
    (fun a c ↦ mul t (a+ofRat c (10^9))) 0
  ONE-mul a (exp (-(mul x x)))

/-- Brent interpolation with the 10% relative tolerance of upstream ntest. -/
def testDim (rem t : Nat) (code : Nat → Fx → Nat) : Nat := Id.run do
  if rem == 0 then return 0
  let residual := fun x ↦ ofInt ((rem : Int)-
    ((List.range t).foldl (fun a i ↦ a+code (i+1) x) 0 : Nat)) - x
  let mut a := 2*ONE
  let mut bx := ofInt (rem+1)
  let mut fa := residual a
  let mut fb := residual bx
  let mut start : Nat := 2
  if fa ≥ 0 && fb ≤ 0 then
    let mut block := a
    let mut fc := fa
    let mut old := bx-a
    let mut step := old
    for _ in [:100] do
      if fa*fb < 0 then
        block := a
        fc := fa
        old := bx-a
        step := old
      if fc.natAbs < fb.natAbs then
        a := bx
        bx := block
        block := a
        fa := fb
        fb := fc
        fc := fa
      let tol := (bx/10+281)/2
      let half := (block-bx)/2
      if fb == 0 || (half.natAbs : Int) < tol then break
      let trial := if (old.natAbs : Int) > tol && fb.natAbs < fa.natAbs then
        if a == block then some ((-fb*(bx-a)).fdiv (fb-fa))
        else some (((a-bx)*fb*fc).fdiv ((fa-fb)*(fa-fc)) +
          ((block-bx)*fa*fb).fdiv ((fc-fa)*(fc-fb)))
        else none
      if trial.any (fun v ↦ 2*(v.natAbs : Int) < min (old.natAbs : Int) (3*(half.natAbs : Int)-tol)) then
        old := step
        step := trial.getD 0
      else
        old := half
        step := half
      a := bx
      fa := fb
      bx := bx + (if (step.natAbs : Int) > tol then step else if half > 0 then tol else -tol)
      fb := residual bx
    start := max 2 ((floor (bx+ONE/2)).toNat-1)
  let mut best : Nat := 1
  for v in [start:rem+1] do
    if (residual (ofInt v)).natAbs ≥ (residual (ofInt best)).natAbs then break
    best := v
  return best

abbrev Estimate := Option (Fx × Nat)

/-- The number of samples for the final distinguisher, given the noise `u`. -/
def samplesNeeded (u : Fx) : Int :=
  if u ≤ -2*ln (ofRat 99 100) then 1 else if mul u LOG2E > 25*ONE then
    let exponent := mul u LOG2E
    let prec := max 53 (2*ceil (exponent/2)).toNat
    let mant := floor (exp2 (ofInt prec-exponent)+ONE/2)
    ceil ((-2*ln (ofRat 1 50)*2^prec)/mant)
    else ceil (div (2*ln (ofRat 1 50)) (ln (ONE-exp (-u))))

/-- The operation count of the reduction steps and of the code steps. -/
def accum (p : LWEParams) (se : Fx) (b n t1 top x : Nat) (codes : List Nat) (m half samples : Int) :
    Int := Id.run do
  let mut c := if p.Xs.stddev > se then (samples-ofInt n)*(p.n+1)*((n+b-2)/(b-1)) else 0
  for i in [1:t1+1] do
    c := c + (p.n+1-i*b)*(samples-i*half)
  let mut coords := top+x
  for (v,i) in codes.zipIdx do
    coords := coords+v
    c := c + 4*(ofInt m+(i+1)*half)*v + coords*(ofInt m+i*half)
  return c

/-- The bound on a guessed secret coordinate. -/
def zOf (p : LWEParams) : Fx :=
  if p.Xs.isGaussianLike then min (width p.Xs) (6*p.Xs.stddev+ONE) else width p.Xs

/-- The guessing step and the total, in bits, with the rounded sample count. -/
def finish (p : LWEParams) (se lq : Fx) (b top x : Nat) (m table samples c : Int) : Estimate := do
  let z := zOf p
  let guesses := if top == 0 then ONE else (2*z+ONE)^top / ONE^(top-1)
  let c := c + guesses*m*top + ofInt (4*m*x) + mul guesses (table*(b*lq+ONE))
  let bits := if top == 0 || se == 0 then log2 c else log2 c - top*log2 (erf (div z (Fx.sqrt (2*se))))
  guard (bits < 1024*ONE)
  let unit : Int := 2^(samples.toNat.log2+1-53)
  let a := samples/unit
  let r := samples%unit
  let rounded := (a + if 2*r > unit || (2*r == unit && a%2 == 1) then 1 else 0)*unit
  return (bits,(ceil rounded).toNat)


def candidate (p : LWEParams) (se lq : Fx) (b steps : Nat) : Estimate := do
  let code := fun (i : Nat) (x : Fx) ↦ (2*b*lq*x / (2*(b-1)*lq*ONE+i*x*ONE)).toNat
  let x := testDim p.n steps code
  let t1 := min (p.n/b) ((List.range steps).countP (fun i ↦ code (i+1) (ofInt x) ≤ b))
  let n := p.n-t1*b
  let t2 := steps-t1
  let x := testDim n t2 code
  guard (x > 0)
  let codes := (List.range t2).map (fun i ↦ code (i+1) (ofInt x))
  let ntot := codes.sum+x
  let top := n-ntot
  let noise := 2^steps*mul se se/(p.q*p.q)
  let quant := mul (mul p.Xs.stddev p.Xs.stddev) (exp2 (-2*(b-1)*lq/x))*ntot/12
  let u := mul (4*mul PI PI) (noise+quant)
  guard (u ≤ 1020*LN2)
  let m := samplesNeeded u
  let table : Int := (p.q : Int)^b
  let half := (table-1)*ONE/2
  let samples := steps*half+ofInt m
  finish p se lq b top x m table samples (accum p se b n t1 top x codes m half samples)

def smaller (budget : Option Nat) (a b : Estimate) : Bool :=
  match a,b with
  | _,none => true
  | none,_ => false
  | some x,some y => x.1 ≤ y.1 && !budget.any (fun m ↦ y.2 ≤ m && m < x.2)

def cost (params : LWEParams) : Cost := do
  let p := params.normalize
  let lq := log2Nat p.q
  let mut budget := p.m
  let mut se := p.Xe.stddev
  -- Distinct amplification weights are bounded by the original sample count.
  for _ in [:(p.m.getD 0)+2] do
    let outer := fun b ↦ (search 2 (max 3 (p.n/b)) (candidate p se lq b) (smaller budget)).join
    let (bits,required) ← (search 2 (3*(ceil lq).toNat) outer (smaller budget)).join
    if budget.all (required ≤ ·) then return bits
    let orig ← p.m
    guard (p.Xe.mean == 0)
    let k ← (List.range (required.log2+1)).find? (fun k ↦ orig.choose k * 2^k > required)
    budget := some required
    se := mul (Fx.sqrt (ofInt k)) p.Xe.stddev
  none
end SigabaNeo.Lattices.Estimator.Bkw
