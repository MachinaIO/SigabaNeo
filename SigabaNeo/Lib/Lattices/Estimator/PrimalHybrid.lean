import SigabaNeo.Lib.Lattices.Estimator.NumPrimal

/-! PrimalHybrid under GSA and MATZOV. We refine grids for guessed dimension and Hamming weight,
and use the upstream local search for block size and rank. Plain BDD additionally optimizes the rank. -/

namespace SigabaNeo.Lattices.Estimator.PrimalHybrid
open Fx NumPrimal

def choose (n k : ℕ) : ℕ := Id.run do
  if k > n then return 0
  let mut a := 1
  for j in [:min k (n-k)] do
    a := a*(n-j)/(j+1)
  return a

def weights (p : LWEParams) (z : ℕ) (mitm : Bool) : Array (Fx × Fx) := Id.run do
  let h := p.Xs.hammingWeight.toNat
  let lo := h-(p.n-z)
  let (a,b) := p.Xs.bounds.getD (0,0)
  let den := log2Nat (choose p.n z)
  let mut space := 0
  let mut hit := 0
  let mut out := #[]
  -- DiscreteGaussian(sigma) retains its infinite bounds when resized upstream.
  let hi := match p.Xs.kind with | .gauss _ => 0 | _ => min z h
  for w in [lo:hi + 1] do
    space := space + choose z w * (b-a).toNat^w
    hit := hit + choose h w * choose (p.n-h) (z-w)
    out := out.push (log2Nat space / (if mitm then 2 else 1),log2Nat hit-den)
  return out

def etaFor (avg delta : Fx) (d : ℕ) : ℕ := Id.run do
  let mut hi := if d > 4096 then min d maxBeta else d
  let mut lo := 0
  for _ in [:d.log2+2] do
    if lo ≥ hi then break
    let k := (lo+hi+1)/2
    if avg-((d-k : ℕ) : ℤ)*delta < threshold k then lo := k else hi := k-1
  return lo+1

/-- The lattice dimension for block size `b`: the optimum of the GSA, capped by the samples. -/
def rankOf (u : ℕ) (q xi : Fx) (m : Option ℕ) (z b : ℕ) : ℕ :=
  let d := (ceil (sqrt (div ((u : ℤ)*(q-xi)) (Reduction.log2Delta b)))).toNat
  max b (min d ((m.map (· - z)).getD d))

/-- The cost at block size `b` and dimension `d`, with `z` guessed coordinates (weights `ws`). -/
def evalAt (p : LWEParams) (mitm : Bool) (m : Option ℕ) (q xi s : Fx) (z : ℕ)
    (ws : Array (Fx × Fx)) (b d : ℕ) : Cost := Id.run do
  let u := p.n-z
  if d < b || (m.any (fun cap ↦ b+z > cap)) then return none
  let delta := Reduction.log2Delta b
  let avg := q-((u : ℤ)*(q-xi))/(d : ℤ)-s
  let red := Reduction.matzovBits b d
  let eta := if mitm then 0 else etaFor avg delta d
  if eta > d then return none
  let k := d-eta
  let svp := if mitm then 2*log2Nat d else
    log2Add (Reduction.matzovBits (eta+1) (eta+1)) (2*log2Nat (max k 1))
  let first := avg+((d : ℤ)-1)*delta
  let lp := profile k first (2*delta) false +
    (if mitm && z > 0 then profile d first (2*delta) true else 0)
  return (minimize 0 (ws.size-1) (fun i ↦ do
    let (a,t) ← ws[i]?
    return log2Add red (svp+a) + repetitions (lp+t))).2

/-- The cost with `z` guessed coordinates: block size by local search below `top + 2`, then
(plain BDD) the dimension. -/
def zcost (p : LWEParams) (mitm plain : Bool) (m : Option ℕ) (top : ℕ) (q xi s : Fx) (z : ℕ) :
    Cost := Id.run do
  let u := p.n-z
  let ws := weights p z mitm
  if ws.isEmpty then return none
  let (b,c) := localMinimum 40 (top+2) 2 (fun b ↦ evalAt p mitm m q xi s z ws b (rankOf u q xi m z b))
  if plain && c.isSome then return (localMinimum u (rankOf u q xi m z b+1) 1 (evalAt p mitm m q xi s z ws b)).2
  return c

def estimate (params : LWEParams) (mitm plain : Bool) : Cost := Id.run do
  let p := params.normalize
  if min p.Xs.stddev p.Xe.stddev ≤ 0 || p.q == 0 || p.n == 0 then return none
  let m := if p.Xs.stddev ≤ p.Xe.stddev then p.m.map (· + p.n) else p.m
  let upper := min maxBeta (m.getD maxBeta)
  let (best,ub) := localMinimum 40 (max 45 upper) 5 (fun b ↦ Usvp.costGsa b p m)
  let top := if ub.isSome then best else upper
  let q := log2Nat p.q
  let xi := Usvp.log2Xi p
  let s := log2 p.Xe.stddev
  return if plain then zcost p mitm plain m top q xi s 0
    else (minimize 0 (p.n-1) (zcost p mitm plain m top q xi s)).2

def costBdd (p : LWEParams) : Cost := estimate p false false
def costMitm (p : LWEParams) : Cost := estimate p true false
end SigabaNeo.Lattices.Estimator.PrimalHybrid
