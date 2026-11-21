import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Sqrt

/-!
# The security function of LWE, Ring-LWE and Module-LWE

`Hardness.securityBits N rank m q s secret` is the number of bits that the assumptions
`ModuleLWE.decision`, `RingLWE.decision` and `LWE.decision` (and their search forms) claim at the
given parameters: Module-LWE over `Z_q[X]/(X^N + 1)` of rank `rank` with `m` samples, errors from
`D_{Z,s}` (`ρ_s(x) = exp(-π x²/s²)`) and the secret law `secret`.

It is a conservative lower bound on the cost of every known classical attack, through the LWE view
of dimension `n = N·rank` with `N·m` samples. The model is in `docs/LWE_HARDNESS.md`:

* **lattice reduction** (primal uSVP and BDD, dual, and their hybrids): the smallest block size `β`
  with which the primal attack succeeds under the geometric series assumption ([ADPS16] "2016
  estimate", as in the lattice estimator, over every number of samples used), costed at
  `2^{0.292 (β - d4f(β))}`: classical sieving [BDGL16] with Ducas' dimensions for free [Duc18]
  and no polynomial factor;
* **algebraic attacks** (Arora–Ge with Gröbner bases): a lower bound on the degree of regularity
  from counting monomials, `binom(n + d, d)^2` operations, and the probability that every error used
  lies in the assumed range;
* **exhaustive search and meet-in-the-middle** on the secret: half its min-entropy;
* the **normal form**: with more samples than `n`, a uniform secret is traded for one distributed
  like the errors, with `n` fewer samples; every bound is also taken on that instance;
* **ring structure**: `log₂ N` bits are subtracted; `N` must be a power of two (otherwise
  `X^N + 1` has a factor over `Z` and the claim is `0`).

The minimum is capped at `bitsCap`. Every quantity is an interval of fixed-point numbers with `P`
fractional bits, rounded in the attacker's favour. `python/lwe_hardness.py` mirrors this file with
the same integer arithmetic and compares it with the lattice estimator.

Everything here is computable: `#eval` gives the value at concrete parameters, and the loops are
structurally recursive with explicit fuel, so `decide` can check `k ≤ securityBits …`. Running out
of fuel gives `0`.
-/

namespace SigabaNeo.Lattices

/-- The law of the secret's coefficients. -/
inductive SecretDist where
  /-- Uniform over `Z_q`. -/
  | uniform
  /-- `D_{Z,s}` reduced mod `q`. -/
  | gauss (s : ℚ)
  /-- Uniform over `{-B, …, B}` reduced mod `q` (`B = 1`: ternary). -/
  | bounded (B : ℕ)
  deriving DecidableEq, Repr

/-- The secret law is non-degenerate: a positive width, or a positive bound. -/
def SecretDist.valid : SecretDist → Bool
  | .uniform => true
  | .gauss s => decide (0 < s)
  | .bounded B => decide (0 < B)

namespace Hardness

/-! ### Fixed point -/

/-- Fractional bits. -/
def P : ℕ := 32
/-- The fixed-point unit `2^P`. -/
def F : ℤ := 2 ^ P
/-- Working precision of the logarithm. -/
def K : ℕ := 64
/-- No claim above this many bits. -/
def bitsCap : ℤ := 1024
/-- Largest block size scanned. -/
def betaMax : ℕ := 4096
/-- Classical sieving costs `2^{0.292 β'}` in sieving dimension `β'` [BDGL16]. -/
def sieveNum : ℤ := 292
/-- Denominator of the sieving exponent. -/
def sieveDen : ℤ := 1000
/-- Bits subtracted from the minimum. -/
def safetyBits : ℤ := 0

/-- Floor division. -/
def fdiv (a b : ℤ) : ℤ := Int.fdiv a b
/-- Ceiling division. -/
def cdiv (a b : ℤ) : ℤ := -Int.fdiv (-a) b

/-- `F · log₂ x` rounded down (for `x ≥ 1`), by repeated squaring of the mantissa. -/
def log2LoNat (x : ℕ) : ℤ :=
  let e := Nat.log2 x
  let m0 := (x <<< K) >>> e
  let r := (List.range P).foldl (fun (acc : ℕ × ℕ) _ =>
    let m := (acc.1 * acc.1) >>> K
    if 2 ^ (K + 1) ≤ m then (m >>> 1, 2 * acc.2 + 1) else (m, 2 * acc.2)) (m0, 0)
  (e : ℤ) * F + r.2

/-- An interval of fixed-point numbers. -/
abbrev Iv := ℤ × ℤ

/-- An enclosure of `log₂ x`. -/
def log2Nat (x : ℕ) : Iv := let l := log2LoNat x; (l, l + 2)

/-- An enclosure of `log₂ r` for `r > 0`. -/
def log2Q (r : ℚ) : Iv :=
  let a := log2Nat r.num.toNat
  let b := log2Nat r.den
  (a.1 - b.2, a.2 - b.1)

/-- An enclosure of `log₂ x` for `x ∈ [lo, hi]`. -/
def log2IvQ (lo hi : ℚ) : Iv := ((log2Q lo).1, (log2Q hi).2)

def ivConst (v : ℤ) : Iv := (v * F, v * F)
def ivAdd (a b : Iv) : Iv := (a.1 + b.1, a.2 + b.2)
def ivSub (a b : Iv) : Iv := (a.1 - b.2, a.2 - b.1)
def ivSmul (k : ℤ) (a : Iv) : Iv := if 0 ≤ k then (k * a.1, k * a.2) else (k * a.2, k * a.1)
def ivDivNat (a : Iv) (k : ℤ) : Iv := (fdiv a.1 k, cdiv a.2 k)
def min4 (a b c d : ℤ) : ℤ := min (min a b) (min c d)
def max4 (a b c d : ℤ) : ℤ := max (max a b) (max c d)
def ivMul (a b : Iv) : Iv :=
  (fdiv (min4 (a.1 * b.1) (a.1 * b.2) (a.2 * b.1) (a.2 * b.2)) F,
    cdiv (max4 (a.1 * b.1) (a.1 * b.2) (a.2 * b.1) (a.2 * b.2)) F)
/-- Division by an interval of positive numbers. -/
def ivDiv (a b : Iv) : Iv :=
  (min4 (fdiv (a.1 * F) b.1) (fdiv (a.1 * F) b.2) (fdiv (a.2 * F) b.1) (fdiv (a.2 * F) b.2),
    max4 (cdiv (a.1 * F) b.1) (cdiv (a.1 * F) b.2) (cdiv (a.2 * F) b.1) (cdiv (a.2 * F) b.2))
def ivSqrt (a : Iv) : Iv :=
  ((Nat.sqrt (max 0 a.1 * F).toNat : ℤ), (Nat.sqrt (max 0 a.2 * F).toNat : ℤ) + 1)
def ivMax0 (a : Iv) : Iv := (max 0 a.1, max 0 a.2)

/-! ### Constants -/

def piLo : ℚ := 314159265 / 10 ^ 8
def piHi : ℚ := 314159266 / 10 ^ 8
def eLo : ℚ := 271828182 / 10 ^ 8
def eHi : ℚ := 271828183 / 10 ^ 8

def log2Pi : Iv := log2IvQ piLo piHi
def log2E : Iv := log2IvQ eLo eHi
def log2TwoPi : Iv := ivAdd (ivConst 1) log2Pi
def log2TwoPiE : Iv := ivAdd log2TwoPi log2E
def log2FourThirds : Iv := log2Q (4 / 3)

/-! ### Lattice reduction -/

/-- An enclosure of `log₂ δ(β)`, the lattice estimator's root-Hermite factor: its table for
`β ≤ 40`, and `δ = (β/(2πe) · (πβ)^{1/β})^{1/(2(β-1))}` above. -/
def log2Delta (β : ℕ) : Iv :=
  if β < 5 then log2Q (102190 / 10 ^ 5)
  else if β < 10 then log2Q (101862 / 10 ^ 5)
  else if β < 15 then log2Q (101616 / 10 ^ 5)
  else if β < 20 then log2Q (101485 / 10 ^ 5)
  else if β < 25 then log2Q (101420 / 10 ^ 5)
  else if β < 28 then log2Q (101342 / 10 ^ 5)
  else if β < 40 then log2Q (101331 / 10 ^ 5)
  else if β = 40 then log2Q (101295 / 10 ^ 5)
  else
    let lb := log2Nat β
    let t1 := ivSub lb log2TwoPiE
    let t2 := ivDivNat (ivAdd log2Pi lb) β
    ivDivNat (ivAdd t1 t2) (2 * ((β : ℤ) - 1))

/-- `k ≥ π log₂(e) (B+1)²/s²`, so that `exp(-π (B+1)²/s²) ≥ 2^{-k}`. -/
def tailExp (B : ℕ) (s : ℚ) : ℤ :=
  let v : ℚ := piHi * ((B : ℚ) + 1) ^ 2 / (s * s)
  let vF := cdiv (v.num * F) v.den
  cdiv (ivMul (vF, vF) log2E).2 F

/-- An enclosure of `log₂` of the standard deviation of `D_{Z,s}`. It is at most `s/√(2π)`, and
at least `√(r) s/√(2π)` with `r` from a table (`docs/LWE_HARDNESS.md`); below `s = 1` the
variance is at least `2 ρ_s(1)/ρ_s(Z) ≥ 2^{1-k}/(1+s)`. -/
def gaussLog2Sigma (s : ℚ) : Iv :=
  let base := ivSub (log2Q s) (ivDivNat log2TwoPi 2)
  let r : Option ℚ :=
    if 2 ≤ s then some (999 / 1000)
    else if 3 / 2 ≤ s then some (97 / 100)
    else if 6 / 5 ≤ s then some (8 / 10)
    else if 1 ≤ s then some (49 / 100)
    else none
  let lo := match r with
    | some r => (ivAdd base (ivDivNat (log2Q r) 2)).1
    | none => fdiv ((1 - tailExp 0 s) * F - (log2Q (1 + s)).2) 2
  (lo, base.2)

/-- A lower bound (fixed point) on `log₂ (1 / Pr[|e| ≤ B])` for `e ← D_{Z,s}`: point masses are at
most `1/max(1, s)`, and `Pr[|e| > B] ≥ 2^{1-k}/(1+s)` with `-log₂(1 - x) ≥ x`. -/
def ell (B : ℕ) (s : ℚ) : ℤ :=
  let l1 := if 1 < s then max 0 ((log2Q s).1 - (log2Nat (2 * B + 1)).2) else 0
  let k := tailExp B s
  let l2 := fdiv (2 * F * s.den) ((s.num + s.den) * 2 ^ k.toNat)
  max l1 l2

/-- An enclosure of `log₂` of the standard deviation of the secret's coefficients. -/
def secretLog2Sigma (q : ℕ) : SecretDist → Iv
  | .uniform => ivDivNat (log2Q (((q * q - 1 : ℕ) : ℚ) / 12)) 2
  | .gauss s => gaussLog2Sigma s
  | .bounded B => ivDivNat (ivSub (log2Nat (B * (B + 1))) (log2Nat 3)) 2

/-- A lower bound (fixed point) on the min-entropy of one coefficient of the secret. -/
def secretMinEntropyLo (q : ℕ) : SecretDist → ℤ
  | .uniform => (log2Nat q).1
  | .gauss s => max 0 (log2Q s).1
  | .bounded B => (log2Nat (2 * B + 1)).1

/-- An upper bound (fixed point) on the dimensions for free `β log(4/3)/log(β/(2πe))`, at
most `β`. -/
def d4fHi (β : ℕ) : ℤ :=
  let den := (ivSub (log2Nat β) log2TwoPiE).1
  if den ≤ log2FourThirds.2 then (β : ℤ) * F
  else min ((β : ℤ) * F) (cdiv ((β : ℤ) * log2FourThirds.2 * F) den)

/-- A lower bound on the bits of BKZ-`β` with sieving: `0.292 (β - d4f(β))`. -/
def sieveBitsLo (β : ℕ) : ℤ :=
  fdiv (max 0 ((β : ℤ) * F - d4fHi β) * sieveNum) (sieveDen * F)

/-- An upper bound on `max f(d)` over `d ∈ [n+1, n+m+1]`, where the primal attack with block size
`β` in dimension `d` succeeds when `f(d) ≥ 0`:
`f(d) = log δ (2β - d - 1) + (log σ + n log ξ + (d - n - 1) log q)/d - log σ - ½ log β`.
`f` is concave in `d`, with its maximum at `d* = √(-C/log δ)`. -/
def usvpFmaxHi (β n m : ℕ) (log2q log2se log2xi : Iv) : ℤ :=
  let x := log2Delta β
  let lhs := ivAdd log2se (ivDivNat (log2Nat β) 2)
  let A := ivSub (ivAdd (ivSmul (2 * (β : ℤ) - 1) x) log2q) lhs
  let C := ivSub (ivAdd log2se (ivSmul n log2xi)) (ivSmul ((n : ℤ) + 1) log2q)
  let a : ℤ := n + 1
  let b : ℤ := n + m + 1
  let f := fun (d : ℤ) => ivAdd (ivSub A (ivSmul d x)) (ivDivNat C d)
  if 0 ≤ C.1 then (f a).2
  else if C.2 < 0 then
    let absC : Iv := (-C.2, -C.1)
    let d2 := ivDiv absC x
    if d2.2 < a * a * F then (f a).2
    else if b * b * F < d2.1 then (f b).2
    else (ivSub A (ivSmul 2 (ivSqrt (ivMul absC x)))).2
  else max (f a).2 A.2

/-- The first block size in `[β, β + fuel)` with which the primal attack succeeds. -/
def firstBeta (n m : ℕ) (log2q log2se log2xi : Iv) : (fuel β : ℕ) → Option ℕ
  | 0, _ => none
  | fuel + 1, β =>
    if 0 ≤ usvpFmaxHi β n m log2q log2se log2xi then some β
    else firstBeta n m log2q log2se log2xi fuel (β + 1)

/-- A lower bound on the bits of lattice attacks, for an LWE instance of dimension `n` with `m`
samples, error standard deviation `2^log2se` and secret standard deviation `2^log2ss`. The target
`(s, e)` is rescaled so that both parts have the larger standard deviation: the secret part by
`ξ_s`, the error part by `ξ_e`, which multiplies the `q`-ary part of the volume (so it enters as
`log q + log ξ_e`). -/
def latticeLb (n m q : ℕ) (log2se log2ss : Iv) : ℤ :=
  let star : Iv := (max log2se.1 log2ss.1, max log2se.2 log2ss.2)
  let log2xi := ivMax0 (ivSub star log2ss)
  let log2q := ivAdd (log2Nat q) (ivMax0 (ivSub star log2se))
  let cap := min betaMax (n + m + 1)
  match firstBeta n m log2q star log2xi (cap - 1) 2 with
  | some β => sieveBitsLo β
  | none => sieveBitsLo cap

/-! ### Algebraic attacks -/

/-- `binom a b`, multiplicatively. -/
def binom (a b : ℕ) : ℕ :=
  if a < b then 0 else (List.range b).foldl (fun c i => c * (a - i) / (i + 1)) 1

/-- Monomials of degree `k` in `n` variables (`0` for `k < 0`). -/
def monomials (n : ℕ) (k : ℤ) : ℤ := if 0 ≤ k then binom (n - 1 + k.toNat) (n - 1) else 0

/-- Iteration bound of the loops of `gbLb`. -/
def fuelFor (n : ℕ) : ℕ := 8 * n + 256

/-- The choices for the secret's equations: degree (none: no equations) and penalty. -/
def gaussChoices (n : ℕ) (s : ℚ) : (fuel Bs : ℕ) → Option (List (Option ℕ × ℤ))
  | 0, _ => none
  | fuel + 1, Bs =>
    let pen := (n : ℤ) * ell Bs s
    if pen = 0 then some [(some (2 * Bs + 1), 0)]
    else ((some (2 * Bs + 1), pen) :: ·) <$> gaussChoices n s fuel (Bs + 1)

def secretChoices (n : ℕ) : Option SecretDist → Option (List (Option ℕ × ℤ))
  | some (.bounded B) => some [(some (2 * B + 1), 0)]
  | some (.gauss s) => gaussChoices n s (fuelFor n) 0
  | _ => some [(none, 0)]

/-- A lower bound (fixed point) on `log₂ (1 / Pr[|e| ≤ B])` for `e` from `dist`. -/
def ellDist (q B : ℕ) : SecretDist → ℤ
  | .gauss s => ell B s
  | .bounded Be =>
    if 2 * Be + 1 ≤ 2 * B + 1 then 0
    else max 0 ((log2Nat (2 * Be + 1)).1 - (log2Nat (2 * B + 1)).2)
  | .uniform =>
    if q ≤ 2 * B + 1 then 0 else max 0 ((log2Nat q).1 - (log2Nat (2 * B + 1)).2)

/-- Solving degrees `d = D + i, D + i + 1, …` for error equations of degree `D`. -/
def degreeLoop (n m D : ℕ) (Ds : Option ℕ) (pen lB : ℤ) : (fuel i : ℕ) → (best : ℤ) → Option ℤ
  | 0, _, _ => none
  | fuel + 1, i, best =>
    let d := D + i
    let bc := 2 * (log2Nat (binom (n + d) d)).1
    if best ≤ bc + pen then some best
    else
      let sec : ℤ := match Ds with
        | some Ds => n * monomials n ((d : ℤ) - Ds)
        | none => 0
      let num := monomials n d - sec
      let Mmin : ℤ := if num ≤ 0 then 0 else cdiv num (monomials n ((d : ℤ) - D))
      let best := if Mmin ≤ m then min best (bc + pen + Mmin * lB) else best
      degreeLoop n m D Ds pen lB fuel (i + 1) best

/-- Error ranges `[-B, B]` for `B = B₀, B₀ + 1, …`. -/
def rangeLoop (n m q : ℕ) (err : SecretDist) (choices : List (Option ℕ × ℤ)) :
    (fuel B : ℕ) → (best : ℤ) → Option ℤ
  | 0, _, _ => none
  | fuel + 1, B, best =>
    let D := 2 * B + 1
    if best ≤ 2 * (log2Nat (binom (n + D) D)).1 then some best
    else
      let lB := ellDist q B err
      match choices.foldlM (fun best c => degreeLoop n m D c.1 c.2 lB (fuelFor n) 0 best) best with
      | none => none
      | some best => rangeLoop n m q err choices fuel (B + 1) best

/-- A lower bound (fixed point) on Arora–Ge with Gröbner bases, or `best` if that is smaller.
Solving at degree `d` with `M` error equations of degree `D = 2B + 1` needs the ideal to contain
every monomial of degree `d`, so `M c(d-D) + n c(d-Ds) ≥ c(d)` (`c = monomials n`, `Ds` the degree
of the secret's equations). It costs at least `binom(n + d, d)^2` and succeeds only if the `M`
errors lie in `[-B, B]`. -/
def gbLb (n m q : ℕ) (err : SecretDist) (sec : Option SecretDist) (best : ℤ) : ℤ :=
  match secretChoices n sec with
  | none => 0
  | some choices => (rangeLoop n m q err choices (fuelFor n) 0 best).getD 0

/-! ### The security function -/

def isPow2 (x : ℕ) : Bool := 1 ≤ x && (x &&& (x - 1)) == 0

/-- One view of the LWE instance: `m` samples, secret law `sec`, error law `err` (dimension `n`,
modulus `q`); folds its bounds into `best`. -/
def viewLb (n q : ℕ) (best : ℤ) (view : ℕ × SecretDist × SecretDist) : ℤ :=
  let (m, sec, err) := view
  let best := min best (latticeLb n m q (secretLog2Sigma q err) (secretLog2Sigma q sec) * F)
  let best := min best (fdiv (n * secretMinEntropyLo q sec) 2)
  gbLb n m q err (if sec = .uniform then none else some sec) best

/-- **The security function.** Bits claimed for Module-LWE over `Z_q[X]/(X^N + 1)` of rank
`rank` with `m` samples, errors from `D_{Z,s}` and secret law `secret`. -/
def securityBits (N rank m q : ℕ) (s : ℚ) (secret : SecretDist) : ℕ :=
  if isPow2 N && 1 ≤ rank && 1 ≤ m && 2 ≤ q && decide (0 < s) && secret.valid then
    let n := N * rank
    let mm := N * m
    let err := SecretDist.gauss s
    -- the instance; its normal form (secret distributed like the errors, `n` samples fewer); with
    -- at least `n` samples, secret and errors swapped (`A⁻¹ b = s + A⁻¹ e`)
    let views : List (ℕ × SecretDist × SecretDist) :=
      [(mm, secret, err)] ++ (if n < mm then [(mm - n, err, err)] else []) ++
        (if n ≤ mm ∧ secret ≠ .uniform then [(n, err, secret)] else [])
    let best := views.foldl (viewLb n q) (bitsCap * F)
    let ring := (Nat.log2 N : ℤ) * F
    (fdiv (best - ring) F - safetyBits).toNat
  else 0

end Hardness

end SigabaNeo.Lattices
