import SigabaNeoStd.Lattices.Estimator.ND

/-!
# LWE parameters of the lattice estimator

`estimator/lwe_parameters.py`; `python/lwemodel/params.py` is the mirror.
-/

namespace SigabaNeo.Lattices.Estimator

/-- An LWE instance: dimension `n`, modulus `q`, secret and error distributions, `m` samples
(`none`: unlimited). -/
structure LWEParams where
  n : ℕ
  q : ℕ
  Xs : ND
  Xe : ND
  m : Option ℕ := none
  deriving DecidableEq, Repr

namespace LWEParams

/-- The estimator resizes `Xs` to `n` and `Xe` to `m`. -/
def mk' (n q : ℕ) (Xs Xe : ND) (m : Option ℕ) : LWEParams :=
  { n, q, Xs := Xs.resize n, Xe := match m with | some m => Xe.resize m | none => Xe, m }

def mGe (p : LWEParams) (k : ℕ) : Bool :=
  match p.m with
  | none => true
  | some m => decide (k ≤ m)

/-- The normal form (`LWEParameters.normalize`). -/
def normalize (p : LWEParams) : LWEParams :=
  if p.Xe.stddev < p.Xs.stddev ∧ p.mGe (2 * p.n) then
    mk' p.n p.q p.Xe p.Xe (p.m.map (· - p.n))
  else if p.Xe.stddev < p.Xs.stddev ∧ p.m = some p.n then
    mk' p.n p.q p.Xe p.Xs (some p.n)
  else p

end LWEParams

end SigabaNeo.Lattices.Estimator
