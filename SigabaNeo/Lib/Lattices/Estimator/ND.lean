import SigabaNeo.Lib.Lattices.Estimator.Fx

/-!
# Noise distributions of the lattice estimator

The subset of `estimator/nd.py` used by the models; `python/lwemodel/nd.py` is the mirror.
-/

namespace SigabaNeo.Lattices.Estimator

/-- The kind of a distribution. -/
inductive NDKind where
  /-- Discrete Gaussian with the given standard deviation (fixed point). -/
  | gauss (stddev : Fx)
  /-- Centered binomial with parameter `η`. -/
  | cbd (eta : ℕ)
  /-- Uniform on `[a, b] ∩ Z`. -/
  | uniform (a b : ℤ)
  deriving DecidableEq, Repr

/-- A distribution of `n` coefficients (`n = none`: unspecified). -/
structure ND where
  kind : NDKind
  n : Option ℕ := none
  deriving DecidableEq, Repr

namespace ND

def stddev (X : ND) : Fx :=
  match X.kind with
  | .gauss s => s
  | .cbd e => Fx.sqrt (Fx.ofRat e 2)
  | .uniform a b => let m := b - a + 1; Fx.sqrt (Fx.ofRat (m * m - 1) 12)

def mean (X : ND) : Fx :=
  match X.kind with
  | .uniform a b => Fx.ofRat (a + b) 2
  | _ => 0

/-- Bounds `(lo, hi)`, or `none` if unbounded. -/
def bounds (X : ND) : Option (ℤ × ℤ) :=
  match X.kind, X.n with
  | .gauss _, none => none
  | .gauss s, some n => let b := Fx.ceil (Fx.mul (Fx.log2 (Fx.ofInt n)) s); some (-b, b)
  | .cbd e, _ => some (-(e : ℤ), e)
  | .uniform a b, _ => some (a, b)

def density (X : ND) : Fx :=
  match X.kind with
  | .gauss s => max 0 (Fx.ONE - Fx.div Fx.ONE (Fx.mul Fx.SQRT2PI s))
  | .cbd e => Fx.ONE - Fx.ofRat ((2 * e).choose e) (4 ^ e)
  | .uniform a b => let m := b - a + 1; if a ≤ 0 ∧ 0 ≤ b then Fx.ONE - Fx.ofRat 1 m else Fx.ONE

def isBounded (X : ND) : Bool := X.bounds.isSome
def isSparse (X : ND) : Bool := decide (X.density < Fx.ONE / 2)
def isGaussianLike (X : ND) : Bool :=
  match X.kind with
  | .gauss _ | .cbd _ => true
  | _ => false

def resize (X : ND) (n : ℕ) : ND := { X with n := some n }

/-- `round(n · density)`. -/
def hammingWeight (X : ND) : ℤ := Int.fdiv (2 * (X.n.getD 0 : ℤ) * X.density + Fx.ONE) (2 * Fx.ONE)

def gauss (stddev : Fx) : ND := ⟨.gauss stddev, none⟩
def cbd (eta : ℕ) : ND := ⟨.cbd eta, none⟩
def uniform (a b : ℤ) : ND := ⟨.uniform a b, none⟩
def uniformMod (q : ℕ) : ND := let a := -((q : ℤ) / 2); ⟨.uniform a (a + q - 1), none⟩

end ND

end SigabaNeo.Lattices.Estimator
