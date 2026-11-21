import SigabaNeo.Lib.Lattices.ModuleLWE
import SigabaNeo.Lib.Lattices.Encoding

/-!
# LWE

LWE with `m` samples, secret dimension `n` and modulus `q`: Module-LWE at ring degree `1`
(`Z_q[X]/(X + 1) = Z_q`). A pair is `(A, b)` with `A ∈ Z_q^{m×n}` and `b = A·s + e`, each entry a
degree-`1` polynomial (`Fin 1 → Z_q`), as cslib-frontier stores it.

## Concrete assumptions (`SigabaNeo.Trusted.Assumption`)

* `LWE.Params`: `n`, `m`, `q`, the error law and the secret law.
* `LWE.decision`, `LWE.search`: the Module-LWE assumptions at ring degree `1`
  (`LWE.Params.toModule`), with the same security function `LWE.H` (no ring penalty).

## Asymptotic form (cslib-frontier)

* `LWE.gaussVec n q s`: `n` entries from `D_{Z,s}`, reduced mod `q`.
* `LWE.Decision m n q secret error`: the decision assumption on cslib-frontier's encoding, which
  does not include `q`; a distinguisher must compute `q κ` itself.
* `LWE.DecisionGauss m n q σ`: a uniform secret and Gaussian errors; `LWE.DecisionGaussSecret`: the
  normal form.
* `LWE.encodePub W q` and `LWE.DecisionPub m n q W secret error`: LWE with a public modulus. The
  sample is `W`-bit numbers, low bit first: `q`, then `Aᵀ ∈ Z_q^{n×m}` row-major (the samples are
  the columns, as in `bᵀ = sᵀAᵀ + eᵀ`), then `b`. This is the usual statement when `q κ` is a
  parameter no machine is known to compute (for example a prime chosen by Bertrand's postulate).
  From this encoding a machine can drop `q`, so `DecisionPub` implies `Decision` for the same laws.
-/

namespace SigabaNeo.Lattices

open Cslib Cslib.Crypto Cslib.Probability

namespace LWE

/-- Concrete LWE parameters. -/
structure Params where
  /-- Secret dimension. -/
  n : ℕ
  /-- Number of samples. -/
  m : ℕ
  /-- Modulus. -/
  q : ℕ
  /-- Law of the error's coefficients. -/
  error : SecretDist
  /-- Law of the secret's entries. -/
  secret : SecretDist
  /-- The modulus is positive. -/
  q_pos : 0 < q := by decide

/-- LWE as Module-LWE at ring degree `1`. -/
def Params.toModule (p : Params) : ModuleLWE.Params :=
  { N := 1, rank := p.n, m := p.m, q := p.q, error := p.error, secret := p.secret, q_pos := p.q_pos }

/-- The security function: Module-LWE's at ring degree `1`. -/
def H (p : Params) : ℕ := ModuleLWE.H p.toModule

/-- **Decision LWE**, with `H p` bits. -/
noncomputable def decision : Assumption where
  Params := Params
  problem p := ModuleLWE.decision.problem p.toModule
  H := H

/-- **Search LWE**, with `H p` bits. -/
noncomputable def search : Assumption where
  Params := Params
  problem p := ModuleLWE.search.problem p.toModule
  H := H

/-- An LWE pair `(A, b)`, `A ∈ Z_q^{m×n}`, at ring degree `1`. -/
abbrev Pair (m n q : ℕ) : Type :=
  Matrix (Fin m) (Fin n) (Fin 1 → ZMod q) × (Fin m → Fin 1 → ZMod q)

/-- `n` entries from `D_{Z,s}`, reduced mod `q`. -/
noncomputable def gaussVec (n q : ℕ) (s : ℝ) (hs : 0 < s) : PMF (Fin n → Fin 1 → ZMod q) :=
  ModuleLWE.gaussVec n 1 q s hs

/-- The real pairs: uniform `A`, `b = A·s + e`. -/
noncomputable def realLaw {m n q : ℕ} [NeZero q] (secret : PMF (Fin n → Fin 1 → ZMod q))
    (error : PMF (Fin m → Fin 1 → ZMod q)) : PMF (Pair m n q) :=
  ModuleLWE.sampleLaw secret error

/-- Decision LWE for a secret law and an error law (cslib-frontier's encoding). -/
def Decision (m n q : ℕ → ℕ) [∀ κ, NeZero (q κ)]
    (secret : (κ : ℕ) → PMF (Fin (n κ) → Fin 1 → ZMod (q κ)))
    (error : (κ : ℕ) → PMF (Fin (m κ) → Fin 1 → ZMod (q κ))) : Prop :=
  ModuleLWE.Decision m n (fun _ => 1) q secret error

/-- Decision LWE with a uniform secret and errors from `D_{Z,σ}`. -/
def DecisionGauss (m n q : ℕ → ℕ) [∀ κ, NeZero (q κ)] (σ : ℕ → ℝ) (hσ : ∀ κ, 0 < σ κ) : Prop :=
  ModuleLWE.DecisionGauss m n (fun _ => 1) q σ hσ

/-- Decision LWE in normal form. -/
def DecisionGaussSecret (m n q : ℕ → ℕ) [∀ κ, NeZero (q κ)] (σ : ℕ → ℝ) (hσ : ∀ κ, 0 < σ κ) :
    Prop :=
  ModuleLWE.DecisionGaussSecret m n (fun _ => 1) q σ hσ

/-- The public-modulus encoding: `q`, then `Aᵀ` row-major, then `b`, `W` bits each. -/
def encodePub {m n : ℕ} (W q : ℕ) (pair : Pair m n q) : List Bool :=
  encEntries W (q :: (matVals (Matrix.of fun (i : Fin n) (j : Fin m) => pair.1 j i 0) ++
    matVals (Matrix.of fun (_ : Fin 1) (j : Fin m) => pair.2 j 0)))

/-- Decision LWE with a public modulus: the real and uniform pairs, encoded with `encodePub`, are
computationally indistinguishable. -/
def DecisionPub (m n q W : ℕ → ℕ) [∀ κ, NeZero (q κ)]
    (secret : (κ : ℕ) → PMF (Fin (n κ) → Fin 1 → ZMod (q κ)))
    (error : (κ : ℕ) → PMF (Fin (m κ) → Fin 1 → ZMod (q κ))) : Prop :=
  ComputationallyIndistinguishable
    (fun κ => (realLaw (secret κ) (error κ)).map (encodePub (W κ) (q κ)))
    (fun κ => (PMF.uniformOfFintype (Pair (m κ) (n κ) (q κ))).map (encodePub (W κ) (q κ)))

end LWE

end SigabaNeo.Lattices
