import SigabaNeo.Lib.Lattices.ModuleLWE

/-!
# Ring-LWE

Ring-LWE over `R_q = Z_q[X]/(X^N + 1)` with `m` samples: Module-LWE of rank `1`. The real sample
is `(a_i, a_i·s + e_i)_{i<m}` for uniform `a_i ∈ R_q`.

## Concrete assumptions (`SigabaNeo.Assumption`)

* `RingLWE.Params`: `N` (a power of two, or the claim is `0`), `m`, `q`, the error width `s` and
  the secret law.
* `RingLWE.decision`, `RingLWE.search`: the Module-LWE assumptions at rank `1`
  (`RingLWE.Params.toModule`), with the same security function `RingLWE.H`.

## Asymptotic form (cslib-frontier)

* `RingLWE.Decision m n q secret error`: the decision assumption for the given laws.
* `RingLWE.DecisionGauss m n q σ`: a uniform secret and Gaussian errors.
* `RingLWE.DecisionGaussSecret m n q σ`: the normal form, secret and errors Gaussian.
-/

namespace SigabaNeo.Lattices

namespace RingLWE

/-- Concrete Ring-LWE parameters. -/
structure Params where
  /-- Ring degree: `R = Z[X]/(X^N + 1)`. -/
  N : ℕ
  /-- Number of samples. -/
  m : ℕ
  /-- Modulus. -/
  q : ℕ
  /-- Width of the error law `D_{Z,s}`. -/
  s : ℚ
  /-- Law of the secret's coefficients. -/
  secret : SecretDist
  /-- The modulus is positive. -/
  q_pos : 0 < q := by decide

/-- Ring-LWE as Module-LWE of rank `1`. -/
def Params.toModule (p : Params) : ModuleLWE.Params :=
  { N := p.N, rank := 1, m := p.m, q := p.q, s := p.s, secret := p.secret, q_pos := p.q_pos }

/-- The security function: Module-LWE's at rank `1`. -/
def H (p : Params) : ℕ := ModuleLWE.H p.toModule

/-- **Decision Ring-LWE**, with `H p` bits. -/
noncomputable def decision : Assumption where
  Params := Params
  problem p := ModuleLWE.decision.problem p.toModule
  H := H

/-- **Search Ring-LWE**, with `H p` bits. -/
noncomputable def search : Assumption where
  Params := Params
  problem p := ModuleLWE.search.problem p.toModule
  H := H

/-- Decision Ring-LWE for a secret law and an error law. -/
def Decision (m n q : ℕ → ℕ) [∀ κ, NeZero (q κ)]
    (secret : (κ : ℕ) → PMF (Fin 1 → Fin (n κ) → ZMod (q κ)))
    (error : (κ : ℕ) → PMF (Fin (m κ) → Fin (n κ) → ZMod (q κ))) : Prop :=
  ModuleLWE.Decision m (fun _ => 1) n q secret error

/-- Decision Ring-LWE with a uniform secret and errors from `D_{Z,σ}`. -/
def DecisionGauss (m n q : ℕ → ℕ) [∀ κ, NeZero (q κ)] (σ : ℕ → ℝ) (hσ : ∀ κ, 0 < σ κ) : Prop :=
  ModuleLWE.DecisionGauss m (fun _ => 1) n q σ hσ

/-- Decision Ring-LWE in normal form. -/
def DecisionGaussSecret (m n q : ℕ → ℕ) [∀ κ, NeZero (q κ)] (σ : ℕ → ℝ) (hσ : ∀ κ, 0 < σ κ) :
    Prop :=
  ModuleLWE.DecisionGaussSecret m (fun _ => 1) n q σ hσ

end RingLWE

end SigabaNeo.Lattices
