import SigabaNeo.Lib.Lattices.ModuleLWE

/-!
# Ring-LWE

Ring-LWE over `R_q = Z_q[X]/(X^n + 1)` with `m` samples: Module-LWE of rank `1`. The real sample is
`(a_i, a_i·s + e_i)_{i<m}` for uniform `a_i ∈ R_q`.

* `RingLWE.Decision m n q secret error`: the decision assumption for the given laws.
* `RingLWE.DecisionGauss m n q σ`: a uniform secret and Gaussian errors.
* `RingLWE.DecisionGaussSecret m n q σ`: the normal form, secret and errors Gaussian.
-/

namespace SigabaNeo.Lattices

namespace RingLWE

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
