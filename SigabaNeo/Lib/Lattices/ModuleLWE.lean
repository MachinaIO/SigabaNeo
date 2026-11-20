import SigabaNeo.Lib.Lattices.Gaussian
import CslibFrontier.Crypto.Computational.LWE.Module

/-!
# Module-LWE

Module-LWE over `R_q = Z_q[X]/(X^n + 1)` with an `m × d` module matrix, as in cslib-frontier
(`Cslib.Crypto.DecisionModuleLWEWith`): the real sample is `(A, A·s + e)` for a uniform `A`, a
secret `s ← secret κ` and an error `e ← error κ`; the random sample is a uniform pair; every
distinguisher is a uniform strict PPT machine on cslib-frontier's encoding of the pair, and must
have negligible advantage.

* `ModuleLWE.gaussVec d n q s`: `d` ring elements whose `n` coefficients are independent draws from
  `D_{Z,s}` (`gaussZ`), reduced mod `q`.
* `ModuleLWE.Decision m d n q secret error`: the decision assumption for the given laws.
* `ModuleLWE.DecisionGauss m d n q σ`: a uniform secret and Gaussian errors of width `σ κ`.
* `ModuleLWE.DecisionGaussSecret m d n q σ`: the normal form, secret and errors Gaussian.

`LWE` (ring degree `1`) and `RingLWE` (rank `1`) are the special cases
(`SigabaNeo.Lib.Lattices.LWE`, `SigabaNeo.Lib.Lattices.RingLWE`).
-/

namespace SigabaNeo.Lattices

open Cslib Cslib.Crypto Cslib.Probability

namespace ModuleLWE

/-- `d` ring elements with coefficients drawn independently from `D_{Z,s}`, reduced mod `q`. -/
noncomputable def gaussVec (d n q : ℕ) (s : ℝ) (hs : 0 < s) : PMF (Fin d → Fin n → ZMod q) :=
  (sampleMat (gaussZ s hs) d n).map fun M i j => (M i j : ZMod q)

/-- Decision Module-LWE for a secret law and an error law (cslib-frontier's encoding). -/
def Decision (m d n q : ℕ → ℕ) [∀ κ, NeZero (q κ)]
    (secret : (κ : ℕ) → PMF (Fin (d κ) → Fin (n κ) → ZMod (q κ)))
    (error : (κ : ℕ) → PMF (Fin (m κ) → Fin (n κ) → ZMod (q κ))) : Prop :=
  DecisionModuleLWEWith m d n q secret error

/-- Decision Module-LWE with a uniform secret and errors from `D_{Z,σ}`. -/
def DecisionGauss (m d n q : ℕ → ℕ) [∀ κ, NeZero (q κ)] (σ : ℕ → ℝ) (hσ : ∀ κ, 0 < σ κ) :
    Prop :=
  Decision m d n q (fun κ => PMF.uniformOfFintype _) fun κ => gaussVec (m κ) (n κ) (q κ) (σ κ) (hσ κ)

/-- Decision Module-LWE in normal form: secret and errors from `D_{Z,σ}`. -/
def DecisionGaussSecret (m d n q : ℕ → ℕ) [∀ κ, NeZero (q κ)] (σ : ℕ → ℝ)
    (hσ : ∀ κ, 0 < σ κ) : Prop :=
  Decision m d n q (fun κ => gaussVec (d κ) (n κ) (q κ) (σ κ) (hσ κ))
    fun κ => gaussVec (m κ) (n κ) (q κ) (σ κ) (hσ κ)

end ModuleLWE

end SigabaNeo.Lattices
