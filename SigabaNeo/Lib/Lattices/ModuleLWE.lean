import SigabaNeo.Lib.Lattices.Gaussian
import SigabaNeo.Lib.Lattices.Hardness
import SigabaNeo.Lib.Assumption
import CslibFrontier.Crypto.Computational.LWE.Module

/-!
# Module-LWE

Module-LWE over `R_q = Z_q[X]/(X^N + 1)` with an `m × rank` module matrix. The real sample is
`(A, A·s + e)` for a uniform `A`, a secret `s` and an error `e`; the random sample is a uniform
pair. Pairs are encoded with cslib-frontier's `ModuleLWE.encodeSample`.

## Concrete assumptions (`SigabaNeo.Assumption`)

* `ModuleLWE.Params`: the ring degree `N`, the rank, the number of samples `m`, the modulus `q`,
  the error width `s` (errors from `D_{Z,s}`, `ρ_s(x) = exp(-π x²/s²)`, reduced mod `q`) and the
  secret law (`SecretDist`: uniform, `D_{Z,s'}`, or uniform on `{-B, …, B}`). The parameters are
  fixed, so an attacker may depend on them.
* `ModuleLWE.decision`: distinguish the real pair from a uniform pair.
* `ModuleLWE.search`: find the secret from the real pair.
* Both claim `ModuleLWE.H p = Hardness.securityBits …` bits (`SigabaNeo.Lib.Lattices.Hardness`,
  `docs/LWE_HARDNESS.md`): a conservative lower bound on every known classical attack.

`HardAt ModuleLWE.decision p k` says that every attacker (an explicit multi-tape Turing machine)
has `(steps + description length) / advantage² ≥ 2^k` at `p`.

## Asymptotic form (cslib-frontier)

* `ModuleLWE.gaussVec d n q s`: `d` ring elements whose `n` coefficients are independent draws from
  `D_{Z,s}` (`gaussZ`), reduced mod `q`.
* `ModuleLWE.Decision m d n q secret error`: cslib-frontier's `DecisionModuleLWEWith`: every uniform
  strict PPT distinguisher has negligible advantage.
* `ModuleLWE.DecisionGauss`, `ModuleLWE.DecisionGaussSecret`: a uniform secret, or the normal form.

`LWE` (ring degree `1`) and `RingLWE` (rank `1`) are the special cases
(`SigabaNeo.Lib.Lattices.LWE`, `SigabaNeo.Lib.Lattices.RingLWE`).
-/

namespace SigabaNeo.Lattices

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

namespace ModuleLWE

/-- `d` ring elements with coefficients drawn independently from `D_{Z,s}`, reduced mod `q`. -/
noncomputable def gaussVec (d n q : ℕ) (s : ℝ) (hs : 0 < s) : PMF (Fin d → Fin n → ZMod q) :=
  (sampleMat (gaussZ s hs) d n).map fun M i j => (M i j : ZMod q)

/-! ### Concrete parameters and assumptions -/

/-- Concrete Module-LWE parameters. -/
structure Params where
  /-- Ring degree: `R = Z[X]/(X^N + 1)`. -/
  N : ℕ
  /-- Module rank (secret length). -/
  rank : ℕ
  /-- Number of samples (rows of `A`). -/
  m : ℕ
  /-- Modulus. -/
  q : ℕ
  /-- Width of the error law `D_{Z,s}`. -/
  s : ℚ
  /-- Law of the secret's coefficients. -/
  secret : SecretDist
  /-- The modulus is positive. -/
  q_pos : 0 < q := by decide

instance (p : Params) : NeZero p.q := ⟨p.q_pos.ne'⟩

/-- The law of one coefficient. A non-positive width gives `0` (and the claim `0`). -/
noncomputable def coeffLaw (q : ℕ) [NeZero q] : SecretDist → PMF (ZMod q)
  | .uniform => PMF.uniformOfFintype _
  | .gauss s => if h : 0 < s then (gaussZ s (by exact_mod_cast h)).map fun z => (z : ZMod q)
      else PMF.pure 0
  | .bounded B => (PMF.uniformOfFintype (Fin (2 * B + 1))).map fun i => ((i : ℤ) - B : ZMod q)

/-- The secret law: `rank` ring elements with independent coefficients. -/
noncomputable def secretLaw (p : Params) : PMF (Fin p.rank → Fin p.N → ZMod p.q) :=
  sampleMat (coeffLaw p.q p.secret) p.rank p.N

/-- The error law: `m` ring elements with coefficients from `D_{Z,s}`. -/
noncomputable def errorLaw (p : Params) : PMF (Fin p.m → Fin p.N → ZMod p.q) :=
  if h : 0 < p.s then gaussVec p.m p.N p.q p.s (by exact_mod_cast h) else PMF.pure 0

/-- A Module-LWE pair `(A, b)`. -/
abbrev Pair (p : Params) : Type :=
  Matrix (Fin p.m) (Fin p.rank) (Fin p.N → ZMod p.q) × (Fin p.m → Fin p.N → ZMod p.q)

/-- The encoded real pairs `(A, A·s + e)`. -/
noncomputable def realLaw (p : Params) : PMF (List Bool) :=
  (Cslib.Crypto.ModuleLWE.sampleLaw (secretLaw p) (errorLaw p)).map
    Cslib.Crypto.ModuleLWE.encodeSample

/-- The encoded uniform pairs. -/
noncomputable def idealLaw (p : Params) : PMF (List Bool) :=
  (PMF.uniformOfFintype (Pair p)).map Cslib.Crypto.ModuleLWE.encodeSample

/-- The encoding of a secret: its coefficients as natural numbers. -/
def encodeSecret {d n q : ℕ} (s : Fin d → Fin n → ZMod q) : List Bool :=
  encList encNat (List.ofFn fun c : Fin (d * n) => (flattenPolyVec s c).val)

/-- The search instances: an encoded real pair and the encoding of its secret. -/
noncomputable def searchLaw (p : Params) : PMF (List Bool × Set (List Bool)) := do
  let secret ← secretLaw p
  let A ← PMF.uniformOfFintype (Matrix (Fin p.m) (Fin p.rank) (Fin p.N → ZMod p.q))
  let error ← errorLaw p
  return (Cslib.Crypto.ModuleLWE.encodeSample (A, Cslib.Crypto.ModuleLWE.sample A secret error),
    {encodeSecret secret})

/-- The security function (`Hardness.securityBits`). -/
def H (p : Params) : ℕ := Hardness.securityBits p.N p.rank p.m p.q p.s p.secret

/-- **Decision Module-LWE**: distinguish real pairs from uniform pairs, with `H p` bits. -/
noncomputable def decision : Assumption where
  Params := Params
  problem p := .decision (realLaw p) (idealLaw p)
  H := H

/-- **Search Module-LWE**: find the secret of a real pair, with `H p` bits. -/
noncomputable def search : Assumption where
  Params := Params
  problem p := .search (searchLaw p)
  H := H

/-! ### Asymptotic form -/

/-- Decision Module-LWE for a secret law and an error law (cslib-frontier's encoding). -/
def Decision (m d n q : ℕ → ℕ) [∀ κ, NeZero (q κ)]
    (secret : (κ : ℕ) → PMF (Fin (d κ) → Fin (n κ) → ZMod (q κ)))
    (error : (κ : ℕ) → PMF (Fin (m κ) → Fin (n κ) → ZMod (q κ))) : Prop :=
  DecisionModuleLWEWith m d n q secret error

/-- Decision Module-LWE with a uniform secret and errors from `D_{Z,σ}`. -/
def DecisionGauss (m d n q : ℕ → ℕ) [∀ κ, NeZero (q κ)] (σ : ℕ → ℝ) (hσ : ∀ κ, 0 < σ κ) :
    Prop :=
  Decision m d n q (fun _ => PMF.uniformOfFintype _) fun κ => gaussVec (m κ) (n κ) (q κ) (σ κ) (hσ κ)

/-- Decision Module-LWE in normal form: secret and errors from `D_{Z,σ}`. -/
def DecisionGaussSecret (m d n q : ℕ → ℕ) [∀ κ, NeZero (q κ)] (σ : ℕ → ℝ)
    (hσ : ∀ κ, 0 < σ κ) : Prop :=
  Decision m d n q (fun κ => gaussVec (d κ) (n κ) (q κ) (σ κ) (hσ κ))
    fun κ => gaussVec (m κ) (n κ) (q κ) (σ κ) (hσ κ)

end ModuleLWE

end SigabaNeo.Lattices
