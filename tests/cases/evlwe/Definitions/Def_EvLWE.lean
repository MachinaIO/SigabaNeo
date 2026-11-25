/-
TEST CASE (submission). Private-coin hiding evasive LWE ([BUW24], Definition 9; as recalled in
[DJMMV25], Definition 4.2) for the sampler of [DJMMV25], Construction 5.1, stated asymptotically
with cslib-frontier's definitions and the lattice library (`SigabaNeoStd.Lattices`).

## The distributions, at security parameter `κ`

* `B ← Z_q^{n×m}` uniform.
* `Samp`: `P ← Z_q^{n×k}` uniform, `S ← D_{Z,σ_LWE}^{ℓ×n}`, `T ← {0, …, ⌊q/2⌋}^{ℓ×k}` uniform,
  `aux = S·P − 2T`.
* `K`: each column `K_j` is drawn from the discrete Gaussian of width `τ` on the coset
  `{x ∈ Z^m : B·x = P_j (mod q)}` (the library's `Trapdoor.preimage`: cslib-frontier's
  `ZLattice.discreteGaussian` on the lattice `Λ^⊥(B)`, shifted by any integer preimage of
  `P_j`). No sampling algorithm is specified. If some column has no preimage, the experiment
  aborts and outputs the empty word (on both sides).
* `E ← D_{Z,σ}^{ℓ×m}`, `E' ← D_{Z,σ'}^{ℓ×k}`, `C, C'` uniform, `R ← {0, …, κ_R}^{n×k}` uniform.

* Pre1: `(S·B + E, S·P + E', aux)` against `(C, C', aux)`.
* Pre2: `(P, aux)` against `(P + R, aux)`.
* Post: `(S·B + E, K, aux)` against `(C, K, aux)`.

Every distinguisher receives `1^κ` and the encoded sample (cslib-frontier's
`ComputationallyIndistinguishable`: one Turing machine and one polynomial clock for every `κ`, and
negligible advantage). The assumption: if Pre1 and Pre2 are indistinguishable, so is Post. This is
implied by [BUW24]'s form (which asks for a reduction from Post distinguishers to Pre
distinguishers), so refuting it refutes [BUW24]'s form too.

## Parameters

`n = κ + 1`, `ℓ = 1`, `w = 8(κ + 1)`, `q` a prime in `(2^w, 2^{w+1}]` (Bertrand), `m = 2n(w + 1)`,
`k = m + 1`, widths `σ_LWE = 2^{κ+1}`, `σ' = 2^{2κ+2}`, `σ = 2^{4κ+4}`, `τ = 2^{κ+3}`, and
`κ_R = 2^{2κ+2}`: `q ≫ σ ≫ σ' ≫ σ_LWE` with superpolynomial gaps, as [DJMMV25] asks.

## Encoding

A sample is a list of `W = w + 2`-bit numbers, each low bit first: `q`, then the entries of the
sample's matrices in row-major order, each as its representative in `[0, q)` (integer matrices
are reduced mod `q`). The dimensions are functions of `κ`, so every entry's position is known.

Deviations to review: `ℓ = 1`; Gaussians have cslib-frontier's width convention
`ρ_s(x) = exp(−π‖x‖²/s²)`; the abort when a preimage does not exist.

[BUW24] Brzuska, Ünal, Woo, "Evasive LWE Assumptions: Definitions, Classes, and
Counterexamples", ePrint 2024/2000.
[DJMMV25] Döttling, Jain, Malavolta, Mathialagan, Vaikuntanathan, "Simple and General
Counterexamples for Private-Coin Evasive LWE", ePrint 2025/374.
-/
import CslibFrontier.Crypto.Computational.Basic
import SigabaNeoStd.Lattices.Gaussian
import SigabaNeoStd.Lattices.Encoding
import SigabaNeoStd.Lattices.Trapdoor
import Mathlib.NumberTheory.Bertrand

namespace TestCase.EvLWE

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM ProbabilityTheory SigabaNeo.Lattices
open scoped Matrix

/-! ### Parameters -/

def n (κ : ℕ) : ℕ := κ + 1
def ell (_κ : ℕ) : ℕ := 1
def w (κ : ℕ) : ℕ := 8 * (κ + 1)
def m (κ : ℕ) : ℕ := 2 * n κ * (w κ + 1)
def k (κ : ℕ) : ℕ := m κ + 1
/-- Bits per encoded number. -/
def W (κ : ℕ) : ℕ := w κ + 2

theorem exists_q (κ : ℕ) : ∃ p, p.Prime ∧ 2 ^ w κ < p ∧ p ≤ 2 * 2 ^ w κ :=
  Nat.exists_prime_lt_and_le_two_mul _ (by positivity)

/-- The modulus: a prime in `(2^w, 2^{w+1}]`. -/
noncomputable def q (κ : ℕ) : ℕ := (exists_q κ).choose

instance (κ : ℕ) : Fact (q κ).Prime := ⟨(exists_q κ).choose_spec.1⟩
instance (κ : ℕ) : NeZero (q κ) := ⟨(Fact.out : (q κ).Prime).ne_zero⟩

noncomputable def σLWE (κ : ℕ) : ℝ := 2 ^ (κ + 1)
noncomputable def σ' (κ : ℕ) : ℝ := 2 ^ (2 * κ + 2)
noncomputable def σ (κ : ℕ) : ℝ := 2 ^ (4 * κ + 4)
noncomputable def τ (κ : ℕ) : ℝ := 2 ^ (κ + 3)
def κR (κ : ℕ) : ℕ := 2 ^ (2 * κ + 2)

theorem σLWE_pos (κ : ℕ) : 0 < σLWE κ := by unfold σLWE; positivity
theorem σ'_pos (κ : ℕ) : 0 < σ' κ := by unfold σ'; positivity
theorem σ_pos (κ : ℕ) : 0 < σ κ := by unfold σ; positivity
theorem τ_pos (κ : ℕ) : 0 < τ κ := by unfold τ; positivity

/-! ### Encoding -/

/-- A sample: `q`, then the entries of the given matrices. -/
noncomputable def encSample (κ : ℕ) (entries : List ℕ) : List Bool :=
  encEntries (W κ) (q κ :: entries)

/-! ### The experiments -/

/-- What every experiment draws: `B`, `P`, `S`, `T`. -/
structure Draw (κ : ℕ) where
  B : Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ))
  P : Matrix (Fin (n κ)) (Fin (k κ)) (ZMod (q κ))
  S : Matrix (Fin (ell κ)) (Fin (n κ)) ℤ
  T : Matrix (Fin (ell κ)) (Fin (k κ)) (Fin ((q κ - 1) / 2 + 1))

noncomputable def draw (κ : ℕ) : PMF (Draw κ) := do
  let B ← PMF.uniformOfFintype (Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ)))
  let P ← PMF.uniformOfFintype (Matrix (Fin (n κ)) (Fin (k κ)) (ZMod (q κ)))
  let S ← sampleMat (gaussZ (σLWE κ) (σLWE_pos κ)) (ell κ) (n κ)
  let T ← PMF.uniformOfFintype (Matrix (Fin (ell κ)) (Fin (k κ)) (Fin ((q κ - 1) / 2 + 1)))
  pure ⟨B, P, S, T⟩

/-- `S` over `Z_q`. -/
noncomputable def Draw.Sq {κ : ℕ} (d : Draw κ) : Matrix (Fin (ell κ)) (Fin (n κ)) (ZMod (q κ)) :=
  d.S.map fun a => (a : ZMod (q κ))

/-- `aux = S·P − 2T`. -/
noncomputable def Draw.aux {κ : ℕ} (d : Draw κ) : Matrix (Fin (ell κ)) (Fin (k κ)) (ZMod (q κ)) :=
  d.Sq * d.P - (2 : ZMod (q κ)) • d.T.map fun t => ((t : ℕ) : ZMod (q κ))

/-- The preimage `K`, column by column (`SigabaNeo.Lattices.Trapdoor.preimage`): the coset
Gaussian of width `τ` for each column of `P`, if every column has a preimage. -/
noncomputable def preimage {κ : ℕ} (d : Draw κ) : PMF (Option (Matrix (Fin (m κ)) (Fin (k κ)) ℤ)) :=
  Trapdoor.preimage d.B d.P (τ κ) (τ_pos κ)

noncomputable def pre1Real (κ : ℕ) : PMF (List Bool) := do
  let d ← draw κ
  let E ← sampleMat (gaussZ (σ κ) (σ_pos κ)) (ell κ) (m κ)
  let E' ← sampleMat (gaussZ (σ' κ) (σ'_pos κ)) (ell κ) (k κ)
  pure (encSample κ (matVals (d.Sq * d.B + intMod (q κ) E) ++
    matVals (d.Sq * d.P + intMod (q κ) E') ++ matVals d.aux))

noncomputable def pre1Random (κ : ℕ) : PMF (List Bool) := do
  let d ← draw κ
  let C ← PMF.uniformOfFintype (Matrix (Fin (ell κ)) (Fin (m κ)) (ZMod (q κ)))
  let C' ← PMF.uniformOfFintype (Matrix (Fin (ell κ)) (Fin (k κ)) (ZMod (q κ)))
  pure (encSample κ (matVals C ++ matVals C' ++ matVals d.aux))

noncomputable def pre2Real (κ : ℕ) : PMF (List Bool) := do
  let d ← draw κ
  pure (encSample κ (matVals d.P ++ matVals d.aux))

noncomputable def pre2Random (κ : ℕ) : PMF (List Bool) := do
  let d ← draw κ
  let R ← PMF.uniformOfFintype (Matrix (Fin (n κ)) (Fin (k κ)) (Fin (κR κ + 1)))
  pure (encSample κ (matVals (d.P + R.map fun r => ((r : ℕ) : ZMod (q κ))) ++ matVals d.aux))

noncomputable def postReal (κ : ℕ) : PMF (List Bool) := do
  let d ← draw κ
  let K? ← preimage d
  let E ← sampleMat (gaussZ (σ κ) (σ_pos κ)) (ell κ) (m κ)
  pure (match K? with
    | none => []
    | some K => encSample κ (matVals (d.Sq * d.B + intMod (q κ) E) ++
        matVals (intMod (q κ) K) ++ matVals d.aux))

noncomputable def postRandom (κ : ℕ) : PMF (List Bool) := do
  let d ← draw κ
  let K? ← preimage d
  let C ← PMF.uniformOfFintype (Matrix (Fin (ell κ)) (Fin (m κ)) (ZMod (q κ)))
  pure (match K? with
    | none => []
    | some K => encSample κ (matVals C ++ matVals (intMod (q κ) K) ++ matVals d.aux))

/-- Private-coin hiding evasive LWE for the sampler of [DJMMV25], Construction 5.1. -/
def target : Prop :=
  ComputationallyIndistinguishable pre1Real pre1Random →
  ComputationallyIndistinguishable pre2Real pre2Random →
  ComputationallyIndistinguishable postReal postRandom

end TestCase.EvLWE
