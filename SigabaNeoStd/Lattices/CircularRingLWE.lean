import SigabaNeoStd.Lattices.RingLWE
import SigabaNeoStd.Lattices.Automorphism.Coeffs

/-!
# Circular Ring-LWE with automorphism keys

Assumption 1 of Suegami, *Implementing Predicate Encryption for Branching Programs* (ePrint
2026/2539, §3.2): over `R_q = Z_q[X]/(X^N + 1)`, for a secret `s̄ ← χ_s`, `a ← R_q^{1×m}` uniform,
and for each automorphism index `k ∈ J` a uniform `a_k ← R_q^{1×τ}`,

  `(a, s̄ a + e, (a_k, s̄ a_k − σ_k(s̄) g + e_k)_{k ∈ J}) ≈_c (a, u, (a_k, u_k)_{k ∈ J})`

with errors from `χ`, uniform `u`, `u_k`, the binary gadget `g = (1, 2, …, 2^{τ−1})` and
`σ_k : X ↦ X^k` (`SigabaNeo.Lattices.aut`, on coefficients `autCoeffs`). The key components are the
automorphism (rotation, Galois) keys of FHE schemes: key-switching keys from `σ_k(s̄)` to `s̄`,
encrypted under `s̄` itself, hence "circular".

## Concrete assumption (`SigabaNeo.Trusted.Assumption`)

* `CircularRingLWE.Params`: the underlying Ring-LWE parameters `base` (ring degree `N`, number
  `m` of plain samples, modulus `q`, error and secret laws), the list `J` of automorphism indices
  and the gadget length `τ`.
* The samples form one Ring-LWE-shaped pair with `rows = m + τ·|J|` rows (`Params.rows`): the `m`
  plain rows `(a_i, a_i s̄ + e_i)`, then for the `j`-th index `k = J[j]` and `i < τ` the row
  `(a_{k,i}, a_{k,i} s̄ − 2^i σ_k(s̄) + e_{k,i})`. They are encoded as Module-LWE pairs of rank `1`
  (`Cslib.Crypto.ModuleLWE.encodeSample`), exactly as `RingLWE.decision`.
* `CircularRingLWE.realLaw`: `s̄ ← secretLaw`, uniform `A`, errors `← errorLaw` (independent
  coefficients from the base laws), the pair `(A, A s̄ + e − keyShift s̄)`; `idealLaw`: uniform
  pairs.
* `CircularRingLWE.decision`, with the security function **`H p = RingLWE.H p.base`**: the
  circular assumption claims the strength of the underlying Ring-LWE problem (the cost model of
  the lattice estimator does not distinguish the key components; this is the standard
  assumption of FHE schemes publishing rotation keys).
* `decision_problem_nil`: at `J = []` the problem *is* decision Ring-LWE's (`RingLWE.decision`)
  at `base`, with the same security function (`decision_H`).

`HardAt CircularRingLWE.decision p k` says that every attacker (an explicit multi-tape Turing
machine) has `(steps + description length) / advantage² ≥ 2^k` at `p`. There is no asymptotic
form: the assumption is used only at concrete parameters.
-/

namespace SigabaNeo.Lattices

open Cslib Cslib.Probability

namespace CircularRingLWE

/-- Concrete parameters of circular Ring-LWE with automorphism keys. -/
structure Params where
  /-- The underlying Ring-LWE parameters: ring degree `N`, `m` plain samples, modulus `q`, error
  and secret laws. -/
  base : RingLWE.Params
  /-- The automorphism indices `k` of the keys (`σ_k : X ↦ X^k`). -/
  J : List ℕ
  /-- The gadget length: `g = (1, 2, …, 2^{τ−1})`. -/
  τ : ℕ

/-- The number of rows: `m` plain samples and `τ` per automorphism key. -/
def Params.rows (p : Params) : ℕ := p.base.m + p.τ * p.J.length

/-- All rows as one Module-LWE shape of rank `1` (same ring, modulus and laws as `base`). -/
def Params.toModule (p : Params) : ModuleLWE.Params :=
  { N := p.base.N, rank := 1, m := p.rows, q := p.base.q, error := p.base.error,
    secret := p.base.secret, q_pos := p.base.q_pos }

instance (p : Params) : NeZero p.base.q := ⟨p.base.q_pos.ne'⟩

/-- The shifts of the rows: `0` on the plain rows, the coefficients of `2^i σ_k(s̄)` on row `i` of
the key of the `j`-th index `k = J[j]`. -/
def keyShift (p : Params) (s : Fin p.base.N → ZMod p.base.q) :
    Fin p.rows → Fin p.base.N → ZMod p.base.q :=
  Fin.addCases (fun _ => 0) fun t =>
    let ij := finProdFinEquiv.symm t
    ((2 : ZMod p.base.q) ^ (ij.1 : ℕ)) • autCoeffs p.base.N (p.J.get ij.2) s

/-- The real samples `(A, A s̄ + e − keyShift s̄)`: plain rows `(a_i, a_i s̄ + e_i)` and key rows
`(a_{k,i}, a_{k,i} s̄ − 2^i σ_k(s̄) + e_{k,i})`. -/
noncomputable def sampleLaw (p : Params) : PMF (ModuleLWE.Pair p.toModule) := do
  let s : Fin 1 → Fin p.base.N → ZMod p.base.q ← ModuleLWE.secretLaw p.toModule
  let A ← PMF.uniformOfFintype (Matrix (Fin p.rows) (Fin 1) (Fin p.base.N → ZMod p.base.q))
  let e : Fin p.rows → Fin p.base.N → ZMod p.base.q ← ModuleLWE.errorLaw p.toModule
  return (A, Cslib.Crypto.ModuleLWE.sample A s e - keyShift p (s 0))

/-- The encoded real samples. -/
noncomputable def realLaw (p : Params) : PMF (List Bool) :=
  (sampleLaw p).map Cslib.Crypto.ModuleLWE.encodeSample

/-- The encoded uniform samples: every second component uniform. -/
noncomputable def idealLaw (p : Params) : PMF (List Bool) :=
  ModuleLWE.idealLaw p.toModule

/-- **The security function**: decision Ring-LWE's at the underlying parameters. -/
def H (p : Params) : ℕ := RingLWE.H p.base

/-- **Decision circular Ring-LWE with automorphism keys** (Assumption 1 of ePrint 2026/2539),
with `RingLWE.H p.base` bits. -/
noncomputable def decision : Assumption where
  Params := Params
  problem p := .decision (realLaw p) (idealLaw p)
  H := H

/-! ### No automorphism keys: decision Ring-LWE -/

theorem toModule_nil (b : RingLWE.Params) (τ : ℕ) :
    (⟨b, [], τ⟩ : Params).toModule = b.toModule := rfl

theorem keyShift_nil (b : RingLWE.Params) (τ : ℕ) (s : Fin b.N → ZMod b.q) :
    keyShift ⟨b, [], τ⟩ s = 0 := by
  funext r
  refine Fin.addCases (fun i => ?_) (fun t => t.elim0) r
  rw [keyShift, Fin.addCases_left]; rfl

theorem realLaw_nil (b : RingLWE.Params) (τ : ℕ) :
    realLaw ⟨b, [], τ⟩ = ModuleLWE.realLaw b.toModule := by
  unfold realLaw sampleLaw ModuleLWE.realLaw Cslib.Crypto.ModuleLWE.sampleLaw
  simp only [keyShift_nil, sub_zero]
  rfl

/-- **At `J = []` the problem is decision Ring-LWE's** at the underlying parameters. -/
theorem decision_problem_nil (b : RingLWE.Params) (τ : ℕ) :
    decision.problem ⟨b, [], τ⟩ = RingLWE.decision.problem b := by
  show Problem.decision (realLaw ⟨b, [], τ⟩) (idealLaw ⟨b, [], τ⟩) =
    Problem.decision (ModuleLWE.realLaw b.toModule) (ModuleLWE.idealLaw b.toModule)
  rw [realLaw_nil]; rfl

/-- The security function is decision Ring-LWE's at the underlying parameters, for every `J`. -/
theorem decision_H (p : Params) : decision.H p = RingLWE.decision.H p.base := rfl

/-- At `J = []`, a strength of decision Ring-LWE is one of circular Ring-LWE, and conversely. -/
theorem hardAt_nil_iff (b : RingLWE.Params) (τ k : ℕ) :
    decision.HardAt ⟨b, [], τ⟩ k ↔ RingLWE.decision.HardAt b k := by
  unfold Assumption.HardAt; rw [decision_problem_nil]

end CircularRingLWE

end SigabaNeo.Lattices
