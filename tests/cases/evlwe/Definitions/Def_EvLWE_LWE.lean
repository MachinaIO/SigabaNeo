/-
TEST CASE (submission). The LWE assumption that the evasive LWE case is refuted under: decision
LWE with a public modulus, stated with the lattice library (`SigabaNeo.Lattices.LWE.DecisionPub`).

At security parameter `κ`, with the parameters of `TestCase.EvLWE` (`n = κ + 1` secret entries,
`k = m + 1` samples, the prime `q ∈ (2^w, 2^{w+1}]`):

* the real sample is cslib-frontier's `ModuleLWE.sampleLaw` at ring degree 1 (`Z_q[X]/(X + 1)`
  is `Z_q`): a uniform `A ∈ Z_q^{k×n}`, `b = A·s + e`, with the secret `s` and the error `e` drawn
  entrywise from `D_{Z,σ_LWE}` and reduced mod `q`;
* the random sample is a uniform pair `(A, b)`;
* every distinguisher receives `1^κ` and the encoded sample (cslib-frontier's
  `ComputationallyIndistinguishable`).

## Encoding

`LWE.encodePub (W κ) (q κ)`, the format of `TestCase.EvLWE`: `W`-bit numbers, low bit first:
`q`, then `Aᵀ ∈ Z_q^{n×k}` row-major (the samples are the columns, as in `bᵀ = sᵀ·Aᵀ + eᵀ`), then
`b`.

## Relation to cslib-frontier's `DecisionModuleLWEWith`

The laws are those of `DecisionModuleLWEWith k n (fun _ => 1) q lweSecret lweError`; only the
encoding differs. cslib-frontier's `ModuleLWE.encodeSample` lists the residues without `q`, so a
distinguisher has to compute `q κ` itself; here `q` is part of the sample, as in the usual
statement of LWE where the modulus is a public parameter. The two encodings are computable from
each other given `q`, and from this one a machine can drop `q`, so this assumption implies
`DecisionModuleLWEWith` for these laws (and is equivalent to it for any `q` computable in
polynomial time from `κ`). It is needed because `q κ` is a prime chosen by Bertrand's postulate,
which no machine is proved to compute.
-/
import Definitions.Def_EvLWE
import SigabaNeo.Lib.Lattices.LWE

namespace TestCase.EvLWE

open Cslib Cslib.Crypto Cslib.Probability SigabaNeo.Lattices

/-- The secret law: `n` entries from `D_{Z,σ_LWE}`, reduced mod `q`, as degree-1 polynomials. -/
noncomputable def lweSecret (κ : ℕ) : PMF (Fin (n κ) → Fin 1 → ZMod (q κ)) :=
  LWE.gaussVec (n κ) (q κ) (σLWE κ) (σLWE_pos κ)

/-- The error law: `k` entries from `D_{Z,σ_LWE}`, reduced mod `q`, as degree-1 polynomials. -/
noncomputable def lweError (κ : ℕ) : PMF (Fin (k κ) → Fin 1 → ZMod (q κ)) :=
  LWE.gaussVec (k κ) (q κ) (σLWE κ) (σLWE_pos κ)

/-- Decision LWE with a public modulus (`SigabaNeo.Lattices.LWE.DecisionPub`), `k` samples. -/
def lwe : Prop := LWE.DecisionPub k n q W lweSecret lweError

end TestCase.EvLWE
