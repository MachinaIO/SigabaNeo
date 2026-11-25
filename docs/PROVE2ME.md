# Claims on Prove2Me

Claims are posed as theorems on [Prove2Me](https://prove2.me), an open Lean 4 platform where
agents prove theorems and Prove2Me's server checks them
([paper](https://arxiv.org/abs/2608.28433)). Prove2Me's verdict is not trusted: the client checks
every proof itself. How a claim becomes Prove2Me objects, and how answers are checked, is in
[DESIGN.md](DESIGN.md) ("Claims on Prove2Me").

What Prove2Me checks, according to its documentation: the type of `theorem solution` against the
statement, and no `sorry`. Its documentation says nothing about axioms, `native_decide`, or
kernel replay.

## Open: the environment

Prove2Me's environments pin only a Lean toolchain and a Mathlib commit. There are three of them
(the default is Lean v4.33.1 with Mathlib `0df444a`), and none has cslib-frontier. Our core pins
cslib-frontier `d25e68f` with Lean v4.36.0-rc2, and claims take their definitions (`IsPPTOn`,
`ProbComp`, `Negligible`) from it.

The check always runs in the core's environment, whatever environment Prove2Me used. A proof made
in another environment is accepted only if it also compiles in ours. There are two ways forward:

* **(a)** Prove2Me adds an environment with the core's pins.
* **(b)** We port the needed part of cslib-frontier to Prove2Me definitions.

Our answer is our own DAG of Prove2Me-style files on GitHub, verified in the core's environment
([GITHUB_PLATFORM.md](GITHUB_PLATFORM.md)).

## How existing Prove2Me crypto statements model efficiency (survey, November 2026)

All of these come from public theorem pages. Every one is still an open statement (`:= by sorry`).

* **Uniform Turing machines.** This is the main approach of the research-paper missions. An
  adversary is a step function `Str → Str` that `PolyTimeComputable` holds of: some Mathlib TM2
  machine computes it in polynomial time. The adversary also has a polynomial bound on its coins.
  Games are Mathlib `PMF`s, negligibility is a plain `ℕ → ℝ` predicate, and hardness is a `Prop`
  given as a hypothesis, for example:

  ```lean
  theorem PPSLattice.lwe_regime_implies_owf (ε : ℝ) (q χ : ℕ → ℕ)
      (hε : 0 < ε) (hε2 : ε < 1 / 2) (hreg : PPSLattice.LWERegime ε q χ)
      (hLWE : PPSLattice.LWEHard q χ) : PPSLattice.OWFExists := by sorry
  ```

  Captains note that this replaces the papers' non-uniform distinguishers with uniform ones. They
  also note that the LWE hypothesis concerns one parameter family, "so it cannot be made vacuous".
* **Non-uniform circuits.** Here efficiency is circuit size (`A.size ≤ t`), and success
  probabilities are finite uniform averages. Some missions state the security notion over all
  adversaries, which makes it information-theoretic. Assumptions are predicates on the primitive
  given as hypotheses (`(hWE : WE.IsWE)`). One mission dropped its LWE headline theorem because
  "the paper never defines LWE or its parameters".
* **Quantum and non-uniform.** Hypotheses are left opaque (`(hLWE : LWEHyp ε)`). One mission
  states what it fixes because the paper leaves it informal: "the LWE parameters, the machine
  model and the honest resource".
* **Purely statistical.** These use a hand-rolled finite PMF over `ℝ` and ℓ¹-distance bounds for
  game hops. Efficiency and negligibility do not appear at all.
* **Randomized algorithms.** One entry uses `IsPolyRandom` and inverse-polynomial advantage
  infinitely often, and replaces exact sampling with a sampler within `2^(-l)` in total variation.

No two missions share a machine model; each mission defines its own. Our cards differ in that
their definitions come from one library (cslib-frontier). The PPT notion is therefore that
library's, not one written for the claim.
