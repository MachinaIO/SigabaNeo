# How far the proofs reach: proven attack costs against the estimator

`H` is the floor of the cheapest attack in the lattice estimator's model
([LWE_ESTIMATOR.md](LWE_ESTIMATOR.md)). That model rests on heuristics. This file tracks, stage by
stage, which part of an attack's cost is proved without them, and how far the proved cost is from
the estimator's. Only results with no `sorry` and no `axiom` count; anything else is listed as
open.

## Stage 1: BKZ output quality without the GSA

**Proved in Lean** (`SigabaNeo/Lib/Lattices/BKZ.lean`, `BKZ/Profile.lean`, `BKZ/Hermite.lean`;
axioms: `propext`, `Classical.choice`, `Quot.sound` only):

| Theorem | Statement |
| --- | --- |
| `BKZ.first_log_bound` | a Gram–Schmidt log-profile in which each block of size `k_i = min(β, n−i)` satisfies Hermite's inequality with constant `c` has Hermite factor `r_0 − S_n/n ≤ c (n−1)/(β−1) + c`, that is `Γ_β^{(n−1)/(2(β−1)) + 1/2}` with `c = ½ log Γ_β`, `Γ_β = max_{k≤β} γ_k` |
| `BKZ.hermite_cube` | Minkowski: every full-rank lattice in `ℝ^k` has a nonzero vector with `‖v‖² ≤ k · covol^{2/k}`, so `γ_k ≤ k` |
| `BKZ.projected_profile`, `BKZ.first_norm_bound` | the same bound from caller-supplied projected block data |
| `BKZ.reduced_first_norm_bound_covolume` | for a BKZ-β-reduced basis `b` of `L` (built with Mathlib's `gramSchmidt`; every projected block's first vector is shortest), `‖b_0‖ ≤ β^{(n−1)/(2(β−1)) + 1/2} covol(L)^{1/n}` |
| `BKZ.blockLattice_covolume`, `BKZ.basis_covolume` | the covolume of a projected block, and of the lattice, is the product of the Gram–Schmidt lengths |
| `BKZ.hermite_ball_linear`, `BKZ.gamma_half_nat_bound` | `γ_k ≤ (k+4)/π` for every `k ≥ 1` (from `Γ(k/2+1) ≤ ((k+4)/4)^{k/2}`) |
| `BKZ.reduced_first_norm_bound_covolume_ball` | for a BKZ-β-reduced basis, `‖b_0‖ ≤ ((β+4)/π)^{(n−1)/(2(β−1)) + 1/2} covol(L)^{1/n}` |
| `BKZ.reduced_approx_factor` | Schnorr's approximation factor: for a BKZ-β-reduced basis and every nonzero `v ∈ L`, `‖b_0‖ ≤ ((β+4)/π)^{(n−1)/(β−1)} ‖v‖` |
| `BKZ.hermite_ball` | Minkowski with the ball volume: some nonzero lattice vector has `‖v‖ ≤ 2 (covol / V_k)^{1/k}`, `V_k = π^{k/2}/Γ(k/2+1)` |

**Open in stage 1:**

* The HPS theorem for polynomially many tours (`2 Γ_β^{(n−1)/(2(β−1)) + 3/2}`) and its tour count
  are not proved. Only the fully reduced case is.
* `γ_β ≤ 1 + β/4` and Blichfeldt's bound are not proved in Lean. `γ_k ≤ k` and
  `γ_k ≤ (k+4)/π` are.

**What it gives the primal attack.** The worst-case approximation-factor bound for BKZ-β,
`‖b_1‖ ≤ γ_β^{(d−1)/(β−1)} λ_1` (proved in Lean with `γ_β ≤ (β+4)/π`: `reduced_approx_factor`), recovers the target when that factor times `‖(e, s, 1)‖` is below
`λ_2`. Here `λ_2` still comes from the Gaussian heuristic, the stage-2 target. The table gives the
smallest `β` (optimised over the number of samples) and its cost in the estimator's `RC.MATZOV`
model. The GSA column is the estimator's primal uSVP.

| Kyber | GSA (estimator) | `γ_β ≤ β` (proved) | `γ_β ≤ (β+4)/π` (proved) | `γ_β ≤ 1 + β/4` | Blichfeldt | `γ_β` at its heuristic value `β/(2πe)` |
| --- | --- | --- | --- | --- | --- | --- |
| 512 | β = 406, 143.8 bits | β = 3440, 988.7 bits | β = 2883, 831.1 bits | β = 2763, 797.2 bits | β = 2384, 690.1 bits | β = 2016, 586.3 bits |
| 768 | β = 624, 204.9 bits | β = 4971, 1422.7 bits | β = 4205, 1205.4 bits | β = 4041, 1159.0 bits | β = 3521, 1011.6 bits | β = 3024, 871.0 bits |
| 1024 | β = 874, 275.1 bits | β = 6876, 1963.8 bits | β = 5862, 1675.7 bits | β = 5645, 1614.0 bits | β = 4957, 1418.7 bits | β = 4304, 1233.5 bits |

The Hermite-factor bound that is proved (`first_norm_bound`) does not by itself recover the target
at any `β < 6000` for these instances. It does not use the shortness of the target.

**What this measures.** Even with `γ_β` at its heuristic value, the worst-case analysis costs about
440 bits more for Kyber512. The gap is the difference between the worst-case shape of a reduced
basis and its average shape on random q-ary lattices, which the GSA models. Closing it needs an
average-case analysis of BKZ on random q-ary lattices. That is an open problem: no theorem in the
literature predicts BKZ's output shape on random lattices.

The attacks that `H` takes into account are therefore not replaced by proven ones. Dropping the
heuristic attacks would raise `H` for Kyber512 from 139 to several hundred bits, an
overestimate. `H` keeps the estimator's model, and this file records the distance.

## Stage 2 (planned): the uSVP success condition on random q-ary lattices

Average-case bounds on `λ_2` and on the projected target from Siegel-type mean value theorems or
counting.

## Direction of the GSA error (checked)

The estimator's CN11 simulator models the BKZ basis shape more closely than the GSA, including the
HKZ tail. It is still empirical. With it, the primal attacks on Kyber cost more than with the GSA:

| Kyber | uSVP GSA | uSVP CN11 | difference | BDD GSA | BDD CN11 | difference |
| --- | --- | --- | --- | --- | --- | --- |
| 512 | 143.8 | 146.8 | +3.0 | 140.2 | 142.1 | +1.9 |
| 768 | 204.9 | 209.9 | +5.0 | 201.0 | 203.9 | +3.0 |
| 1024 | 275.1 | 282.3 | +7.2 | 270.7 | 275.4 | +4.7 |

So the GSA errs in the attacker's favour here, which keeps `H` on the safe side. This is a
comparison of two models, not a proof.

## Stage 3: sieving (assumption (B))

The sieving cost `2^{0.292 β}` rests on three assumptions:

* **(A)** the Gaussian heuristic for lattice-point counts. For Haar-random lattices it is a
  theorem (Siegel, Rogers).
* **(B)** the list behaves like i.i.d. uniform points on a sphere. This is the open core.
* **(C)** BKZ's projected blocks behave like random lattices.

Research note: [research/provable_sieving.md](research/provable_sieving.md). Status:

* A claimed solution of (B) for Haar-random lattices: Doulgerakis–Laarhoven, arXiv:2609.37482
  (2026, not refereed). It solves exact SVP in `2^{0.2924n+o(n)}` time and `2^{0.2075n}` space. It
  rests on Laarhoven, arXiv:2609.13635 (quenched lattice statistics). Both are **claimed**, not
  verified here.
* The note proves the algorithmic layer on paper, given static hypotheses S1–S5 on a fixed
  lattice: exact uniformity of the lists, the acceptance rate, correctness in time `2^{0.415n}`.
  It also proves Lemma S3′ (SVP coverage from Rogers' formula at `k ≤ 3`) and the `q`-ary
  mean-value formula (Lemmas Q1, Q2).
* The deep input for exact SVP is gap **G1**: [Laa26] Proposition 5.1, quenched bounds on high
  moments of lens counts with every non-partition penalty below `3/4`. An adversarial audit
  ([research/g1_audit.md](research/g1_audit.md)) re-derived both bounds and found G1 **holds on
  the domain it states**, *given* the classical Rogers formula and spherical Gram density:
  * the feared two-free-parent relation `x₃ = x₁ + x₂ − d` has empty support, because the
    longitudinal constraint forces projection `≈ d/2`;
  * the worst surviving base is `e/4 < 3/4`;
  * the prefactor is `e^{O(h² log n)}`, a correction to the note, still `2^{o(n)}` at
    `h ≈ ln n`;
  * the endpoint bound excludes `α = 1`, which the SVP route does not use.

  Not verified: proofs of Rogers' formula and of the Gram density, and their instantiation for the
  Haar measure. [Laa26]'s Lean development assumes both (`ClassicalRogersFormula`,
  `ClassicalGramFormula`). For Haar-random lattices the result is therefore conditional on two
  classical theorems not formalized here.
* **`q`-ary lattices (the LWE side).** Here Lemma Q1 replaces Rogers' formula by linear algebra over
  `F_q`. Proved in Lean (`SigabaNeo.QAry`; axioms `propext`, `Classical.choice`, `Quot.sound`):

  | Theorem | Statement |
  | --- | --- |
  | `kernelCount`, `meanValue` | Lemma Q1: for uniform `A ∈ Z_q^{n×m}`, the average of a finite weighted tuple sum over `Λ_q^⊥(A)` is `Σ_x F(x)/q^{n·rk_{F_q}(x)}` |
  | `shortRank` | Lemma Q2: integer tuples with row norms `≤ R`, `R^k < q`, have equal ranks over `F_q` and `Q` |
  | `firstMoment` | Siegel analogue: a shell of nonzero integer vectors of radius `R < q` has expected count `|S|/q^n` |
  | `secondMoment`, `variance` | exact second moment and variance of shell counts for `R² < q` |

  Lemma Q3 (integer points in lens fibres, needed to compare the counts with volumes): proved on
  paper for separations in `[R/2, 3R/2]`, shell width `≍ 1/n`, `m ≥ n` and `R/m^{3/2} → ∞`
  ([research/qary.md](research/qary.md)). The general range and the higher-moment integrands are
  open, and the paper part is not in Lean. Modular coincidences at `m = 2n` are quantified there.
* **Reverse Minkowski dichotomy for (C) (new; negative;
  [research/reverse_minkowski_blocks.md](research/reverse_minkowski_blocks.md)).** The idea was
  that every block either has a dense sublattice (recurse into it) or is semistable, in which case
  reverse Minkowski bounds the counts. **It fails on both branches.**
  * A minimum-slope piece of the canonical filtration can miss every shortest vector.
  * Semistable lattices can exceed the S1 and S2 predictions by exponential factors.
  * Decisively, on `Z^n` squared norms are integers, so the sieve's thin terminal shell is
    **empty** in infinitely many dimensions, also after any fixed-prime-index re-randomization.
    The last transition then accepts nothing, which defeats T1 and the averaged route of
    Remark A′. Non-vacuous S2 counterexamples are given in dimensions 168 and 1542 (exact
    rational interval checks).
  * Lean: `RevMink.card_le_of_gaussian_mass`, a count bound from a Gaussian-mass bound. Axioms
    `propext`, `Classical.choice`, `Quot.sound`. The counterexamples are paper proofs.

  Conclusion: the shell-based provable sieve is inherently average-case. It cannot certify the
  sieve calls on arbitrary (worst-case) BKZ blocks. A growing, input-dependent re-randomization
  index remains unexplored.
* In progress: a Lean formalization of the algorithmic layer (S1–S5 as hypotheses), and the `q`-ary
  sieving statistics (T4).
* **Re-randomization for (C) (new; [research/rerandomization.md](research/rerandomization.md)).**
  Replace a block `B` by a uniformly random index-`p` sublattice. A tuple whose residues span
  dimension `r` survives with probability `(p^{d−r} − 1)/(p^d − 1)`, which gives exact moments of
  every order for **every** input lattice.
  * Proved in Lean: `Rerand.meanValue` (the finite-support weighted identity, any arity) and
    `Rerand.nonzeroKernelCount`. Axioms: `propext`, `Classical.choice`, `Quot.sound`.
  * Paper proof only (not in Lean): **negative result**. For every `d ≥ 2` and prime `p` there are
    determinant-one lattices with HKZ-reduced bases, `diag(η, η⁻¹, 1, …)ℤ^d` with `η → 0`, for
    which every index-`p` sublattice violates the shell-count hypothesis S1. So
    re-randomization alone does not give the sieve's static hypotheses for arbitrary blocks.
    The obstruction is to S1, not to solvability: such blocks have `λ₁` far below the Gaussian
    heuristic. Treating "skewed" blocks separately is a possible next step.
* Open: (C) has no proof. BKZ's projected blocks are not Haar-random, and no analogue of
  Rogers' formula is known for them. So even a verified [DL26] would make sieving a theorem for
  random lattices, not for the sieve calls inside BKZ on LWE lattices.

## Stage 4 (planned): dual attacks

Following the Pouly–Shen line of rigorous dual-attack analyses.

The stage-1 numbers come from `python/proof_gap.py` (estimator `RC.MATZOV` costs, `python/lwemodel`).
