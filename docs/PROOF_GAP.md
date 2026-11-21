# How far the proofs reach: proven attack costs against the estimator

`H` is the floor of the cheapest attack in the lattice estimator's model
([LWE_ESTIMATOR.md](LWE_ESTIMATOR.md)). That model rests on heuristics. This file tracks, stage by
stage, which part of an attack's cost is proved without them, and how far the proved cost is from
the estimator's. Only results with no `sorry` and no `axiom` count; anything else is listed as
open.

## Stage 1: BKZ output quality without the GSA

**Proof.** In progress: the Hanrot–Pujol–Stehlé / Gama–Nguyen analysis. It covers the
Gram–Schmidt profile of a BKZ-β-reduced basis from Hermite's inequality in each block, and an
explicit bound on the Hermite constant `γ_β` from Minkowski's theorem. Lean files:
`SigabaNeo/Lib/Lattices/BKZ*.lean`.

**What it gives the primal attack.** A proven worst-case bound for BKZ-β is an approximation factor
`‖b_1‖ ≤ γ_β^{(d−1)/(β−1)} λ_1` (Schnorr; HPS for the version with polynomially many tours). The
attack then recovers the target when that factor times `‖(e, s, 1)‖` is below `λ_2`. Here `λ_2` is
still taken from the Gaussian heuristic, which is the stage-2 target. The table gives the smallest
`β` (optimised over the number of samples) and its cost in the same `RC.MATZOV` model as the
estimator. The GSA row is the estimator's primal uSVP.

| Kyber | GSA (estimator) | proven factor, `γ_β ≤ 1 + β/4` | proven factor, Blichfeldt bound on `γ_β` | factor with `γ_β` at its heuristic value `β/(2πe)` |
| --- | --- | --- | --- | --- |
| 512 | β = 406, 143.8 bits | β = 2763, 797.2 bits | β = 2384, 690.1 bits | β = 2016, 586.3 bits |
| 768 | β = 624, 204.9 bits | β = 4041, 1159.0 bits | β = 3521, 1011.6 bits | β = 3024, 871.0 bits |
| 1024 | β = 874, 275.1 bits | β = 5645, 1614.0 bits | β = 4957, 1418.7 bits | β = 4304, 1233.5 bits |

A proven Hermite-factor bound (`‖b_1‖ ≤ 2 γ_β^{(d−1)/(2(β−1)) + 3/2} det^{1/d}`) does not recover
the target at any `β < 6000` for these instances. It does not use the shortness of the target.

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

## Stage 3 (planned): sieving

The unconditional `2^{n + o(n)}` sieve of Aggarwal–Dadush–Regev–Stephens-Davidowitz, then the gap
to the heuristic `2^{0.292 n}`.

## Stage 4 (planned): dual attacks

Following the Pouly–Shen line of rigorous dual-attack analyses.

The stage-1 numbers come from `python/proof_gap.py` (estimator `RC.MATZOV` costs, `python/lwemodel`).
