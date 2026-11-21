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
| `BKZ.hermite_ball` | Minkowski with the ball volume: some nonzero lattice vector has `‖v‖ ≤ 2 (covol / V_k)^{1/k}`, `V_k = π^{k/2}/Γ(k/2+1)` |

**Open in stage 1:**

* The HPS theorem for polynomially many tours (`2 Γ_β^{(n−1)/(2(β−1)) + 3/2}`) and its tour count
  are not proved. Only the fully reduced case is.
* `γ_β ≤ 1 + β/4` and Blichfeldt's bound are not proved in Lean. `γ_k ≤ k` and
  `γ_k ≤ (k+4)/π` are.
* The approximation-factor bound `‖b_1‖ ≤ γ_β^{(d−1)/(β−1)} λ_1` used below (Schnorr) is not
  formalized.

**What it gives the primal attack.** A worst-case approximation-factor bound for BKZ-β,
`‖b_1‖ ≤ γ_β^{(d−1)/(β−1)} λ_1`, recovers the target when that factor times `‖(e, s, 1)‖` is below
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

## Stage 3 (planned): sieving

The unconditional `2^{n + o(n)}` sieve of Aggarwal–Dadush–Regev–Stephens-Davidowitz, then the gap
to the heuristic `2^{0.292 n}`.

## Stage 4 (planned): dual attacks

Following the Pouly–Shen line of rigorous dual-attack analyses.

The stage-1 numbers come from `python/proof_gap.py` (estimator `RC.MATZOV` costs, `python/lwemodel`).
