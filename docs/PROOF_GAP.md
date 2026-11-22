# How far the proofs reach: proven attack costs against the estimator

`H` is the floor of the cheapest attack in the lattice estimator's model
([LWE_ESTIMATOR.md](LWE_ESTIMATOR.md)). That model rests on heuristics. This file tracks, stage by
stage, which part of an attack's cost is proved without them, and how far the proved cost is from
the estimator's. Only results with no `sorry` and no `axiom` count; anything else is listed as
open.

## Stage 1: BKZ output quality without the GSA

**Proved in Lean** (`SigabaNeo/Lib/Lattices/Reduction/BKZ.lean`, `Reduction/BKZ/Profile.lean`, `Reduction/BKZ/Hermite.lean`;
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
| `BKZ.hermite_blichfeldt` (`Reduction/Hermite2.lean`) | Blichfeldt: `γ_k ≤ (2/π) Γ(k/2+2)^{2/k}`, with corollaries `reduced_first_norm_bound_covolume_blichfeldt` and `reduced_approx_factor_blichfeldt` (machine-checked; axioms `propext`, `Classical.choice`, `Quot.sound`) |
| `BKZ.hermite_ball` | Minkowski with the ball volume: some nonzero lattice vector has `‖v‖ ≤ 2 (covol / V_k)^{1/k}`, `V_k = π^{k/2}/Γ(k/2+1)` |

**Open in stage 1:**

* The HPS theorem for polynomially many tours (`2 Γ_β^{(n−1)/(2(β−1)) + 3/2}`) and its tour count
  are not proved. Only the fully reduced case is.
* `γ_k ≤ k`, `γ_k ≤ (k+4)/π` and Blichfeldt's bound are proved in Lean.
  Kabatiansky–Levenshtein is open.

**What it gives the primal attack.** The worst-case approximation-factor bound for BKZ-β,
`‖b_1‖ ≤ γ_β^{(d−1)/(β−1)} λ_1` (proved in Lean with `γ_β ≤ (β+4)/π`: `reduced_approx_factor`), recovers the target when that factor times `‖(e, s, 1)‖` is below
`λ_2`. Here `λ_2` still comes from the Gaussian heuristic, the stage-2 target. The table gives the
smallest `β` (optimised over the number of samples) and its cost in the estimator's `RC.MATZOV`
model. The GSA column is the estimator's primal uSVP.

**Correction (block size `β ≤ d`).** The earlier version of this table reported `β` up to 6876. That
is invalid: Kyber gives at most `m = n` samples, so the embedding dimension is
`d ≤ n + m + 1` (1025 for Kyber512), and the theorems need `β ≤ d`. With `β ≤ d` enforced
(`python/proof_gap.py`), **no admissible block size exists for Kyber512/768/1024 under any of the
constants**: the proved `β`, `(β+4)/π`, the exact Minkowski ball, Blichfeldt, and even the
heuristic `β/(2πe)`. The worst-case approximation-factor route therefore gives no cost at all for
Kyber. At `β = d`, BKZ is an exact SVP call, and Schnorr's bound is loose there. Solving SVP
directly in dimension `d` is exactly the full-dimension sieve route below.

| Kyber | GSA (estimator) | worst-case BKZ route, any proved or heuristic `γ_β`, `β ≤ d` |
| --- | --- | --- |
| 512 | β = 406, 143.8 bits | no admissible `β` |
| 768 | β = 624, 204.9 bits | no admissible `β` |
| 1024 | β = 874, 275.1 bits | no admissible `β` |

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

## Wall 1: the average-case BKZ profile on random `q`-ary lattices (in progress)

* **First step (new; [research/avg_bkz.md](research/avg_bkz.md); audited: passes for the stated ensemble, [research/avg_bkz_audit.md](research/avg_bkz_audit.md)).** For an i.i.d.
  uniform prime-field parity-check matrix, one fixed coordinate projection preserves an exact
  random modular-kernel law. Given that the prefix columns span `S`, the projected lattice is the
  modular kernel of independent uniform columns in the quotient by `S`. Before BKZ, the next
  Gram–Schmidt length of the coordinate-adapted basis is `q` with probability `1 − q^{r−n}` and
  `1` otherwise.
* **Obstruction.** Once the prefix spans the syndrome space, the projected lattice is exactly
  `Z^{d−t}`, the thin-shell-empty type. So random coordinate orderings and internal basis changes
  alone cannot enforce the sieve's statistics.
* Lean: `AvgBKZ.coordinateProjection` and `AvgBKZ.quotientColumnCount`. Axioms `propext`,
  `Classical.choice`, `Quot.sound`.
* **Part 2 (obstruction; [research/avg_bkz2.md](research/avg_bkz2.md)).** The exact law fails after one
  exact SVP selection. In dimension two the projected spacing lies strictly between 1 and `q` with
  probability `≥ (1 − 1/q)²`. Lean: `AvgBKZ.planeShortestSq`, `AvgBKZ.planeNormalSq`.
* **Part 3 (obstruction; [research/avg_bkz3.md](research/avg_bkz3.md)).** Few prefixes per BKZ run do
  not justify a union bound over fixed prefixes, because of selection bias: fixed-index failure `1/N`,
  yet a selecting run fails with probability 1. Lean: `AvgBKZ.diagonalSelectionCounts`,
  `AvgBKZ.diagonalWeightHalf`.
* **Part 4 (obstruction, audited; [research/wall1_new.md](research/wall1_new.md)).** In the iid
  plain-LWE embedding with `m = n = 512`, `q = 3329`, with probability `> 1 − 2^{−275}` every
  coordinate projection of dimension 2–400 (coordinates may be chosen after seeing `A, b`) is the full
  grid `Z^k`, which has no unique shortest pair. Coordinate-block routes (random orders, progressive
  deletion, best-of-many projections) and block-internal potentials therefore cannot work; adaptive
  BKZ prefix spans are not covered.
* **Part 5 (partial result, audited; [research/wall1_sublattice.md](research/wall1_sublattice.md)).**
  For Haar-random unimodular lattices, a simultaneous lower bound on `λ₁` of the projection onto the
  complement of **every** primitive prefix of covolume `≤ X` (Kim's flag mean-value theorem + Markov), so it
  holds for prefixes chosen adaptively by BKZ — immune to selection bias. Missing: a bound on the selected
  prefix's covolume, and the polynomial-`q` q-ary ensemble; at the GSA values the bound becomes vacuous as
  `n` grows.
* **Part 6 (audited; [research/wall1_prefix.md](research/wall1_prefix.md)).** Deterministic prefix-covolume
  envelope and a Schnorr-type ratio bound `g_t ≥ g_0 e^{−p_0^{(t)}}` for fully BKZ-β reduced bases (proven Hermite
  constants; both recursions are exact LP optima). With `g_0 ≥ λ1(L)` for Haar lattices, the 99% terminal height at
  `n = 700, β = 200` is only **9.22 bits below GSA**. The ratio bound is deterministic and holds for q-ary lattices too;
  the cost of producing a fully reduced basis and the projected planted law are not addressed.
* **Part 7 (audited negative result; [research/ratio_unique.md](research/ratio_unique.md)).** Rigorous: if every
  vector outside `ℤu` exceeds `R` and `‖u‖ ≤ R e^{−p_0^{(d−β)}}`, any fully BKZ-β reduced basis has `b_0 = ±u`. For the
  Kyber plain-LWE shapes the smallest certified `β` is `d` (701/1017/1351), i.e. exact full-dimensional SVP: the
  ratio bound gives no block-size saving, because the projected planted length is only bounded by `‖u‖`.
  *Superseded for the full-dimension SVP size by Part 39:* an exact integer-point first-moment certificate lowers the
  plain-LWE 512 dimension from 701 to 662 (1 − 2^-64) or 647 (99%).
  *In Lean* (`Attacks/Primal/RatioPlanted*.lean`): `reduced_finds_plant` composes the Part 7 ratio lemma with the q-ary
  competitor count — outside an explicitly counted exceptional set of designs, if ‖v‖ ≤ R·e^{−p(D,β)} every fully BKZ-β reduced
  basis of the embedding lattice has first vector ±v; `competitor_design_bound` gives the count for radii J < 4‖v‖² (beyond
  that, 2v is always a competitor: `cutoff_counterexample`). Only a toy instance is certified (q = 4051, D = 3, β = 2: ≥ 4011 of
  4051 designs); at the Kyber shapes the certified β is d (above).
* **Part 8 (audited; [research/wall1_planted_flags.md](research/wall1_planted_flags.md)).** The flag criterion for
  terminal-block recovery must include the case `π_W(u) = a·v`, `a ≥ 2` (a shorter vector on the planted line's image);
  the corrected necessary-and-sufficient criterion is `a = 1` plus "every other line in `Q_W` is longer". Counterexamples:
  a fully reduced plain planted lattice with `a = 2` (outside the uSVP regime), and a reduced generic lattice where the
  unique shortest vector keeps its full length in the complement yet the terminal minimum is shorter. The probability of
  these events for random planted instances is open.
* **Part 9 (audited negative result; [research/wall1_planted_prob.md](research/wall1_planted_prob.md)).** At `β = 406` for the
  Kyber512 plain-LWE shapes (`m = 188, 511, 512`), for every `A` and every planting with coordinates `≤ 3`, some primitive prefix
  below the Part 6 cutoff violates the corrected criterion (witness `2b_k + u`, `a = 2`). So no all-prefix statement certifies
  `β = 406`; the failure probability for the prefix BKZ actually selects is open. For a fixed `W ⊂ L0`, `a = 1` and
  `‖π_W u‖²` concentrates (proved).
* **Part 10 (audited negative result; [research/wall1_selected.md](research/wall1_selected.md)).** Rotation equivariance gives
  an exact beta law for the projection of an *external* direction onto the complement of the selected prefix, but not for a
  short vector of the same lattice; choosing the prefix from the `u`-independent lattice `L0` gives exactly equal quotient
  covolumes, yet an explicit example has a projected horizontal vector shorter than the unique ambient shortest plant. Symmetry
  and independence alone cannot certify `β = 406`; what remains is the probability of a competing vector in the quotient that
  the actual algorithm selects.
* **Part 11 (audited; [research/wall1_markov_flags.md](research/wall1_markov_flags.md)).** Rerandomized tours are not a Markov
  chain on flags in general (two bases with the same prefix give disjoint next-prefix laws under the same unimodular update),
  and a symmetric irreducible walk on primitive lines has no stationary probability. A specific tour with a metric-dependent
  reduction step is not excluded.
* **Parts 12–14 (audited obstructions).** [wall1_gaussian_blocks.md](research/wall1_gaussian_blocks.md): with Gaussian block
  insertion the projected plant lies on the unique shortest line but with multiplicity `|b|`; as the width grows (smoothing error
  → 0) the probability of multiplicity one → 0. [wall1_duality.md](research/wall1_duality.md): exact dual criterion (primitive
  plant + strictly smallest marked hyperplane kernel), and two lattices with identical reversed dual blocks where the criterion
  holds in one and fails in the other — unmarked block statistics cannot certify recovery. [wall1_dynamics.md](research/wall1_dynamics.md):
  along an exact trajectory with a deterministic tie rule, the next block's law is not determined by its covolume (1/3 vs 1/2);
  random tie-breaking removes this discrepancy in the example.
* **Part 15 (audited; [research/wall1_fresh_samples.md](research/wall1_fresh_samples.md)).** A norm cutoff on the planted vector
  couples disjoint sample batches even with a fixed secret (two-sample example: 1/3 versus 1/2 or 0 after one observed bit);
  with errors fixed in advance the design coefficients stay independent. Open: whether a fresh batch represents the original
  projected block and keeps the planted line.
* **Part 16 (audited; [research/wall1_information.md](research/wall1_information.md)).** Uniform random tie-breaking does not
  restore covolume-only conditioning: a 4-dimensional binary kernel gives 2/5 vs 4/9 for two histories with the same terminal area.
  Transcript-length (entropy) bounds limit total leakage but a few bits can encode the next minimum itself; a concentration proof
  needs an information bound on that specific observable.
* **Part 17 (audited; [research/wall1_coupling.md](research/wall1_coupling.md)).** Replacing blocks by fresh Haar lattices has
  total variation error exactly 1 (rational vs atomless minima); path coupling and a discrete reference (exact for unexamined
  coordinate blocks) are proved. **Audit finding:** in the 4-dimensional example of Parts 16–17 the discrepancy disappears once
  one conditions on the full in-block Gram–Schmidt profile, so *profile-only* conditioning (rather than covolume-only) is still
  open and is the most promising lead.
* **Part 18 (audited; [research/wall1_smoothed.md](research/wall1_smoothed.md)).** Generic continuous metric noise makes
  reduction trajectories almost surely tie-free and locally stable, but an arbitrarily small anisotropic perturbation still gives
  conditional tail probabilities 1/3 vs 1/2 for two histories at almost every common covolume. Isotropic smoothing and
  profile-only conditioning remain open.
* **Part 19 (audited; [research/wall1_profile.md](research/wall1_profile.md)).** Given the history of selected lines, even the
  full Gram–Schmidt profile does not determine the next block's law, with uniform random tie-breaking: dimension 3 (revisits,
  same profile and current block, 4/5 vs 0; dimension-minimal) and dimension 5 (one forward sweep, 1/3 vs 2/5). Open: the
  process observed through successive scalar profiles only.
* **Wall 1 as Lean statements (local Prove2Me server, [P2M_LOCAL.md](P2M_LOCAL.md)).** `Wall1SlideTerminalRecovery`
  (probability over uniform `A`, fixed CBD-support `(e,s)` in a norm shell, basis = output of the verified slide loop on the
  canonical q-ary rows, tolerance 1/10) and `Wall1GSATerminalRecovery` (parameterized by an explicit GSA-type inequality; concrete
  instance: 99% recovery at m = 511, n = 512, q = 3329, β = 512) are registered with SKETCH_ACCEPTED decompositions
  (`Research/Wall1/SelectedSlide.lean`): each reduces by a union bound to two open selected-prefix estimates (same-line: the plant
  does not project to zero and no shorter vector lies on its projected line; off-line: no competing line is as short). Also
  registered: `Wall1FixedCBD2Projection` (open; fixed-projector concentration), `wall1_terminal_primitive_iff` (proved),
  `wall1_prefix_ratio` (open).
* **Parts 20–21 (audited).** [wall1_reachable.md](research/wall1_reachable.md): the Part 9 divisibility failure depends only on the
  prefix plane modulo any prime p ≠ q, so union bounds over reachable prefixes are vacuous whenever one reachable plane contains
  the plant mod p; the selected failure probability equals the fraction of inputs whose output plane contains the plant mod p.
  [wall1_small_exact.md](research/wall1_small_exact.md): in dimension 3 with plant (1,1,1), every fully BKZ-2 reduced basis has
  terminal success probability exactly 5/q (proved ≤ 11/q); every ambient-unique instance puts ±p in the FIRST row. **Consequence:**
  'terminal recovery' undercounts success (early recovery), so the Lean core statements registered with terminal-only success can
  be false; they are being re-registered with success = '±u is an output basis vector or the terminal criterion holds'.
* **Parts 22–29 (audited; ten parallel routes, Nov 2026).** All ten routes ended in obstructions or partial results:
  [isotropic](research/wall1_isotropic.md) (isotropic smoothing does not give covolume-only conditioning),
  [profile_only](research/wall1_profile_only.md) (observed profiles are not Markov: 12/17 vs 0),
  [exchangeable](research/wall1_exchangeable.md) (input randomization does not survive reduction),
  [second_moment](research/wall1_second_moment.md) (sharp moment bound allowing adaptivity; reruns fail),
  [embedding_factor](research/wall1_embedding_factor.md) (success set in τ² is an open interval; divisibility unaffected),
  [haar_marked](research/wall1_haar_marked.md) (short marks are recovered early, so terminal recovery → 0),
  [stability](research/wall1_stability.md) (stability radius explicit; averaging loss too large),
  [literature](research/wall1_literature.md) (closest: Laarhoven 2610.15265 Prop. 3, prefix covolumes of quasi-HKZ bases of Haar
  lattices; nothing bounds the selected terminal block), plus reachable and small_exact (Parts 20–21).
* **Corrected Lean core statements (local P2M).** `Wall1SlideCaptureOrTerminalRecovery` and `Wall1GSACaptureOrTerminalRecovery`
  (success = some output basis row is ±u, or the terminal criterion holds; everything else unchanged) are SKETCH_ACCEPTED with four
  open leaves (`Wall1{Slide,GSA}CaptureOr{SameLine,OffLine}`); `Research/Wall1/CapturedSlide.lean`. The terminal-only originals stay
  registered and open; no disproof at the registered width (n ≥ 512, β ≥ 40) was found.
* **Parts 30–37 (audited; eight more parallel routes, Nov 2026).** One positive partial result and seven obstructions; every
  explicit example re-checked in exact arithmetic by two independent auditors:
  [contained](research/wall1_contained.md) (**positive**: for prefix rank k ≤ β, containment plus ambient uniqueness forces capture,
  so the contained-without-capture stratum has probability ≤ 2^-63 at d = 701, β = 406 — implied by Part 7's uniqueness event;
  fails already at k = β+1, explicit d = 5 example),
  [interior](research/wall1_interior.md) (exact fixed-plane interior probability via finite-field rank expectations; adaptive
  selectors reach 1 and 0 where every fixed plane has 1/3),
  [capture_depth](research/wall1_capture_depth.md) (ambient uniqueness forces capture-or-terminal only at β = d: integral bases in
  every d ≥ 3, BKZ-β reduced for all β < d, missing the unique shortest pair),
  [canonical](research/wall1_canonical.md) (two HKZ reducers with the same flag, one captures and one misses: flag-only counting
  fails), [ties](research/wall1_ties.md) (no tie at the minimum for terminal dimension 2, odd q, irrational height; q = 5
  terminal-dimension-3 tie on [1/24, 1]), [monotone_beta](research/wall1_monotone_beta.md) (one basis BKZ-2 and BKZ-3 reduced:
  success at width 2, failure at width 3), [lower_bound](research/wall1_lower_bound.md) (BKZ reducedness alone gives no necessary
  block size above 2: an HKZ selector captures w.p. > 1 − 2^-1900 at (511, 512, 3329)),
  [random_scale](research/wall1_random_scale.md) (signed-permutation averaging keeps the plant correlated with the prefix:
  TV distance 3/4 in a 4-dimensional example). **Consequence:** any β < d bound must use how the concrete slide/BKZ algorithm
  selects its output; reducedness, flags, monotonicity and symmetrization arguments are each refuted.
* **Part 38 (audited, minor caveats).** [analyzable_reducer](research/wall1_analyzable_reducer.md): selection-bias bound
  D_Ber(p‖h) ≤ I(A; P | U) between the bad-event probability p under the adaptive prefix P and h under an A-independent prefix
  with the same conditional law; tight on the three-plane example (likelihood ratio constant on the event). Hence
  p ≤ (I + 1)/log₂(1/h): a 2^-128 reference bound plus one bit of conditional design information would give p ≤ 1/64.
  Caveats (audit): the 'I(U;P) = 0' illustration is the degenerate fixed-plant case; if the bad event depends on output rows or
  coins R, I(A; P, R | U) is needed. Open: the reference bound in π_{P⊥}L_A and an information bound for a concrete reducer.
* **Part 39 (audited, minor caveats).** [projected_reference](research/wall1_projected_reference.md): for an A-independent
  coordinate prefix (deleted sample axes, spanned by q·e_i) the projected lattice is exactly the standard embedding of the
  punctured design, so an exact integer-point count (not a volume estimate) and the exact CBD norm law give a rigorous
  terminal-recovery certificate with one exact SVP call. Plain LWE (511, 512, 3329): CBD(3) dimension 647 at 99% (≥ 99.51664%),
  662 at 1 − 2^-64; CBD(2) 627 / 641 (all reproduced in exact arithmetic by the auditor). This is the sample-count optimisation
  made rigorous and tightens Part 7's 701 → 662 at matched confidence. Heuristic sieve cost 2^{0.2925·647} ≈ 2^189 — the proven
  cost is only Micciancio–Voulgaris 2^{2D}. General fixed rational planes: exact first moment via finite-field ranks; a fixed
  rank-one plane fails with certainty. Says nothing about adaptive BKZ prefixes (β ≈ 400–512).
  **Formalized in Lean** (`Attacks/Primal/SampleDeletion*.lean`; axioms `propext`, `Classical.choice`, `Quot.sound`;
  numeric checks by `decide +kernel`, no `native_decide`): `competitor_probability_662` — over iid CBD(3) `(e', s)` and uniform
  `A' ∈ Z_3329^{149×512}`, Pr[∃ z ∉ {0, ±v}, ‖z‖² ≤ ‖v‖²] < 2^-64 — plus `failure_647` (< 1/100) and `exact_svp_recovery`
  (an exact SVP output is ±v and yields s). Independent audit: faithful (true probability, genuine uniform and CBD laws,
  ties counted).
* **Part 40 (audited, minor caveats).** [finite_family](research/wall1_finite_family.md): (i) width–count tradeoff: deleting
  sample and secret axes (each costs one factor q; secrets are eliminated by linear algebra, not guessed) gives terminal
  dimension 600 with > 99.57% recovery for plain LWE (511, 512, 3329), CBD(3), using a family of ≤ 2^575 coordinate planes
  (existence by averaging, i.e. non-uniform advice; the explicit family has 2^996) and a public selector verified by the
  Part 36 ambient bound — cost ≈ 2^575 SVP_600 calls, irrelevant as an attack; (ii) over all single fixed rational planes the
  RMS-vs-GH crossing is first at D = 641, attained by horizontal coordinate planes (Part 39 benchmark is optimal);
  (iii) at D = 406 every fixed rational plane passes the unique-terminal-pair criterion w.p. < 2^-678.61 (for k > m the
  projected lattice is A-independent), so a family needs ≥ 2^679 planes; (iv) cardinality does not bound I(A;P|U): a
  plant-aware selector with zero conditional design information passes the (degenerate) criterion at D = 406.
  **Consequence:** fixed or low-cardinality A-independent prefixes cannot reach β ≈ 406; any proof there needs adaptive
  (A-dependent) prefixes, i.e. the actual BKZ/slide selection.
* **Part 41 (audited, minor caveats).** [sublattice_union](research/wall1_sublattice_union.md): a union bound over the
  determinant-only family (all primitive rank-k sublattices of covolume ≤ the Part 6 cutoff) cannot certify success for any
  2 ≤ β ≤ 1007 on the full 1024-dim embedding: for every A and planting, B_a = V_{k−1} + Z(u + a b_k) (HKZ basis of the
  horizontal part) are primitive prefixes under the cutoff on which π u is |a| times a shorter vector — > 2^635 of them at
  β = 406, > 2^286 at 647 (interval-certified; also with GSA cutoffs). At β = 406 the rational-rank (Haar) mean is exactly 0
  because consistency mod q forces a rank loss ≥ 106. Only β = d = 1024 is certified (< 2^-1900). Caveat: these witnesses
  have last Gram–Schmidt length ≈ |a|·‖b_k*‖ and are not BKZ-like; a family constrained by the per-index Part 6 profile (or
  a λ_1/last-GS condition) is not ruled out.
* **Part 42 (audited, minor caveats).** [profile_union](research/wall1_profile_union.md): intrinsic BKZ/HKZ reducedness of a
  prefix does not discard the Part 41 pencil (once the last spacing is large the displayed basis is HKZ); a basis-invariant
  bound (any basis of B_a has a GS length ≥ ‖π(u + a b_k)‖) means per-index ceilings limit a — at the real parameters to
  t_a ≲ 2^5.8 (dozens of a), versus 2^635 for the determinant-only family. Off-line competitor tuples lose ≥ 107 ranks mod q at
  β = 406 and ≥ 1 at 512; at punctured width 647 the prefix is empty and Part 39 applies. No new width certified: the filtered
  first moment at positive prefix rank is not evaluated, and whether divisible witnesses survive for every planted matrix at
  406/647 is open.
* **Part 43 (audited, minor caveats).** [filtered_moment](research/wall1_filtered_moment.md): first rigorous filtered first
  moment at positive prefix rank, simultaneous over all reduced outputs: at punctured D = 699 (plain LWE (511,512,3329) CBD(3)),
  every fully BKZ-698-reduced basis yields recovery with probability > 99.218% (bad-line mean ≤ 2^-301 + 2^-7 + 2^-1774;
  certificate passes for D = 699..800 at k = 1). Not useful as a cost (BKZ-698 is worse than Part 39's single SVP at 647).
  Decisive negative: at D = 647, β = 646 the k = 1 filtered mean exceeds 2^163 (consistent full-rank witnesses), so first
  moments over profile-admissible prefixes cannot lower the width — any improvement needs information about the reducer's
  selection, not counting. D = 1024 at widths 512/647: rank-stratified upper bounds too large to decide.
* **Part 44 (audited, minor caveats).** [zshape](research/wall1_zshape.md): for exact BKZ on the full 1024-dim embedding
  (det q^511) with the canonical basis and the repo's strict-insertion scan (`needsInsertion`), a head q·e_i survives a scan
  iff its projected block has no strictly shorter vector. Block Hermite bounds force the first row of any fully BKZ-β-reduced
  basis below 2138 / 2131 < q at β = 646 / 647, so no q-prefix persists (k = 0) for every A; at β = 406 / 512 at most 105 / 22
  q-heads can persist, leaving ≈ 513 / 490 adaptive directions before the terminal block. While the coordinate prefix
  survives, the quotient is exactly the Part 39 punctured lattice — the Z-shape route re-derives Part 39 and gives no β < 647.
* **Part 45 (audited, minor caveats).** [randomized_reducer](research/wall1_randomized_reducer.md): a reducer that picks a
  uniformly random (1+ε)-near-shortest primitive vector per block keeps the Part 6 profile with c_d + log(1+ε); a randomized
  equal-width slide terminates surely (integer prefix-covolume potential decreases on dual updates) with the slide Hermite
  bound. But candidate counts do not control selection bias: in a rank-r example the mark is chosen w.p. 1/r while one
  excluding congruence shifts the selection law by TV 1 − 1/r. At β = 406, 99% terminal uniqueness needs I((A,U);P) > 670.82
  bits; at 512 an A- and plant-independent plane succeeds w.p. < 9.03·10⁻⁸; at 647 (Part 39 deletion) the terminal shell is a
  single line w.p. ≥ 0.99516648 for ε < 8.598·10⁻⁵. The randomized reducer's failure probability on the full input is not bounded.
* **Part 46 (audited, minor caveats).** [haar_prefix_law](research/wall1_haar_prefix_law.md): on Haar lattices, the
  quotient by a shortest vector of length r has an exact law (Haar tilted by a torus-avoidance probability; transverse
  minima below (√3/2)·r excluded), TV distance from Haar ≤ min(1, V_n r^n/2) for n ≥ 3 — small only when b_1 is atypically
  short; the full HKZ profile has an exact recursive joint density (estimator acceptance 2^{-n(n−1)/2}, infeasible at scale);
  primitive Palm-plant capture probability is explicit. Laarhoven 2610.15265 Prop. 3 (checked) controls prefix covolumes only
  to o(n log n). Checked numerically in d = 2, 3. Does not give a finite-width slide/BKZ law or transfer to planted q-ary lattices.
* **Part 47 (audited, minor caveats).** [decoupled](research/wall1_decoupled.md): L = L_0 ⊕ Zu with L_0 (the height-0 part)
  depending on A only. Reducer: BKZ/slide on L_0, then one SVP on T = π_{W⊥}L. Given A and coins the plant keeps its product CBD
  law, so the adaptivity of Parts 30–46 disappears for this reducer: exact mean ‖πu‖² = 1 + (β−1)η/2 with explicit McDiarmid
  concentration; λ_1(π L_0) > ‖πu‖² suffices at every height (essentially sharp; λ_1 > 2‖πu‖ fails at height 2); lifting
  succeeds by Babai on the prefix with failure ≤ Σ_i 2exp(−g_i²/(4η)) given A. **Wall 1 thus reduces, for this close variant
  of the primal attack, to a plant-free statement: lower quantiles of the Gram–Schmidt profile of BKZ/slide on the uniform
  q-ary lattice L_0.**
* **Part 48 (audited, minor caveats).** [null_terminal](research/wall1_null_terminal.md): worst-case propagation
  λ_1(T) ≥ λ_1(L_0)·e^{−P_k} with a Gaussian count λ_1(L_0) > 443.07 (99%) certifies λ_1(T) > 79.04 > sqrt(6β) only at
  β = 1000 for the rank-1023 null lattice of (511, 512, 3329) (slide: only the trivial 1023; punctured ranks: none); GSA would
  cross at β = 506. Haar analogues and a dual-minimum prefix bound are proved. So the plant-free statement is as hard as wall 1
  itself: the core difficulty is the average-case BKZ profile, not plant-induced selection bias.
* **Part 49 (audited, minor caveats).** [rankin_route](research/wall1_rankin_route.md): λ_1(T) ≥ μ_{k+1}(L_0)/covol(W) (and the
  identical dual form) with Part 6 cutoffs certifies λ_1(T) > 88.98 only at width 1020 (rank 1023); a modular-rank-aware count
  μ_2(L_0) > 193000 (failure < 0.000838) combined with propagation lifts the width-1000 radius 79.04 → 80.21, crossing still
  1000; quadratic target never; punctured shapes never. Babai lifting is certified at 99% from width ≈ 915 (audit), so lifting
  is not the bottleneck — the terminal minimum is.
* **Parts 50–53 (audited; plant-free routes, Nov 2026).** All on the residual statement of Part 47 (lower quantiles of the GS
  profile of BKZ/slide on the plant-free lattice):
  [volume_method](research/wall1_volume_method.md) (Part 50: Pr[∃ basis in U] ≤ Haar(U)/covol with the exact Iwasawa density;
  with only Part 6 profile inequalities the certified Haar terminal radii are 0.005–0.08 (covolume 1) at β = 406–800, versus
  linear targets 0.86–1.21 — the relaxation discards the coefficient-dependent SVP tests);
  [random_block_reducer](research/wall1_random_block_reducer.md) (Part 51: exact TV identity ½E|1 − C/EC| for random-block
  selection; the eligible-block scale has no slack at rank 1023; no width certified);
  [hecke_transfer](research/wall1_hecke_transfer.md) (Part 52: graph q-ary lattices → Haar as q → ∞ (N, m fixed); the event
  'some BKZ basis has terminal GS < ρ' has Haar-null boundary, so it transfers asymptotically; at q = 3329 the Sobolev order
  > 523264 makes every explicit transfer vacuous);
  [avg_prefix](research/wall1_avg_prefix.md) (Part 53: on Haar lattices at proportional prefix rank the Rankin numerator over the
  largest BKZ prefix determinant is exp(−Ω(n log n)) — the Rankin route cannot work in the bulk even with average-case
  denominators; with the exact GSA denominator as hypothesis it would first pass at width 1018).
* **Parts 54–56 (audited).** [qary_basis_count](research/wall1_qary_basis_count.md) (Part 54: whp > 1 − 2^-360 every
  fully BKZ-reduced basis of the rank-1023 null lattice has terminal g ≤ 600 at β = 406/506/647/800 — so Part 47's worst-case
  quadratic condition (≥ 608.5) is unattainable; the linear target √(6β) also fails whp on punctured ranks 700/661/646, uniformly
  over data-dependent projectors); [volume_svp_weights](research/wall1_volume_svp_weights.md) (Part 55: keeping SVP tests on
  disjoint intervals (each interval HKZ, independent coefficients) improves the Haar terminal radii only to 0.006/0.015/0.039/0.140
  at β = 406/506/647/800; crossing-block tests and exponential suppression are open); [literature2](research/wall1_literature2.md)
  (Part 56: no theorem gives the needed quantile; closest: Laarhoven Prop. 3, Joux–Węgrzycki's all-coordinate slide upper
  bound, El-Baz–Lee–Strömbergsson's Hecke rate; conditioning a uniform kernel to the graph law costs < 1/3328 in TV).
* **Part 57 (audited, minor caveats).** [volume_suppression](research/wall1_volume_suppression.md): for a fixed profile, short
  counts grouped by last nonzero column are orthogonal martingale differences (deterministic conditional means), giving
  Pr(pass) ≤ T/(E² + T) — at best order-1/E, not exponential suppression; a conditional product over all crossing starts; one
  crossing test retained in the integral removes positive mass but changes no displayed digit. Certified Haar terminal radii stay
  0.0058/0.0154/0.0392/0.1399 (β = 406/506/647/800) vs targets 0.86–1.21; the bound's modal prefix covolume (log ≈ 420) is far
  from GSA (≈ 984). A uniform exp(−cE) suppression over overlapping tests remains the missing ingredient.
* **Part 58 (audited).** [random_plant_heights](research/wall1_random_plant_heights.md),
  [height_union_fix](research/wall1_height_union_fix.md): for the decoupled attack, with the plant's projection independent of H,
  CBD(3) is sub-Gaussian (proxy 3/2), with explicit upper and (new) lower norm tails; for |k| ≥ 2 the height-k event is a
  fixed-direction tail on {‖v‖ ≥ R_-}. Using only λ_1(H) and packing counts, the union over (k, x) cannot beat the geometric
  condition λ_1(H) > T(R_+) ≈ R_+² (742 at β = 406 … 1702 at 1000 — far above the certified 80–89 and above GSA at every width).
  Heights 0, ±1 alone need λ_1(H) > 2√(R_+² − 1), certified at width 1020. Heights ≥ 2 need anti-concentration of k·v mod H,
  i.e. information on det H or the dual minimum — again the average-case profile.
* **Part 59 (audited).** [volume_product](research/wall1_volume_product.md): the crossing-start product bound in its
  exponential form exp(−Σ_j p_j), p_j ≤ 1, removes at most ≈ 1022 log units, while the bad Haar mass is ≈ e^{34000}; a feasible
  box proves the integral > 0.01 at the bracket ends, so this relaxation cannot pass the HKZ-certified radii (0.0058…0.1399).
  The missing ingredient is a Poisson-type small-ball bound Pr[no short vector] ≤ exp(−c·E[#short]) for the μ-random lattice
  family with fixed profile (in progress).
* **Part 60 (audited).** [poisson_smallball](research/wall1_poisson_smallball.md): for a fixed profile with uniform μ,
  conditioning on the two diagonal blocks at a cut makes the cross block independent and Haar column-wise; for suffixes of full
  row rank over Q the shifts are jointly Haar, so Pr_μ[no vector shorter than g_0] ≤ Π_v (1 − p_v) = e^{−E'} (Monte Carlo checked
  at d = 4). Factorial-moment bounds alone cannot force exponential void decay (explicit mixture counterexample). Whether E'
  captures a fixed fraction of E[N] on the bad-mass profiles is open (in progress); radii unchanged (0.005832301 … 0.139941828).
* **Part 61 (audited).** [poisson_exponent](research/wall1_poisson_exponent.md): a degree-3 Delsarte LP (spherical-code)
  bound gives block inequalities sharper than Blichfeldt at large ranks (by 3.6–6.6 nats at d ≈ 406–799), valid for every μ;
  they exclude the Part 50 relaxed-mass witness boxes and the Part 59 modal slabs entirely (zero SVP weight). Yet the certified
  radii move only to 0.005933/0.015621/0.039603/0.140798 at β = 406/506/647/800: the bad mass relocates. The A5 exponent is
  > 227 on the witness boxes (moot there). Hypothesis under test: typical lattices genuinely have BKZ-reduced bases with short
  terminal GS, capping all 'for every reduced basis' methods.
* **Part 62 (audited).** [bad_reduced_bases](research/wall1_bad_reduced_bases.md): hypothesis 'typical lattices have
  BKZ-reduced bases with short terminal GS' is open at rank 1023. At full width the minimum over reduced bases is λ_1, and
  λ_1/GSA → 1 on Haar lattices (Pr[≤ c·GSA] ≤ c^N/2). At rank 3, width 2: an open set admits two reduced bases differing by 10%
  in terminal length, yet Pr[some reduced basis ≤ 0.9·GSA] ≤ 39.3%. Exhaustive q = 47 rank-3 graph lattices (2209): 625 admit a
  basis ≤ 0.9·GSA, 48 have several terminal values, 24 have a BKZ basis strictly below every HKZ choice (independently
  brute-forced). Medium-rank experiments are in progress.
* **Part 63 (audited).** [profile_rigidity](research/wall1_profile_rigidity.md): two-sided profile rigidity of all BKZ-β
  bases is false — full HKZ bases are BKZ-β reduced for every β and (Laarhoven Prop. 3) lie ≈ ((1−a+a log a)/2)·N log N below the
  GSA prefix at k = N−β (a = β/N); deterministic Blichfeldt bounds at rank 1023 force errors ≥ 167.7 / 86.2 / 7.1 at
  β = 406/506/647 for every covolume-1 lattice. The one-sided statement 'every BKZ-β basis has g_{N−β} ≥ c·GSA' remains open (it
  depends on a difference of adjacent prefix errors); the unrestricted short-vector deficit has infinite supremum on every
  lattice, so any moment argument must use the crossing windows (in progress).
* **Part 64 (experiment, audited).** [bad_bases_experiment](research/wall1_bad_bases_experiment.md): at ranks 24–60, β = 8–20
  (q-ary and Goldstein–Mayer, exact verification), the smallest terminal GS found over fully BKZ-β reduced bases is ≈ 0.84–0.87×
  typical (depending on the baseline), always via a single local dip g_k/g_{k−1} → √3/2 with prefix covolumes almost unchanged.
  So 'every BKZ basis has g_{N−β} ≥ 1·typical' is false, while ≈ 0.8·typical is consistent with the data — the volume method's
  gap (Parts 50–61) is a weakness of the method, not of the statement (small ranks; large-N steepening not excluded).
* **Part 65 (audited, minor caveats).** [one_sided_terminal](research/wall1_one_sided_terminal.md): higher-degree
  spherical-code (Christoffel–Darboux/Gegenbauer LP) block bounds improve H_d in 867 dimensions (up to ≈ 40.7 nats near
  d ≈ 1022); with the Part 61 cap/chain-counting framework this gives, per width at 99%, g_{N−β} ≥ 0.00609 / 0.01588 / 0.03996 /
  0.14264 and g_{N−β}/R_T ≥ 0.00357 / 0.00858 / 0.01425 / 0.03307 (R_T the Gaussian radius of the terminal quotient) at
  β = 406/506/647/800, rank 1023 — still ≈ 60× below 0.85·GSA. Asymptotically (β/N → a): g_{N−β}/R_T ≥ exp[−O_a(log² N)] for all
  BKZ-β bases simultaneously, off an event of probability ≤ 2^{-N}: the terminal minimum is never exponentially below its own
  Gaussian radius.
* **Part 66 (audited, minor caveats).** [terminal_constant](research/wall1_terminal_constant.md): on Haar lattices
  (β/N → a), simultaneously over all fully BKZ-β bases with failure ≤ 2^{-N}: log(g_{N−β}/R_T) ≥ −¼ log² N − O_a(log N); the
  geometric mean of the last Θ(N) GS lengths has only a polynomial loss, and in this argument the log² loss comes from mean →
  endpoint. Obstructions: (i) worst case — Hanrot–Stehlé HKZ bases attain −¼ log² N at the terminal index with every crossing
  window enforced, so any improvement needs Haar typicality; (ii) on the Haar typical event, primitive prefixes within a factor 2
  of the GSA determinant can have quotient ratio exp[−Ω(N log N)] (−166 / −85 / −6.0 at N = 1023, widths 406/506/647) — such
  prefixes need not be BKZ-completable, so a proof must combine Haar typicality with BKZ-completability of the prefix.
* **Part 67 (audited, minor caveats).** [completable_prefixes](research/wall1_completable_prefixes.md): counting only
  BKZ-completable prefixes (unfolding over flags with exact completability consequences) drives the expected number of bad
  completable prefixes below 2^{-1023} at relative radii c = 0.00354 / 0.00850 / 0.01413 (β = 406/506/647, rank 1023), versus a
  divergent count for all primitive prefixes; but E B ∝ c^{kb}, so the radius sits at a steep break-even and essentially recovers
  Part 65. The open ingredient is unchanged: the joint acceptance probability of the overlapping windows' shortest-vector tests.
* **Part 68 (audited, minor caveats).** [covering_fraction](research/wall1_covering_fraction.md): for every column
  history, one Gram–Schmidt box gives a candidate lift for all crossing starts at once, yielding a profile-only lower bound on the
  forbidden fraction; an m = 2 correction (via the doubled torus point) is strictly positive on some profiles; the Babai
  half-diagonal exclusion adds no new constraint (it follows from adjacent windows). The exact column product certifies only
  0.00553 / 0.01338 / 0.03098 / 0.08202 (β = 406/506/647/800), weaker than Part 65. Summary of Parts 50–68: every
  'for all reduced bases' certificate at rank 1023 stays ≈ 60× below 0.85·GSA, while experiments (Part 64) suggest the true
  all-bases floor is ≈ 0.85·typical — the gap is methodological (joint acceptance of overlapping windows).
* **Part 69 (audited).** [joint_acceptance](research/wall1_joint_acceptance.md): the joint acceptance of all overlapping
  BKZ-3 window tests (fixed profile, uniform μ) has an exact one-state transfer operator for arbitrary profiles (confirmed by
  Monte Carlo, including a profile where the box product is rejected at ≈ 36σ). For g_i = r^i the Part 68 box is exact when
  1 − r⁴ ≤ r²/4; at r = 0.92, rank 8, the true probability is in [4.45, 7.49]·10⁻¹¹ versus the box's 2.70·10⁻⁸ (spectral radius
  0.017–0.032); at r = 0.90 one triple already has zero acceptance. Width-3 tests bite only at slopes ≲ 0.92, while GSA slopes at
  β ≈ 406 are ≈ 0.99, so closing the rank-1023 gap needs the asymptotics of width-β joint acceptance (or the algorithm's
  trajectory).
* **Part 70 (audited).** [window_asymptotics](research/wall1_window_asymptotics.md): a width-w geometric block with excess
  ε over the balanced ratio has E = (1+o(1))·e^{w(w−1)ε/2}/2 short pairs (6.92·10⁶ at w = 406, ε = 0.0002); a Q-independent suffix
  family scores E' ≤ min(E, w − 1), so across disjoint windows the exponential relaxation supplies ≤ N − h ≤ 1022 nats
  (≤ 511 with horizontal caps), whereas the exact product has no dimension-only cap. The 34000-nat figure was the relaxed mass
  of boxes later excluded by Part 61; the bad mass on the surviving domain is being computed.
* **Part 71 (audited).** [surviving_mass](research/wall1_surviving_mass.md): after all Part 65 deterministic block
  inequalities, the relaxed bad Haar intensity (first moment of relaxed basis counts, rank 1023) is still ≥ 2.3·10⁵–8.3·10⁵ nats
  at ρ = 0.25–0.85·GSA (e.g. [829271, 842097] at β = 406, 0.85·GSA; [230166, 253386] at β = 800, 0.25·GSA), explicit lower boxes
  verified row by row; the exponential relaxation (≤ 1022 nats) and the exact width-3 acceptance (333–490 nats on the boxes)
  are far too weak. Suppression of this size can only come from the width-β shortest-vector tests.
* **Part 72 (audited, minor caveats).** [mu_moments](research/wall1_mu_moments.md): exact factorial moments of the short
  count N for the fixed-profile μ-random block (unfolding each coefficient row over cosets of the suffix lattice; distinct last
  indices factor). The estimate E[(N)_k] ≈ E^k fails (at w = 406, excess 0.0002, E ≈ 6.92·10⁶, the log ratio at k = 20000 exceeds
  162944, from rare near-diagonal coefficient sets with ≥ 2^49 short pairs); Bonferroni parity and Chen–Stein (complete
  dependency graph) and positive association (Harris fails) are ruled out as shortcuts. On every Part 71 box one window has
  log E > 131–247, so a void bound as weak as Pr[N = 0] ≤ exp(−10^{-49}·E) would eliminate the box: **the remaining core of
  wall 1 is a dense-packing large-deviation bound for the μ-random block** (in progress).
* **Part 73 (audited, minor caveats).** [dense_packing_ld](research/wall1_dense_packing_ld.md): the full Levenshtein
  ratio with Cohn–Zhao's same-dimension packing inequality gives full-width block caps 3.6–5.7 nats below Part 65's H_b
  (129.82/159.10/200.08/244.28 vs 133.44/162.87/204.11/249.99 at b = 406/506/647/800); the Part 71 boxes saturate Part 65's H_b,
  so all twelve have zero void probability in a full-width window (deterministically). This shows the Part 65 relaxation was
  loose at d = b; feeding the bound back into Part 65's candidate list relocates the relaxed mass rather than certifying a radius.
* **Part 74 (audited; ten parallel routes on the void probability of the fixed-profile μ-random block).** Problem: bound
  Pr_μ[no vector shorter than g_0] in terms of E = E[#short] (needed on the surviving rank-1023 domain).
  Positive: [void_numerics](research/wall1_void_numerics.md) (V7) proves, for ANY profile, Pr[N=0] = Π_j (1 − e_j) ≤ e^{−E} when
  min_j g_j/g_0 ≥ √3/2, and −log Pr[N=0] ≥ Σ_{j: g_j/g_0 > 1/√2} (2g_j²/g_0² − 1)·e_j in general (bounded-overlap of lifts on a
  surviving prefix); width-3 extinction at r* = 0.898733468…; Monte Carlo up to width 30 shows −log P ≈ A·E^{≈1} (Poisson-like).
  Second-moment-type bounds (log-size suppression only): [void_affine](research/wall1_void_affine.md) (V2),
  [void_fourier](research/wall1_void_fourier.md) (V5; its per-history Fourier/Hoeffding martingale is capped at j/2 per column,
  ≤ 1.72·10⁵ nats in total at rank 1023 — an obstruction, below the residual 2.3·10⁵–8.3·10⁵),
  [void_concentration](research/wall1_void_concentration.md) (V3), [void_multiscale](research/wall1_void_multiscale.md) (V4; per-cut
  miss ≤ (1 + Σ p_v/(1−p_v))^{-1} from pairwise independence of distinct primitive directions, sharp: Θ(1/k) example).
  Obstructions: [void_janson](research/wall1_void_janson.md) (V1; restricted families capture a vanishing part of E, Suen ≤ |J|),
  [void_entropy](research/wall1_void_entropy.md) (V8; projections lose the whole exponent; overlapping-window Hölder = disjoint
  product), [void_duality](research/wall1_void_duality.md) (V9; the reversed reduced dual of a μ-uniform basis is again μ-uniform,
  but theta duality maps the void to a dual lower tail), [void_theta](research/wall1_void_theta.md) (V10; Θ_t is neither convex
  nor concave in a shear), [void_haar_transfer](research/wall1_void_haar_transfer.md) (V6; void probability is monotone under
  componentwise ratio comparison, but not ordered by E). **Common missing ingredient:** coverage of the fresh column's torus
  conditioned on prefix survival when the terminal GS ratios drop below 1/√2 (deep windows) — beyond both the probabilistic
  ceilings and the deterministic packing bounds.
* **Part 75 (audited, minor caveats).** [void_combined](research/wall1_void_combined.md): combining V7 on truncated shallow
  windows, V5 on deep columns (granting the full j/2 budget) and Part 73 caps over disjoint schedules still leaves ≥
  706153 / 720898 / 723246 (β = 406), 435237 / 451925 / 456300 (506), 225368 / 239938 / 244817 (647), 50526 / 67010 / 73211 (800)
  nats at ρ = 0.25 / 0.5 / 0.85·GSA. Probabilistic suppression on the relocated boxes is capped (≤ 6 per shallow column, ≤ j/2
  per deep column); closing wall 1 this way needs exact (deterministic) coverage of the fresh column's torus on deep windows,
  e.g. further packing certificates at the relocated boxes' widths.
* **Part 76 (audited).** [jw_slide](research/wall1_jw_slide.md): reversing and reciprocating GS lengths preserves the
  Joux–Węgrzycki decline inequality and swaps its endpoint bounds, giving a simultaneous lower envelope for the same slide output
  (the repo's slide predicate itself is not closed under dual reversal: 3-dim counterexample). For the rank-1023 null lattice
  (P > 0.996) the envelope gives g_{1023−β} ≥ 1.5·10⁻³¹ / 0.158 / 1.1·10⁻⁵⁴ / 1.2·10⁻³¹ at β = 406/506/647/800 — weaker than direct
  propagation; no width certified.
* **Part 77 (audited).** [lcz_all_widths](research/wall1_lcz_all_widths.md): Levenshtein/Cohn–Zhao block caps at every
  width (strictly better than Part 65 for d = 72..1023; exact-rational LP checks) give the best certified all-bases radii so far:
  g_{1023−β} ≥ 0.00625 / 0.01622 / 0.04068 / 0.14425 and g/R_T ≥ 0.00368 / 0.00876 / 0.01450 / 0.03344 (β = 406/506/647/800, 99%
  per width). Even with width-3 acceptance and truncated V7, the relaxed residual is ≥ 2.19·10⁵ nats (β = 800, 0.25·GSA) up to
  8.1·10⁵ (β = 406). **Status:** the best LP packing bounds and all audited probabilistic suppressions are exhausted; closing wall 1
  needs a new estimate — coverage of the fresh column's torus conditioned on prefix survival in deep windows.
* **Part 78 (audited, minor caveats).** [dual_coverage](research/wall1_dual_coverage.md): hard coverage of the fresh column's
  torus via the dual (Micciancio–Regev smoothing; the reversed dual is μ-random by V9, so its short vectors are an upper-tail
  event) fails on the relocated Part 77 boxes: no deep column reaches the Gaussian hard-coverage threshold even with the exact
  smoothing parameter (all 794 deep prefix ranks, interval-certified); exact Gaussian tails give < 2356 nats along a rank-1023
  chain, leaving > 2.17·10⁵ nats at β = 800, 0.25·GSA. Scope: height-one Gaussian test only.
* **Parts 79–81 (audited).** [multiheight_coverage](research/wall1_multiheight_coverage.md) (Part 79: joint multi-height
  coverage gives only ≈ 6.5 nats on the closest Part 77 box; complete coverage ruled out for 377375/437602 deep pairs);
  [hole_filling](research/wall1_hole_filling.md) (Part 80: a second coset at a deepest hole gives μ(D) ≤ R(F/2)^{1/j} when the
  density ratio F to a periodic-packing cap is < 2; every lattice has 2μ/R ≥ √(2j/(j+1)); with Part 77 caps the hard test misses
  by 0.34 nat); [hole_filling2](research/wall1_hole_filling2.md) (Part 81: with the rigorous Cohn–Elkies cap (Table 3, exact
  rational arithmetic + Sturm), a rank-33 tail window of every Part 77 box exceeds the packing cap by > 0.127 nat, so those
  boxes are excluded outright — Part 77 used Blichfeldt at small d).
* **Part 82 (audited, minor caveats).** [small_d_caps](research/wall1_small_d_caps.md): rigorous small-dimensional packing caps
  (three-point bounds d = 4–16, Cohn–Elkies LP d = 17–72, Leech/E8 optima, exact Hermite for lattice windows) plus LCZ give the
  best certified all-bases radii: g_{1023−β} ≥ 0.00654 / 0.01697 / 0.04256 / 0.15090 and g/R_T ≥ 0.00385 / 0.00917 / 0.01517 /
  0.03498 (β = 406/506/647/800, 99% per width). The relaxed bad mass relocates again (W2 kills the first replacement boxes; a
  second relocation evades every hard exclusion) and the residual stays ≥ 2.18·10⁵ nats. **Pattern:** each stronger
  deterministic exclusion kills specific boxes but the relaxed mass relocates with an essentially unchanged residual; closing
  wall 1 needs a genuinely new estimate (conditioned deep-window coverage), not more caps.
* **Part 83 (audited, minor caveats).** [basis_multiplicity](research/wall1_basis_multiplicity.md): the relaxed residual is
  partly basis multiplicity — for exact BKZ with fixed width the Haar mean number of reduced bases grows like e^{Θ_β(n³)}
  (width-2 means certified through rank 10; full width: one basis a.s.); counting each eligible primitive prefix once lowers the
  quarter-GSA log mean at width 800 to ≤ 152955 (vs Part 82's weighted 218002), the mean number of profile-bad completions per
  prefix exceeding e^{70921}. Consistent with Part 67 (different radii; counts are extremely steep in ρ). Audit side finding:
  the single-cut chain [0, k, k+1, n] (no piece-size limit is needed for the counting identity) would raise the width-406
  absolute radius from 0.00654 to ≈ 0.0076 (bisection check, to be certified).
* **Parts 84–85 (audited, minor caveats).** [prefix_level](research/wall1_prefix_level.md) (Part 84, Z1): counting distinct
  BKZ-completable prefixes once (Schmidt-normalized unfolding; T = L/W with its exact Haar law; HKZ-by-truncation caps incl.
  Korkin–Zolotarev and Pendavingh–van Zwam rank-3/5 inequalities) gives, jointly at 99% per width, g_{1023−β} ≥ 0.00788 / 0.01754
  / 0.04395 / 0.15577 and g/R_T ≥ 0.00585 / 0.00949 / 0.01567 / 0.03611 (β = 406/506/647/800) — the best single-sided
  all-bases radii (21–47× below 0.85·GSA). [canonical_bad_basis](research/wall1_canonical_bad_basis.md) (Part 85, Z2): local
  canonicalization cannot separate bad flags (window endpoints fix internal HKZ flags on generic lattices); rank-(k+1) prefix
  counting gives 0.00766 / 0.01704 at β = 406/506 (superseded by Part 84).
* **Part 86 (audited; significant).** [dual_pinning](research/wall1_dual_pinning.md): bounding the rank-(k+1) prefix
  covolume from the DUAL side. For bases reduced by Micciancio–Walter self-dual BKZ (Definition 1, produced by their Algorithm 1),
  on Haar lattices of rank 1023 with probability ≥ 99%: **g_{1023−β} ≥ 0.1266 at β = 406 and ≥ 0.3655 at β = 506** — ≈ 19–21×
  better than the best all-BKZ-bases bound (Part 84) and ≈ 34% / 45% of 0.85·GSA. Under Definition 1 no uniform bound exists at
  β = 647 / 800 (k < β − 1 allows in-block changes with g_k → 0). Under the stronger 'primal and reversed dual both fully
  BKZ-reduced' predicate the bounds are 0.1266 / 0.3655 / 0.5897 / 1.0181, but that predicate may be empty on typical lattices.
  Deterministically (Part 48 event), width 985 under the stronger predicate.
  *Qualification:* MW prove Definition 1 only when Algorithm 1's stabilization test fires (left open in their paper), so
  the bound applies to bases satisfying Definition 1. Survey: [literature3](research/wall1_literature3.md) (Kelmer's
  mean-square theorem over random triangular coefficients matches the open void lemma's setting; Li–Walter generalized slide
  reduces widths 406/506 at rank 1023 to two blocks).
* **Part 87 (audited, minor caveats).** [selfdual_extend](research/wall1_selfdual_extend.md): under MW Definition 1 no width in
  300..512 reaches 0.85·G_β (best 0.38627 at 512; relative bounds g/R_T = 0.0939 / 0.1972 / 0.2047 at 406/506/512). A new
  terminal-block reducer variant (provably terminating; each continuing step lowers the rank-k prefix covolume by a fixed factor,
  with a uniform LLL-based lower bound, so polynomially many rank-≤β SVP calls in the oracle model) always outputs a basis whose
  terminal head is the true quotient minimum and whose dual annihilator passes an SVP test; on Haar lattices of rank 1023 this
  gives g_{1023−β} ≥ 0.58986 (β = 647) and 1.01835 (β = 800) at 99% — the predicate is never empty. Scope: only the terminal block is
  controlled (the first k columns are unreduced).
* **Part 88 (audited, minor caveats).** [li_walter](research/wall1_li_walter.md): the provably terminating generalized slide
  reduction (ALNS20 / Li–Walter; no MW stabilization assumption) at rank 1023 has exactly two blocks for β = 406, 506; its output's
  twin tests force a small terminal head to give a small rank-(k+1) prefix determinant, so on Haar lattices w.p. ≥ 99% the
  terminal minimum is ≥ 0.12531 (β = 406) and ≥ 0.36189 (β = 506) with 1% slack (0.12657 / 0.36551 at exact twin quality) —
  34% / 45% of 0.85·GSA, now for a terminating algorithm.
* **Part 89 (audited, minor caveats).** [twin_qary](research/wall1_twin_qary.md): Part 88 transferred to the actual q-ary
  lattice L_0 of (511, 512, 3329) with no Haar or GSA input — an exact q-ary first moment of primitive rank-(k+1) sublattices below
  the twin cap (rigorous graph-chart height count with explicit constants; every modular-rank deficiency stratum included) is
  < 0.01, so w.p. ≥ 99% every output of the terminating generalized slide reduction (1% twin slack, exact terminal SVP) has
  terminal projected minimum ≥ 2.964 (β = 406) and ≥ 6.837 (β = 506) in physical units (normalized 0.0516 / 0.1190; 41% / 33% of
  the Haar values). Caveats of Part 88 (Hermite value in η, LLL pre-pass) apply. Not yet sufficient for the planted lifting.
* **Part 90 (audited, minor caveats).** [selfdual_sharpen](research/wall1_selfdual_sharpen.md): Markov on the count of distinct
  primitive extensions admitting a passing basis cannot beat Part 88's radius by more than 4·10⁻¹² (relative; a second-moment
  lower bound on that specific count — other first-moment objects, e.g. canonical selections or weighted counts, are not ruled
  out). Multi-block twin chains are worse (27.6% of 0.85·G at β = 341, 18.6% at β = 255); within two blocks the fraction rises to
  45.3% at β = 511. The residual 2–3× gap comes from the worst-case Hermite factors in the twin tests.
* **Part 91 (audited).** [twin_typical](research/wall1_twin_typical.md), [twin_weighted](research/wall1_twin_weighted.md):
  two further first-moment objects fail. Counting pairs B ⊂ P (first b-window inside the passing extension) gives an infinite
  mean for every cutoff: each passing P carries infinitely many primitive B with λ_1(B) fixed and det B → ∞, on a set of positive
  Haar measure; counting each P once recovers Part 90 (0.12656786 / 0.36551260). Selecting the extension of globally least
  determinant does help strictly, but only by a relative e^-584 (β = 406) / e^-734 (β = 506), and the full one-hyperplane exchange
  test can improve Part 88's radius by at most e^-170. Canonical selection is therefore not where the 2–3× gap comes from.
* **Part 92 (audited, minor caveats).** [qary_gap](research/wall1_qary_gap.md): on the actual q-ary L_0 of (511, 512, 3329),
  any sufficiently small passing extension forces a short vector in the ambient dual qL_A^*. A single width-independent event
  (λ1 > T, probability > 99%, thin margin) then gives normalized terminal radius 0.05852472 at β = 406 and 0.12909231 at β = 506,
  jointly and for every twin-passing basis (46.70% / 35.67% of Haar; Part 89 had 0.05157150 / 0.11896865). The deepest defect is
  exactly the stratum where the extension's saturation contains the graph code; an explicit twin-passing basis realizes terminal
  minimum 1.
* **Part 93 (audited, minor caveats).** [combined_reducer](research/wall1_combined_reducer.md): a width curve over 342–900 for the
  certified terminal fraction of 0.85·G. The best values are 45.32% at β = 511 (two-block slide) and 45.44% at β = 512 (terminal
  variant; Part 87's MW certificate gives 0.38627 there). For widths ≥ 512, a combined primal+dual reducer (one extra SVP call)
  exists and terminates but admits exactly the same extensions, so it gives no gain at 647/800. Narrow widths are unresolved.
* **Part 94 (audited, minor caveats).** [threshold](research/wall1_threshold.md): this part recalibrates the target. In the
  final projected block (horizontal slice H of rank β−1, plant image (y, 1)), uniqueness of the plant image up to sign holds iff
  λ1(H) > R, the open-Voronoi condition holds at height 1, and dist(ky, H)² > R² − k² for 2 ≤ k ≤ R. Given only the plant norm,
  the sharp sufficient cutoff on λ1(H) is T(R) ≈ R². That is ~35× / ~19× of 0.85·GSA at 406 / 506 and about 255× / 142× the
  Part 92 bound, and it never drops below 0.85·GSA at any width up to 1023. A tail-GS profile cutoff (√((1+2d)(1+a²))) drops
  below it only from width 892. So terminal-length bounds alone cannot certify uniqueness below 647. The missing input is
  distributional control of the coset distances dist(ky, H), using independence of u (Part 47).
* **Part 95 (audited, minor caveats).** [hkz_terminal](research/wall1_hkz_terminal.md): HKZ-reducing only the last t columns
  cannot improve Part 88, because a free intermediate prefix can make the last height arbitrarily small. Completing the
  intermediate prefix by recursive dual SVP (≤ 60 exact calls, all in dimension < β) bounds all 60 tail heights at once. Jointly
  at both widths, with probability > 99%, the fractions of row-specific 0.85·GSA are: block head 33.94% / 44.33%, literal last
  height 52.00% / 61.76% (deterministic for this completion). On the q-ary ensemble the heads are 15.85% / 15.81%. No GSA slope
  follows.
* **Part 96 (audited, minor caveats).** [rankin_twin](research/wall1_rankin_twin.md): the Part 88 twin determinant cap is sharp
  (an orthogonal basis attains it), so Rankin or Minkowski inequalities cannot improve it. Stronger predicates do improve it, but
  each needs rank-617 / 517 conditions above β:
  * a minimum-area plane test gives 0.2626 at 406, up from 0.1257;
  * exact SVP on both twin blocks gives 0.2819 / 0.3781.

  Ceilings for the uniform-cap Markov method with exact twins are 0.3850 / 0.5184. That excludes the 0.85·GSA target at 506 and
  leaves 406 open.
* **Part 97 (audited, minor caveats).** [dist_unique](research/wall1_dist_unique.md): distributional uniqueness for a fixed
  horizontal slice H with independent CBD(3) plant, via a CBD-weighted dual theta bound and finite primal shell counts. At d = 406
  the certified determinant root (3.099) fails already at k = 2. At d = 506 the root (7.259) clears the benchmark 5.806, and two
  inputs remain open:
  * a bound F_k ≤ 10⁴⁹ on the CBD-weighted dual sums at heights 2..31;
  * actual λ1(H) > 24.66 (necessary, Paley–Zygmund). Only 7.42 is certified (Part 92).
* **Part 98 (audited, minor caveats).** [hermite_caps](research/wall1_hermite_caps.md): certified enlarged-ball LP Hermite
  caps at every rank 400–511, each at least 0.727 nats below Part 86 (γ_406 ≤ 45.6963, γ_506 ≤ 56.2142). The Part 88
  exact-twin radius rises only to 0.126915 / 0.366057 (34.38% / 44.84% of 0.85·GSA), or 0.125656 / 0.362426 with 1% slack.
  Sharper Hermite caps therefore do not close the gap.
* **Part 99 (audited).** [theta_heights](research/wall1_theta_heights.md): for heights k = 2..31, the CBD-weighted dual sum
  F_k is < 3 + A_k. Here A_k is a finite weighted count of nonintegral dual vectors of physical length < 10. Exact aliases
  (< 1.014·10⁻¹³) and the tail (< 10⁻⁵⁰⁷) are harmless. Each nonintegral residue has weight < 0.587 (Part 92 event). The
  ceilings A_k ≤ 10⁴⁸ / 10⁴⁹ (rank 505 / 506) would give higher-height failure < 0.004 / 0.0021. Still open: multiplicity
  control of A_k, height one, and λ1(H) > 24.66.
* **Part 100 (audited).** [residue_count](research/wall1_residue_count.md): the Part 99 budget cannot be met by summing over the
  whole ambient dual. For every A the height-2 ambient weighted count exceeds 10^257. Prefixes engineered for the cosine weight
  alone reach > 10^101 inside H*, but they do not pass the reduction tests. Open: the heat-weighted count inside H* for prefixes
  that do pass the width-506 tests. Part 92's minimum event is sharpened to > 99.5888%.
* **Part 101 (audited, minor caveats).** [qary_rogers](research/wall1_qary_rogers.md): an exact mixed modular counting
  identity over uniform A gives a weighted count of short ambient dual vectors. One Markov event then bounds every
  annihilator's determinant. At horizontal width 506, the certified head minimum rises from 7.4188 to 8.1466 physical
  (8.1588 = 0.14197 normalized with the sharpened universal twin cap), with design probability ≥ 0.990001. A width curve covers
  450–647. The necessary height-zero floor sharpens to 27.4810 (Cantelli). The remaining factor is ≈ 3.4.
* **Part 102 (audited).** [voronoi_height1](research/wall1_voronoi_height1.md): two sufficient conditions keep height-one
  failure below 0.0025 at ranks 505 and 506. The first is λ1(H) ≥ 24.66 together with a full GS floor of 9 (failure < 0.00176).
  The second is λ1(H) ≥ 61.3 alone (failure < 0.00207). The height-zero floor alone is not enough: a fixed lattice with minimum
  above 25 and arbitrarily large covolume has CBD height-one failure > 70%. For the actual q-ary quotient, height one remains
  open.
* **Part 103 (audited after correction).** [width_scan](research/wall1_width_scan.md):
  * **Necessary floor.** The Cantelli height-zero floor for 99% conditional success is √(1 + 1.5d − √(4.5d/99)), d = β − 1,
    which is 27.4538 at β = 506.
  * **Probability.** Part 101's design guarantee 0.990001 leaves ≤ 1/990001 for all conditional plant failures.
  * **Width scan.** Extended to width 1020, Part 101's certified q-ary minimum first exceeds the height-zero floor at final rank
    955. The profile-free height-one condition is first met at final rank 999.
  * **Conclusion.** The current terminal-minimum certificates give no improvement over Part 39's dimension 647 (10.62 vs 31.06
    at 647). Beating 647 needs distributional control of the selected block itself.
* **Part 104 (audited; four earlier notes).**
  * [markov_reducer](research/wall1_markov_reducer.md): for the one-pass shortest-in-block chain, the infimum of the terminal 1%
    quantile over unrestricted fresh-basis selectors is 0 (by choosing the penultimate basis). Every fixed selector has a
    positive quantile.
  * [smoothed](research/wall1_smoothed.md) (appendix): a vector common to all graph lattices forces near-one TV distance to Haar
    for any small perturbation.
  * [list_success](research/wall1_list_success.md): an exact signed competitor count conditional on the prefix. CBD
    independence gives no uniform torus translate.
  * [selfdual_qary](research/wall1_selfdual_qary.md): an exact finite first moment of primitive sublattices in the graph
    ensemble. It needs height-stratified plane counts to evaluate.
* **Part 105 (audited).** [selection_law](research/wall1_selection_law.md): the first direct result on the output law of one SVP
  step. For a Haar block of rank b, the projected shape conditional on λ1 = GH_b has density ≤ 2 with respect to Haar.
  Unconditionally, Pr[normalized quotient minimum < 0.925·GH_{b−1}] < 0.0234% at b = 406 and < 0.0063% at b = 506. Tour-level
  chaining is open: the law of the appended column given the history is missing.
* **Part 106 (audited).** [chain_law](research/wall1_chain_law.md): Part 105 cannot be chained uniformly over selectors. A
  rotation-equivariant fresh-basis selector forces the terminal minimum below any fraction of its own GH, at ranks b and b − 1,
  on every parent. So there is no selector-uniform density bound and no selector-independent terminal certificate. A proof must
  use the concrete reducer's inherited sliding window.
* **Part 107 (audited, minor caveats).** [lit_random_bases](research/wall1_lit_random_bases.md): a literature survey of rigorous
  random-reduced-basis results (Kim–Venkatesh, Li–Nguyen, HPS, Nguyen–Stehlé, Bai–Stehlé–Wen, Södergren, Strömbergsson). It
  adds two finite-rank facts. At Haar rank 1000, λ1 ∈ [0.99540, 1.00601]·GH with probability ≥ 99%. After projecting off the
  global shortest vector, the rank-999 quotient minimum is within 2% of its own GH with probability > 99.499%. No checked source
  gives a 99% bound for the final block of finite-width BKZ, because window selection is not global selection.
* **Part 108 (audited).** [first_tour](research/wall1_first_tour.md): an exact law for the first BKZ pass on the q-ary basis
  (qI first, no lookahead, lexicographic ties). Each unread graph column has perpendicular height 1. Given the history, its
  displacement is uniform on a finite subgroup H of the retained torus, updated by H' = Q_*H. This gives an exact finite
  recursion. A simultaneous whole-tour 99% guarantee is impossible above 0.2036 (b = 406) / 0.1826 (b = 506), because of the
  cubic initial window. The deterministic floor is 2.76·10⁻³⁷. Terminal-only thresholds are open (BG).
* **Lean (Nov 2026).** SigabaNeo/Lib/Lattices/Research/Wall1/HaarMinimumTails.lean is built and axiom-clean:
  * `count_hit_bounds`: m/(1+m) ≤ P(M>0) ≤ m, given E[M(M−1)] ≤ m²;
  * `primitiveBallPairs_mean`: the Haar mean of primitive sign pairs in a ball is t/(2ζ(n));
  * `primitiveBallPairs_hit_upper`;
  * `independentBallPairs_mean`: the Haar mean of independent ordered pairs is t².

  HaarMinimumLower.lean is also built and axiom-clean. It closes the lower tail:
  * `primitiveIndependentPairs_mean` = vol²/ζ(n)², via divisibility π-systems;
  * `primitiveBallPairs_secondMoment`: E[M²] = m + m²;
  * `primitiveBallPairs_hit_lower`: Pr[M>0] ≥ m/(1+m).

  Together with `primitiveBallPairs_hit_upper`, this gives the two-sided Haar λ1 window of Part 107 (i) in Lean.

  UniquenessCriterion.lean (`allHeightsUniquenessCriterion`) formalizes the exact all-heights criterion of Part 94 for any
  additive subgroup of a normed group. It is accepted on Prove2Me.
  FreshDisplacement.lean (`fiber_card`, `uniform_image`, `conditional_image`) formalizes the counting core of Part 108's
  fresh-column uniformity: a homomorphic image of a uniform fresh column, given any prefix history, is uniform on its range.
  It is accepted on Prove2Me.
  CBDTail.lean (`cosh_six_le`, `coordinate_mgf`, `product_mgf_le`, `lower_tail`, `half_energy_tail`) formalizes the CBD(3)
  sub-Gaussian tail used per vector in Parts 97 and 102. It is accepted on Prove2Me.
  QaryMembership.lean (`dual_fixed`, `kernel_fixed`, `dual_counts`, `kernel_counts`) proves that a fixed vector with a nonzero
  residue lies in the q-ary dual or kernel lattice for exactly a q^{−n} (resp. q^{−m}) fraction of A. It also proves the first
  moment and the hit bounds, halved under ± symmetry, used in Part 92. It is accepted on Prove2Me.
  CBDQuadratic.lean proves the CBD(3) moments (0, 3/2, 6, odd moments 0), E[XᵀQX] = (3/2)·tr Q, the exact variance, the bound
  Var ≤ (9/2)·tr Q for projections, and Cantelli. These are the ingredients of the height-zero necessary floor (Parts 94/103).
  All ten theorems are accepted on Prove2Me.
  HeightZeroFloor.lean (`heightZeroFloor`) combines the uniqueness criterion with Cantelli. Take a fixed projection Q of
  trace d and a fixed subgroup H. If H has a nonzero h with ‖h‖² ≤ 1 + (3/2)d − √((9/2)d/99), then the CBD(3) probability of
  all-heights uniqueness is ≤ 99/100. This is the necessary floor of Parts 94/103, end to end in Lean, and it is accepted on
  Prove2Me.
  NormOnlyCertificate.lean (`allHeightsUnique_of_normOnly`, `allHeightsUnique_of_normSq`) proves the matching sufficient side
  (Part 94). If every nonzero h ∈ H satisfies ‖h‖ > k‖y‖ + √(R² − k²), or simply ‖h‖ > R², then all-heights uniqueness holds.
  Both are accepted on Prove2Me.
  SelectionLaw.lean (`shortest_projection_gap`, `haar_short_vector_upper`) formalizes two pieces of Part 105. The first is the
  √3/2 projection gap after removing a shortest vector. The second is the Haar bound Pr[λ1 < r] ≤ V_n·r^n/(2ζ(n)). Both are
  accepted on Prove2Me. The void-probability inequality and the selected-quotient law remain open in Lean.
* **Part 109 (audited, minor caveats).** [terminal_mixing](research/wall1_terminal_mixing.md): every first-tour path satisfies
  the deterministic terminal floors 6.5·10⁻⁸ (b = 406) / 3.3·10⁻⁸ (b = 506) × own GH. History-uniform mixing is impossible:
  reachable histories (probability q^{−Θ(b·n)}) force terminal ratios < 0.21 with 1 draw left, and < 0.73 / 0.51 with 64 draws
  left. The unconditional 1% quantile requires averaging over histories (BH).
* **Part 110 (audited).** [additive_tour](research/wall1_additive_tour.md): an additive recursion over the first tour fails.
  The propagated threshold contracts by √3/2 per projection even with zero fresh-layer charges. The exact averaged layer count
  #(L_k ∩ B)/|kH| is valid but cannot rescue it. Tracking the final subunit run gives zero-failure floors of
  8.7·10⁻⁶ / 5.3·10⁻⁶ × own GH. Diagnosis: short terminal vectors trace back to earlier window vectors longer than GH, where
  counting is powerless. A tool that captures the conditioning effect of the SVP selections is missing.
* **Part 111 (audited).** [hecke_gap](research/wall1_hecke_gap.md): the full-torsion append is, up to < 1/q, an index-q Hecke
  correspondence. Its mean-zero norm is ≤ 2√q/(q+1) < 0.0347 (Clozel–Oh–Ullmo, d ≥ 3). An L²(Haar) iteration still fails, for
  two reasons. Every appended window has parallel primal and dual vectors, which is a Haar-null condition. From the cubic start
  the retained shape law is finitely supported, so no density exists. The terminal floors are unchanged.
* **Summary of the direct output-law program (Parts 105–111).** The one-step selection law is near-Haar (Part 105), and the
  first-tour law is an exact finite recursion (Part 108). Chaining fails in every form tried: selector-uniform (Part 106),
  worst-case/additive (Parts 109–110), and spectral/L² (Part 111). The best pathwise floor is ≈ 10⁻⁵ × own GH, against the
  ≈ 0.9 needed. A tool for the conditioning effect of the SVP selections on discrete laws is missing.
* **Part 112 (audited).** [void_monotone](research/wall1_void_monotone.md): SVP void conditioning is not negatively
  associated. In a rank-4 window, conditioning on a primitive mark being shortest raises the expected short quotient pairs from
  9/4 to 4. Conditioning on a reachable history raises the next-window hit probability from 5^{−2(b−1)} to 5^{−(b−1)}. Both
  were verified by exact enumeration. FKG/Harris-type chaining is ruled out.
* **Part 113 (audited).** [idea_coupling](research/wall1_idea_coupling.md): replacing the finite displacement by continuous
  torus noise changes a terminal window hit only on a shell event, and a first moment bounds its probability. Exhaustive tests
  in ranks 2–5 show that windows keep history dependence even with full torsion. In rank 4 every coupling to a fresh cubic
  restart disagrees on ≥ 88/729. No improved terminal floor follows.
* **Part 114 (audited, minor caveats).** [idea_drift](research/wall1_idea_drift.md): in Part 108's first pass the retained
  log-determinant obeys the exact recurrence D_t = D_{t−1}/s_t. With the Part 98 Hermite caps, at b = 506 the rank-505 retained
  lattice has GH radius ≥ 28.8095 on every history. So the height-zero necessary floor 27.4538 is met as soon as the terminal
  minimum is ≥ 0.954 × its own GH. The target becomes a relative ratio, comparable with Part 105 (0.925, 99.98%) and Part 107
  (±2%). At b = 406 the first pass cannot reach the floor even with zero error (15.50 < 24.58). The probability of the 0.954
  ratio is open. Upper SVP bounds plus a fixed determinant cannot force a terminal minimum.
* **Part 115 (audited, minor caveats).** [idea_variants](research/wall1_idea_variants.md): a simultaneous Haar flag bound
  (Kim's unfolding). At final width 506, outside probability 0.005, every primitive prefix K with det K ≤ T yields a rank-505
  quotient with λ1 ≥ 0.9 × its own GH. Adaptive selection is covered. The reducer must still land on such a prefix, and that is
  open. Dual-section constants of 0.986 / 0.989 hold in the section metric only. A coordinate restart on the graph ensemble
  gives a cubic quotient.
* **Part 116 (audited).** [flag_prefix](research/wall1_flag_prefix.md): Part 114's deterministic prefix-determinant cap is far
  too weak for Part 115. At 506, log T = 1207.55, but 0.954·GH needs log T ≤ 547.80. For every A, some primitive prefix under the
  cap has quotient minimum < 10⁻¹⁷⁶. So no claim that holds simultaneously over all capped prefixes can work. Only the selected
  prefix (or a random, typical cap) can.
* **Part 117 (audited).** [idea_round2](research/wall1_idea_round2.md): with probability > 0.99977696, the first 105 graph
  steps of the first pass freeze prescribed axes. The rest of the pass then couples exactly to a fresh uniform 400×105 graph, so
  a 99% terminal guarantee needs suffix failure ≤ 0.00977696. A random typical cap cannot rescue Part 115: it would need SVP
  lengths averaging < 0.154 × own GH. Symmetrization, entropy, a plane sieve and multiscale were triaged as not closing the gap.
* **Part 118 (audited, minor caveats).** [lit_projections](research/wall1_lit_projections.md): a second literature survey,
  focused on projections and sections of random lattices: Schmidt, Kim flags, Horesh–Karasik, Aka–Einsiedler–Shapira,
  Aka–Musso–Wieser, EMSS and its effective versions, COU, Benoist–Oh, Strömbergsson, Alam–Ghosh–Han, Laarhoven, Ducas–Loyer.
  None bounds an adaptively selected projected minimum. For a prescribed rational projection the finite-field law is exact. The
  open obligation is exactly the selection-weighted sum p_suffix ≤ 0.00977696 left by Part 117.
* **Part 119 (audited, minor caveats; empirical).** [experiments](research/wall1_experiments.md): an exact implementation of
  Part 108's first pass, run 10,240 times at small parameters. Empirically, at n = 8, q = 17, the 1st percentile of the terminal
  ratio is 1.139 at width 4, 0.926 at width 10, and 0.930–0.940 at widths up to 20. Short final selections accompany low ratios,
  and subgroup deficiency does not predict them. Proved: for fixed n, q, the terminal ratio → V_d^{1/d}·q^{n/d} → 0 as the width
  grows, because the cubic structure persists. A sufficient condition via short planes through the final selected line is
  given. Its expected-count estimate is open.
* **Part 120 (audited).** [plane_count](research/wall1_plane_count.md): the remaining obligation is split at the last step.
  The horizontal failure is exactly Pr[old shortest line wins] × 1{it lies in an old plane of area < A}. The positive-height
  failure has an exact fiber-retaining first moment. At width 506 every witness has area < 1.04144·GH(W)². It now suffices to
  bound two history averages, the horizontal failure and the positive-height moment, by 0.00488848 each. Plane counts at a fixed
  area cutoff do not propagate (a scaled D_3 example), so the induction for these averages is open.
* **Part 121 (audited).** [global_quotient](research/wall1_global_quotient.md): Part 120's horizontal term involves the
  global-selection statistic ψ(Λ) = λ1(π_{x_0}Λ)/GH. However, (λ1/GH, ψ) does not determine the next ψ: an explicit
  rectangular counterexample with equal determinant and subgroup gives different next values. Horizontal witnesses can need one
  more old direction per step (rank 408 over the width-506 suffix), and fixed-depth hierarchies fail on the general state space.
  Small exact runs (evidence only) show depth ≤ 1 in 1,280 designated planes.
* **Part 122 (audited).** [depth_truncation](research/wall1_depth_truncation.md): the depth of horizontal chains has a
  block-start product bound ∏(1 − p_j), but it must be averaged: a reachable width-506 past has depth exactly 103 with a bad
  terminal plane. Truncating at depth K leaves old kernels of rank ≤ K+2, and their number under the late-state law is
  uncontrolled even at depth 0. Diagnosis of Parts 105–122: every route needs short-sublattice statistics of the old retained
  lattice, which is the law being sought.
* **Part 123 (audited, minor caveats; empirical).** [experiments2](research/wall1_experiments2.md): proportional-width exact
  first passes (m = n − 1, b = n − 6, 8,816 runs, three primes). At q = 3329 the conservative ratio target 0.954 fails in
  7/512 runs at n = 30 and 3/48 at n = 36. The PHYSICAL height-zero floor fails in 389/512, 187/512, 36/512 and 2/512 runs at
  n = 10, 12, 14, 16, and in 0 runs at every n from 20 to 36 (0/48 at 36). This is empirical support for the necessary
  condition in the proportional regime. It is not a proof, and the floor is only necessary.
* **Part 124 (audited).** [moment_closure](research/wall1_moment_closure.md): an averaged sublattice-moment class compared
  with Haar at every rank and every cutoff fails before the suffix starts. Zero restart columns give unit lines, a factor
  10^375 above Haar at cutoffs near 1. The linear unmarked recursion amplifies by ≥ q^504 per step. On the relevant GH band,
  however, the restart comparison is benign: the rank-1 ratio is < 5.803 for 0.954·GH ≤ x ≤ q. Propagating a GH-band comparison
  through the suffix is open.
* **Part 125 (audited, minor caveats).** [annealed_selection](research/wall1_annealed_selection.md): forced SVP inequalities on
  subunit runs give a restart floor of 2.78·10⁻⁷ × own GH, weaker than Part 110's pathwise 5.21·10⁻⁶. At the 0.954 target a
  terminal witness can first appear in the last window, with a winner up to 1.096607 × window GH. The selection-weighted finite
  probability (Part 118) remains the obligation.
* **Part 126 (audited, minor caveats).** [band_moments](research/wall1_band_moments.md): three relaxations of the GH-band
  moment propagation lose too much:
  * killing sub-band restarts costs only 1.4·10⁻¹⁰, but a single q-axis then carries weight 10^{279.7};
  * marking winner incidence through rank 2 leaves a rank-3 Haar mean 10^{45.2} times the budget;
  * a scalar physical-floor recursion drops below 27.4538 at step 34 of 407.

  The exact marked recursion with history-averaged incidence remains the only open route (cf. Part 122).
* **Part 127 (audited, minor caveats).** [adjacent_methods](research/wall1_adjacent_methods.md): a survey of rigorous
  greedy/adaptive analyses outside lattice cryptography: Vallée–Vera Gauss dynamics, Daudé–Vallée LLL, deferred decisions
  (Achlioptas), revealment (OSSS), Wormald, stochastic approximation, packing, Grassmann walks, Poisson limits. None supplies the
  history-averaged bound. Exact limitation: a fixed coprime-height mark determines the fresh displacement, so any gain must come
  from excluding witnesses or earlier histories. A two-winner rank-3 survival test is proposed and is unverified.
* **Part 128 (audited, minor caveats).** [two_winner](research/wall1_two_winner.md): the two-winner rank-3 survival test is a
  valid conditional upper bound. It is nearly tight at b = n = 3 (0.4608 vs 0.4168), but ≥ 1 at b = 4, n = 10. After averaging
  the two fresh draws, a survival-weighted count of old incident flags remains, so it gives only the trivial bound 1 at width 506.
* **Status of the direct output-law program after Parts 105–128.** About twenty routes were tried; all reduce to
  history-averaged short-sublattice statistics of the old retained lattice under greedy SVP selection. Established:
  * an exact first-pass recursion (108);
  * the one-step law (105);
  * the reductions to the ratio target (114), a 105-step freeze (117) and a last-step split (120);
  * empirical satisfaction of the physical floor for n ≥ 20 (123);
  * Lean formalizations of the uniqueness criterion, the necessary and sufficient certificates, CBD tails and moments, q-ary
    membership, and Haar λ1 tails.

  The core probability estimate is an open problem beyond current tools.
* **Part 129 (audited, minor caveats).** [idea_round3](research/wall1_idea_round3.md): five designs for separating
  adaptivity from the final block's randomness: deferred columns, random deletion, split rows, dual selection, independent
  pilot.
  * Deferring 466–505 fresh columns provably fails height zero at 506: a subset-sum collision gives a horizontal vector of
    length < 23.
  * Deferring 256 columns gives an exact conditional first moment for fresh competitors (R < q). It leaves the rank-249 old
    part's minimum and counts open.
  * None of the five gives a 99% certificate.
* **Frontier after Parts 1–129 (Nov 2026).** Rigorous today for plain LWE (511, 512, 3329), CBD(3): one exact SVP call in
  dimension 662 (1 − 2^-64) or 647 (99%) suffices (Part 39, in Lean), with no proven cost for that call (the prescribed
  provable sieve fails on these integral lattices, even with an irrational height). Ruled out as routes to β < 647:
  reducedness/flag/monotonicity/symmetrization arguments (Parts 30–37), A-independent or low-cardinality prefix families
  (Part 40, ≥ 2^679 planes needed at 406), union bounds over all bounded-covolume sublattices (Part 41, fails for β ≤ 1007)
  and over profile-admissible prefixes (Parts 42–43, mean > 2^163 at 647); the q-ary Z-shape only re-derives Part 39 (Part 44);
  randomized near-shortest selection keeps the profile but not the selection law (Part 45); exact Haar prefix laws exist but
  are quantitatively useless at finite width (Part 46). Any proof at the estimator's β ≈ 406 must analyse the concrete
  reducer's output distribution — an open research problem.
* Open, and the core of wall 1:
  * the law of the adaptively reduced prefix (after BKZ) — the only remaining route;
  * the projection bound for the planted vector under that law;
  * the resulting provable block size and cost for Kyber.

## Wall 2: the sieve on BKZ-produced blocks (in progress)

* **Necessary condition for a smoothing invariant (new; [research/wall2.md](research/wall2.md)).**
  Take a determinant-one block of dimension `d` with a nonzero dual vector of length `1/T`. For
  every index-`p` sublattice, smoothing at width `R` after normalization requires
  `p ≥ ((T/R)·√(log(2/ε)/π))^d`. The dual vector survives every sublattice, and it and its
  negative alone contribute `2·exp(−πR²p^{2/d}/T²)` to the dual Gaussian mass. Skewed blocks
  therefore defeat every index cap based on dimension and determinant alone.
* Lean: `Wall2.dualPair_exceeds`, the scalar Gaussian inequality. The lattice argument and the
  index bound are on paper.
* **Fixed coordinate blocks are fine (new; [research/wall2b.md](research/wall2b.md)).** For a fixed
  coordinate block of dimension `d` in either i.i.d. `q`-ary ensemble, the normalized dual
  satisfies `Pr[λ₁(D) ≤ δ^{1/d}/3] ≤ δ`. At the Gaussian-heuristic radius the expected dual
  Gaussian mass is `e^{−Ω(d)}`, so index `p = 1` suffices w.h.p.: before BKZ, the obstruction above
  does not occur. A zero-plant example shows that unrestricted `q` can force a superpolynomial
  reciprocal dual minimum. Lean: `Wall2.incidenceTail` (finite incidence inequality); the
  applications are on paper.
* **Simultaneous statistics fail (audited; [research/wall2_simultaneous.md](research/wall2_simultaneous.md)).** For Haar
  lattices at `n = 700`, `b ∈ {100, 200, 400}`, the expected number of terminal prefixes below the GSA cutoff violating S1
  exceeds `2^{141599}` (mostly from the prefix count itself); interior blocks admit S1-violating continuations when the
  continuation determinant is unrestricted. A first-moment, all-blocks argument cannot certify the sieve on BKZ blocks.
* Open: blocks chosen adaptively by BKZ (this reduces to wall 1).

## A route around walls 1 and 2: the full-dimension sieve

Walls 1 and 2 only arise because the estimator's attacks call a sieve inside BKZ. Running the
average-case provable sieve on the planted LWE embedding lattice itself, with no BKZ, needs neither.
Choose the number of samples `m` to minimise the dimension `d = m + n + 1` subject to two
conditions:
* the stage-2 bound gives `λ₂ > R = 1.05·‖(e, s, 1)‖` except with probability `≤ 2^{−64}`;
* `R √(1 + B²) < q`.

Then the planted vector is the unique shortest vector and the sieve finds it (`python/full_dim_sieve.py`):

| Kyber (plain-LWE shape, `q = 3329`) | `d` | sieve `2^{0.2925 d}` (with P′) | T1 `2^{0.415 d}` | estimator | worst-case BKZ route |
| --- | --- | --- | --- | --- | --- |
| 512 | 688 | **201** | 286 | 143.8 | no admissible β |
| 768 | 1004 | **294** | 417 | 204.9 | no admissible β |
| 1024 | 1336 | **391** | 554 | 275.1 | no admissible β |

For Kyber512 the gap to the estimator is about 57 bits. The worst-case BKZ route gives no cost at all once `β ≤ d` is enforced. What
this route still needs:
1. **Static statistics S1, S2, S3′ for the planted embedding lattice at polynomial `q = 3329`**,
   with ratio `m/d ≈ 0.25`. T4b covers quasi-polynomial `q` and no planted vector: open, in
   progress.
2. Stage 2 (below): audit and Lean in progress.
3. The sieve: T1 is in Lean given the static hypotheses; `0.2925` uses P′ (paper) and the audited
   GFH theorem.
4. S5 initialization (`IdealUniformLeaves`). It is easier for `q`-ary lattices, since
   `qZ^d ⊂ Λ`.
5. The bit model.

**Obstruction found, and the repair to try ([research/planted_polyq.md](research/planted_polyq.md)).**
At the Kyber512 shape `(q, n, m, d) = (3329, 512, 175, 688)`, S1 fails for **every** `A`. The
terminal shell's squared-radius interval lies strictly inside `(4475, 4476)`, while every vector of
the embedding lattice has integer squared norm. So the shell is empty, and S3′ fails too. Lean:
`PolyQ.shell_empty_of_sq_gap` (the integer-spectrum obstruction; the endpoint inequalities were
checked by exact rational arithmetic outside Lean).

This is the `Z^n` obstruction again. The cause is the sieve's shell width `w = n^{−2}`, which is too
thin for integer lattices: the squared-radius width is about `0.02`. The note's §4 already says
integer lattices need width `Θ(1/n)`, giving a squared-radius width of about `13` at `d = 688`. That
in turn needs the algorithmic layer to tolerate constant-factor variation of lens volumes across a
shell (windows `[μ/C, Cμ]`). The Lean T1 (`prescribedScan_T1`) is stated for the thin shells, so it
must be redone for wide shells. In progress.

This does not replace walls 1 and 2: the estimator's cheaper BKZ-based attacks still have no
proof. It is the cheapest attack whose cost proof is within reach.

## Stage 2: the uSVP success condition with a planted vector (in progress)

* **`λ₂` lower bound, polynomial `q` (new; [research/usvp_planted.md](research/usvp_planted.md);
  audited: holds, [research/usvp_planted_audit.md](research/usvp_planted_audit.md);
  **proved in Lean: `Planted.badMatrices_probability`**).** For the plain-LWE embedding lattice
  (`d = m + n + 1`, planted `(e, s, 1)` with coordinates bounded by `B`), and with
  `G = (q^m / V_d)^{1/d}` the Gaussian-heuristic radius:
  `Pr_A[λ₂(L) ≤ R] ≤ ((R + √d/2)/G)^d` whenever `R √(1 + B²) < q`.
  * At `m = 2n`, bounded `B` and prime `q = Θ(n^a)` with `a > 3/2`, the failure probability is
    exponentially small at every fixed fraction of `G`.
  * Plain-LWE example of Kyber size: `q = 3329`, `m = 1024`, `n = 512`, `B = 3`, `R = 1000`
    (`G ≈ 2113`) gives failure probability `≈ 2^{−1616}`.
* Lean (`SigabaNeo.Planted`; axioms `propext`, `Classical.choice`, `Quot.sound`):
  * `badMatrices_probability`: for prime `q`, fixed `e, s` with `|coords| ≤ B`, `R ≥ 0` and
    `R √(1+B²) < q`, the uniform probability over `A` that the embedding lattice
    (`x + Ay ≡ t(As + e) mod q`) contains a nonzero `z` of norm `≤ R` that is not an integer
    multiple of `(e, s, 1)` is `≤ ((R + √d/2)/G)^d`;
  * `badMatrices_card` (probability `≤ #integer ball/q^m`) and `integerBall_card_le_volume`
    (`#integer ball ≤ V_d (R + √d/2)^d`, by disjoint unit cubes);
  * `planted_iff`: embedding membership is `A(y − ts) = te − x` over `F_q`;
  * `affineCount`: a feasible system has `q^{(n − rk X) m}` solutions;
  * `lift_multiple`: short points congruent to multiples of the planted vector are integer
    multiples.
* Open:
  * the success condition for windows chosen by BKZ from the same matrix (fixed windows have
    exact moments in the note);
  * full shell statistics at polynomial `q`;
  * Kyber's module structure.

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

  [Laa26]'s Lean development assumes `ClassicalRogersFormula` and `ClassicalGramFormula`.
  **`ClassicalGramFormula` is now proved** for Lebesgue measure on every finite-dimensional real
  inner product space (`SigabaNeo.Rogers.Gram.classicalGramFormula_volume`,
  `Reduction/Rogers/ClassicalGram.lean`, from the spherical Gram law for every `s`,
  `spherical_gram_formula_all`; axioms `propext`, `Classical.choice`, `Quot.sound`). The archive
  statement was transcribed locally (`GramDensity.lean`); the archive itself was not rebuilt.
  **The order-1 case of `ClassicalRogersFormula` (Siegel's mean value theorem) is now proved**:
  `siegel_mean_value` (`Reduction/Rogers/SiegelMeanValue.lean`, assembled from the closed local-P2M
  decomposition, files `SiegelAssembly*.lean`, `UnitBallQR*.lean`; axioms `propext`, `Classical.choice`,
  `Quot.sound`): for `n ≥ 2` there is a measurable fundamental domain `D` of `SL_n(ℤ)` with
  `0 < Haar(D) < ∞` whose normalized pushforward to `SL_n(ℝ)/SL_n(ℤ)` is an `SL_n(ℝ)`-invariant
  probability measure with `E[Σ_{v ∈ L∖0} f(v)] = ∫ f` for every measurable `f ≥ 0`. Independent audit:
  faithful (genuine nonzero Haar measure, correct action, each nonzero vector counted once; a
  Minkowski–Hlawka corollary was derived from it). **Order 2 is now proved**: `rogers_order_two`
  (`Reduction/Rogers/RogersOrder2.lean`): for `n ≥ 3` and admissible `F`, the mean of `Σ_{v,w ∈ L∖0} F(v,w)`
  (ordered pairs, diagonal included) equals Rogers' diagram sum `∫∫F + Σ_{Q ≥ 1, b ≠ 0, gcd(b,Q)=1} Q^{-n} ∫F(x, (b/Q)x) dx`
  (independent pairs via shear invariance and Haar uniqueness; dependent pairs via order-1 Siegel on lines). Independent
  audit: faithful (equals the classical ζ(n)^{-1}·Σ_{a ≥ 1, b ≠ 0} a^{-n} form; `Admissible` = bounded, bounded support,
  zero on zero coordinates — the general case follows by monotone convergence). **Order 3 is now proved**:
  `rogers_order_three` (`Reduction/Rogers/RogersOrder3.lean`; `n ≥ 4`; rank split, rank-1 for all k, rank-2 via reduced-diagram
  reindexing and the order-2 frame measure, full rank via Cramer shears + Haar uniqueness + lattice-point counting calibration).
  Independent audit: faithful (the congruence coefficient |row image|^{-n} equals Rogers' Π (gcd(ε_i,q)/q)^n; checked on 9000
  rank-2 diagrams and 3000 random matrices). So orders 1–3, the ones the sieve analysis uses, are all proved. Still open for
  discharging [Laa26]'s hypothesis literally: the structure `ClassicalRogersFormula` asks for every order k < n.
  **This is now proved too**: `rogers_formula_all` (`Reduction/Rogers/RogersAllOrders.lean`; axioms `propext`,
  `Classical.choice`, `Quot.sound`): for every `n ≥ 2` there is a measurable fundamental domain of positive finite Haar mass
  whose normalized quotient measure is an `SL_n(ℝ)`-invariant probability satisfying `ClassicalRogersFormula` with
  `congruenceCoefficient n` (every `1 ≤ k < n`); `rogers_formula_domain` gives it for any finite-mass fundamental domain.
  **Both hypotheses of [Laa26]'s Lean development (`ClassicalGramFormula`, `ClassicalRogersFormula`) are therefore
  discharged**. The local statements are paraphrases (different diagram type, set-based workload); the bridge
  `Reduction/Rogers/Laa26Bridge.lean` copies the archive's statement-level definitions verbatim (arXiv:2609.13635v1 source)
  and proves `archive_rogers` and `archive_gram` — the archive's own `ClassicalRogersFormula` (with an invariant probability
  measure) and `ClassicalGramFormula` (on every `(span ℝ {e})ᗮ`) — with axioms `propext`, `Classical.choice`, `Quot.sound`.
  Independent audit: faithful. **Archive rebuilt (Nov 22, 2026)**: the arXiv:2609.13635v1 Lean project (599 files; no
  `sorry`/`axiom`/`native_decide`/`implemented_by`/`#eval` found by scan) builds under its own toolchain v4.32.2 with Mathlib
  v4.32.2, and its consumer theorem `SphericalStatistics.IntrinsicMarkedMomentPaper.intrinsic_marked_moments_paper` depends
  only on `propext`, `Classical.choice`, `Quot.sound`. Its only hypotheses are `ClassicalGramFormula` (as `hgram`) and
  `ClassicalRogersFormula ν c` (per ν), exactly the statements `archive_gram` / `archive_rogers` prove verbatim here. So the
  [Laa26] marked-moment bounds for Haar-random lattices hold unconditionally, across two environments (archive proofs on
  v4.32.2, hypotheses on v4.36.0-rc2; not merged into one build). This concerns Haar-random lattices; it does not address
  assumption (C)/wall 2 (BKZ blocks) or the planted q-ary obstruction above.
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
* **Planted q-ary sieve (audited; negative; [research/planted_qary_sieve.md](research/planted_qary_sieve.md)).** The
  Doulgerakis–Laarhoven prescribed shell schedule (stated for Haar-random unimodular lattices), applied after rescaling to
  the Part 39 planted q-ary lattices L ⊆ Z^D, has a terminal squared-norm shell containing no integer for every
  D = 647..662 (e.g. [1956.928, 1956.947] at 647; nearest integer ≥ 0.0528 away), so the last merge aborts for every
  design and plant: no proven sieve cost for the Part 39 SVP call. Also: exact planted tuple identity (order ≤ 3), a
  modular-deficit example, and the observation that DL26's S4 chain (1 + 1/ℓ)R* < R_cat fails at ℓ = 7. Wider shells
  remove the integrality obstruction but their acceptance and plant coverage are unproved.
* **Planted sieve with irrational height (audited; negative; [research/planted_sieve_scaled.md](research/planted_sieve_scaled.md)).**
  At D = 647, squared height h ∈ [1.02076213, 1.02076215] populates the terminal shell (≈ 12× the Siegel prediction, i.e. S1
  fails by overpopulation) and keeps Part 39's uniqueness ≥ 0.99516648; yet the prescribed sieve accepts nothing: source
  heights are {9, 30}, only height-0 differences reach the terminal shell, where parity excludes every pair, and all terminal
  heights are multiples of 17 so the height-1 plant is never found. For any plant-independent height law the plant lies in
  the terminal shell with probability < 0.008109. No planted-sieve exponent is certified.
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
* **The algorithmic layer in Lean (`SigabaNeo.Lattices.Sieve`).** The finite-shell sieve, for a
  fixed lattice given as finite shells, with the static hypotheses explicit. Axioms `propext`,
  `Classical.choice`, `Quot.sound` in all 17 checks:

  | Theorem | Statement |
  | --- | --- |
  | `exactCancellation`, `acceptance` | Lemma A: every target difference gets weight `b_min/(a_max |U|)`. The acceptance rate is exactly `(1+θ_T)/(12(1+θ_U))`, at least `99/1212` under S1. This corrects the note's `1/12`: the constant changes, the argument does not |
  | `bankFailure`, `mergeSurvival` | Lemma B: concentration gives a bad-bank bound; one merge survives with probability `≥ (1−δ)(1−ε)` |
  | `shellTree_uniform`, `survival_recurrence` | Theorem D: from i.i.d. uniform leaves, all output lists at a level have equal mass; the survival recurrence |
  | `terminalFailure_count`, `latticeScan_shortest` | Lemma F: under terminal coverage, S3′ and S4, every minimizer of the filtered scan is a shortest nonzero vector |
  | `scanBudget_le` | the exhaustive-scan comparison budget `≤ m·2^m·(2B²) + B²` |

  Added (`Reduction/Sieve/{Core,Bounds,Movers,Tree,Estimates}.lean`, same axioms):

  | Theorem | Statement |
  | --- | --- |
  | `scanBudget_prescribed` | for fixed `K`, all large `n` and depth `m ≤ K (log n)³`, the prescribed scan uses at most `(4/3)^n · e^{(2K+8) n/log n}` comparisons, i.e. `2^{0.415n + o(n)}` |
  | `bankFailure_explicit`, `moverChernoff`, `shellMerge_survival` | from S1 and S2, an explicit bad-bank bound `δ`; at a good bank, missing the `⌊M/16⌋` mover target has probability `≤ e^{−M/1000}` (Chernoff); one-merge survival `≥ (1−δ)(1−e^{−M/1000})` |
  | `prescribedScan_dimension` | under explicit geometric margins and coverage, the two-tree terminal scan finds a specified short vector with probability `≥ 1 − e^{−n/(2 log n)}` |
  | `idealUniformLeaves_factor` | the named hypothesis `IdealUniformLeaves` (the S5 sampler) gives the leaf product used by the recurrence |

  **T1 is complete in Lean, given the static hypotheses (`Sieve.prescribedScan_T1`).**
  * Statement: for fixed `K ≥ 0`, all large `n` and depth `m ≤ K (log n)³`, every lattice whose
    shells satisfy S1, S2, S3′ and S4, given ideal uniform leaves, has a shortest nonzero vector
    `v`. The exhaustive sieve hits `v` with probability `≥ 1 − e^{−n/(2 log n)}`, using
    `≤ (4/3)^n e^{(2K+8) n/log n}` comparisons, and every minimizer of a successful filtered scan
    is a shortest vector.
  * The lens margins (`prescribedLensMargins`, via a cylinder inside the lens:
    `lensVolume_relative`) and the terminal occupancy (`terminalOccupancy_eventually`) are proved.
  * Axioms `propext`, `Classical.choice`, `Quot.sound`.
  * Remaining assumptions: S1–S4, S3′ (about the lattice) and `IdealUniformLeaves` (the S5
    initialization sampler), all explicit premises.
* **`q`-ary sieving statistics (T4; new; [research/qary_sieving.md](research/qary_sieving.md)).**
  * **Paper proof (new).** For `Λ_q^⊥(A)` with lattice dimension `m`, `n = ⌊√m⌋` parity checks and a
    prime `q ∈ [e^{m^8}, 2⌈e^{m^8}⌉]`, the hypotheses S1, S2 and S3′ hold simultaneously with
    probability `1 − e^{−Ω(m)}` over `A`.
    * The proof moves the centered marked moments, up to order `O(log m)`, onto the Euclidean
      diagram sums with additive error `≤ e^{−m²}`. It then reuses the continuum diagram bounds of
      [Laa26] Prop 5.1 audited in g1_audit.md.
    * Lemma Q1 takes the place of Rogers' formula, so **no Haar measure and no Rogers formula
      are needed**. The remaining classical inputs are the spherical Gram density and the
      audited (not formalized) continuum diagram bounds.
    * With the algorithmic layer, this gives exact SVP on these lattices in time `(4/3)^{m+o(m)}`,
      or `(3/2)^{m/2+o(m)}` with Hypothesis P. The exponent is in the lattice dimension `m`.
  * Lean (`SigabaNeo.QAry`): `shortMeanValue`, `markedTail`. Axioms `propext`, `Classical.choice`,
    `Quot.sound`. The integration estimate and the sieve corollaries are paper proofs.
  * This first regime needs `n ≈ √m` and a doubly exponential `q`.
* **Toward cryptographic shapes (T4b; new; [research/qary_crypto_shapes.md](research/qary_crypto_shapes.md)).**
  * **Paper proof (new).** At **`m = 2n`**, and for every aspect ratio with `n/m` bounded away from 0
    and 1, S1, S2 and S3′ hold simultaneously with probability `1 − e^{−Ω(m)}`. This needs a
    **quasi-polynomial** prime `q ≍ exp(⌈log m⌉^6)`.
  * The new ingredient is a counting bound for modular coincidences. A tuple whose rational rank
    `t` drops to residue rank `u` is suppressed by `q^{−(t−u)(m−n)}`. Centering at the discrete
    fibre mean cancels the singleton terms exactly.
  * At fixed moment order, polynomial primes already suffice for the rank bound. The full sieve
    theorem still uses the quasi-polynomial prime.
  * Result: exact SVP on random `q`-ary lattices of these shapes in `(4/3)^{m+o(m)}` time w.h.p.,
    in the real-RAM model. The `(3/2)^{m/2+o(m)}` variant rested on Hypothesis P, which the audit
    found self-contradictory (below).
  * Lean: `QAry.meanValue_le_add_defect`, the finite mean-value transfer inequality with a
    rank-defect term. Axioms `propext`, `Classical.choice`, `Quot.sound`. The geometric counting
    bound and the corollaries are paper proofs.
  * **Audit ([research/t4_audit.md](research/t4_audit.md); independent, adversarial).**
    * T4 and T4b **hold** at the stated sieve radii, including `m = 2n`, given the classical Gram
      density and the Euclidean diagram estimates of the G1 audit. The exhaustive real-RAM bound
      `(4/3)^{m+o(m)}` follows.
    * Two overclaims fail. A transfer "at every positive radius" fails on the event `A = 0`.
      **Hypothesis P** (§3.9 of the note, behind every `(3/2)^{m/2}` / `2^{0.2925·}` time claim)
      **is self-contradictory as written**: at cosine `0.45`, P1 demands reporting with
      probability → 1 while P2 makes candidacy exponentially unlikely. The `0.2925` time bounds
      of the notes were therefore unverified until the repair below.
    * **Repair, Hypothesis P′ ([research/search_lemma.md](research/search_lemma.md); new).**
      Recall is required only at the query cosines the sieve actually uses. For arbitrary fixed
      indexed lists, Gao–Feng–Hu's product code with fresh rotations misses each required pair
      with probability `≤ e^{−Cn}`. With Lemmas H and I this gives real-RAM time
      `2^{(0.29248…+o(1))n}` and space `2^{(0.20751…+o(1))n}`.
      * [DL26]'s own `0.2924` claim is **not** affected: its Lemma 19(ii) asks for recall only on
        cosines in `[1/2 − 1/ℓ, 2/3]`.
      * Lean: `Search.transcriptMiss_le`, the finite-transcript union bound. The product-code
        construction and the running time are paper proofs.
      * P′ relies on [GFH26b] Theorem 4.2 / Proposition 4.3 (ePrint 2026/1844, not refereed).
        **Audit ([research/gfh_audit.md](research/gfh_audit.md)):** they support P′ for non-empty
        fixed lists in the real-RAM regime. Eq. (19) has a harmless empty-input defect, since P′
        returns immediately on empty lists. One shared Haar rotation per batch suffices.
        * Lean: `Search.productCodeMiss_le`, the conditional `m·q^B` miss bound. Axioms
          `propext`, `Classical.choice`, `Quot.sound`.
        * Checked on paper only: Haar concentration, wedge volumes, averaging over rotations,
          and traversal correctness and cost.
    * Priority: Kim–Kwon–Lee–Lee (ePrint 2026/2711) already prove exact SVP for random `q`-ary
      kernels in a different density regime. What may be new here is narrower: the
      shrinking-shell statistics at these radii. Even that is not confirmed.
  * **Lean (`SigabaNeo.Lattices.QAryMain`, partial; axioms `propext`, `Classical.choice`,
    `Quot.sound`).** No continuum or Gram-density hypothesis is used.

    | Theorem | Statement |
    | --- | --- |
    | `markedRawSum`, `markedCenteredSum` | exact raw and centered marked moments over all check matrices |
    | `markedDeviationUnion`, `staticFailure_le_rankSum` | Markov's inequality and a union bound over marks and levels: `P[S1, S2 or S3′ fails]` is at most an explicit finite sum of modular-rank terms, for the repository's sieve predicates |
    | `rankReplacement` | modular minus rational raw sums equals a sum over discrepant rank pairs with exact multiplicities |
    | `innerBallProbability` | for `1 ≤ R < q`, `P[Λ_q^⊥(A) meets the nonzero integer ball of radius R] ≤ #B/q^n` |

    Added (`QAry/MainCounting.lean`):
    * `projectedRankStratum` counts projected integer arrays with entries `≤ B`, rational rank `t`
      and residue rank `u`, with the factor `q^{−(t−u)m}`;
    * `centeredPartitionSum` proves the exact singleton cancellation.

    Added (`QAry/MainRowSpaces.lean`):
    * `rationalRowSpaceCount`: at most `(2B+1)^{kd}` rational row spaces of rank `d`;
    * `rationalRowPivots`: an injective coordinate projection on each such space;
    * `rationalRankStratumCount`, `modularRankStratumCount`: stratum counts, including pivots
      that lose rank mod `q`;
    * `freeingPivotError`: the error from dropping rational independence.

    Open in Lean, to reach `e^{−cm}` and the exact-SVP corollary:
    * identifying the partition arrays inside `rankMoment` and applying `centeredPartitionSum`;
    * summing the error over patterns;
    * the enlarged-window continuum estimates at the T4b radii.
  * **Still far from Kyber and LWE.** `q = 3329` is polynomial and far below `exp(log^6 m)`. LWE
    lattices contain a planted short vector. BKZ runs the sieve on projected blocks, which is
    assumption (C), refuted for worst-case blocks above. The bit model is open.
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

## Dual attacks: list correlations (audited; [research/dual_list_correlation.md](research/dual_list_correlation.md))

For a complete shell under uniform input the off-diagonal score variance is exactly a (half-weighted) count of
modular collisions up to sign; for non-uniform input distinct, non-antipodal dual vectors can be perfectly
correlated (variance `N²`); sign flips and uniform subset selection do not remove correlations. Conditional guarantee:
mean gap `g` and variance sum `≤ g²/16` give advantage `≥ 3/4` for the midpoint test. Open: establishing these for
actual BKZ+sieve lists, and bridging fresh-input tests with Pouly–Shen's fixed-input Theorem 6.

## Dual attacks: MATZOV modulus switching and FFT (audited; [research/matzov_rigorous.md](research/matzov_rigorous.md))

Conditional extension of Pouly–Shen Theorem 6: with exact independent DGS draws, FFT over the rounded residues is exact and
recovery holds if the population gap exceeds `2(B + ε + d)` (rounding, numerical, sampling errors); guesses equal mod `p`
are indistinguishable, so lifts need separate handling. Not certified at the estimator's parameters. Estimator heuristics
listed (including an `Nf` bits/nats mix and the GJ21 independence heuristic in `fft_solver`); the estimator's secret entropy
exceeds the exact CBD entropy by 0.0062 / 0.0165 bits per coefficient.

## Dual attacks: tightening Pouly–Shen (audited; [research/pouly_shen_tight.md](research/pouly_shen_tight.md))

Union over candidate scores instead of `q^m`, a Banaszczyk-type tail and an explicit Hoeffding `N` lower the modeled cost at
the fixed Table 1 parameters by ≈ 0.50 / 1.67 / 0.02 bits (matched key coverage); the BKZ term (237.45 / 345.24 / 478.33)
is the floor. The dual gap to the estimator (≈ 88 bits for Kyber512) is essentially the BKZ/sieve part, i.e. walls 1–2.

## Dual attacks: exact counting (audited, minor caveats; [research/dual_exact_count.md](research/dual_exact_count.md))

Exact first moment, variance and Paley–Zygmund bound for the number of dual vectors in a ball (line indicators are pairwise
independent), and exact mean/variance of the cosine score from the CBD(3) Fourier transform cos⁶(πw/q) — list size alone does
not certify advantage. The headline 'no informative dual vector at 511 samples × 512 secret coordinates (Pr < 9.03·10⁻⁸)' is
the elementary rank fact that a uniform 511×512 matrix has injective transpose mod q (audit): the pure dual needs m > n,
guessing, or the augmented/normal-form dual of MATZOV and Pouly–Shen. No improved certified dual cost was obtained.
