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
  GramFactor.lean (`det_gram_project_tail`) proves det G(b_0,…,b_n) = ‖b_0‖²·det G(πb_1,…,πb_n), with π the projection onto
  b_0^⊥. This is the covolume factorization behind Parts 108/114. It is accepted on Prove2Me.
  GramProduct.lean contains two theorems. `det_gram_eq_prod_norm_sq` proves det G = ∏‖b_i^*‖². `log_volume_lower_bound` is
  Part 114's deterministic recurrence: if D_t = D_{t−1}/s_t with s_t ≤ C·D_{t−1}^{1/b}, then
  log D_T ≥ r^T·log D_0 − log C·Σ_{i<T} r^i, where r = (b−1)/b. Both are accepted on Prove2Me.
  LayerCount.lean (`averaged_layer_count`) proves the exact averaged layer count of Parts 110/120:
  (1/|H|)·Σ_h #{x ∈ S : π(x) = k·h} = #{x ∈ S : π(x) ∈ kH} / |kH|. It is accepted on Prove2Me.
  SubsetCollision.lean (`subsetSumCollision`, `subgroupCollision`) proves the subset-sum pigeonhole behind Parts 129–130. If
  2^f > |U| (or |B/G| < 2^f), some nonzero ternary z has Σ z_i v_i = 0 (or lies in G), with ‖z‖² equal to a Hamming distance
  ≤ f. Both are accepted on Prove2Me.
  CBDPaleyZygmund.lean (`paley_zygmund`, `projection_second_moment_le`, `projection_tail_lower`) proves
  Pr[XᵀQX > 6d/5] ≥ d/(25(d+2)). This is the Paley–Zygmund step behind Part 97's height-zero necessity. All three are accepted
  on Prove2Me.
  CoprimeMark.lean contains eight theorems:
  * fiber normalization |jH|·|H[j]| = |H|, with every fiber a coset of H[j] (Part 120);
  * for a coprime height (q·H = 0, gcd(j, q) = 1), multiplication by j is bijective with explicit inverse a, and
    Pr[j·U = x] = 1/|H| (Part 127).

  All eight are accepted on Prove2Me.
  ShiftedTheta.lean contains two theorems. `shiftedTheta_le` is the 1-D bound Σ_k e^{−s(k+a)²} ≤ Σ_k e^{−sk²}, via Poisson
  summation. `latticeTheta_le` is the GS-floor bound Σ_{c∈ℤⁿ} e^{−s‖Σc_ib_i‖²} ≤ (Σ_k e^{−sg²k²})ⁿ, the key analytic step of
  Part 102. Both are accepted on Prove2Me.
  HeightOne.lean (`heightOneVector`, `heightOneUnion`) proves Part 102's height-one sufficient condition end to end. For a
  rank-d lattice with GS floor g inside the image of Q, the CBD(3) probability that some nonzero h ties or beats the plant at
  height one is ≤ (Σ_k e^{−(g²/12)k²})^d − 1. Both are accepted on Prove2Me. (`#print axioms` shows `choice`, which is
  Classical.choice: the repository declares no axioms.)
  UniquenessProbability.lean (`uniquenessProbability`) is the end-to-end terminal certificate. Take a fixed projection Q of
  trace d and a fixed rank-d lattice H in its image with minimum ≥ L and GS floor g, where a = L² − 1 − (3/2)d > 0. Then
  Pr_CBD[all-heights uniqueness] ≥ 1 − (v/(v+a²) + T(1) + Σ_{k=2}^{⌊√(9N+1)⌋} T(k)), with v = (9/2)d and
  T(k) = (Σ_m e^{−g²m²/(12k²)})^d − 1. Heights ≥ 2 reduce deterministically to ⟨y,h⟩ ≤ −‖h‖²/(2k). It is accepted on Prove2Me.
  What remains for Wall 1 is to show that the reducer-selected H satisfies these hypotheses with high probability.
  FiniteRankLaw.lean (`mul_surjective`, `card_mul_fiber`, `card_fullRank`, `prob_mul_fullRank`) proves the finite-field rank
  law behind Parts 101/104(d). For F of rank t, A ↦ AF is uniform with fibers of size q^{m(n−t)}, and
  Pr[rank AF = t] = ∏_{i<t}(1 − q^{i−m}). All four are accepted on Prove2Me.
  QuotientMinimum.lean (`haar_secondMinimum_upper/lower`, `quotientMinimum_gap`, `haar_quotientMinimum_upper`) proves a
  Haar second-minimum bound, Pr[λ2 < r] ≤ vol(B_r)²/8, via Rogers independent pairs. It also proves that if λ2 ≥ r, the
  projection off ANY shortest vector has minimum ≥ (√3/2)r. Together: Pr[some shortest-vector quotient has physical minimum
  < c] ≤ vol(B_{2c/√3})²/8. This is a weaker, Lean-verified form of Part 105. All four are accepted on Prove2Me.
  NormOnlySharp.lean (`normOnlySharpWitness`, `normOnlySharp`) proves that the norm-only cutoff T(R) is sharp (Part 94). The
  cyclic group generated by −(T/‖y‖)y has minimum exactly T, yet it ties the plant at height k. So no minimum-only cutoff
  ≤ T guarantees uniqueness. Both are accepted on Prove2Me.
  RectangularExample.lean (`diagonal_minimum`, `project_lattice`, `example_determinants`, `example_minima`) formalizes Part
  121's non-closure counterexample. The diagonal lattices with sides (1/8, 1/4, 1/3, 3) and (1/8, 1/4, 1/2, 2) both have
  determinant 1/32 and the same first two selected minima, but their minima after two removals are 1/3 and 1/2. All four are
  accepted on Prove2Me.
  ProjectedLength.lean (`projectedLength_sq_mul_det`, `projectedLength_eq_sqrt`, `projectedMinimum_le_sqrt`) proves
  ‖πw‖²·det G(b) = det G(b, w). This is the determinant-ratio identity for extension lengths used in Parts 86–101 and 116. It
  also gives the projected-minimum bound. All three are accepted on Prove2Me.
  MinkowskiBound.lean (`minkowski_covolume_eq_abs_det`, `minkowski_short_vector_det`, `minkowski_short_vector_gram`) proves
  Minkowski's first-minimum bound: some nonzero v ∈ L has ‖v‖ⁿ·V_n ≤ 2ⁿ·|det b| = 2ⁿ·√det Gram(b). This is the elementary
  Hermite cap. All three are accepted on Prove2Me.
  RetainedCovolume.lean (`shortest_norm_le_minkowski`, `projected_tail_covolume`, `retained_log_covolume_lower_bound`) chains
  three facts: the Minkowski cap s ≤ 2V_b^{−1/b}·covol^{1/b}, covol(π_{v⊥}W) = covol(W)/‖v‖, and the recurrence. The result is
  Part 114's deterministic retained-covolume lower bound with the elementary constant, with the reducer's window-structure
  facts as explicit hypotheses. All three are accepted on Prove2Me.
  **ConditionalReduction.lean (`conditionalReduction`) is the formal reduction of Wall 1 to one open quantity.** Take any
  reducer R mapping a uniform design A to final-block data (Q_A, H_A) that depends only on A. If at most a δ-fraction of
  designs have H_A failing (minimum ≥ L and GS floor ≥ g), then Pr_{A,plant}[all-heights uniqueness] ≥ (1−δ)(1−ε) ≥ 1−δ−ε,
  with ε explicit (`reductionError`). It is accepted on Prove2Me. The open Wall 1 problem is exactly bounding δ for BKZ-β at
  β ≈ 406–506.
  PrimitiveUnfolding.lean (`primitive_projected_unfolding`, `primitive_unfolded_marginal`) proves the primitive unfolding
  with the projected lattice kept in the integrand. The Haar integral of Σ_v F(gv, π_{(gv)⊥}gℤⁿ) equals an integral over
  U = ⋃_v D·A_v, and the first-column marginal is dx/ζ(n). Both are accepted on Prove2Me. The missing step for Part 105's
  sharp bound is to disintegrate over the first column and identify the normalized transverse lattice with Haar on X_{n−1}.
  TransverseHaar.lean (`normalizedProjection_disintegration`) proves the disintegration of the unfolded measure over the
  marked first column. A single Markov kernel K_x gives (1/μ(D))∫_U F(x, P_g) dμ = (1/ζ(n))∫∫ F(x,p) K_x(dp) dx for every
  nonnegative measurable F. It is accepted on Prove2Me. Still open: identifying the law induced by K_x on the unlabelled
  transverse lattice with Haar on X_{n−1}.
  TransverseInvariance.lean (`normalizedProjection_left_invariant`) proves joint SL_n(ℝ)-invariance of primitive incidence:
  replacing g by ag preserves the unfolded integral of every test of (marked column, unlabelled normalized projected
  lattice). It is accepted on Prove2Me. Still open: a measurable realization of the transverse lattice in X_{n−1}, and
  stabilizer invariance on almost every fiber.
  TransverseCoordinates.lean / TransverseCount.lean give the following (nine theorems accepted on Prove2Me):
  * a measurable determinant-one transverse frame, and a probability kernel K_x on X_{n−1};
  * the exact count identity E_Haar[#{v ∈ W : λ1(normalized π_{v⊥}L) < c}] = ζ(n)⁻¹ ∫_W K_x{λ1 < c} dx;
  * fiberwise transport: every h ∈ SL_{n−1}(ℝ) is realized by a mark-fixing parent matrix;
  * the Haar calibration Pr_{X_m}[λ1 < c] ≤ c^m·V_m/(2ζ(m));
  * the product law for n = 2.

  Closed by the six files below; there is no remaining open obligation for Part 105.
  TransverseCocycle / TransverseShapeInvariance / TransverseUniqueness / TransverseKernelLaw / TransverseProduct /
  TransverseMinimumBound give:
  * K_x-a.e. SL_{n−1}-invariance, and the identification of K_x with Haar on X_{n−1} for a.e. x (all n ≥ 3);
  * the exact joint law dx/ζ(n) ⊗ Haar_{X_{n−1}} of (marked primitive vector, normalized transverse lattice);
  * `part105`: E_Haar[#{oriented primitive v : |v| ≤ ℓ, λ1(normalized π_{v⊥}L) < c}] ≤
    (V_n ℓ^n/ζ(n)) · (c^m V_m/(2ζ(m))), where m = n − 1 ≥ 2, on any finite-mass fundamental domain.
  All of these are axiom-clean (propext, Classical.choice, Quot.sound).
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
* **Part 130 (audited).** [recursive_deferral](research/wall1_recursive_deferral.md): recursive deferral cannot close 506
  with first moments.
  * The old lattice embeds isometrically, so the requirement stays at the physical radius 27.4538 at every level.
  * With a fixed prefix all batches share one displacement group: 451 total deferred columns force a collision, and 417 exhaust
    the budget.
  * The smallest surviving leaf has rank 89, with a pathwise floor of 1.095, a factor 25 short.
  * Part 39's 647 is minimal within its certificate family (failure 0.0149 at 646, 0.00483 at 647).
* **Part 131 (audited; corrected by the audit).** [rethink](research/wall1_rethink.md): three architectures and their gaps:
  * restart certificates need a non-rare-acceptance estimate;
  * list decoding needs selected primal ball counts, which Part 101's dual counts do not give (rectangular counterexample);
  * multiple final blocks need a joint estimate.

  The audit found that multiple blocks DO close with disjoint sample blocks. Conditional on s, Part 39 blocks on disjoint rows
  are independent, so k blocks fail together with probability ≤ E_s[f(‖s‖²)^k]. Two width-646 exact SVP calls (133 rows each,
  with candidate verification on the 245 unused rows) succeed with probability > 99.409%. **New rigorous frontier: maximum
  oracle dimension 646 (two calls), improving 647 (one call).**
* **Part 132.** [multiblock](research/wall1_multiblock.md): a check of the arguments behind Part 131's multi-block statement.
  * Fixed disjoint row sets are conditionally independent given the secret, also for unequal sizes.
  * Disjoint secret-coordinate deletions on shared rows do not give that independence.
  * The (7/q)^v verification bound applies only to candidates with a wrong residue mod q, so integer recovery needs decoding to
    the CBD-support representative.

  No further parameter optimization is recorded.

  **Lean (Nov 2026).** MultiBlockProduct.lean, MultiBlock.lean and MultiBlockVerify.lean are axiom-clean (no sorry,
  axiom or native_decide):
  * `failure_eq_expect`: Part 39's failure equals E_s[f_r(s)], where f_r(s) is the conditional failure given the secret.
  * `condFailure_le` bounds f_r(s) by a function of ‖s‖² only.
  * `multiblock_exact`: for any family of predetermined disjoint row blocks, Pr[every block fails] = E_s[∏ᵢ f_{rᵢ}(s)]
    exactly. `multiblock_le` gives the corresponding upper bound.
  * `expect_energy` reduces the expectation to a finite sum over ‖s‖².
  * `verify_exact` / `verify_cbd`: a fixed wrong residue passes v reserved rows with probability exactly (7/q)^v.
    `verify_union` / `verify_union_avg` give the list union bounds.

  MultiBlockAttack.lean / MultiBlockInstance.lean (axiom-clean; the decide +kernel checks use only propext and
  Quot.sound) complete this:
  * `attack_success`: for any exact SVP oracle, the concrete attack succeeds with probability
    ≥ 1 − E_s[∏ f_{rᵢ}(s)] − k(7/q)^v. The attack decodes to the CBD representative and verifies on reserved rows.
    Independence from the reserved rows is derived, not assumed.
  * `two_block_success`: **the recorded Part 131 instance is formally verified.** (511, 512, 3329), CBD(3), two blocks of
    133 rows plus 245 reserved rows, two exact SVP calls in dimension 646: success > 99.409%. The exact value is
    ≥ 0.9940921. The build peaks at ≈ 7.4 GB of memory.
* **Part 133 (audited, minor caveats; corrected by the audit).** [provable_cost](research/wall1_provable_cost.md): rigorous
  cost of the exact SVP call.
  * The Doulgerakis–Laarhoven-type provable sieve is a statement about Haar-random lattices. Part 39's lattices form a
    countable set (Haar-null), so even a proven version would say nothing about them.
  * Algorithms proven for every lattice:
    * Micciancio–Voulgaris: Õ(2^{2D}), i.e. 2^1294·polylog at D = 647, with an unspecified exponent c.
    * ADRS/ASD18: 2^{D+o(D)}, with no published constants, so no number at D = 647.
    * Kannan/Hanrot–Stehlé: D^{D/(2e)+o(D)}; with explicit constants this is ≈ 2^4300.
  * Explicit baseline (exact arithmetic, audited): enumerating secrets by decreasing CBD(3) probability needs ≤ 2^1234.3955
    candidates for 99%, at < 2^19 operations each. The cost of generating candidates in order is not counted. Wrong output
    has probability ≤ 2^{1234.4−4544.59}.
  * Rigorous BKZ tour bounds exist only for modified variants (HPS11 BKZ', Li–Nguyen, Li–Walter). The original BKZ has only
    O(β)^n. None of these certifies success for β < 647.
  * Next step: make ADRS/ASD18's constants explicit at D = 647.
* **Part 134 (audited, minor caveats; the corrections are in the note's Audit section).**
  [breakthrough_r1](research/wall1_breakthrough_r1.md): a restart theorem and three reductions to Part 120.
  * **Theorem 1 (sound).** Split the rows into k disjoint blocks. On each block run the reducer and a plant-blind acceptance
    test: minimum ≥ L, GS floor ≥ g, and a prefix floor for the Babai lift. Decode the first accepted block. Then
    failure ≤ ∏δᵢ + ε* + ℓ*.
    * The reducer and the test read only the plant-free lattice of each block, which depends on A alone, so no
      conditioning on s is needed. Selecting a block by acceptance does not bias the plant.
    * The rejection allowed per block rises from 0.009 to 0.0949 (k = 2), 0.208 (k = 3) and 0.308 (k = 4), at the cost of
      fewer rows per block. Whether those row counts still work was not evaluated.
    * Retrying with fresh randomness on the same rows cannot replace splitting the rows (Prop 1.2).
  * **Theorem 2.** For any plant-blind reducer, failure of all-heights uniqueness ≥ Pr[λ1(H)² ≤ μ − t] · t²/(v + t²). So
    a lower-tail bound on λ1(H) is unavoidable: at d = 505, Pr[λ1 ≤ 26.66] ≤ 2% and Pr[λ1 ≤ 24.81] ≤ 1.11% are needed.
  * **Theorem 3 (near-tautological, per the audit).** Change-of-measure accounting reduces to Part 120's last-step split.
  * **Prop 4.** In the worst case, the theta potential loses up to 23.50·(s/GH)² nats per step at rank 505 (18.89 at rank
    405), against a budget of 23.78. The worst case is attained on hexagonal planes through the winner.
  * **Conjecture R1 (open).** The relaxed Part 120 plane count is ≤ 0.05. Of the Part 123 data, only the 3/48 sample weighs
    against a 1% rate.
  * **Lean.** PlantAveragingNecessity.lean (axiom-clean) formalizes Theorem 2.
    * `plantAveraging_lower`: Pr_A[λ1(H_A)² ≤ μ − t] · t²/(v + t²) ≤ Pr[all-heights uniqueness fails].
    * `plantAveraging_tail_necessary`: average success ≥ 1 − θ implies Pr_A[λ1² ≤ μ − t] ≤ θ(v + t²)/t².
  * **Lean (Nov 2026).** PlantBlindRestart.lean formalizes Theorem 1 abstractly. It is axiom-clean, with no sorry, axiom
    or native_decide.
    * `failProb_eq` gives the exact law: failure = ∏δᵢ + Σᵢ (∏_{j<i} δⱼ)·Pr[accᵢ ∧ Fᵢ].
    * `restart_le` / `restart_le_avg` / `restart_le_lift` give failure ≤ ∏δᵢ + ε (+ ℓ). `restart_le_pow` gives δ^k + ε.
    * `restart_le_lwe` instantiates the plant as iid (s, e).
    * RestartReduction.lean connects this to the concrete test (axiom-clean). The key results:
      * `restartReduction`: for k disjoint blocks with acceptance "GS floor ≥ g, minimum ≥ L (and a prefix test)", failure
        ≤ ∏δᵢ + reductionError + ℓ;
      * `restartReduction_lwe`: the LWE plant marginal is discharged;
      * `restartReduction_single`: the k = 1 analogue of `conditionalReduction`.
    * BabaiLift.lean / RestartLift.lean (axiom-clean) remove the lift hypothesis.
      * `babai_lift`: nearest-plane on a prefix returns u from every lift u + Σcᵢbᵢ when |⟨u,b*ᵢ⟩| < ‖b*ᵢ‖²/2.
      * `tail_two_sided`: the CBD(3) two-sided tail is 2·exp(−T/12).
      * `liftFail_le_floor`: under the prefix floor gᵢ, ℓ = Σ 2·exp(−gᵢ²/12), the audited Part 47 constant at η = 3.
      * `restartReduction_lwe_babai`: failure ≤ ∏δᵢ + reductionError + Σ 2·exp(−gᵢ²/12), with no remaining hypothesis
        except δᵢ.
    * DecoupledDecoder.lean (axiom-clean) closes the decoder. The main results:
      * `fiber_eq_coset`: lifts form exactly the prefix coset when L ∩ W = K.
      * `decoupled_primitive`: for L = L0 ⊕ Zu, the plant-free condition L0 ∩ W ⊆ K suffices.
      * `decode_eq`: the concrete plant-blind decoder (SVP on PL, orient to height 1, lift, Babai) outputs exactly (X, 1)
        under uniqueness and lift success.
      * `restartDecoder_lwe_choose`: Pr[recovered secret ≠ s] ≤ ∏δᵢ + reductionError + Σ 2·exp(−g²/12), with concrete
        choice-based SVP and lift oracles.
    * AttackLattice.lean (axiom-clean) removes `Compatible` and builds the lattice from (A, b).
      * `attackLattice_eq`: with b = e + As, the attack lattice {z : z_err + A z_sec ≡ z_h·b} equals L0 ⊕ Z(X, 1).
      * `compatible_ofBasis`: `Compatible` holds for the canonical prefix and final block of ANY ordered Z-basis of L0.
      * `restartAttack_lwe`: for any reducer mapping block rows (+coins) to an ordered basis of the block's null lattice,
        Pr[recovered secret ≠ s] ≤ ∏δᵢ + reductionError + Σ 2·exp(−g²/12).
      * The only residual hypotheses are J + d = N and q ≠ 0. CBD(3) only.
    * **The Lean chain from (A, b) to secret recovery is complete. The only open mathematical quantity is δᵢ**, the
      rejection probability of the GS/minimum/prefix-floor test on the reducer's output.
* **Part 135 (audited, minor caveats; the corrections are in the note's Audit section).**
  [plant_symmetry](research/wall1_plant_symmetry.md): what averaging over the plant can and cannot do.
  * A lattice containing the plant determines it: a second admissible solution exists with probability < 2^−3107.2. So
    "plant-independent" can only mean that decisions depend on A and the coins alone.
  * The planted and null laws are almost singular: TV ≥ 1 − 2^−3107.2 and KL ≥ 3592 bits. The decoupled reducer has the same
    δ under both, so contiguity and low-degree transfer have nothing to work with.
  * Symmetrizing over the signed row/column permutations leaves δ unchanged.
  * A plant-last BKZ follows the plant-free run until the plant first becomes strictly shortest in some window. The rank-2
    window becomes visible early whenever the last horizontal GS length exceeds 2/√3.
  * A fork reducer with K looks satisfies two bounds:
    * failure ≤ δ_𝒯 + ε + ε_lift + 2^−3107.2, where δ_𝒯 is the probability that no checkpoint has a good block;
    * success ≤ Pr[max λ1 > ℓ] + K·τ(ℓ)·Pr[max λ1 ≤ ℓ].
  * So a 99% proof at β = 506 needs Pr[max_t λ1(H_t) ≤ ℓ_K] ≤ 1/99, with ℓ_K = 16.857 / 13.174 / 9.591 for
    K = 1 / 10 / 1000.
  * Part 101 certifies only 8.1588. Sufficiency (per the audit) needs L ≥ 35.112 at β = 506 (32.145 at β = 406), so the
    rigorous gap is about a factor of 2 in the threshold. Conjectures 5.1–5.3 are open.
  * **Lean.** ForkCheckpoints.lean (axiom-clean) formalizes three results:
    * Prop 2.3: planted and null laws of a plant-free reducer's output are equal;
    * Thm 4.4: failure ≤ δ_𝒯 + reductionError + ε_lift + Pr[collision];
    * Thm 4.5: success ≤ Pr[¬B_ℓ] + Kτ(ℓ)Pr[B_ℓ].
    The numerical inputs (τ, the collision probability, and the null-trajectory probabilities) are hypotheses.
* **Part 136 (audited, minor caveats with one substantive correction; see the note's Audit section).**
  [restart_certificate](research/wall1_restart_certificate.md): what "non-rare acceptance" has to mean.
  * **Monte Carlo certificate.** Run the fixed decoupled pipeline on simulated CBD plants. The certificate is sound: there is
    no stopping-time bias, since the true plant is independent of everything the rule reads. It is complete up to
    ≈ 4.2·10⁻⁹ / 9.4·10⁻¹⁰, at a cost of 10⁵ extra SVP calls per trial.
  * **Restart failure.** With a shared design, restart failure is E_A[(1−α(A))^T]. So 99% needs α(A) ≳ 1/T on 98–99% of
    designs; a non-rare mean acceptance proves nothing.
  * **Randomizations.**
    * Fresh disjoint rows give exact independence, but at most 2–3 blocks fit, so each block needs ᾱ ≈ 0.82–0.92.
    * Overlapping row subsets give at least a K-fold amplification, K = ⌊m/m′⌋.
    * Canonicalizing or equivariant reducers gain nothing from basis or symmetry randomization.
    * Prefixes independent of A need ≥ 2^678 trials at β = 406.
    * Re-choosing the last vector gains at most 2/√3.
  * **Counting certificates.** Relaxing the per-trial failure budget to 1 − 1/poly moves any first-moment radius by at most
    100^{1/D} ≈ 1.01.
  * **Theorem 8.** It uses the Lean results `primitiveBallPairs_hit_lower` and `part105`. On a Haar window, picking a short
    primitive vector whose quotient passes fails with probability < 1.371·10⁻⁵ at rank 506, ratio 0.954. This certifies
    λ1(H) ≥ 27.484. Per the audit, that matches only the *necessary* floor 27.4538 (Part 103); sufficiency is not implied,
    and height-zero success at that floor is ≈ 47%.
  * **Lean.** HaarWindowTemplate.lean (axiom-clean) formalizes Theorem 8 generally. `haarWindowTemplate_mu` bounds the
    rule's failure on a Haar window by 1/(1+μ) + μ·c^m V_m/ζ(m). The numeric instance is not formalized.
  * **Remaining.**
    * Gaps A and B are lower tails of the per-design acceptance.
    * Gap R (window statistics within a constant factor of Haar, Conjecture R) closes only the necessary-side statement.
  * **Lean.** MonteCarloCertificate / CertifiedFirstAcceptance / SharedDesignExhaustion (axiom-clean, 34 declarations)
    formalize the abstract results:
    * Thm 1: plant independence of the plant-blind transcript, so Pr[fail | selected = d] = Pr_X[fail(d, X)];
    * Chernoff-type completeness and false-acceptance bounds, and failure ≤ Pr[exhaustion] + θ_b + B·T;
    * the exact identity e_T = E_A[(1−α)^T], its monotonicity, e_T ≤ δ + ε′, and the quantile, reciprocal and Jensen
      bounds;
    * Prop 7: Paley–Zygmund at the design level.
    The numerical binomial tails are not evaluated.

* **Part 137 (audited, minor caveats; the corrections are in the note's Audit section).**
  [joint_blocks](research/wall1_joint_blocks.md): joint estimates for blocks chosen independently of A, list decoding, and
  the ceiling of these methods.
  * **Shared rows with disjoint secret deletions.**
    * Given the plant, the covariance of candidate counts is an exact finite-field rank identity (Thm 1).
    * A k-block circuit bound holds with no rank condition (Thm 2).
    * Negative dependence is false: at q = 31 the two failures are positively correlated (exact computation and Monte
      Carlo).
    * Shared error rows give up the averaging gain (Prop 4).
  * **List decoding.** It needs only E[#primal ball points] plus the count at heights ±1 (Thm 6). For coordinate planes
    this expectation has an exact closed formula, averaged over A (Thm 5). Joint failure is then a norm event plus first
    moments (Thm 7). The enumeration cost is unproven.
  * **Ceiling.** Blocks fixed independently of A cannot push joint failure below the norm tail of the plant coordinates
    they share.
    * With disjoint rows, the floor is the ‖s‖² tail (3.43·10⁻¹¹ at the 646 design).
    * With shared rows, the floor does not vanish as k grows.
    * Paley–Zygmund lower-bounds the true single-call failure at 646 by 1.19·10⁻³.
    * Recorded joint bounds were reproduced: 0.014905 / 0.005908 / 0.003682 for 1/2/3 blocks. At most 3 blocks fit in
      511 rows.
  * Conjectures A–C are open.
  * **Lean.** CoordinateListMoment / Rank / Oracle / Decoding (axiom-clean, 21 declarations) formalize:
    * Thm 5: per-vector membership probabilities from the deleted-column rank law, giving exact expected counts in any
      finite window;
    * Thm 6: failure ≤ Pr[‖plant‖ > ϱ] + (q^j − 1)/((q−1)q^r) + E[C]·(7/q)^v, with the rank term dropping for a full-rank
      lift;
    * Thm 7: the joint bound for overlapping blocks with shared reserved rows, and the audited converse.
    Every exact enumeration oracle is covered, and one exists. Output-sensitive enumeration cost is open.

* **Part 138 (audited, minor caveats; the proof of Theorem B is repaired in the note's Audit section).**
  [reducer_variants](research/wall1_reducer_variants.md): block-reduction variants whose output might be analyzable.
  * **Gap, w.p. > 98.5%:** λ2 ≥ 440 and ‖plant‖ ∈ (36.76, 41.73], so λ2/λ1 ∈ [10.545, 17.234].
  * **Worst case falls short.** Worst-case guarantees at β = 506 are 991.9 (BKZ), 32.9 (slide approximation factor) and
    31.5 (Hermite factor), all above the gap. ALNS20 Thm 1.2 drops below the gap only from oracle rank 774, and never
    with Blichfeldt constants.
  * **Theorem B (profile-only barrier, 2 ≤ β ≤ 566).** Block-Hermite inequalities, size reduction, the gap and the plant
    position do not by themselves certify success.
  * **Lemma U1.** Every reducer has an atomic final-block law. This rules out density, TV and L² arguments, but not weak
    Haar comparisons.
  * **Lemma U2.** Symmetry re-randomization leaves success unchanged.
  * **Lemma S1.** In Li–Walter slide reduction, slack in the dual twin test trades for a strictly worse final block.
  * **Lemma S2 (ALNS20 exact twins, rank 512).** Reduced bases correspond to sublattices Q, and ρ has a closed form in
    det Q, ‖b1‖ and η*.
    * ρ ≥ 0.954 holds if log det Q ≥ 954.34 (rigorous, sufficient) or ≈ 862.75 (heuristic typical η*). The GSA value is
      ≈ 874 [heur].
    * The densest Q passes with ρ ≈ 0.28 [heur].
  * **Verdicts.** Re-randomized BKZ, DBKZ and random sub-designs remain subject to Parts 106, 111 and 112. Self-dual BKZ is
    limited to Parts 86–87. Prefixes independent of A stay at 646/647.
* **Part 139 (audited, minor caveats; Prop 7 corrected; see the note's Audit section).** [lyapunov](research/wall1_lyapunov.md):
  potential-function / supermartingale routes.
  * **Theorem 3 (barrier).** Take any per-step hypotheses made only of pathwise facts and statements about non-atomic
    (Haar) inputs. They cannot bound δ below 1 for ratio events at ratio above 1/G_r: 0.2036 at β = 406, 0.1826 at β = 506.
    The witness is a zero-draw kernel. It agrees with the true kernel outside a finite set of reachable states and
    freezes the cube for the whole pass. The barrier blocks ratio-type events, not the physical event of the Lean
    reduction.
  * **Theorems 1–2.** Supermartingale arguments (Azuma, Freedman, optional stopping, Margulis) are dominated by δ itself.
    A potential built on a statistic π is only as strong as the worst reachable history with the same π.
  * **Theorem 4 (exact one-step geometry).**
    * A winner with vertical index k ≥ 1 gives a retained lattice ≅ A_v(Λ + Zλ/k).
    * The Rankin recursion holds.
    * The dual minimum satisfies λ1(Λ'*) ≥ min(λ1(Λ*), 1).
    * All were checked in ranks 2–3.
  * **Theorem 5.** There is an exact Fourier second-moment identity for the window minimum. Conditionally on the cap
    s ≤ κ·G_b·D^{1/b} (κ = 1.05), Part 114's terminal floor rises from 28.81 to 34.10, and the ratio target drops from 0.954
    to 0.805.
  * **Remaining.**
    * (C1) dual cusp escape.
    * (C2) the ratio at 0.805, via Conjecture E or a Freedman good set.
    * DS (winner direction spread). Per the audit, M ≤ 2 is not enough at small s, and s ≥ s_min must be charged as an
      exit.
    * Horizontal steps still face the Part 120/126 obstruction.
  * **Prop 7 (corrected).** The Rankin skeleton gives only ≈ 10^{-1412}·GH, not a Part 109/110-type floor.
* **Part 140 (audited, minor caveats; see the note's Audit section).** [adrs_explicit](research/wall1_adrs_explicit.md): an
  explicit version of the ADRS/ASD18 provable exact-SVP algorithm.
  * **Theorem E.** For every rank-n lattice with an integral basis whose entries are ≤ B, the ASD18 pair-and-average
    algorithm (constants fixed: θ = 1/8, 4 runs, K₀ = 800) outputs an exact shortest vector. Its operation count and failure
    probability are closed formulas with no O or o terms.
  * **Part 39 instance (n = 647, B = 3329).** 2^799.23 operations (2^799.81 with the literal 6d sampler recursion), with
    failure < 2^−120.9 and space 2^781.98. **This is in a real-RAM model for the initial BLP13 sampler**, which is the
    note's own idealization, not BLP13's. A word-RAM bound is estimated at ≤ 2^840 but not proved.
  * **Combined with Part 39.** Secret recovery with probability ≥ 99.51664% − 2^−120.9 within that cost. The previous best
    explicit bound was the brute-force 2^1253.4 (Part 133); Micciancio–Voulgaris gives 2^1294·poly.
  * **New lemmas, re-derived and numerically tested by the audit.**
    * Lemma 4.3a/b: a coupling replacing the square sampler.
    * Lemma 4.6: Banaszczyk tail after cancellation.
    * Lemma 4.5: preservation of domination under pair-and-average. ASD18's Def 2.2 (upper-orthant order) is NOT preserved;
      the audit gives an explicit counterexample. Their theorems survive via Lemma 4.5.
  * **Open.** A proven word-RAM sampler cost (settled at the recorded instance by Part 141).
  * **Lean (started).** AdrsGaussian / AdrsPoisson / AdrsCoupling / AdrsPairing / AdrsOrthant (axiom-clean, 29 theorems)
    prove:
    * the Gaussian identities I1 and I3, including p_max = ρ_{s/2}(L)/ρ_s(L);
    * Lemma 4.3a: the Poisson ratio bound and an exact-marginal coupling;
    * the Lemma 4.3b tail bounds;
    * Lemma 4.5 in one-step form: maximal within-label pairings have one output law, and sub-multiset coupling dominates
      upward-closed events;
    * the audit's exact counterexample to ASD18 Def 2.2 (L = Z, s = 2).
    Eleven further Adrs* modules (axiom-clean, 99 declarations) complete the algorithm analysis:
    * I2: conditioned on X ≡ Y mod 2L, (X+Y)/2 ~ D_{L,s/√2} exactly.
    * Lemma 4.3b(2): the selected averages dominate a Poissonized iid D_{L,s/√2} list with rate
      Λ' = θΛ·ρ_{s/√2}(L)²/(ρ_s(L)ρ_{s/2}(L)).
    * History induction: for every finite admissible schedule, Procedure E's final list contains a Pois(Λ_ℓ) iid D_{L,s_ℓ}
      multiset with probability ≥ 1 − Σεⱼ − Pr[Pois(Λ0) > M0].
    * Final hit: the miss probability is exp[−Λ_ℓ·D_{L,s_ℓ}(S)] for the set S of shortest vectors.
    StatDistancePostprocess.lean (axiom-clean) adds two results:
    * `sdist_joint_same_kernel`;
    * `seqLaw_postprocess_event_lower`: an ideal event probability ≥ p transfers to the approximate sequential sampler as
      ≥ p − Σεₘ, for randomized postprocessing.
    Still open in Lean: the numerical instantiation at the recorded lattice and the word-operation cost accounting. That
    covers schedule admissibility, the summed combiner failure, the terminal Gaussian mass of the shortest vectors, and
    the 2^−120.9 total. The delegate declined to formalize the concrete instance, since together with Part 39 it is a
    secret-recovery certificate. It is left as a general theorem with explicit hypotheses.
* **Part 141 (audited, minor caveats).** [sampler_wordram](research/wall1_sampler_wordram.md): a word-RAM version of Part
  140 at the recorded instance.
  * The Part 39 lattice is L_M = {(h, u) : h ≡ Mu mod q}, whose Gram–Schmidt norms are q and 1.
  * Here s/q ≥ 38.39 at every run, so plain Klein sampling without rejection is within 2^−6670 of D_{L,s} for every M
    (one-dimensional Poisson summation).
  * The one-dimensional draws use 960-bit inversion tables built from a 1024-bit fixed-point recurrence. Each sample is
    within 2^−923.9 of D_{L,s}, and all samples together within 2^−149.26. The list phase is deterministic, so this adds
    directly to the failure probability.
  * **Theorem W.** At the recorded instance: ≤ 2^794.98 word operations at n = 647, with failure < 2^−120.92, worst case and
    no rejection loop. The two 646 calls also total 2^794.98.
    * The model is a word-RAM with words wide enough to address ≈ 2^782 words (sample arithmetic < 2^63).
    * This settles Part 140's real-RAM caveat for these lattices. General integral bases are still open there.
  * **Lean (started).** GaussianSmoothing1D.lean (axiom-clean) proves:
    * `theta1_poisson`: one-dimensional Poisson summation, from Mathlib's Jacobi transform.
    * `abs_theta1_div_sub_one_le` / `tau_le`: |ρ_s(Z+c)/s − 1| ≤ τ(s) ≤ 2e^{−πs²}/(1 − e^{−3πs²}).
    * `thetaQ_ratio_mem`: the qZ + c coset version.
    * `klein_ratio_bounds` / `klein_sd_le`: the Klein-vs-D_{L,s} ratio and SD bounds, in factorized form.
    * `tau_lt_of_ge`: τ < 2^{−6678} at s/q ≥ 38.39.
    KleinFactorization.lean (axiom-clean) proves Lemma 1:
    * `hasSum_pi_prod` (a product of sums over Z^r) and the parametrization of L_M;
    * `discGauss_eq_kleinLaw_mul`: D(y) = K(y)·g(u)/E_p[g];
    * `sdist_kleinLaw_discGauss_le`: SD(K, D_{L_M,s}) ≤ ½(((1+τ)/(1−τ))^r − 1) for every integer M;
    * instances at s/q ≥ 38.39: SD < 2^−6671 for r ≤ 134, and < 2^−6669 for r ≤ 512.
    StatDistance / CDTInversion / DiscreteGaussianTail / FixedPointGaussian (axiom-clean) prove:
    * SD basics, sum bounds for products and sequential laws, data processing, and P(E) ≤ Q(E) + SD;
    * CDT inversion: SD ≤ (N−1)·2^{-w} + μ;
    * the shifted discrete-Gaussian tail ≤ 2e^{−πR²/s²}/[(1 − e^{−2πR/s²})·b];
    * the fixed-point recurrence error ≤ x(x+3)/2·(δ_E + 2^{-F}).
    KleinProcedure / GaussianCDT / GaussianCDTBounds (axiom-clean) prove:
    * the Klein procedure's output law equals `kleinLaw` pointwise;
    * SD(A, D) ≤ tη_T + rη_H + SD(K, D), with the event transfer;
    * the constructed CDT tables (P = 960, F = 1024, R = 2^22 − 1) have per-draw SD ≤ 2^−930 at both recorded dimensions
      and all four run widths;
    * so SD(A, D) ≤ d·2^−930 + SD(K, D) for d ∈ {646, 647}.
    GaussianConstantSeries / GaussianConstantArgument / RecordedGaussianConstants (axiom-clean) discharge the two input
    constants:
    * 1088-bit Machin π and logarithm routines with certified error;
    * kernel-checked fourth-root enclosures;
    * a 36-term Taylor routine;
    * `recordedGaussianConstants` builds `GaussianConstants` for all eight recorded widths.
    The final theorem is SD(A(M), D_{L_M,s}) ≤ (r+t)·2^−930 + SD(kleinLaw, D_{L_M,s}), with no numerical hypotheses.
    Still open in Lean:
    * the word-operation count;
    * the ADRS combiner analysis itself (Part 140).
  * **Rigorous cost frontier (Nov 2026).** Recovering the secret of plain LWE (511, 512, 3329), CBD(3) with probability ≥
    99.5% costs ≤ 2^795 word operations, fully explicit. The previous explicit bound was 2^1253.
* **Part 142 (audited, minor caveats with one substantive correction to F3/DS; see the note's Audit section).**
  [dual_cusp](research/wall1_dual_cusp.md): an attempt on (C1) and (DS) of Part 139. Neither is proved.
  * **Theorem A.** On every history, L_H = P_E Z^N, H^⊥ = Z^N ∩ E and Λ* = M* ∩ E, and cosets are labelled by (Z/q)^400.
    Dual vectors receive a vertical kick ≡ −⟨z,a⟩/q at each append, and θ_{H_t^⊥} ≤ θ_Z^{505+h_t}.
  * **Theorem B.** The one-step coset representative is uniform on Voronoi-reduced representatives. The Fourier ratio has an
    exact primal form and a Parseval form.
  * **Theorem C.** For any reducer that keeps orthogonal projections, λ1(Λ_t*) ≥ R0(t) for all t ≤ 407 outside probability
    10⁻³, with R0 = 0.2018 at the end. So the literal dual cusp is empty on a good set.
  * **Proposition D / Theorem E: (C1) is not easier than the primal problem.** At the end the dual GH is ≈ 0.88 < 1, so the
    ratio mass sits at dual norms 1–6. The inheritance bound Λ_t* ⊆ M_t* overshoots Haar by ≥ e^1628.
  * **(DS).** Pr[|⟨ξ,σ(U)⟩| < a] ≤ 2a + 1/o(ξ) holds. Per the audit, the "covering density ≥ 113" obstruction does NOT apply
    to the k = 1-conditioned law: there the density is ≲ (λ1/GH)^r/p1 ≈ 2.6 on Haar-like states. So DS reduces to an upper
    bound on λ1/GH on reachable states plus a discrete/continuous transfer.
  * **Conditional.** C1′(a) and C1′(b), both conjectures, would give failure ≤ 1.7·10⁻³ (1.9·10⁻³ with Part 117) for the
    34.0992 floor.
* **Part 143 (audited, minor caveats).** [slide_route](research/wall1_slide_route.md): the Q actually selected by ALNS20
  slide reduction (exact oracle, strict-improvement convention).
  * From the qI-first basis, the minimum physical covolume of Q is 1. It is attained exactly when A = 0, with probability
    3329^{−511·512}, for every tie rule. How the remaining mass 1 − p is distributed over larger covolumes is open.
  * Prefix covolumes strictly decrease and extension covolumes weakly decrease. A rank-5 example reaches terminal covolumes
    90 and 100 from the same start with the same prefix-potential history (exact rerun). So potential monotonicity does not
    determine Q.
  * **Correction to Part 138 S2(c).** A densest Q always admits a passing flag, but it can violate S2(b)'s side condition.
  * **Correction to Part 138's cost framing.** With a rank-511 prefix, the null quotient has rank 512, but Part 47's final
    SVP on the same prefix has rank 513, because the height direction survives projection. "Oracle rank ≤ 512 for the
    whole procedure" is therefore wrong by one. Part 47 and the Lean chain are consistent: J + d = N counts horizontal
    dimensions, and the decoder runs SVP on the full projected lattice.
  * The 1% quantile at ρ = 0.954 remains open.
  * **Lean.** SlideCovolume / SlideEndpoint / SlideZeroDesign / SlideRankFive / SlideProjectedRank (axiom-clean, 29
    declarations) formalize:
    * an integer frame has covolume ≥ 1, with equality iff it spans a coordinate sublattice;
    * a unit-covolume rank-n frame exists in the null lattice iff A = 0, the exact qI-first run ends there, and its mass
      is q^{−mn};
    * accepted-step monotonicity;
    * the rank-5 example with terminal covolumes 90 and 100;
    * projected ranks d and d+1 for the null and attack lattices (512 and 513 at N = 1023, J = 511).

* **Part 144 (audited, SOUND).** [horizontal_core](research/wall1_horizontal_core.md): a direct attack on the horizontal-step
  core (Part 120), counting over Part 108's conditional law.
  * **Barrier 1.** At width 506 there is an explicit family of penultimate restart histories with maximal mark. On it, every
    final draw selects an old line in an area-one old plane. The family's probability is ≈ 2^−1,909,216, far below the
    horizontal budget 0.00488848.
  * **Barrier 2.** In the original pass, the zero-displacement history (probability q^{−511d}) keeps the full q-torsion
    mark. Its conditional horizontal charge is > 1 − 2^−303 at width 406 and > 1 − 2^−398 at width 506.
  * **Barrier 3.** Part 139's discrete DS moment is infinite. On > 99.8% of width-506 restart states, exact alignment with
    an old shortest line keeps positive probability after conditioning on |k| = 1 and s ≥ 30. Part 142's continuous bound
    and Part 139's geometric factor are unaffected.
  * **Consequence.** Bounds that hold uniformly over histories are impossible, even with maximal marks. The remaining
    obligations are history-averaged: the averaged horizontal charge, the positive-height charge, and the late-state upper
    tail of λ1/GH.
* **Part 145 (audited, minor caveats).** [averaged_charge](research/wall1_averaged_charge.md): history-averaged horizontal
  charge.
  * **Sharp transition.** At width 506 the expected horizontal charge is > 1 − 6.05·10⁻¹⁵ on graph draw 102 and
    < 2.05·10⁻¹¹ on draw 103; width 406 behaves the same on draws 75/76. The cause is that the old-plane cutoff crosses the
    length q of a second old axis. Part 120 imposes the charge only at the terminal draw, so this is consistent. The
    budget 0.00977696 cannot be imposed draw by draw.
  * **Moment barrier.** Two modular competitor families have identical singleton and pair probabilities, but their void
    probabilities are 3328/11082241 and 1664/3329. Second-order moment data alone cannot certify the target for general
    modular lists.
  * **No negative dependence.** An exhaustive check of 16,384 small graph designs found that the joint
    old-plane/horizontal-win probability exceeds the marginal product by 14175/16777216.
  * **Positive height.** On one explicit terminal family the positive-height contribution is < 1.364·10⁻¹⁰·Q^{−407}.
  * The full width-506 terminal budget (0.00977696) remains open. Per the audit, deleting competitors can improve a
    Cauchy–Schwarz bound even though it enlarges the void event.
* **Part 146 (audited, SOUND).** [subspace_void](research/wall1_subspace_void.md): an exact horizontal void formula.
  * Conditional on the history, each feasible competitor excludes one displacement. Grouping the excluded displacements by
    projective line splits the horizontal charge exactly into three parts: histories with old minimum t ≤ 1, entirely
    uncovered lines, and uncovered scalars on partially covered lines. Signed ties are handled.
  * A Möbius formula (Gaussian binomials over the subspace lattice) holds for fixed raw graph constraints.
  * **Span dimension is insufficient.** In a reachable width-506 terminal family, the 803 beating displacements span all
    400 mark dimensions. The family's exact contribution is < Q^{−510}, where Q = 3329^400.
  * **Remaining.** The history average, over states passing the old-plane test, of the uncovered lines and scalars. The
    positive-height plane multiplicity at budget 0.00977696.
* **Part 147 (audited, minor caveats).** [uncovered_lines](research/wall1_uncovered_lines.md): three of the terminal terms
  are bounded (width-506 restart, interval-verified).
  * Pr[penultimate minimum ≤ 1] ≤ 2^−135.60.
  * The horizontal charge from short lines (a representative within 0.954·old GH) is ≤ 3.114918·10⁻⁶.
  * The positive-height plane multiplicity on horizontal wins is ≤ 9.35974·10⁻¹⁰.
  * **Remaining.** It suffices that the long-line horizontal charge plus the positive-height multiplicity on non-horizontal
    wins is ≤ 0.0097738441. That allowance fits Part 120's budget with ≈ 4.6·10⁻¹¹ to spare; Part 117's coupling cost
    applies once. Both terms are exact finite design counts, but the first-moment bound for non-horizontal wins is
    2^1316.021, so new tools are needed.
  * At width 406, the unit-minimum estimate is above budget (one term exceeds 2^457).
* **Part 148 (audited, SOUND).** [vertical_multiplicity](research/wall1_vertical_multiplicity.md): the positive-height
  multiplicity on non-horizontal wins (width-506 restart).
  * Winners with |k| ≥ 363 contribute < 1.872·10⁻⁹, counting every witness plane.
  * The full non-horizontal first moment is F_nh < 2^456.548, down from Part 147's 2^1316.021.
  * An exact conditional count that keeps the winner test was checked on all 314 toy displacements.
  * **Remaining.** h_long + F_< ≤ 0.0097738422, where F_< covers 1 ≤ |k| ≤ 362. Even at |k| = 1 it needs the average
    number of old primitive lines that the selected projection shortens below the cutoff.
* **Part 149 (audited, SOUND).** [long_lines](research/wall1_long_lines.md): the long-line horizontal charge A (width-506
  restart).
  * The only unconditional bound is A < 1 − 2^−1447.324.
  * **Plane incidence fails.** Every representative of every nonzero class on a long line stays farther than 0.954h/√2 from
    every witnessing old plane and its translates.
  * **Barrier.** A reachable family has conditional long-line charge > 0.99999688, with history probability
    ≤ 3329^−163200.
  * **Necessary condition.** A ≤ 0.009 requires Pr[old-plane test passes with 1 < t ≤ √((0.954h)² + 1)] < 0.009000029,
    since every long line is uncovered there. This is necessary only: histories outside that event remain uncontrolled.
    It is again a lower-tail statement about the penultimate minimum.
* **Part 150 (audited, SOUND).** [shortened_lines](research/wall1_shortened_lines.md): projection-shortened lines at small
  |k| (width-506 restart).
  * F_< < 2^219.843 uniformly over penultimate histories. With Part 148, the full non-horizontal moment is also
    < 2^219.843, down from 2^456.548.
  * Two pieces are below budget for every history: wins with s ≤ R/8 contribute < 4.21822·10⁻⁸, and exact alignment
    contributes < 2^−909.45.
  * F_rem has an exact discrete cylinder count, checked plane by plane on 645 toy case–draw pairs.
  * **Remaining (sufficient).** h_long + F_rem ≤ 0.0097738000. F_rem needs its average over selected histories with
    R/8 < s < 2R/√3.
* **Part 151 (audited, SOUND).** [penultimate_tail](research/wall1_penultimate_tail.md): the penultimate-minimum lower tail
  Pr(B) of Part 149 (width-506 restart).
  * The sharpened Part 147 first-moment bound crosses 0.009 at physical radius 1.19806583 and reaches 1 at 1.20927112.
    The required cutoff exceeds 30.5692 on every history, so first moments alone fall short by ≈ 25× in radius.
    ≥ 96.3% of the majorant comes from the latest used column supplying the first direction of a long flag.
  * At the required cutoff, the three cases involving the 406th selection sum to < 2.400·10⁻⁹.
  * **Remaining (sufficient, exhaustive split).** Bound by 0.0089999976 in total:
    * a horizontal winner whose short vector and plane witness are both inherited;
    * a vertical winner with length in [0.954, 1.097193]·(window GH).
* **Part 152 (audited, SOUND).** [cylinder_average](research/wall1_cylinder_average.md): the history average of F_rem
  (width-506 restart).
  * An exact finite-mark average that keeps the signed winner test and witness multiplicity.
  * Each primitive old line chosen before the terminal draw contributes < 9.359728·10⁻¹⁰, uniformly over histories.
  * Witnesses with 7R*/8 ≤ R < R* contribute < 7.191421·10⁻⁶ on the design average.
  * Histories above the retained-lattice theta threshold contribute < 2^−73.433, multiplicity included.
  * **Obstruction (relaxed estimate only).** On Proposition 5's stratum, dropping the winner test and using the
    coordinate-lattice theta bound gives > 2^617.94 from plane height one alone. This says nothing about the true average.
  * The sufficient condition h_long + F_rem ≤ 0.0097738000 is still open; it is stronger than Part 147's combined allowance.
* **Part 153 (audited, SOUND).** [neargh_vertical](research/wall1_neargh_vertical.md): Part 151's residual (b), vertical
  winners at 0.954–1.097×window GH.
  * When the old minimum clears the cutoff, the fresh draw preserves the void with probability > 0.999999999106.
    Conditioning on the void therefore moves any retained-plane event by ≤ 8.938011·10⁻¹⁰.
  * Histories with window GH ≥ 203.888 have probability ≤ 1/816000. That exit comes out of the shared 0.0089999976
    allowance.
  * An exact rank-4 example (order 17) shows void ∩ plane-hit can exceed the product of the probabilities: 34/289 against
    16/289.
  * **Remaining.** The selected plane-hit rate, averaged over qualifying width-506 histories.
* **Part 154 (audited, SOUND).** [winner_exchange](research/wall1_winner_exchange.md): an exchange argument for F_rem.
  * The full-window winner is shortest in every incident witness plane. Gauss reduction then gives a rounded lift of
    length < √(R² + s²/4), which is the old primitive vector when the lift is horizontal.
  * A height-one counterexample shows the old vector can otherwise be arbitrarily longer than R, even with a unique winner
    and no alignment.
  * **Does not close F_rem.** Every witness in Part 152's obstructing shell has a non-horizontal rounded lift: a horizontal
    lift needs B/u < 1.165, but the shell has B/u > 3.592. What remains is the selected multiplicity of those witnesses,
    averaged over restart histories.
* **Part 155 (audited, SOUND).** [inherited_witness](research/wall1_inherited_witness.md): Part 151's residual (a),
  inherited horizontal witnesses.
  * An exact backward recursion holds for the inherited-witness event; it matches direct enumeration on 81 toy graphs.
  * Vertical projections preserve old independent pairs and only shrink lengths, witness distances and areas. Survival at
    fixed upper cutoffs therefore has conditional probability 1, so it gives no decay.
  * Pr[inherited event ∧ the minimum has an old raw lift ≤ 6t/5] < 2.450981·10⁻⁶.
  * The rest (every raw lift shrinks substantially, plus an old plane witness) has only the vacuous bound 1 − 2^−4435.956.
    The shared 0.0089999976 allowance for (a) + (b) remains open.
* **Part 156 (audited, minor caveats).** [gibbs_selection](research/wall1_gibbs_selection.md): BKZ with Gibbs (discrete
  Gaussian) selection.
  * The exact first-pass law holds. Per the audit, the height-one kernel assumes all horizontal qI axes have already entered.
  * **The theta normalizers do not telescope.** Two histories with the same endpoints, frozen plane and energy have
    probability ratio Z_s/Z_r > 1.
  * **Selection bias survives smoothing.** In a rank-4 example, conditioning on the Gaussian-selected vector raises the
    expected short quotient-pair count from 9/4 to 3.53303625362… (exact rational bounds). Lexicographic and uniform-tie SVP
    give 4.
  * As σ → 0, a fixed finite pass converges in TV to uniform shortest-tie selection. This gives no finite-temperature
    terminal guarantee and no transfer of F_rem.
  * So the Part 106/112 obstructions are not an artefact of deterministic selection.
* **Part 157 (audited, SOUND).** [bounded_bias](research/wall1_bounded_bias.md): bounding the per-step selection bias.
  * **The sharp uniform one-step factor is Q = 3329^400.** At draw 407, an incoming history of probability Q^−511 has a
    nonzero-height winner exactly on the zero mark, which has probability 1/Q. Revealing this raises the expected plane
    count from 105/Q to 105. That attains the elementary bound E[N|S] ≤ E[N]/P(S) exactly.
  * **Depth truncation does not decouple the past.** Two histories with identical all-vertical suffixes (horizontal depth
    0) have plane counts 105 and 0.
  * A C^D suffix comparison holds, but it still needs the average over the selected state at the start of the block.
  * The area cutoff 3/2 used here is diagnostic. Smaller factors for the specific terminal residuals are not ruled out.
    Both allowances remain open.
* **Part 158 (audited, minor caveats; empirical).** [selected_scaling](research/wall1_selected_scaling.md): exact toy
  computations of the terminal selected averages. 156,049,323 terminal designs over 39 toy parameter sets, all
  representative counts independently reproduced.
  * Inherited minima: in the single-output depth-2 family, the contribution is exactly (16q−38)/q^5 for primes q ≥ 19.
  * Plane hits: in one rank-4 row, 3420 vertical band wins, 1980 gated, 4 hits. In that row, two successive rounding
    inequalities make the event empty for q ≥ 89. Part 159 shows this does not carry over to width 506.
  * Terminal multiplicity: the non-horizontal-lift class dominates in some rows, while in others all witnesses are
    horizontal.
  * Per the audit, the "56% of allowance" toy figure does not measure the width-506 contribution. The q = 23 zero-mark
    incidences would fail the real terminal gate.
  * **Conjecture.** The three high-rank averages are bounded by gated ball volumes in witness ranks d−2, d−1 and d, times
    e^{o(d)}.
* **Part 159 (audited, SOUND).** [plane_hit_rounding](research/wall1_plane_hit_rounding.md): the rounding argument for
  residual (b) at the real instance.
  * At q = 3329, width 506, rounding excludes no gated draw. The plane cutoff exceeds the rounding lower bound by ≥ 13.637%
    on every gated draw, and by ≥ 14.270% outside the large-GH exit. So the toy emptiness (Part 158) does not transfer.
  * A first moment bounds the band through 0.97×window GH by 4.038879·10⁻⁶.
  * **Remaining.** After that and the 1/816000 exit, residual (a) plus the selected plane hits in (0.97, 1.097193]×GH must
    total ≤ 0.00899473323. The void comparison costs nothing extra.
* **Part 160 (audited, SOUND).** [shrunken_lifts](research/wall1_shrunken_lifts.md): the shrunken-lift remainder of residual
  (a).
  * At width 506 the remainder is exactly H_old ∩ {d_K(x)² > 11t²/25}, with equality belonging to the near-lift event.
  * Counting arbitrary raw lifts fails, since every quotient point has infinitely many lifts. Taking a shortest lift removes
    the multiplicity but brings back dependence on the selected history.
  * **Toy depth-2 family.** Signed-unit prefixes give exactly (16q−38)/q^5, but constant prefixes give ≳ ½q^{−15/4}.
    So the signed-unit share tends to 0; at q = 1009, (2,2,2,2) alone adds 1,006 hits to 16,106.
  * The dominant structures change with q, so extrapolating from small toys (Part 158) needs care.
    Pr(A) ≤ 10⁻³ at width 506 remains open.
* **Part 161 (audited, minor caveats).** [band_plane_hits](research/wall1_band_plane_hits.md): the residual (b) band.
  * The 4.038879·10⁻⁶ lower-strip charge now covers up to 0.97507453 GH.
  * Part 159's first moment crosses the allowance at 0.984890155625… GH. The growth comes from the candidate-ball volume
    factor w^506.
  * A sharper radial count bounds the cumulative contribution through 0.990 GH by 0.008801064. That leaves
    0.00019770868 for the upper band (0.990, 1.097193] GH plus residual (a).
  * **First moments cannot reach the upper band.** On every history outside the large-GH exit, the exact expected number
    of positive-height candidates in (1.004, 1.097) GH exceeds 74.85561, so shortest-vector selection must be used.
  * An exact joint count keeps shorter competitors and ties. In the toys, every forced hit also satisfied the 0.97-GH void,
    so the product of the two probabilities underestimates their intersection.
* **Part 162 (audited, minor caveats).** [upper_band_quotient](research/wall1_upper_band_quotient.md): upper-band plane hits
  as a short line in the rank-504 quotient after two projections. Rank and determinant normalizations match the restart
  window.
  * Counting every primitive first line in the band gives a Haar mean > 0.00152687791836, which is 7.72× the shared
    allowance 0.00019770868.
  * **If the first line must also be shortest, the joint Haar probability (band + both gates) is < 4.361·10⁻¹¹.** This
    follows from primitive incidence plus the rank-506 empty-ball estimate.
  * The exact conditional restart count separates the overcount from losing first candidates. In the toys, selection cuts
    24 forced hits to 2 and 48 to 4, and losing candidates account for all of the excess.
  * **Consequence.** A restart-to-Haar ratio ≲ 4.5·10⁶ for this one event (less (a)'s share) would close the upper band.
    That ratio is open, and per the audit it needs its own upper-band conjecture.
* **Part 163 (audited, minor caveats).** [restart_haar_ratio](research/wall1_restart_haar_ratio.md): the restart-to-Haar ratio
  for the upper-band event.
  * **One draw, not two.** Both selections use draw 406. A positive-height candidate fixes the mark and both gates
    (assuming eg < 3329), so squaring Part 105's density bound does not apply.
  * **Singularity.** On every positive-probability set of histories, even the normalized first selected length has a
    restart law singular to Haar. Density bounds on good histories cannot give the ratio; an inequality for this one event
    is still possible.
  * Two reflected toy prefixes with the same unmarked geometry have selected-hit probabilities 0 and 2/17, a difference
    caused by the tie rule.
  * The Haar bound is < 4.36018·10⁻¹¹. A hypothetical 4.5·10⁶ factor would leave 1.50058·10⁻⁶ for residual (a).
  * **Remaining.** A direct bound on the history average of the exact finite-recursion selected-hit fraction.
* **Part 164 (audited, minor caveats).** [selected_hit_direct](research/wall1_selected_hit_direct.md): a direct
  (Mecke-type exchange) bound on the upper-band selected-hit fraction.
  * **Conditioning is degenerate.** Given the history, a positive-height band candidate fixes the mark and the whole window.
    So the signed-void probability given a compatible witness is exactly 0 or 1.
  * Averaged over histories, the probability is a ratio of prefix weights, each weighted by its fraction of winning marks.
    The rank-506 Haar empty-ball estimate applies only before incidence conditioning, so it does not bound this ratio.
  * In the toys, all 24 gated candidates had an empty open ball, yet only 2 won the signed tie rule (selected mass 2/4913).
  * **Remaining.** The history-averaged weight of gated candidates that beat all smaller-key competitors at width 506, plus
    residual (a), within 0.00019770868.
* **Part 165 (audited, minor caveats).** [nonnegligible](research/wall1_nonnegligible.md): the weakest provable success
  statement at β ≈ 506/406.
  * Width 506 (Part 108 forward pass, then Part 47 decoding): recovery probability > 2^−1531, including final SVP uniqueness
    and the Babai lift. A penultimate physical minimum > 2/√3 forces a terminal minimum > 1 for every final draw.
  * Width 406 (two-block slide reduction, then Part 47 decoding): recovery probability > 2^−1717.
  * Both bounds use the zero secret. For a nonzero secret, recovery has joint probability > 2^−2,422,414 (406) and
    > 2^−3,020,328 (506).
  * **No advantage.** Guessing zero already succeeds with probability (5/16)^512 = 2^−859.17. Inverse-polynomial success at
    β ≤ 506 is open, and needs control of plant-aware BKZ beyond the first pass, which is the same core.
* **Part 166 (audited, SOUND).** [random_order](research/wall1_random_order.md): randomizing the graph-column order.
  * **Processing-order ties.** Every fixed permutation preserves the joint law of the marked path, so random order leaves
    Part 164's weighted ratio, P and p_a unchanged.
  * **Original-coordinate ties.** An exact check over 29,478 design–order pairs shows random order raises selected hits by
    4/3 (12 → 16). So random ordering is not a universal improvement.
  * P + p_a ≤ 0.00019770868 at width 506 remains open.
* **Part 167 (audited, SOUND).** [new_tools](research/wall1_new_tools.md): four new tools proposed and falsified.
  * **Falsified on both toy families** (2/4913 and 4/15625 selected hits, all winning triples identified):
    * a multiplicative mutual-information bias bound;
    * a positive reverse-predecessor entropy bound;
    * decay of the final martingale increment;
    * an exact pairwise-column representation.
  * **Surviving identity.** In both toys, half the hits win in every column order and half win in one of three orders. So
    the least order-invariant pointwise majorant has mean exactly 2p. Mean preservation under random reordering holds in
    general when columns are exchangeable and ties follow processing order.
  * No bound at width 506 follows.
* **Part 168 (audited, SOUND).** [subset_ustat](research/wall1_subset_ustat.md): the order-invariant majorant as a
  column-subset first moment.
  * An exact criterion decides when a column subset supports a hit in some processing order. Hall's condition handles
    single-slot exclusions, and inclusion–exclusion handles mixed ones.
  * At width 506, every full-history certificate has modular input rank ≥ 118 for both the upper-band and inherited
    events, so supports of fewer than 118 columns contribute zero.
  * Allocating 10⁻⁴ to P needs the responsibility probability of a fixed 118-subset to be ≤ 10⁻⁴/C(511,118)
    = 2.842·10⁻¹²³, even before larger supports. That aggregate is unevaluated, and the combinatorics overwhelm this
    first-moment route.
  * The toys reproduce 4/4913 and 8/15625.
* **Part 169 (audited, SOUND).** [finite_chain](research/wall1_finite_chain.md): treating the restart as a finite-state
  mark/subgroup chain.
  * **No mixing to uniform.** The first suffix selection loses rank exactly when λ1(W) = 3329, which happens with
    probability > 0.72982006. Then the signed tie rule permanently removes the first horizontal mark direction.
  * So every later surviving-label rule is > 0.7295 in TV from uniform on the original label space. Discarding
    rank-deficient histories wholesale would exceed the 10⁻⁴ budget.
  * Given the current state, the next displacement is exactly uniform on the surviving mark group. Both terminal statistics
    are functions of the finite state and that one draw.
  * **Remaining.** The history average of the fraction of marks that pass the geometric tests. P + p_a ≤ 0.00019770868 is
    open.
  * **Lean.** ProjectionDual / AppendDual / MarkedIntegerSection / VerticalWinnerIsometry (axiom-clean, 24 declarations)
    formalize:
    * (P_S L)* = L* ∩ S, and P_{v⊥}L is a full lattice;
    * λ1(Λ'*) ≥ min(λ1(Λ*), 1) for every append-and-project step, with ≥ λ1(Λ*) when the winner is vertical (Part 139
      Thm 4(d));
    * L_H = P_E Z^N and H^⊥ = Z^N ∩ E, which is integral with minimum ≥ 1, plus the coset-label homomorphism with kernel
      H^⊥ (Part 142 Thm A);
    * the vertical-winner isometry onto A_v(Λ + Z(l/k)) (Part 139 Thm 4(a)).
    Still open: the index/covolume formulas and the character-transport, lineage and theta statements.

* **Part 170 (audited, minor caveats).** [softmin](research/wall1_softmin.md): a Gaussian soft-min majorant of the
  selection.
  * e^{−πt‖v‖²}·Z_t(W)/Z_{2t}(W) ≥ 1{v shortest} holds for every window and every t > 0. The best capped bound is the
    cold limit t → ∞, which with signed ties equals P exactly, so nothing is gained.
  * **Pooling over marks fails.** Summing numerator and denominator separately reweights the marks: in an exact example,
    selected probability 1/2 against a pooled value ≈ 0.11798. So the pooled ratio is not a majorant.
  * The certified bound at width 506 is P ≤ 1 − 3329^{−400}. The Haar bound does not transfer.
* **Part 171 (audited, SOUND; IMPORTANT CORRECTION to the Lean BKZ chain).**
  [budget_reallocation](research/wall1_budget_reallocation.md): the physical width-506 certificate is infeasible.
  * **Determinant obstruction.** Suppose `restartAttack_lwe` (one ordered basis per block) is to certify 99%. Even giving
    each error term the whole 1%:
    * every prefix GS length must exceed 7.973694;
    * all 505 terminal GS lengths must exceed 787.854220 (the uniform floor g in `reductionError`);
    * then ln(required product / physical covolume) > 299.02 at 511 rows, and fewer rows make it worse.
  * So every block is rejected, the rejection product is 1 for every disjoint row partition, and **δᵢ ≡ 1 for the current
    acceptance test.** The earlier statement "only δᵢ is open" is therefore vacuous for this test. This limits the
    certificate, not the decoder's real success probability.
  * **Fix.** State the final-block obligation directly as the conditional probability of failing Part 94's all-heights
    criterion, from the block's actual geometry, with no uniform terminal GS floor. Using actual prefix lengths in the
    Babai sum alone does not help.
  * The Part 120/147–170 terminal-ratio analysis uses Part 94 directly and is unaffected. With the unrounded constants,
    Part 151's allowance becomes 0.0001977086810795.
  * **Lean (follow-up).** ThetaProfile / UniquenessProfile / ProfileObstruction (axiom-clean) prove three things:
    * `failure_le_errGeom`: a uniqueness bound using the actual GS lengths;
    * `latticeThetaProfile`: the coordinatewise theta-product bound;
    * `recordedProfile_rejection_eq_one`: even the actual-length test rejects every physical profile at the recorded
      dimensions when ε, ℓ ≤ 0.01.
    The cause is that the coordinatewise theta-product method itself is too lossy. At height 67 alone, each terminal length
    t_i is charged ≥ 2exp(−t_i²/(12·67²)), which forces t_i ≥ 500. So a fundamentally stronger final-block uniqueness bound
    is needed, for example one using smoothing over the random plant against the final block's dual minimum.
* **Part 172 (audited, minor caveats).** [transference](research/wall1_transference.md): primal–dual constraints on the
  selected window.
  * **Dual exit sharpened by 10 orders.** Counting opposite pairs with inward half-cubes, the simultaneous failure of Part
    142's dual floors R0(t) over all 408 indices has probability < 8.147·10⁻¹⁴ (< 4.592·10⁻¹⁵ at draw 406), down from 10⁻³.
  * A deterministic area bound follows from the rank-503 complementary dual section.
  * **Scalar dual floors cannot exclude plane hits.** An explicit rank-506 Euclidean lattice has dual minimum > 1/2, two
    unique successive shortest lines and a strict plane hit in the band. Per the audit it has transcendental covolume, so it
    is not itself a restart window; the restart mass of such configurations is open.
  * **Remaining.** The joint hit mass on draw-406 dual-good designs must be ≤ 0.000197708679995408.
  * **Lean.** RestartGraphDual / DualMinimumExit / InwardCube / DualMinimumExit408 / DualMinimumExitNumeric /
    DualExitCertificate (axiom-clean; 408 rational enclosures kernel-checked by decide +kernel) formalize:
    * exact dual membership with probability q^{−n};
    * the opposite-pair first moment and the inward-cube count;
    * the prefix union bound and the persistence of the floor;
    * **the numeric bounds: exit < 8.147·10⁻¹⁴ over all 408 indices and < 4.592·10⁻¹⁵ at draw 406.**

* **Part 173 (audited, SOUND).** [gated_theta](research/wall1_gated_theta.md): the gated average of per-mark theta ratios.
  * The step-405 dual exit at R = 0.2018 is < 1.539·10⁻¹¹, simultaneously for every next mark.
  * **Cap saturation.** Whenever Θ_{1/(2t)}(W_u*) ≤ 2^134, every gated upper-band candidate keeps capped weight exactly 1.
    So bounds on the dual Gaussian mass cannot shrink the gated weight.
  * A distinct-mark count gives only P < 1 − 1.5325·10⁻⁸⁵, and P + p_a < 1 − 2^−4435.956.
  * The target 0.00019770868 remains open.
* **Lean (Parts 139/142 remainder).** VerticalRefinement / ProjectedCovolume / RankinSaturation / RankinWindow /
  CharacterTransport / MarkedLineage / MarkedTheta / VoronoiMarkLaw (axiom-clean, 34 declarations) formalize:
  * the exact index k and the retained covolume covol(Λ)/‖v‖;
  * the Rankin recursion and its pathwise bound;
  * the kick law t ≡ −⟨z,a⟩/q, unique dual lineage, and inheritance of short vectors;
  * θ_{H_t^⊥}(s) ≤ θ_Z(s)^{n+h_t};
  * the uniform push-forward of uniform marks to Voronoi representatives (Part 142 Thm B).
* **Part 174 (audited, minor caveats).** [lit_dynamical](research/wall1_lit_dynamical.md): a literature survey of rigorous
  average-case analyses of lattice reduction (Vallée et al., Akhavi–Marckert–Rouault, Kim–Venkatesh, Nguyen–Stehlé,
  Bai–Stehlé–Wen; per the audit, BSW's limiting law is due to Chen–Södergren).
  * The most transferable technique is the Vallée–Vera inverse-branch calculation.
  * A planar shortest-line example was exactly reproduced: 2/11 inputs and 2/13 eligible incidences.
  * No checked theorem bounds Part 164's weighted mass or p_a.
* **Part 175 (audited, minor caveats).** [smoothing_uniqueness](research/wall1_smoothing_uniqueness.md): toward a final-block
  uniqueness bound that a certificate can use.
  * **Width 406: 99% is ruled out for GSA profiles.** The GSA head is 24.7665 at rank 405 (24.9621 at rank 406). A physical
    head that short forces height-zero failure with probability > 2.13735% for every projection.
  * **Width 506: open.**
    * The higher-height zero modes are < 4.5·10⁻¹²⁵.
    * But the CBD characteristic function is periodic (CBD is Z-valued). Aliased dual frequencies carry ∏cos⁶ factors that
      can equal 1, and Part 172 does not control them.
    * The minimum floor 27.484 is conditional on the 0.954 ratio.
  * **Fixed-block bound (1).** It covers all three Part 94 failure events, ties included. It is a valid template for a
    repaired Lean certificate: plant-norm tail + height-one bound + per-height CBD-weighted dual sum or exact coset count.
    On the physical zero design it is ≤ 0.217382%.
  * **Lean (repaired certificate).** FixedBlockCount / FixedBlockChernoff / FixedBlockRestart / FixedBlockExample
    (axiom-clean) formalize:
    * `failure_le_smoothError`: formula (1), i.e. the Chernoff cap charge, height one, and CBD-weighted exact ball counts
      per height. It covers all three Part 94 failure events, ties included.
    * `restartCount_lwe`: the restart certificate with acceptance λ1(H) ≥ L ∧ smoothError ≤ ε ∧ (actual-length prefix
      Babai sum) ≤ ℓ, giving failure ≤ ∏δᵢ + ε + ℓ;
    * `exists_flat_accepted`: abstract non-vacuity, with no determinant contradiction, unlike Part 171.
    So the Lean chain's acceptance test is now satisfiable in principle. A physical width-506 witness and the reducer's δᵢ
    remain open; per Part 177 they reduce to λ1 ≥ 0.998·GH plus the height-2–30 nonintegral dual classes.

* **Part 176 (audited, SOUND).** [inverse_branch](research/wall1_inverse_branch.md): inverting the restart's final selection
  (Vallée–Vera style).
  * On every reachable draw-406 upper-band output, the embedded projected lattice and the oriented positive-height winner
    uniquely determine the framed parent S and the final mark.
  * Exactly N(S)·|ker φ_S| raw designs produce that output, where N(S) is the number of prefixes reaching S.
  * The toys confirm this: all 2,654 positive-height winners in 17³ designs are recovered.
  * **Remaining.** The projection Jacobian fixes the covolume change, but the branch weight N(S) is the penultimate law
    itself. The weighted prefix sum over gated outputs (and p_a) is still the core.
  * **Lean.** InverseBranch.lean (axiom-clean) formalizes:
    * `framed_injective`: for gcd(k,q) = 1, any winner in W, ties included;
    * the recovery formulas R = M + Z(ũ − y/k), M = R ∩ K, [ũ] = [a·y];
    * `raw_fiber_card`: N(S)·|ker φ_S|;
    * a toy check mod 17.

* **Part 177 (audited, minor caveats).** [aliasing](research/wall1_aliasing.md): the width-506 final-block certificate and
  CBD aliasing.
  * **Profile data alone cannot certify.** A genuine null-lattice block (prescribed 518-vector prefix, recorded determinant,
    all 505 terminal GS lengths within 0.75% of GSA) has height-zero failure > 99.60305%.
  * **With a verified minimum, almost everything is tiny.** Take λ1(H) ≥ 54.82, which is 0.99759×GH (54.95253) and so a
    plausible shortest-vector scale. Then:
    * the norm cap costs < 0.000478351;
    * height-one failure on the cap is < 6.44·10⁻¹⁴;
    * all nonzero exact aliases are < 2.23·10⁻¹³⁸.
  * **Remaining.** The nonintegral dual-class contribution at heights 2–30, which is checkable from finite residue data of
    the actual block. How often width-506 BKZ meets the minimum floor is a separate question (the 0.954-ratio issue).
* **Part 178 (audited, SOUND).** [transfer_operator](research/wall1_transfer_operator.md): a transfer-operator recursion on
  framed states.
  * In the rank-4 toy, the least majorant determined by the parent's entire theta data (primal, dual and every labelled
    mark-coset series) has mean exactly 4× the true gated probability (8/4913 against 2/4913). Four reflected parents share
    all theta data, and only one wins under the signed tie rule.
  * An exact telescoping identity shows that earlier drift slack cannot cancel a terminal majorant's overestimate.
  * The factor 4 is a toy figure. The bound at width 506 is open.
* **Part 179 (audited, SOUND).** [invariant_majorant](research/wall1_invariant_majorant.md): isometry-invariant majorants of
  the selected indicator.
  * The least isometry-invariant majorant can exceed the signed-tie probability by exactly 2^r on a uniform orbit of r
    reflected old axes. A rank-22 integer graph realizes this with factor 2^20 = 1,048,576, keeping the normalized band and
    both quotient gates. So the toy factors 4 and 2 are not width-independent.
  * The excess is at most the probability that different shortest-line choices change the test outcome. How often that
    happens, or reflection orbits arise, under the restart law is unknown.
* **Part 180 (audited, minor caveats; KEY STEP for the repaired certificate).**
  [nonintegral_classes](research/wall1_nonintegral_classes.md): a satisfiable width-506 final-block test.
  * **Theorem.** Let a fixed, plant-independent width-506 block satisfy:
    * (i) a verified horizontal minimum ≥ 54.82 (≈ 0.998·GH);
    * (ii) every terminal GS length ≥ 99.25% of its GSA value;
    * (iii) a finite Gram-determinant projection test, exactly checkable from the physical projection and integer bases.
  * Then R < 0.005792 and Part 94 failure < 0.006271.
  * In terms of the Lean `smoothError` (full theta charge for height one, < 3.635·10⁻²⁶), the bound is < 0.006269755 at the
    99.25% floor and < 0.000607730 at the full GSA floor.
  * Heights 2–4 contribute < 10^−41.86, 10^−31.74 and 10^−9.71. On the physical zero design, R ≈ 6.4276·10⁻⁵³.
  * **Consequence.** The repaired Lean certificate's acceptance test (`restartCount_lwe`) can be met by explicitly
    checkable block conditions, so it is no longer vacuous. A BKZ-then-check-then-restart algorithm is rigorously correct
    whenever it accepts (Las Vegas).
  * **Remaining (the core, restated).** δ = Pr[the reducer's output fails (i)–(iii)], i.e. how often a reducer-selected
    width-506 block is near-GSA with λ1 ≥ 0.998·GH and passes (iii). Equivalently, the runtime of the Las Vegas algorithm.
* **Part 181 (audited, minor caveats).** [test_acceptance](research/wall1_test_acceptance.md): which Part 180 condition binds,
  and a revised test.
  * (iii) has acceptance exactly 0 on Part 108's forward pass: a frozen coordinate axis violates the height-5 dual minimum
    for every witness.
  * (i) at floor 54.82 rejects 13.73% of Haar lattices (16.63% at 0.998h). Lowering the floor to 52.20 keeps the 0.006269755
    bound.
  * (ii) asks for more than the Chen–Nguyen tail model gives (last GS ≈ 62.73% of GSA) [model comparison].
  * **Revised score test.** Accept on a computable bound for the expected number of nonzero horizontal competitors in the
    capped, shifted balls.
    * Every accepted plant-independent block has terminal failure < 0.000607731, ties included.
    * An independent Haar lattice at the model determinant is rejected with probability < 4.193·10⁻¹²² for any fixed
      orientation.
  * **Lean gap.** `restartCount_lwe` needs MinFloor plus a bound on smoothError, so the score needs a small adapter
    theorem.
  * **Remaining.** The probability that the reducer's output meets both the score and lift budgets on the same prefix.
* **Part 182 (audited, minor caveats).** [restart_passes_test](research/wall1_restart_passes_test.md): does the restart's
  terminal block pass the score test?
  * Via Markov, δ ≤ 0.005 would need E[score] ≤ 6.469·10⁻⁷, which already requires Pr[λ1(H_terminal) ≤ 26] < 4.318·10⁻⁷.
    Here 26 ≈ 0.47·GH, a much milder ratio than 0.954.
  * Existing first moments do not give this. Part 151 controls only the penultimate minimum, and Part 161's pre-projection
    count misses inherited horizontal vectors and projection-shortened vectors.
  * Part 117 transfers the exact-score rejection between the first pass and the marginal restart, with error
    < 0.00022304.
* **Lean (score test, Part 181).** FixedBlockScore / FixedBlockScoreRestart (axiom-clean):
  * 1 − success ≤ capTail(a) + score(a), with no MinFloor needed;
  * `restartScore_lwe`: with acceptance score ≤ s ∧ (prefix Babai sum) ≤ ℓ on the same prefix,
    Pr[wrong secret] ≤ ∏δᵢ + (c + s) + ℓ.
* **Lean (Part 177 bounds, width 506).** FixedBlockCap506 / Height506 / Packing / Fourier / DualCharge / IntegralAliases /
  Model506 / Aliasing506 / Score506 (axiom-clean, kernel-checked numerics) formalize:
  * `smoothError506_projected_null`: for the projected integer null lattice at rank 505 with λ1 ≥ 54.82 and the model
    covolume, smoothError ≤ 0.000478351 + 6.44·10⁻¹⁴ + 2.24·10⁻¹³⁸ + R.
    * The cap bound uses Taylor enclosures.
    * Height one uses a two-shell inequality plus packing.
    * The higher heights use an exact Poisson identity grouped by dual class with CBD weight ∏cos⁶, and integral aliases
      are < 2.23332·10⁻¹³⁸.
  * `failure_lt_score506`: score(1919/2) ≤ 0.00012938 implies terminal failure < 0.000607731.
  The remaining per-block obligation is the explicit nonintegral-class sum R (Part 180 bounds it under (i)–(iii)).
* **Lean (Part 180 lattice estimates).** SphericalPacking / GaussianPackingIntegral / GaussianPacking505 / GaussianGramPivots /
  ProjectionThetaBound / LogThetaConvex (axiom-clean) formalize:
  * the packing bound (3) for nonzero Gaussian mass under a minimum;
  * the height-one bound: λ1 ≥ 54.82 at rank 505 gives oneTheta and oneCharge ≤ 3.635·10⁻²⁶, with no outstanding
    hypothesis;
  * the Gram-pivot theta bound (2), the uniform-projection bound (4), and the projection-test predicate (5), with global
    convexity of log θ(e^x).
  Not formalized: equation (1), the height-2–30 charges, smoothError ≤ 0.006269755, and the `restartCount_lwe` corollary.
  The delegate declined these because the combined certificate would validate a concrete LWE key-recovery procedure, the
  same scope line as Part 140's numeric instance.
* **Part 183 (audited, SOUND).** [terminal_tail_047](research/wall1_terminal_tail_047.md): the terminal-minimum lower tail
  at ratio ≈ 0.47·GH.
  * **Removing the last draw.** Uniformly over histories through draw 406, the terminal event "λ1 ≤ 26" agrees with the
    old-witness event "projecting the penultimate lattice M off its designated shortest vector gives a nonzero vector of
    length ≤ 26", up to error < 3.210·10⁻¹⁴. Projection-shortened witnesses and ties are covered.
  * Outside probability < 4.249·10⁻¹², every raw lift of such a witness has length > 250 and loses > 98.9184% of its
    squared length.
  * **Remaining.** The probability of that penultimate-projection event. It is still a property of the reduction chain.
  * **Lean.** TerminalProjection / TerminalProjectionCount (axiom-clean) formalize:
    * F △ J ⊆ {N₊(2r/√3) > 0}, ties included;
    * E[N₊(R)] = |B₊(R)|/|K/M|;
    * Pr(F) ≤ Pr(J) + ε;
    * the kernel-checked numeric bound Pr(F △ J) < 3.210·10⁻¹⁴, conditional on two analytic inputs (C ≤ 1.4227…,
      g ≥ 31.9457…) stated as hypotheses.

  * **Lean (analytic inputs).** TerminalMajorant506 / TerminalScale506 (axiom-clean, kernel-checked) prove:
    * C(z) ≤ 1.422743743939 over the full 4096-bin sum;
    * g_floor > 31.9457118986 from the audited recurrence;
    * the numeric majorant < 3.209079·10⁻¹⁴;
    * `discrepancy_506_of_terminal_count`.
    Two geometric transfer obligations remain: the rank-506 Hermite cap s_i² ≤ 56.2142·D_i^{2/506}, and Part 161's
    complex-Gaussian Poisson/dual-coordinate count for the marked preimage.
* **Part 184 (audited, SOUND).** [penultimate_projection](research/wall1_penultimate_projection.md): first moments for Part
  183's penultimate-projection event E.
  * **Conditioning obstruction.** For a fixed raw candidate, membership plus the preceding columns fix the mark at its pivot.
    So a compatible branch has joint mass N(S)/Q^511, which is |H(S)| times the product of the marginals.
  * An exact finite sum counts each design in E ∩ G once. Its weighted estimate, and so Pr(E) ≤ 4·10⁻⁷, is open.
* **Part 185 (audited, SOUND).** [winner_alignment](research/wall1_winner_alignment.md): conditioning on y ∈ L(A) for Part
  183's event.
  * This gives an exact first moment for any prescribed family of raw vectors.
  * For a shortest lift y, zero is a closest kernel point to a·y for |a| ≤ 1; larger multiples need a torus return.
  * **Obstruction.** An exact width-3 example at q = 3329 with genuine shortest selections leaves quotient minimum 8.407,
    while every nonzero raw vector has length > 250. So shortestness and the cutoffs cannot force a short integer relation.
  * **Remaining.** The membership-weighted sum of conditional selection probabilities for E ∩ G, with budget
    3.9999566953·10⁻⁷.
* **Part 186 (audited, SOUND).** [quotient_slack](research/wall1_quotient_slack.md): how much slack the 0.47-ratio quotient
  event leaves.
  * **Haar benchmark.** The penultimate quotient has rank 504. At 0.47×its own GH the Haar hit probability is ≈ 2.7308·10⁻¹⁶⁶.
    At physical radius 26 with the audited determinant floor, the Haar parent gives 3.33666·10⁻⁶⁰. So the certified
    comparison budget is e^{122.218} ≈ 3329^{15.069}, not e^{365}.
  * **Coin comparison.** A fair coin choosing horizontal/vertical, then the shortest vector of that type, reproduces every
    path on matching strings, so Pr(E) ≤ 2^406·R_406(E). That loses e^{281.4}, which exceeds the budget by e^{159.2}.
* **Part 187 (audited, SOUND).** [local_comparison](research/wall1_local_comparison.md): local comparison of the quotient
  event E within the 3329^15 budget.
  * A reachable width-506 state forces E on every 103-draw continuation. A twin state with the same determinant, maximal
    mark order and a unique signed shortest vector misses E on the all-zero continuation (quotient minima √5 and √1601).
    Both are removed by Part 184's radius-250 exit, so worst-case states are not the issue.
  * At a 3329^15 comparison, the additive room is 1.71956·10⁻⁷.
  * Coarsening one inverse branch to the plane indicator costs exactly |H(S)|/k_S. The parent weights and k_S are
    unevaluated, and Pr(E) ≤ 4·10⁻⁷ is open.
* **Part 188 (audited, SOUND).** [state_counting](research/wall1_state_counting.md): counting bad framed states.
  * **Reach bound.** N(S)/Q^510 ≤ h_S^{−510}, with equality at maximal mark rank.
  * **Obstruction.** The Q² explicit raw-pair membership events partition the design space. Every such pair meets the
    length bounds, spans a saturated plane and has input rank 2 mod q, so congruence counting alone gives probability 1.
  * One fixed pair realizes both designated shortest lines at ≥ (Q−1010)^103 reachable parents, though these fall inside
    the radius-250 exit.
  * **Remaining.** How often the actual shortest-vector selections produce a compatible frame.
* **Part 189 (audited, SOUND).** [canonical_pair](research/wall1_canonical_pair.md): a fixed canonical lift pair.
  * On every hit, the designated first vector is < 0.93743·GH_505. At such radii a determinant-matched Haar lattice is
    empty with probability ≥ 1 − 3.373·10⁻¹⁵, so the void alone gives nothing. What is needed is the void conditional on the
    marked plane.
  * If the pair's last two input rows are independent mod q, each 509-column prefix has exactly one completion with pair
    membership. Both shortest-line tests are then deterministic functions of a uniform prefix.
  * Toys: of 15,625 designs, 25 prefixes are compatible and 9 give quotient hits; the pair realizes both lines on only 2.
* **Part 190 (audited, SOUND).** [rank2_transverse](research/wall1_rank2_transverse.md): a rank-two transverse law (paper proof;
  the Lean files cover the rank-one precedents).
  * **Rank-2 Haar incidence law.** A marked primitive plane is distributed as an explicit shape density times Haar on
    X_{n−2}. This gives a bounded-plane count and a formula for the conditional shortest-vector void (plane, quotient and
    lift shear).
  * **Which event matters.** Part 183's J (= E of Parts 184–186) is the INTERNAL spacing ≤ 26 of a primitive plane modulo
    the designated shortest line. The unrestricted outer-quotient event holds for every lattice in ranks 505/506.
  * At the rank-505 determinant floor, the Haar probability of E is 9.971193576034·10⁻⁶³ (enclosure). Part 186's 3.34·10⁻⁶⁰
    was a valid upper bound for the same event.
  * Times 3329^15 this gives < 6.815·10⁻¹⁰. **Equation (5), the event-specific chain-to-Haar comparison, remains open.** It
    needs the history-weighted probability that the canonical pair wins both shortest-vector selections.
* **Lean (Part 190, rank two).** RankTwoDivisors / Frames / Saturation / Mean / PlaneMean / Transverse / MinimumBound
  (axiom-clean) formalize:
  * `plane_mean` for all n ≥ 3: the primitive rank-2 mean value with normalization 1/(ζ(n)ζ(n−1));
  * `plane_disintegration`, a kernel on X_{n−2}, identified with Haar for n = 3;
  * a conditional count bound.
  Still open: a.e. SL_{n−2}-invariance of the kernel for n ≥ 4, the ShapeWindowLaw calibration, and OuterMinimumGeometry.
* **Lean (Part 190, rank-two product law).** RankTwoTransport / OrderedIncidence / Product / OuterGeometry / PhysicalCount /
  FrameVolume / AreaJacobian / ReducedWindow (axiom-clean) prove, for all n ≥ 4:
  * `kernel_ae_invariant` and `kernel_ae_haar`, hence `haarProduct`: joint law = planeMarginal ⊗ Haar_{X_{n−2}};
  * `outerMinimumGeometry`;
  * `bounded_physical_count`, an unconditional bound on the expected number of saturated planes passing the three
    physical gates.
  Still open: the ShapeWindowLaw transfer to basisDomain (generic multiplicity 4 of Gauss-reduced bases, boundary ties).
* **Part 191 (audited, SOUND).** [plane_comparison](research/wall1_plane_comparison.md): the chain-to-Haar comparison
  reduces to a single rank-2 Rankin lower-tail event, namely a saturated plane of area ≤ 1352/√3 in the penultimate lattice.
  Its Haar count loss is < 3329^{1.39}. The chain-side bound remains open.
* **Lean (Part 183 transfers).** ComplexGaussianLattice / ProjectedDualCoordinates / RadialCountingBins / ProjectedBallCount /
  TerminalCountObstruction / HermiteWitness506 (axiom-clean) formalize:
  * `projected_candidates_count`, for a projected-grid realization, proved via complex-Gaussian Poisson summation, the
    dual-coordinate bound and a 4096-bin radial sum;
  * an obstruction showing a fixed-floor count needs history hypotheses;
  * the Hermite witness checks: Blichfeldt gives s² < 61.45238·D^{2/506} unconditionally, and the sharper 56.2142 cap still
    needs the spherical-addition / lens second-moment estimate.
* **Lean (Part 183 discrepancy, unconditional in the Hermite cap).** BlichfeldtTerminal506.lean (axiom-clean, kernel-checked)
  proves the bound using only Blichfeldt's coefficient 61.45238:
  * L_406 ≥ 879.78234064;
  * terminal scale > 31.19677083 on every realized window path;
  * the majorant < 5.244·10⁻⁹;
  * Pr(F △ J) < 5.244·10⁻⁹ for every finite law of realized projected-grid histories with a uniform fresh mark.
  This uses 1.3% of the 4·10⁻⁷ budget. Applying it to the concrete generator still needs its TerminalDraw data (embedding,
  determinant normalization, tie agreement).
* **Part 192 (audited, SOUND).** [rank2_tail](research/wall1_rank2_tail.md): the rank-2 Rankin lower tail for the chain.
  * **Haar.** A saturated plane of area ≤ 1352/√3 occurs with probability in (2.00059·10⁻⁵⁸, 2.07179·10⁻⁵⁸). The comparison
    budget is < 1.84782·10⁻¹⁰.
  * **Chain.** A hit through draw 154 has probability < 5.284·10⁻¹⁵. Adding the controlled cases and exits gives
    Pr(A_406) ≤ Z + 6.515·10⁻¹².
  * **Remaining.** Z = Z₁ + Z₂:
    * Z₁: first hits at horizontal wins on draws 155–406 where every shortest vector of the hit plane is inherited;
    * Z₂: first hits at positive-height wins on draws 395–406 with winner length in (30, 33.22505).
* **Lean (Part 192 controlled cases).** Controlled* modules (8 files, axiom-clean) formalize:
  * the exact pair-membership law q^{−mr} and a first moment with an inward-cube count of the reduced Gram shell;
  * the binary Hermite bound on the retained winner;
  * the adaptive draw law;
  * raw and dual exit certificates, and the three later Gaussian sums;
  * the first-hit decomposition Pr(A₄₀₆) < Z₁ + Z₂ + 6.515·10⁻¹², with Z₁ and Z₂ disjoint.
  This is conditional on: last-used-coordinate coverage; the forced-state candidate estimates; the flag-charge enclosure
  ≤ 5.28399·10⁻¹⁵; the ternary winner cap; and the per-draw comparisons of event probabilities with their Gaussian charges.
* **Part 193 (audited, SOUND).** [z2_vertical](research/wall1_z2_vertical.md): the vertical-win residual Z₂.
  * Draw 395, heights k ≥ 13, and winner lengths s ≤ max(30.5, 0.945g) together contribute < 2.515·10⁻¹¹.
  * The conditional plane count is exact. A candidate fixes the fresh mark, and the fixed-radius void controls short
    competitors.
  * **Remaining.** Draws 396–406 with 1 ≤ k ≤ 12, s > 30.5 and 0.945 < s/g < 1.032298. This needs ≤ 6.485·10⁻¹¹ and requires
    the old-plane distribution on surviving prefixes.
  * An exact example has 2 qualifying marks (141 and 3188) out of 3329.
* **Part 194 (audited, SOUND).** [z1_horizontal](research/wall1_z1_horizontal.md): the horizontal-win residual Z₁.
  * The controlled mixed cases contribute < 1.36697·10⁻¹¹.
  * The angular argument fails in two ways:
    * a wholly old plane can cross the cutoff after arbitrarily little compression;
    * a mixed plane can take its second generator from the fresh column with zero compression.
  * An exact membership-conditioned sum counts the rest once.
  * **Remaining.** p_old (wholly old hits) + p_late (the mixed class on draws 403–406) ≤ 7.6330·10⁻¹¹.
* **Part 195 (audited, SOUND).** [plane_moment_recursion](research/wall1_plane_moment_recursion.md): a recursion for
  plane-count moments.
  * The one-step plane-count inequality holds.
  * On the Z₂ residual band, every incoming plane has area > (11163/10816)·a.
  * Horizontal wins bring in counts of saturated old rank-3 sublattices through the selected line.
  * **Obstruction.** In an exact rank-3 example, two mark groups with the same order and identical plane counts at every
    cutoff give next-hit probabilities 0 and 2/3. So the recursion does not close from counts alone, and the 6.485·10⁻¹¹
    residual remains open.
* **Part 196 (audited, SOUND).** [z1_old_planes](research/wall1_z1_old_planes.md): wholly old plane hits (p_old).
  * A wholly old horizontal first hit forces a < a₂(M_{i−1}) ≤ √(3/2)·a. The constant is sharp, attained by a scaled fcc
    lattice (Bergé–Martinet / Bangert–Katz).
  * At the enlarged cutoff, one summand of Part 192's draw-154 bound already exceeds 1.0039·10⁷.
  * The incoming state fixes the horizontal candidate, so the fresh mark gives only the conditional win probability.
  * **Remaining.** The win-weighted incidence on surviving prefixes plus p_late must total ≤ 7.6330·10⁻¹¹.
* **Lean (Part 183, concrete chain).** ConcreteTerminal506 / TerminalChainState / TerminalColumnLaw / TerminalGridFrame /
  TerminalRestartPath / TerminalWindowVolume (axiom-clean) prove `matrix_discrepancy_lt`. For a uniform 400×512 matrix over
  Z/3329 under Part 108's append-and-project rule, Pr(F △ J) < 5.244·10⁻⁹, with all geometric and probabilistic hypotheses
  discharged:
  * the projected-grid isometry;
  * the determinant path with D₄₀₆ normalization;
  * lexicographic tie agreement;
  * surjectivity of the fresh mark.
  The bound also holds conditionally on every 511-column history. Only the frequency of J itself remains (Parts 185–196).
* **Part 197 (audited, SOUND).** [enlarged_cutoff](research/wall1_enlarged_cutoff.md): early-draw plane first moments.
  * Keeping the terminal plane's area inside the flag constraints, Pr[any saturated-plane hit at cutoff 676√2] is
    < 5.412·10⁻³⁶ through draw 154 and < 2.041·10⁻¹² through draw 161. The majorant crosses 10⁻¹¹ at draw 162, or draw 168 at
    the original cutoff.
  * The old 10⁷ summand came from dropping 117 flag constraints at draw 38.
  * A small raw plane through draw 406 has probability < 10⁻⁶⁰⁴, so small planes effectively arise only through projection.
  * The Haar floor means at draw 406 sum to < 2.221·10⁻¹³.
  * **Remaining.** The selected-chain probability on draws 162–406.
* **Part 198 (audited, SOUND).** [flag_horizon](research/wall1_flag_horizon.md): extending the first-moment horizon.
  * Pr[any saturated-plane hit] < 8.336·10⁻¹³ through draw 164 at 676√2, and < 5.055·10⁻¹² through draw 171 at 1352/√3.
  * The previous crossing was dominated by j = 0 terms, which dropped subsequent winner tests. The new bound keeps the
    overlapping shortest-vector constraints and the realized determinant recursion.
  * **Scaling.** Near the crossing, each extra draw multiplies the majorant by ≈ 2000. At draw 406 a single radial term
    exceeds 10⁶³¹, so this technique cannot reach 406 without a stronger joint-selection estimate.
* **Part 199 (audited, SOUND).** [survival_constraint](research/wall1_survival_constraint.md): the joint-selection survival
  constraint gives no improvement.
  * Survival requires D_t ≥ D_{i−1}/R^{t−i+1}, which is compatible with the Blichfeldt floor. An explicit history keeps a
    length-√2 vector through all 406 freezes.
  * The vector in a j = 0 term wins immediately.
  * Deleting all j = 0 terms buys at most one draw. At draw 406, single j = 1 terms exceed 10⁶⁰⁸. The horizons stay at
    draws 164 and 171.
* **Part 200 (audited, SOUND).** [hybrid_tail](research/wall1_hybrid_tail.md): a non-adaptive prefix followed by a short
  adaptive tail.
  * The proven horizon counts adaptive selections from the specified marked restart law. A prefix may be dropped from the
    count only if it reproduces that law; knowing a different law exactly does not transfer the bound.
  * Stopping the restart after ≤ 171 selections and one fresh draw gives Pr(λ1 ≤ 26) < 5.0864·10⁻¹². But that window has
    GH > 297 with 235 columns unread, so it is not the terminal block Parts 180–183 need.
  * A fixed coordinate prefix leaving 7 draws yields Z^505, with minimum and least plane area exactly 1.
  * The adaptive tail removes Part 130's fixed-projector premise. Part 40 still applies when the total frozen plane ranges
    over a small predetermined family.
* **Part 201 (audited, SOUND).** [multistep_branch](research/wall1_multistep_branch.md): multi-step inverse branches.
  * Grouping k inverse branches preserves exact mass: conditional probability h^{−k} per coprime positive-height record.
  * In the dominant draw-406 radial terms, the final 117–118 winners lie in the earlier window, so they impose no equations
    on later marks (only competitor tests).
  * Joint competitor tests can help: an exhaustive toy leaves 24/121 mark tuples instead of 64/121.
  * Meeting the budget would still need a discount of > 10^620.27 on a single radial term.
* **Lean (Part 192 hypotheses, partly discharged).** Nine further Controlled* modules (axiom-clean) prove:
  * the forced-state candidate estimates;
  * the kernel-checked flag sum ≤ 5.28399·10⁻¹⁵ over 12,089 indices;
  * the ternary winner cap ‖v‖⁶ ≤ 2·det Gram;
  * the per-draw Gaussian comparisons for t ≤ 20, and for later t given a covolume floor.
  The terminal theorem now has exactly two hypotheses:
  * LastCoordinateCoverage for 1 ≤ t ≤ 154;
  * LaterDeterminantFloor for 21 ≤ t ≤ 405, which the 56.2142 Hermite cap would give. The proved Blichfeldt 61.45238 is
    weaker.
* **Part 202 (audited, SOUND).** [joint_exclusion_scale](research/wall1_joint_exclusion_scale.md): the uniform
  joint-exclusion ceiling.
  * For 117 and 118 later winners, the exclusion divisor guaranteed over all reachable prefixes is exactly 1. One reachable
    prefix keeps the old flag for every mark tuple; another loses it for every tuple.
  * A positive-height, maximal-mark example has survival > 1 − 10⁻⁵⁶¹, with a terminal old plane below both cutoffs. It
    already had a plane hit by draw 170–172.
  * The weighted first-hit estimate at draw 406 remains open.
* **Part 203 (audited, SOUND).** [delayed_plane_survival](research/wall1_delayed_plane_survival.md): delayed planes with
  survival.
  * There are reachable prefixes whose first sub-cutoff plane appears at draw 273 or 275, yet old-flag survival with a
    qualifying draw-406 plane has conditional probability > 1 − 10⁻²⁹⁸ (or > 1 − 10⁻³⁰¹). So "survival forces an early hit"
    is false in general.
  * Both prefixes fail Part 192's raw-good condition at draw 0 (raw squared norm 4773 < 250²), so they contribute zero to
    Z₁ and Z₂. The gated residual estimate remains open.
* **Part 204 (audited, SOUND).** [rawgood_dichotomy](research/wall1_rawgood_dichotomy.md): the raw-good gate alone does not
  force the early-hit dichotomy.
  * There is a raw-good reachable prefix whose first qualifying plane appears at draws 265–278, and whose old-flag failure
    probability is < 5.436·10⁻¹²⁷.
  * The family fails the dual floor at draw 156, so it contributes zero to Z₁ and Z₂. The weighted estimate under both
    gates (raw-good and dual floor) is open.
* **Lean (Hermite cap 56.2142 and Part 192 coverage).** The HermiteSphere* / HermiteLens* / ControlledPrefix* /
  ControlledCertifiedBounds / ControlledSuffixProfile modules (12 files, axiom-clean) formalize:
  * **‖z‖² ≤ 56.2142·covol(L)^{2/506} for every full rank-506 lattice**, via the spherical pair-sum inequality and the signed
    lens integral;
  * `LaterDeterminantFloor` for all 406 states;
  * LastCoordinateCoverage through draw 31.
  * Blichfeldt's 61.45 alone would not suffice: the charges total 2.74·10⁻⁷.
  * The sole remaining hypothesis of the Part 192 terminal theorem is InheritedPrefixCoverage for draws 32–154 (a
    horizontal winner with a short line already in the old projection). It is equivalent to LastCoordinateCoverage, and
    InheritedSuffixLift would suffice.
* **Part 205 (audited, minor caveats).** [doubly_gated](research/wall1_doubly_gated.md): the early-hit dichotomy under both
  gates.
  * Part 204's family fails the dual floor by draw 120. At draw 156 the floor needs block rank ≥ 8.
  * Any rank-deficient 256×120 coordinate rectangle through draw 406, even with adaptive choices, has probability < 10⁻²⁵⁰.
  * On every doubly-gated draw-406 history, projection-to-section indices are ≥ 1,893 for every rational plane.
  * The doubly-gated dichotomy and both residual ceilings remain open. Per the audit, shortening the horizontal tail to
    start at draw 172 requires separately accounting for draws 155–171 in p_old.
* **Part 206 (audited, SOUND).** [raw_section_compression](research/wall1_raw_section_compression.md): raw section area
  versus the terminal plane index.
  * The two gates give [C:P][P:B] ≥ 1893. The raw gate alone gives [P:B] ≥ 70 at the area cutoff.
  * Every draw-406 raw graph has a saturated plane of area < 266,710 < 1893a, so a raw first moment at that cutoff cannot
    give rarity.
  * The horizontal budget after charging draws 155–171 is 7.1275·10⁻¹¹. The vertical ceiling 6.485·10⁻¹¹ is open.
* **Part 207 (audited, CONFIRMED; negative).** [z2_terminal_law](research/wall1_z2_terminal_law.md): terminal-law attack
  on Z_rem.
  * The rank-505 Haar second moment of the primitive-plane count is infinite. With the common line cut off at
    b = 30.5·√3/2, intersecting pairs give 2.4297·10⁻⁷⁷, which is 4.16·10³⁷ times the disjoint-pair term.
  * Matching the full determinant profile does not transfer the least-area law: the chain law is finitely supported and
    the Haar law is atomless, so their total variation distance is exactly 1. Z_rem ≤ 6.485·10⁻¹¹ remains open.
* **Part 208 (audited, CONFIRMED with correction).** [z1_terminal_law](research/wall1_z1_terminal_law.md): terminal-law
  attack on Z₁.
  * Exact split: Z₁ includes a separate term Pr(B ∩ Sᶜ ∩ A₄₀₆) for terminal hits after the first hit plane is lost, so
    following the first plane alone is insufficient. A padded example has a plane of area 777 that collapses for ≥ 3328/3329
    of second marks, replaced by a plane of area 28√19346/5 with internal spacing 28. Audit correction: the example is
    unreachable (restart probability 0). Whether collapse-and-replace happens on reachable doubly gated histories is open.
  * Haar benchmark × 3329¹⁵ for internal spacing ≤ 26 exceeds the allowance by 9.5613. For the terminal-area event the
    conservative factor is 3329^13.49584. A factor ≤ 3329^14.72 covers only the spacing part; the residual needs an
    area hit (see Part 210).
* **Part 209 (audited, CONFIRMED with correction).** [zrem_flag_moment](research/wall1_zrem_flag_moment.md):
  line-conditioned first moment for Z_rem.
  * Conditioning on a primitive line removes the divergent second moment of Part 207. Counting a shortest line of each
    witness plane is an exact hit test, with eleven-draw Haar mean 1.908267663·10⁻⁵⁸.
  * Tests in the rank-504 quotient by the globally shortest line have eleven-draw Haar sums 3.0955·10⁻¹⁴ (single ball;
    permitted distortion 2094.97) and 9.3340·10⁻¹⁸ (line plus plane; permitted 6,947,681).
  * Part 193's abstract example (which needs a factor > 3.3022·10¹⁰) is unreachable: every reachable prefix has
    qM* ⊆ ℤᴺ, which the example violates. Open: an upper bound on the test means over reachable doubly gated prefixes.
* **Part 210 (audited, CONFIRMED).** [distortion_sharpening](research/wall1_distortion_sharpening.md): origin and
  slack of the 3329¹⁵ comparison factor.
  * 3329¹⁵ is Part 187's round-down of the allowed exponent 15.06928; Part 190 leaves the comparison conjectural. At draw
    406 there are ≥ 3329¹¹¹ incoming marks; the missing quantity is the fraction that pass the selected-history tests.
  * Refining the Haar spacing count gains < 1 + 2.37·10⁻¹³. More than 99.995% of Haar area hits at the determinant floor
    have spacing > 26, so a spacing bound does not cover the residuals.
  * Sufficient exponents (zero additive error): spacing 14.72162705 (horizontal) / 14.70997924 (vertical); terminal area
    13.49584267 / 13.48419485.
* **Part 211 (audited, CONFIRMED; negative).** [history_free_compression](research/wall1_history_free_compression.md):
  union over candidate prefixes × exact q-ary membership.
  * One family has > 10^589062 distinct final subspace pairs, all consistent with the reveal order and the width-506 GS
    caps, each with terminal area ≤ 729 and membership probability exactly 3329⁻¹⁶³²⁰⁰. The membership sum before clipping
    exceeds 10^14220.396.
  * Keeping the last j selections and only the earlier determinant allows terminal-hit probability 1 for every
    0 ≤ j ≤ 406 (≈ 1.5·10¹⁰ × the allowances). Membership counting alone cannot give rarity; the gates, the SVP comparisons
    and the first-hit exclusions must enter.
* **Part 212 (audited, CONFIRMED; partial positive).** [integrality_bound](research/wall1_integrality_bound.md):
  reachability integrality for Z_rem.
  * Outside an event of probability < 10^-749.44, the frozen integer section has squared covolume ≥ 2^99 at every draw
    395–406 and the terminal mark group has rank ≥ 115. Exceptional contributions: < 10^-466.5 (single ball),
    < 10^-95.3 (line plus plane), < 10^-749.4 (horizontal terminal area).
  * **Proved under the actual chain law (no Haar assumption):** vertical hits with incoming GH length g ≥ 35.15 have
    eleven-draw joint hit probability ≤ 6.57448·10⁻¹². Each positive-height candidate fixes one fresh mark before
    selection, because its height is invertible mod 3329. Remaining Z_rem budget for g < 35.15: ≈ 5.83·10⁻¹¹.
  * Negative: the direct Gaussian majorant exceeds 10³⁰ at every eligible endpoint outside the exception (this concerns
    the majorant only).
* **Part 213 (audited, CONFIRMED).** [hecke_randomization](research/wall1_hecke_randomization.md): Hecke randomization
  of the reducer.
  * For each fixed finite prime sequence there is a starting lattice (chosen after the sequence) for which every endpoint
    hits both the area and spacing events. Deep examples violate the inherited dual floor.
  * The mean-zero L² contraction 2√p/(p+1) per step is valid in rank 505 (Clozel–Oh–Ullmo). The pointwise conversion has
    local exponent (505²−1)/2 = 127512. Many unconditional Hecke steps from a fixed compact set give near-Haar
    probabilities uniformly there; no numerical step count is established yet (W1-R84). Conditioning later steps on the
    gates changes the kernel.
* **Part 214 (audited, CONFIRMED).** [hecke_gated_mixing](research/wall1_hecke_gated_mixing.md): explicit Hecke mixing
  from gated starts.
  * 46,595,465 independent index-two Hecke steps give discrepancy ≤ 9.89321·10⁻⁶¹ on the smoothed plane-area test,
    uniformly over gated draw-406 starts. The endpoint area probability is < 2.19843·10⁻⁵⁸.
  * Blocked: a fixed primitive vector survives with probability < 2^-46,595,465. Conditioning on survival eventually
    forces a small plane on every path. Superlattice steps keep the vector but can change primitivity and the selected
    winner. A shorter walk with an event-specific distortion bound is not established for the marked histories.
* **Part 215 (audited, CONFIRMED; partial positive).** [fresh_mark_extension](research/wall1_fresh_mark_extension.md):
  fresh-mark bounds under the actual width-506 chain law.
  * Vertical residual hits on draws 396–406 with incoming g ≥ 34.807: ≤ 6.44697363·10⁻¹¹. This uses per-height counting,
    plus determinant separation between eligible draws, which turns the factor 11 into a geometric sum. The certified
    draw-406 floor is g ≥ 32.18553678. Remaining Z_rem budget for g ∈ [32.1855, 34.807): ≈ 3.8·10⁻¹³.
  * Two qualifying vertical wins, both with g ≥ 34: ≤ 2.78189202·10⁻¹². Horizontal mixed hits on draw 403 (all scales):
    ≤ 2.87954220·10⁻¹¹. This leaves ≈ 4.2475·10⁻¹¹ of Z₁ for wholly old hits and for mixed hits on draws 404–406.
  * Obstruction for small g: when g ≤ 32.5 the conditional mean number of height-one shell candidates exceeds 118.27,
    so per-prefix first moments fail. The missing quantity is the frequency of small-g prefixes (W1-R86).
* **Part 216 (audited, CONFIRMED; reduction).** [small_g_frequency](research/wall1_small_g_frequency.md): small-g
  frequency for Z_rem.
  * Under the actual chain law, vertical residual hits on draws 396–406 with incoming g ≥ 34.807 cost < 3.75987·10⁻¹¹
    (improving Part 215). This leaves 2.72513·10⁻¹¹ for g < 34.807.
  * Any crossing below g = 34.807 on those draws requires at least 100 of the first 405 winners to exceed 1.10 × their own
    incoming GH length. With 99 exceptions, the draw-406 floor is 34.8186.
  * **Z_rem reduced to one lemma (long-winner ceiling):** if, on every incoming history, the conditional probability of a
    winner > 1.10·GH is ≤ 0.126, a binomial coupling (valid for dependent draws) bounds any crossing by 2.58815·10⁻¹¹, and
    Z_rem ≤ 6.485·10⁻¹¹ follows. The ceiling is open (W1-R88).
* **Part 217 (audited, CONFIRMED; reduction).** [long_winner_ceiling](research/wall1_long_winner_ceiling.md): the
  long-winner ceiling.
  * Long winners are impossible through draw 7; the incoming determinant floor covers draws 8–10. On every remaining
    unresolved prefix the conditional height-one candidate mean exceeds 1.85135·10¹⁶. The exact same-mark collision sum
    gives the variance but is not yet bounded.
  * Weaker sufficient ceilings: 0.126 on draws 11–380 only (all of 381–405 may be long) gives crossing < 2.456·10⁻¹¹;
    0.1795 on draws 11–405 gives < 2.478·10⁻¹¹. Both fit the 2.72513·10⁻¹¹ allowance. Open (W1-R89: covering / dual
    Poisson route).
* **Part 218 (audited, CONFIRMED; partial positive).** [z1_remainder](research/wall1_z1_remainder.md): Z₁ remainder under
  the actual chain law.
  * Mixed first-hit bounds: draw 403 ≤ 2.723·10⁻¹⁴, 404 ≤ 1.233·10⁻¹², 405 ≤ 5.536·10⁻¹¹, 406 unrestricted ≤ 2.468·10⁻⁹.
    Together with the covered parts of draw 406 and seven wholly old lookback bounds, the joint charge is
    6.4261010·10⁻¹¹ (replacing Part 215's draw-403 charge). This leaves 7.01399·10⁻¹² of the 7.1275·10⁻¹¹ Z₁ budget.
  * Uncovered: (a) mixed hits at draw 406 with 32.32 < g < 32.8, height 1–4, inherited plane minimum in (28.22, 29.2);
    (b) gated masses of surviving old planes and terminal replacements. A reachable prefix whose first area hit is at draw
    406 (spacing 28.0220) fails the raw gate at draw 0.
* **Part 219 (audited, CONFIRMED; negative).** [covering_ceiling](research/wall1_covering_ceiling.md): covering / dual
  Poisson attack on the long-winner ceiling.
  * The exact finite-group second moment sums Fourier coefficients within each class of M*/K* before squaring. A long
    winner occurs exactly when every admissible height misses its ball under the same mark.
  * Gaussian smoothing certifies a covered fraction < 4.18·10⁻²⁸ on every unresolved entry. Dual counting from the dual
    floor and integrality alone admits shell energy > 10^109.46 on every corridor. Both ceilings (Part 217) remain open.
* **Part 220 (audited, CONFIRMED; reduction).** [long_winner_routes](research/wall1_long_winner_routes.md): threshold
  tradeoff and sufficient criteria for Z_rem.
  * A crossing below 34.807 requires at least 175 winners > 1.00g, 100 > 1.10g, or 46 > 1.15g (closed form on
    [1, 1.15]).
  * Nearest-plane searches at 1.10g find a witness with probability ≤ 5.372·10⁻³⁷ (fixed order) or ≤ 0.00999 (exact
    search in 12 flag dimensions). This is a limit of the search method, not of the winner law.
  * Sufficient (open): ceilings 0.60 above 1.05g and 0.15 above 1.15g on draws 11–405 give crossing ≤ 4.21342·10⁻¹⁴; a
    conditional fourth moment E[(sᵢ/gᵢ)⁴ | history] ≤ 1.7860 gives ≤ 2.69977·10⁻¹¹. Both are valid for dependent draws
    (predictable stopping).
* **Part 221 (audited, CONFIRMED; partial positive).** [z1_last_pieces](research/wall1_z1_last_pieces.md): last pieces of
  Z₁.
  * Reaching g₄₀₆ < 32.8 needs ≥ 305 long winners. A conditional ceiling 0.5 would give < 9.85·10⁻²⁸, and 0.75 on draws
    11–405 would give < 2.215·10⁻¹² for the mixed piece (both open). Unconditionally, the paid mixed range now covers
    g₄₀₆ ≥ 32.75.
  * A gated wholly old hit on draw 406 forces ≥ 36 independent earlier column constraints for each fixed lift, with last
    used draw ≥ 57. Four terminal rank tests cost < 6.227·10⁻¹⁶ across surviving and replacement planes.
  * Balance: > 4.02079·10⁻¹² remains for mixed hits with 32.32 < g < 32.75 and the remaining wholly old mass.
* **Part 222 (audited, CONFIRMED; partial positive).** [long_winner_handle](research/wall1_long_winner_handle.md):
  raw-graph winner caps.
  * Counting short raw-graph vectors bounds early winner lengths under the original graph law. Hölder's inequality allows
    arbitrary dependence. The conditional hypotheses are now needed only on later draws: (A) on 67–405 → crossing
    < 2.3750·10⁻¹¹; (B) on 54–405 → < 2.4681·10⁻¹¹; (C) on 49–380 → < 2.0204·10⁻¹¹. Each fits 2.72513·10⁻¹¹.
  * Outside one exceptional set of probability < 2.417·10⁻¹¹, (B) holds for every next mark on draws 11–19. This lies
    inside each unconditional prefix, so there is no double charge.
* **Lean (InheritedSuffixLift).** ControlledSuffixWindow / Family / Mordell / Descent (axiom-clean) formalize:
  * `physicalSuffixOrigin_of_short`, unconditionally: every short retained winner through draw 154 comes from the initial
    lattice or from the window of the last used coordinate;
  * the suffix-family covolume identity;
  * the Mordell steps (rank 4 from 3, rank 8 from 7);
  * the Blichfeldt constants at ranks 9–155 except 24.
  The Part 192 terminal theorem now depends only on four classical Hermite constants: γ₅ = 8^{1/5}, γ₆ = (64/3)^{1/6},
  γ₇ = 64^{1/7} (Blichfeldt / Vetčinkin) and γ₂₄ = 4 (Cohn–Kumar). These are published theorems, not yet in Lean.
* **Lean (Hermite inputs, partial).** MordellBlichfeldtProfile / MordellBlichfeldtEnclosures / WatsonMinimalFamily
  (axiom-clean) formalize:
  * an unconditional suffix-length bound in every rank from Blichfeldt and Mordell constants;
  * five independent shortest vectors in rank 5 generate a sublattice of index ≤ 2, via Watson's inequality.
  * Weaker constants do not close Part 192: the prefix majorant rises to 1.128·10⁻⁹. So the sharp γ₅, γ₆, γ₇, γ₂₄ are needed.
    An external Lean formalization of rank-24 optimality exists but uses another toolchain.
* **Lean (sharp Hermite constants, partial).** HermiteRootExamples and the Watson* modules (7 files, axiom-clean) prove:
  * the rank-5 index-2 case λ1^{10} ≤ 8·covol², via a polynomial certificate;
  * the integral-form bounds in ranks 5, 6 and 7;
  * the D5/E6/E7 lower bounds;
  * Watson index bounds ≤ 4 in rank 6 and ≤ 10 in rank 7.
  Still open: the general rank-5 index-1 determinant bound and the reduction to full shortest families, the non-integral
  rank-6/7 upper bounds, and γ₂₄.
* **Lean (γ₅, nearly closed).** WatsonWellRounded / WatsonFiniteGram / WatsonGramVertices (axiom-clean) formalize:
  * the well-rounded reduction in every rank;
  * the exact finite Gram criterion for rank 5 (201 tests);
  * det ≥ 1/8 at all 24 vertex representatives.
  The only remaining obligation for γ₅⁵ = 8 is VertexCoverage: every extreme point of the normalized Gram polytope is a signed
  permutation of the 24 representatives. An exact edge walk (docs/research/scripts/watson_gram_vertex_audit.py) finds 15,040
  vertices in 24 orbits.
* **Lean (γ₅ closed).** WatsonGramChart / GramFeasible / Pivot / PivotChecks / PivotData / VertexCoverage (axiom-clean)
  prove:
  * `vertexCoverage`, via a symmetry-reduced integer certificate (448 local frames; generator in
    docs/research/scripts/watson_pivot_certificate.py);
  * **`rank_five`: ‖v‖^{10} ≤ 8·covol(L)² for every rank-5 lattice**, and `sharp_five`, so γ₅⁵ = 8.
  * The Part 192 terminal theorem now depends only on γ₆, γ₇ and γ₂₄ (`terminal_bound_of_six_seven_twentyfour`).
* **Lean (γ₆ closed).** WatsonRankSix / WatsonHigherChartBounds and supporting Watson* modules (axiom-clean) prove
  `rank_six` (λ₁¹² ≤ (64/3)·covol² for every rank-6 lattice), `intrinsic_rank_six` and `sharp_six` (γ₆⁶ = 64/3). The
  proof is a symmetry-reduced pivot and tangent-cone certificate over seven representative forms. The Part 192 terminal
  theorem `terminal_bound_of_seven_twentyfour` now depends only on γ₇ and γ₂₄.
  * Rank 7, partial: the finite residue-code test (d ≤ 10, max|zᵢ| ≤ 11d) and det G ≥ 1/64 for 33 representatives are
    proved. Still open is `Seven.Coverage`, which says every chart extreme point is a congruence image of a
    representative. It implies γ₇⁷ = 64 (`Seven.intrinsic_of_coverage`). The external walk did not finish at E₇, whose cone
    has 79,900,912 facets in 157 orbits.
* **Lean (Hermite budget for Part 192).** HermiteSevenTwentyFour (axiom-clean) proves the unconditional caps
  g₇ = (64/3)^{1/5} ≈ 1.84422 (Mordell, from γ₆), g₈ = (64/3)^{7/30}, and g₂₄ = (2/π)(13!)^{1/12} ≈ 4.16937 (Blichfeldt).
  Script: docs/research/scripts/wall1_hermite_budget.py.
  * These are too weak: with both substitutions the prefix flag sum is 3.78·10⁻¹⁴, against an allowance of
    6.54·10⁻¹⁵.
  * Thresholds (one cap varied, the other sharp), after reevaluating the three late sums: g₇ < 1.816489 and
    g₂₄ < 4.086149. With Lean's current rounded late bounds: 1.816034 and 4.078315. Sharp values are 1.811447 and 4.
  * Rogers' center-density bound gives g₂₄ ≈ 4.0811. That fits the reevaluated budget but is not formalized.
* **Frontier after Parts 1–132 (Nov 2026).** Rigorous today for plain LWE (511, 512, 3329), CBD(3): one exact SVP call in
  dimension 662 (1 − 2^-64) or 647 (99%) suffices (Part 39, in Lean), with no proven cost for that call (the prescribed
  provable sieve fails on these integral lattices, even with an irrational height). Ruled out as routes to β < 647:
  reducedness/flag/monotonicity/symmetrization arguments (Parts 30–37), A-independent or low-cardinality prefix families
  (Part 40, ≥ 2^679 planes needed at 406), union bounds over all bounded-covolume sublattices (Part 41, fails for β ≤ 1007)
  and over profile-admissible prefixes (Parts 42–43, mean > 2^163 at 647); the q-ary Z-shape only re-derives Part 39 (Part 44);
  randomized near-shortest selection keeps the profile but not the selection law (Part 45); exact Haar prefix laws exist but
  are quantitatively useless at finite width (Part 46). Any proof at the estimator's β ≈ 406 must analyse the concrete
  reducer's output distribution — an open research problem.
* **Frontier after Parts 1–206 (Nov 2026).** For plain LWE (511, 512, 3329), CBD(3):
  * **Success (in Lean).**
    * One exact SVP call in dimension 647 succeeds with probability ≥ 99% (Part 39).
    * Two calls in dimension 646 succeed with probability > 99.409%. This is kernel-checked end to end from (A, y), for any
      exact SVP oracle (`two_block_success`, Parts 131/132).
  * **Cost (on paper, audited).** An explicit ADRS/ASD18 exact-SVP algorithm costs ≤ 2^794.98 word operations at the
    recorded instance (Parts 140–141). Part 141's sampler lemmas are partly in Lean.
  * **BKZ route (in Lean, modulo δᵢ).**
    * The chain from (A, b) through a reducer's ordered basis, the plant-blind restart over k disjoint row blocks, the
      final-block test, uniqueness, the Babai lift and decoding to the secret is formalized (`restartAttack_lwe`).
    * Its bound is failure ≤ ∏δᵢ + reductionError + Σ 2·exp(−g²/12).
    * **δᵢ, the rejection probability of the reducer's output, is the only open quantity.** Part 171 corrects this: the
      current test's uniform terminal GS floor makes δᵢ ≡ 1, so the test must be restated (see Part 171).
  * **What δᵢ needs (Parts 134–144).**
    * Necessary: Pr[λ1(H) ≤ 16.86] ≤ 1/99 at β = 506.
    * Sufficient: λ1 ≥ 35.11.
    * Routes reduced or blocked:
      * plant averaging, change of measure, potentials and restarts all reduce to the selected window's lower tail;
      * Haar-only per-step hypotheses fail above ratio 0.18–0.20;
      * history-uniform horizontal bounds are impossible.
    * Remaining: history-averaged bounds on the horizontal and positive-height charges, and on the late-state upper tail of
      λ1/GH.
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
