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
* **Frontier after Parts 1–61 (Nov 2026).** Rigorous today for plain LWE (511, 512, 3329), CBD(3): one exact SVP call in
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
