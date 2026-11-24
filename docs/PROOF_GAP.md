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

**What this measures.** With the required constraint `β ≤ d`, this worst-case
approximation-factor route supplies no admissible block size for Kyber512, so it
does not supply a finite attack cost to subtract from the estimator's cost.
The former "about440 bits more" comparison is invalid after this correction.
The missing step is a sufficiently strong average-case analysis of BKZ's selected
profiles on the relevant random q-ary ensemble. The results recorded here do not
yet establish that step. The local residual/error budgets below are probabilities
in a proof route, not differences in attack-cost bits.

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
* **Part 223 (audited, CONFIRMED; partial positive).** [wholly_old_mass](research/wall1_wholly_old_mass.md):
  low-codimension sections.
  * The height cutoff fixes the candidate list before any column is revealed, so section counting covers adaptively
    selected witnesses. Unconditional joint bounds:
    * any terminal hit (including a replacement plane) with full-lift syndrome codimension ≤ 128: < 10⁻⁵⁰⁵;
    * wholly old creation on draw 406 with old triple lift codimension ≤ 128: < 10⁻⁶⁸³;
    * Part 218's residual mixed hit (‖x‖ < 29.2, 32.32 < g < 32.75) with codimension ≤ 129: < 10⁻⁸⁹;
    * the same for g ≥ 32.68 through codimension 130: < 10⁻³⁶.
    The codimension cutoff is part of the joint event.
  * Open: codimensions up to ~405. A codimension-400 wholly old family has membership first moment > 10^10163.41, so the
    gates and the selection rules must exclude it (W1-R95).
* **Part 224 (audited, CONFIRMED).** [budget_ledger](research/wall1_budget_ledger.md): global failure-budget ledger.
  * Every allowance traces to its source, and each exit is charged once. Z₁: 9·10⁻¹¹ (remainder 7.1275·10⁻¹¹). Z₂: 9·10⁻¹¹
    (Z_rem 6.485·10⁻¹¹, small-g part 2.72513·10⁻¹¹). Terminal remainder 6.515·10⁻¹². Spacing target 4·10⁻⁷.
  * A tighter radius-250 raw-exit bound, 2.35454·10⁻¹² (Lean-checked in scratch), releases 1.89446·10⁻¹². The initial
    prefix test then needs radius 2896, whose raw charge also passes Lean.
  * Recomputing all 12,089 flag terms gives a whole-prefix allowance of 3.782·10⁻¹⁴ under the proved Mordell/Blichfeldt
    caps. The total is 4.651680465762·10⁻¹² < 6.515·10⁻¹², i.e. Pr(A₄₀₆) < Pr(Z₁) + Pr(Z₂) + 4.652·10⁻¹²
    **without γ₇ or γ₂₄**. Formalization is in progress (W1-L81).
* **Part 225 (audited, CONFIRMED; partial positive).** [raw_graph_winner_cap](research/wall1_raw_graph_winner_cap.md):
  raw-graph winner caps, extended.
  * Unconditional: the draw-396 crossing below g = 34.807 has probability < 3.855·10⁻¹⁹. The fourth-moment bound (B)
    holds through draw 21 outside failures summing to < 1.083·10⁻¹¹.
  * Charging the vertical hit directly shrinks the sufficient windows for Z_rem itself to (A) 156–405 → 6.011·10⁻¹¹,
    (B) 132–405 → 6.355·10⁻¹¹, (C) 129–380 → 6.296·10⁻¹¹. Crossing-only windows: 71–405, 60–405, 52–380.
  * Outside a draw-55 exception < 4.659·10⁻¹⁵, a crossing needs ≥ 36 winners above 1.15gᵢ on draws 55–405.
  * At draw 405 the raw GH is 259.091 and the corridor endpoint 35.074; a raw vector that short has log₁₀ probability
    −709.2. The missing estimate is the projected volume contraction along the selected frozen space (needed below
    0.16135^k for rank k; W1-R97).
* **Part 226 (audited, CONFIRMED; partial positive).** [high_codim_sections](research/wall1_high_codim_sections.md):
  height counts through codimension 132–134.
  * Unconditional:
    * terminal hits including replacement planes through syndrome codimension 132: < 10⁻⁵³³;
    * draw-406 wholly old creation through 132: < 10⁻⁷⁰⁷;
    * mixed hits through 133: < 10⁻¹⁴⁹;
    * mixed hits through 134 with g ≥ 32.66: < 10⁻⁵².
  * R93's codimension-400 flags are selected with probability < 10^-47.36 (global comparison on draw 21). A modified
    family with ≤ 185 long winners has membership first moment > 10^356.14; its selected probability is open, and it is
    tied to the long-winner/frozen-contraction gap (W1-R97).
  * Balance > 4.0203·10⁻¹². Unpaid: mixed codimension 134–400 (32.33547 < g < 32.66) and 135–400 (32.66 ≤ g < 32.75);
    wholly old creation and terminal codimension 133–400.
* **Part 227 (audited, CONFIRMED; negative).** [frozen_contraction](research/wall1_frozen_contraction.md): raw-vector
  counts cannot bound long winners.
  * With probability > 1 − 3.276·10⁻⁵⁰, every draw 55–405 has > 2.14·10⁵² primitive height-one raw vectors of length
    ≤ 2383 (pairwise independence suffices). The frozen covolume is exactly ∏_{j<i} sⱼ.
  * The 0.16135^k contraction condition is necessary only for a projected Hermite determinant certificate. It gives no
    probability bound for simultaneous projected misses. The crossing on draws 397–406 remains open.
* **Part 228 (unaudited; negative/strategic).** [parameter_slack](research/wall1_parameter_slack.md): raising β does not
  remove the gap by existing certificates alone.
  * A higher deterministic floor could kill the small-g branch, but it cannot exclude wholly old Z₁ planes, since any
    covolume admits arbitrarily small primitive planes.
  * Verified Hermite squared caps: 56.21420, 56.79788, 57.84689, 58.89576, 60.99269 at ranks 506, 510, 520, 530, 550.
  * Cost correction: Part 140's 2^799.23 applies at rank 647, and Part 141 gives 2^794.98 word operations; neither gives
    a 0.29·Δβ increment.
* **Part 229 (audited, CONFIRMED; negative).** [sumset_covering](research/wall1_sumset_covering.md): deferred decisions
  and Kneser for the long-winner ceiling.
  * Deferred decisions reproduces exactly the all-heights law of Parts 217/219: one uniform mark in H = K/M shared by all
    heights.
  * At t = 1.10, each half-radius image occupies < 8.535·10⁻¹³¹ of H. Even granting disjoint credit, the aperiodic Kneser
    guarantees sum to < 6.043·10⁻¹²⁹, against the targets 0.8205 / 0.874.
  * Reaching the target needs a stabilizer of rank ≥ 37 (40 at t = 1.05, 34 at t = 1.15), and group structure alone gives
    no short dual representative. Diagnosis: r = t·GH lies beyond the smoothing regime, so only typicality inherited from
    earlier randomness can give coverage (W1-R100).
* **Part 230 (audited, CONFIRMED; partial positive).** [inductive_typicality](research/wall1_inductive_typicality.md):
  two-mark drift.
  * One-step drift: E[next height-one void | history] ≤ p(b₀)·p(b₁), where p is the current void profile at two smaller
    radii. This holds even though the first mark selects the projection: the inequality holds per first mark, and the
    map (U,V) ↦ (V, V+U) is a bijection on H². Contraction at the moving threshold still needs a shell-mass bound. At
    g = 35, t = 1.10, the smaller ball has 1.7660% of the volume.
  * From draw 129, outside < 10^-13.64, every qualifying draw-405 lift loses > 89.998% of its squared norm to the 276
    frozen directions.
  * A 0.18 void ceiling on draws 129–405 plus one 10⁻¹² exit gives Z_rem < 5.338·10⁻¹¹ (direct recomputation: 9.287·10⁻¹²
    before the exit charge). The ceiling is open (W1-R101).
* **Part 231 (audited, CONFIRMED; negative).** [drift_recursion](research/wall1_drift_recursion.md): a radial
  void-profile recursion fails.
  * Initialization at draw 129: corridor radius 641.6028, raw height-one hit probability ≤ 1.629·10⁻¹³⁰ on every
    incoming prefix. Outside < 10^-16.19, lifts lose > 56.248% of their squared norm to 128 frozen directions.
  * First transition: even the optimal mean-projector eigenvalue 1/505 credits no gain above 553.6765, against reference
    radius 560.3305, so a shell of width 6.654 is uncontrolled.
  * Two rank-505 examples share incoming distances mark by mark and the winner line, yet their voids are ≥ 602/3329 and
    ≤ 594/3329. They lie at scale 1.2815, below the reachable floor 32.428. A successful potential must track direction
    information (W1-R103).
* **Part 232 (audited, CONFIRMED; negative/strategic).** [worstcase_decoding](research/wall1_worstcase_decoding.md):
  worst-case reduction plus independent-error decoding.
  * Sample-space lattice: with 3329 error cosets, even exact translation-equivariant CVP succeeds with probability
    < 2^-847.47. This does not bound the usual graph-lattice decoder.
  * No guarantee can hold uniformly in A: for the identity with a zero row appended, optimal full-secret recovery is
    exactly (1716/4096)^511 < 2^-641.38.
  * Certifying a width needs a (1−δ) fraction of designs with conditional success ≥ 1−ε for both terminal decoding and
    lifting, with (1−δ)(1−ε) ≥ 1/2; the minimal β is open (W1-R105). Part 141's 2^794.98 covers its structured rank-647
    call on the 511-sample / 512-secret design only.
* **Part 233 (audited, CONFIRMED with qualifications).** [randomized_reducer_addendum](research/wall1_randomized_reducer_addendum.md):
  randomized reducers that keep the lattice.
  * A uniform primitive prefix up to a covolume cutoff preserves the lattice and gives the exact finite law of the
    projected quotient. In the Z³ example, 7,092 of 7,117 primitive lines hit. Shape equidistribution (Horesh–Karasik)
    alone cannot certify separation, because the prefix covolume sets the quotient scale. Developed in W1-R106.
  * Randomized near-shortest winners can only increase long returns on the current block. Without lookahead, the next
    displacement stays uniform on Q_*H.
  * Independent retries amplify as 1−(1−p(X))^R, but symmetries give no per-input lower bound on p(X).
  * Protected-span membership is equivalent to guaranteed retention; otherwise survival is < 1/p per step. An equal-index
    up/down pair that retains every original vector returns the original lattice.
* **Part 234 (audited, CONFIRMED; negative).** [directional_potential](research/wall1_directional_potential.md):
  directional (tensor) potentials for the void.
  * Two rank-505 marked lattices have identical nearest vectors for every label and the same winner, yet voids of
    exactly 600/3329 and 598/3329. Only labels ±1365 change, through projection of non-nearest representatives. Both lie
    below the reachable scale floor.
  * The two-mark bijection gives branch expectation h_uᵀT_S h_u. A reachable all-zero draw-129 prefix (probability
    3329⁻⁹³²⁰⁰) captures nothing, so no history-uniform lower bound exists.
  * Mean capture 1/505 per step gives only 42.136% squared-norm loss over 276 steps, against the > 89.999% a qualifying
    final witness needs. Potentials that follow individual witnesses cannot reach the 0.18 ceiling; selection among
    many witnesses must enter.
* **Part 235 (audited, CONFIRMED; negative).** [random_prefix](research/wall1_random_prefix.md): uniformly random
  primitive prefixes.
  * The quotient hit probability needs a first moment over nested flags (P, E). The unweighted sublattice-count ratio can
    underestimate it (example: 3/4 vs 1/240).
  * Rank-406 prefixes in the rank-911 raw lattice: for C ≤ 2^2090 the list is empty on every raw-gated input; for
    C ≥ 3329⁴⁰⁰ there are ≥ C(911,406) > 2^897 coordinate sections.
  * For a fixed horizontal lattice, a unique (or tied) shortest height-one terminal pair has probability O(C^{-n}) (Kim),
    so large cutoffs destroy recovery. No intermediate cutoff is certified.
* **Part 236 (audited, CONFIRMED; POSITIVE — alternative rigorous attack).** [selfdual_envelope](research/wall1_selfdual_envelope.md):
  exact-CVP primal decoding at width 638, without analyzing any reduction output law.
  * The attack uses four disjoint groups of 127 samples. On each group it solves exact CVP in the rank-638 graph lattice
    (secret retained), then validates on four held-out rows.
  * Success > 64.3162094%, reproduced with independent integer arithmetic.
    * Proof: a translated-ball first moment over uniform A, with ties charged as failures and zero-secret-residue points
      of membership probability 0.
    * The groups are conditionally independent given the shared secret; validation costs 4(7/3329)⁴.
    * Discarded coordinates lift correctly since |eᵢ| ≤ 3 < q/2.
  * Variants: width 632 → 1.8988940%; one 128-row group at width 639 → 61.4728334%. At width 506 this method's
    terminal-minimum floor stays < 0.879.
  * Cost:
    * Bounded enumeration gives < 2^1298 word operations. CBD-aware exhaustive search (squared norm ≤ 785) gets
      > 67.22% in < 2^1226, against a secret entropy of ≈ 1192.35 bits.
    * Randomized exact CVP (ADS, Cor. 5.7) costs 2^640 time and 2^638 space for four rank-638 calls, up to lower-order
      factors that still need finite bounds.
* **Part 237 (audited; negative + DEPENDENCY CORRECTION).** [detect_repair](research/wall1_detect_repair.md):
  detect-and-repair, and what Pr(E) actually suffices for.
  * Repair cannot be deterministic on E. The all-zero design reaches E with spacing 1, and any decoder there succeeds with
    probability ≤ (5/16)^512; that design fails the raw-good gate. Failure happens before lifting: on every F block the
    score exceeds 1.4984 > 0.00012938, so the block always rejects. No cheap complete detector is known.
  * **Correction:** Pr(E) ≤ 4·10⁻⁷ settles only the Part 184 spacing target. The proposed mean-score estimate forces
    Pr(F) < 4.317204·10⁻⁷; meeting both residual allowances would give Pr(E) < 1.84652·10⁻¹⁰.
  * The width-506 success proof also needs:
    * **score rejection frequency (Parts 181–182) — open.** Signed multiplicities, height-zero radii up to √960.5, and
      shifted counts at heights 1–30 are uncontrolled;
    * **joint acceptance with the prefix lift on the same returned basis (Parts 47, 181) — open.** `plantProb_liftFail_le`
      gives only the conditional lift.
  * Already proved: `failure_lt_score506` (terminal failure < 0.000607731 on acceptance), `restartScore_lwe`
    (composition), `terminal_bound_unconditional`.
* **Part 238 (audited, CONFIRMED; FIRST COMPLETE RIGOROUS ATTACK on plain LWE (511, 512, 3329), CBD(3)).**
  [cvp638_cost](research/wall1_cvp638_cost.md): the Part 236 attack, with an explicit finite cost.
  * The attack runs four sequential rank-638 exact-CVP calls (shifted discrete-Gaussian sampling following ADS15, with
    the ASD18 domination gap handled by an explicit joint coupling and an integral-midpoint terminal guarantee), plus
    validation.
  * Cost: < 2^778.825 word operations and < 2^766 words of space on a 768-bit word-RAM.
  * Each call returns a closest point for every admissible (A, b), with failure probability < 2⁻¹⁶⁸.
  * Recovery probability under the iid design and CBD(3) planting: > 64.31620941663886%. This includes validation and all
    solver failures, and was confirmed by exact integer arithmetic.
  * Ties: the guarantee holds for whichever closest point is returned.
  * Comparison: more than 447 bits below CBD-aware exhaustive search (< 2^1226 for 67.22%).
  * Unconditional, with no heuristics and no reduction-output law. The heuristic width-506 BKZ attack remains open
    (Part 237).
* **Part 239 (audited, CONFIRMED; partial).** [score_rejection](research/wall1_score_rejection.md): score-rejection
  frequency and joint acceptance with the lift at width 506.
  * Two reachable designs:
    * one where the score test rejects (C > 0.52566) although both radius-26 spacing events are false;
    * one with C = 0 and a uniquely shortest terminal line, while 407 discarded secret coordinates stay independent of
      the observation. So terminal success does not make the lift deterministic.
  * Bounds under the actual marginal restart law:
    * fresh-coordinate competitors on horizontal wins: mean score < 1.173483·10⁻⁷;
    * all signed multiples through deficiency 131: < 9.408·10⁻⁹²¹;
    * translated raw lifts ≤ 250: < 5.467503·10⁻⁹;
    * a winner of length ≤ 13 in the first 210 draws: < 4.929920·10⁻¹⁸.
  * Open: a remaining mean-score bound of 5.2408·10⁻⁷ (long raw lifts, higher deficiency); a score-accepted design with a
    late winner of length ≤ 13 and deficiency ≥ 133; the 0.005 rejection target; 99% recovery.
* **Part 240 (audited, CONFIRMED; negative).** [high_deficiency](research/wall1_high_deficiency.md): the high-deficiency
  region is typical and cannot be excluded deterministically.
  * Every frozen prefix through draw 407 has deficiency ≥ 133 with probability > 1 − 10⁻¹⁰⁶⁹.
  * A construction passes both raw gates, keeps two old vectors of length ≤ √65 after draw 406, selects at draw 407 an
    old winner of deficiency ≥ 134, and leaves a short line of full-lift deficiency ≥ 133 with all raw lifts > 250. Its
    two signs contribute > 1.98963754 to the score at plant height 0. The construction (with its column restrictions) has
    probability in [10⁻²⁰⁰⁵⁰, 10⁻²⁰⁰⁴³].
  * So the gates and shortestness cannot deterministically exclude high-deficiency contributors. The width-506 pieces
    (score mean 5.2408·10⁻⁷, score-accepted lift, unpaid Z₁) need a genuine probability bound on this region.
* **Part 241 (audited, CONFIRMED; partial).** [height_split](research/wall1_height_split.md): splitting the width-506
  score by plant height.
  * The full Part 47 prefix history preserves the product CBD(3) law of (e, s). This gives exact conditional score
    formulas at every height and a conditional bound S(D) on correct projection followed by failed lifting.
  * Bounded classes contribute < 5.283493·10⁻⁸ (height 0) and < 6.998082·10⁻⁸ (positive heights) to the mean score. The
    raw-lift class must be assigned before averaging over the plant.
  * Obstructions: a reachable design with C₀ > 0.5256662 while E, Z₁, Z₂ are all false; the all-zero design with averaged
    C₁ > 72.137. Error averaging is justified, but the selection frequency of such geometries is uncontrolled.
  * Open: the two rejection probabilities, the shared residual mean 5.2408·10⁻⁷, and the extra prefix rejection (the
    511-row transfer charges 111 axes).
* **Part 242 (audited, CONFIRMED; negative).** [score_first_moment](research/wall1_score_first_moment.md): a
  selection-free first moment for the width-506 score fails.
  * Every design admits a rank-407 prefix within the terminal covolume cap with primitive old-line spacing
    < 7.077·10⁻¹⁰⁷ and deficiency ≥ 140. After removing raw lifts ≤ 250, the height-0/1 mean over designs and plants
    exceeds 2.23·10¹⁰⁶ (> 4.26·10¹¹² × the 5.2408·10⁻⁷ allowance).
  * With chronological supports and all 407 caps, the height-zero incidence sum still exceeds 10^355.83 before the
    shortestness and raw-lift tests.
  * Only the residual at the actually selected prefix can fit the allowance; rejection and lifting remain open too.
* **Part 243 (audited, CONFIRMED; partial positive — coordinate deletion).** [fresh_review](research/wall1_fresh_review.md):
  * Coordinate deletion: if some input coordinates are untouched by every frozen vector, fixing the remaining columns
    determines the forced prefix, which agrees with the actual prefix on selection. The anchor tests on the untouched
    coordinates then use independent uniform marks.
    * The prescribed codimension-400 family (Parts 226/242) is selected with its three anchors with probability
      < 10^-1111.57.
    * Terminal small-area planes with rank 2 mod 3329 on untouched inputs (incl. replacement planes): < 2.377830·10⁻⁴¹.
    * Rank-3 wholly old first hits over draws 155–406: < 1.097258·10⁻²⁰.
  * Reformulated width-506 targets on the same returned basis: residual mean score ≤ 5.2408·10⁻⁷, and extra prefix
    rejection on score-accepted designs ≤ 0.003546229.
  * Conditional routes (open): an entropy bound (the sum of 405 conditional long-winner probabilities exceeds 48.6 with
    probability ≤ 7.6·10⁻¹²); three deferred probes (void ≤ 0.3914 at the smaller radius). The latter cannot hold
    uniformly: the all-zero start has void > 0.6427, though its draw-3 long-winner probability is 0.
  * Open: geometries touching all input coordinates.
* **Part 244 (audited, CONFIRMED; partial).** [generalized_deletion](research/wall1_generalized_deletion.md): generalized
  coordinate deletion. Rank-increase-detected contributions are negligible: Z₁ < 4.66·10⁻²⁰ and < 3.45·10⁻¹⁹; residual
  mean score at heights 9–30 < 1.31·10⁻⁸; length-cutoff violations < 4.95·10⁻⁶. Undetected configurations remain open.
* **Part 245 (unaudited; structural, negative for bounds).** [undetected_span](research/wall1_undetected_span.md): vectors
  passing every k-block span test form D_k^⊥, where D_k is the span of the column relations supported on ≤ k
  coordinates. Local membership forces global membership iff D_k spans all relations; k ≥ r + 1 always suffices and is
  sharp. Short lengths alone don't remove the exception (explicit example). This gives no new numerical bound.
  Remaining allowances: Z₁ > 4.0203·10⁻¹², residual mean score ≥ 5.1098·10⁻⁷, extra prefix rejection ≥ 0.00354128.
* **Part 246 (unaudited; reduction).** Entropy route for Z_rem (W1-R117, reported in chat only).
  * Part 230 gives a pointwise cap p_{i+1} ≤ a_i and a mean bound E[p_{i+1} | F_{i−1}] ≤ a_i·b_i, where a_i ≤ b_i are
    the small-radius void fractions.
  * A chord bound plus a supermartingale gives P(Σp_i > 48.6) ≤ P(L_λ > K) + e^{K−48.6λ}. With ρ = 0.273 this reduces
    the target to a single exit bound: P(max_{2≤i≤404} b_i > 0.273) ≤ 3.64·10⁻¹² (the remaining term is
    3.955368·10⁻¹²).
  * Deletion independence (Parts 243–244) alone cannot give this. A finite-group model satisfying both lemmas has tail
    > 1.0664·10⁻⁸; its reachability as a lattice history is unproved. Open: the small-radius void exit bound.
* **Part 247 (unaudited; negative).** [void_exit](research/wall1_void_exit.md): a reachable family of draw-2 histories
  has b₂ > 0.2974 (probability < 10⁻⁶⁶⁸⁹), so the Part 246 exit bound must allow exceptions even at draw 2. The exit
  probability on the remaining histories is uncontrolled.
* **Part 248 (geometry on paper; finite occupancy inequalities in Lean; no independent audit).**
  [projected_occupancy](research/wall1_projected_occupancy.md): for a primitive positive-height
  winner with height coprime to q, retain the exact projection quadratic form on the refined
  grid T = K + R. If N counts ellipsoid points and J counts ordered same-class pairs, the
  next void fraction is at most 1 − N²/(|H|J). The integer condition 727|H|J ≤ 1000N²
  suffices for a 0.273 ceiling. Checked on 68 planar branch/radius cases, including heights
  2 and 3. This is a sufficient statistic, not an exceptional-history bound; horizontal
  branches, the selected-history collision estimate, and the Part 246 exit bound remain open.
* **Lean (finite occupancy and history exits).** CosetOccupancy: `support_bound`,
  `void_ceiling`, `void_ceiling_273`, `void_ceiling_280`, and `history_exit_count_of`.
  Exact integer inequalities, with label types varying by draw and history. File compilation
  and axiom audits pass with only the standard three axioms. The geometric identification
  and the probability of certificate failures are not proved by these counting lemmas.
* **Part 249 (paper proof; interval checks, no independent audit).**
  [correlation_mgf](research/wall1_correlation_mgf.md): a nontrivial character of an
  exponent-3329 mark group obeys |â(χ)| ≤ sin(πp)/(3329 sin(π/3329)) for an indicator
  of density p. This improves the two-mark correlation second moment and exponential bound.
  Since the first seven long-winner probabilities vanish deterministically, it suffices to
  prove P(max_{7≤i≤404} b_i > 0.280) ≤ 6.426·10⁻¹²; the remaining compensator tail
  is < 1.174·10⁻¹². Alternatively threshold 0.281 and allowance 4.864·10⁻¹² suffice.
  These exit probabilities remain open. The Fourier and stopping proof is not Lean-formalized;
  80-digit interval checks and 640 exhaustive small-group subset checks pass. This addresses
  the vertical crossing route only, not the remaining score/horizontal/prefix obligations.
* **Part 250 (paper proof; exact finite and interval checks, no independent audit).**
  [affine_void_moments](research/wall1_affine_void_moments.md): under the original marginal,
  P(max_{7≤i≤12} b_i > 0.280) < 7.150·10⁻¹⁴. Projected voids are bounded by raw affine
  coset voids uniformly over the selected projector. An eighth-moment expansion classifies
  compatible affine ranks and also pays for inconsistent input dependencies. All 3327
  three-point affine coefficient classes have verified primitive integer normals, improving
  the Gaussian circuit bound. The verifier passes 893 finite-subset regressions and 80-digit
  interval checks. The remaining Part 249 target becomes
  P(max_{13≤i≤404} b_i > 0.280) ≤ 6.354·10⁻¹², still open. The numerical bound is
  not formalized. At the fixed raw radius on draw 16, the raw void fraction exceeds
  0.292912 for every matrix (interval-checked count bound); this rules out extending
  that same dominating raw-ball test by moment order alone, not the projected claim.
* **Lean (exact affine graph moments for Part 250).** AffineGraphMoments:
  `system_probability`, `joint_probability`, `first_moment`, `raw_moment`,
  `central_moment`, and `void_le_rank_sum`. The independent offset is encoded as
  the first uniform matrix column; incompatible and rank-deficient systems are handled.
  All nine public theorem axiom audits and file compilation pass with only the standard
  three axioms. Fixed candidate lists only. Geometric transfer, circuit enumeration bounds,
  Gaussian estimates, and the final 7.150·10⁻¹⁴ numerical bound remain paper results.
* **Part 251 (cancellation and pruned moments Lean-formalized; rank counts open).**
  [centered_affine_cancellation](research/wall1_centered_affine_cancellation.md):
  centered affine-incidence products vanish whenever one augmented input lies outside
  the span of all others. This gives an exact moment sum over tuples without coloops,
  retaining output-consistency indicators and repeated entries. All 1490 rational
  finite checks pass, including 799 forced cancellations. Counting the surviving
  patterns at width 506 remains open; no improvement to the history exception budget
  or the final BKZ success bound is claimed. `AffineGraphMoments` now proves
  `centeredProduct_zero_of_separator`, `centeredProduct_zero_of_coloop`,
  `central_moment_no_coloops`, and `void_le_no_coloop_sum`. File compilation and
  all thirteen axiom audits pass with only the standard three axioms. The formal
  pruned sum uses exact expectations; the explicit subset-rank expansion and
  rank-count majorant remain paper results. Candidate lists must be fixed.
  A further paper identity expresses each centered term as p^k(qD_0-D)/(q-1),
  where D counts full-support block relations and D_0 imposes one scalar output
  pairing. Inclusion-exclusion proves the identity without an analytic limit.
  It improves the termwise bound from 2^k p^r to p^r(1-p)^(k-r). Input circuits
  contribute p^(k-1)(1-p) for compatible outputs and exactly -p^k otherwise.
  An extension-field version replaces q by Q=q^m and uses a K-valued pairing,
  sharpening the negative bound to -p^k D/(Q-1); the positive bound is unchanged.
  Integer relation enumeration and the independent affine averages agree in all
  finite checks. The width-506 pattern counts and selected-history bound remain open.
* **Part 252 (paper proof and 781 exact finite checks; not Lean-formalized).**
  [affine_fiber_moments](research/wall1_affine_fiber_moments.md): the rank-one
  contribution alone forces the normalized Part 251 input-rank-only majorant
  above ((q^m-1)/q^d)^(k-1). At draw 13 and order eight it exceeds 10^6977,
  by exact integer comparison. Thus exact input-rank pattern counts cannot make
  that majorant useful; this is not a lower bound on actual failure probability.
  Grouping all candidate outputs at each input into one Bernoulli variable gives
  an exact centered moment expansion with output-compatibility counts. The entire
  same-input contribution is then at most mu^(1-k) after normalization. All 781
  candidate-set regressions pass at orders 2, 4, 8, including dependent inputs.
  Bounding dependent-support compatibility counts and retaining the later
  selected projection remain open. No final BKZ probability improvement is claimed.
* **Part 253 (paper proof, rational and interval checks; not Lean-formalized).**
  [affine_nullity_one](research/wall1_affine_nullity_one.md): a support with exactly
  one independent relation splits into its unique circuit and independent coloops.
  Its centered-moment correction factors exactly; singleton coloops cancel.
  Summing the circuit and repeated-coloop patterns with existing Part 250 counts
  bounds the normalized order-12 nullity-one correction at draw 13 by 2.468e-54.
  The normalized independent baseline is below 2.845e-13. **This does not bound
  the whole failure probability:** the correction from supports of nullity at
  least two is still present and unbounded. The interval verifier passes, and
  grouped-moment regression now covers 908 candidate sets, including a circuit
  with an independent fourth input. Later selected-history obligations remain open.
* **Part 254 (paper proof; exact finite and interval checks).**
  [affine_circuit_components](research/wall1_affine_circuit_components.md): supports
  that are direct sums of circuits and coloops admit a component expansion. The
  correction is bounded by k![z^k] exp(mu(e^z-1-z)) (exp(G(z))-1), with
  G(z)=sum_j epsilon_j(e^z-1)^j/j! and the existing circuit discrepancy bounds.
  At draw 13, order 12, the normalized correction is below 2.468e-54; terms with
  at least two activated circuit factors are below 4.174e-96. The verifier checks
  192 exact inequalities on two independent circuit components and the interval
  estimates. Supports containing a connected component of nullity at least two,
  including four collinear distinct inputs, remain unbounded. No complete void
  probability or BKZ success bound is claimed; this addition is not Lean-formalized.
* **Part 255 (paper proof; exact finite and interval checks).**
  [affine_rank_two](research/wall1_affine_rank_two.md): for h distinct collinear
  inputs, all multiplicity corrections share an envelope whose ordered sum is
  at most (2^h-1-h-binomial(h,2)) q^(h-3) epsilon_3. Three anchor points fix the
  input line, compatible outputs are determined, and all remaining fiber densities
  are retained as weights. This covers overlapping relations in rank-two components.
  Adding these activities to Part 254 keeps the normalized draw-13 order-12 correction
  below 2.468e-54. Terms with an activated rank-two noncircuit component are below
  4.506e-98. All 576 rational multiplicity checks, 64 aggregate checks, and interval
  assertions pass. Components with rank >=3 and nullity >=2, plus later selected
  histories, remain unbounded; no complete exit or BKZ probability is claimed.
* **Part 256 (paper proof; exact finite and interval checks).**
  [affine_rank_extensions](research/wall1_affine_rank_extensions.md): circuit
  anchors plus inner and outer basis extensions bound the weighted correction
  envelope at arbitrary input rank. At draw 13, order 12, including all connected
  components through size eight gives normalized correction <1.562e-23; through
  size nine gives <5.218e-12. Both include the earlier circuit/rank-two classes.
  The formula passes 768 rational rank-three support checks and interval assertions.
  Components of sizes 10--12, rank >=3 and nullity >=2 remain unbounded at a useful
  scale: the displayed size-12 majorant alone exceeds 9e32. This is a majorant
  limitation, not a true failure lower bound. No full draw-13 or BKZ probability
  improvement is claimed; the general lemma is not Lean-formalized.
* **Part 257 (paper proof; exact polynomial and interval checks).**
  [affine_square_certificate](research/wall1_affine_square_certificate.md): a
  degree-ten square certificate uses the Poisson orthogonal-polynomial kernel.
  Its draw-13 reference term divided by rho is <2.274e-12, with the independent
  nonuniform Bernoulli correction explicitly bounded by 2.575e-293. Exact rational
  centered coefficients transfer the earlier component estimates: all components
  through size eight, plus all circuits/rank-two components, contribute <4.859e-22.
  The size-nine transferred majorant exceeds 8.68e-11 and is insufficient. The
  new route leaves size-nine/ten connected components of rank >=3 and nullity >=2;
  it needs no size-eleven/twelve supports. All 139 rational checks and interval
  assertions pass. The remainder and later selected histories are unbounded;
  no total draw-13 or BKZ probability is claimed. This addition is not Lean-formalized.
* **Part 258 (paper proof; exact polynomial and interval checks).**
  [affine_nine_cancellation](research/wall1_affine_nine_cancellation.md): adding
  C_4/16 to the degree-five square root enforces c_9=-45c_10 in its centered square.
  The combined nine-input contribution then carries fiber-density factors and an
  eight-input remainder. At draw 13, the reference is <2.390e-12, the independent
  Bernoulli error <2.597e-293, earlier small components <4.950e-22, and all nine-input
  supports <3.210e-22. All 84 exact checks and interval assertions pass; the old
  polynomial helpers keep their original default behavior. The only remaining
  draw-13 class for this certificate is a connected ten-input support with rank >=3
  and nullity >=2, with an explicit unbounded remainder. Later histories remain
  open. This is not a total failure bound or a Lean-formalized result.
* **Part 259 (paper deduction; exact finite and interval checks).**
  [affine_four_circuit_stratum](research/wall1_affine_four_circuit_stratum.md):
  the remaining ten-input rank-three/eight correction is <2.197e-18 after
  normalization. On supports without a four-element input circuit, deleting c=4
  from the rank-extension witness sum is valid; ranks 4--7 then contribute
  <3.981e-14. The remaining signed term is restricted to connected ten-input
  supports of rank 4--7 containing a four-circuit. Its old majorant still exceeds
  752, so it is not bounded usefully. A ten-point F_11 moment-curve fixture checks
  all 210 four-subset ranks and two exact weighted envelopes using all affine maps;
  interval assertions pass. The new constant 2.432e-12 excludes the explicit
  remaining term and is not a full draw-13 probability. Later histories remain open.
* **Part 260 (paper deduction; exact finite and interval checks).**
  [affine_proper_subset](research/wall1_affine_proper_subset.md): a proper subset
  of a coloop-free support leaves at least one dependent outer completion. Keeping
  its fiber-density factor bounds the normalized proper-subset correction by
  6.927e-293. Compatible full tuples containing a three-circuit contribute <4.803e-59.
  Thus the remaining signed term reduces to a positive count N_r of compatible
  connected ten-point configurations, rank 4--7, with no three-circuit and with a
  four-circuit. All 17148 finite rank-deficit checks and interval assertions pass.
  The 2.432e-12 constant still excludes the explicit sum of N_r q^(-mr); that
  count and later selected histories remain open. This addition is not Lean-formalized.
* **Part 261 (paper proof; external Pollard theorem, exact finite/interval checks;
  not independently audited or Lean-formalized).**
  [affine_two_constraints](research/wall1_affine_two_constraints.md) closes the
  draw-13 raw-void step: P(b_13>0.280)<2.432e-12. Connectedness extracts a second
  circuit with a nonzero lift outside the original four-circuit span. The six-point
  case uses a precisely stated odd-set rearrangement corollary of Pollard's theorem;
  larger unions use Holder. Gaussian majorization retains both modular equations.
  The positive full-incidence remainder is <3.510e-31. Checks pass for 4160 odd-set
  cases, 282 six-form products, 132 extension witnesses, and the concrete interval
  calculation. Combining Part 250 and Part 249 leaves the sufficient open target
  P(max_{14<=i<=404} b_i>0.280)<=3.922e-12. The later fixed-raw-ball obstruction
  and score/horizontal/prefix obligations remain; this is not the full BKZ proof.
* **Part 262 (paper method obstruction; exact and interval checks).**
  [affine_reference_barrier](research/wall1_affine_reference_barrier.md) proves that
  the independent-fiber reference for the fixed draw-15 raw ball has zero-count
  probability >9.2603e-5. Every nonnegative pointwise void certificate has reference
  expectation at least that large, regardless of polynomial degree. Therefore an
  absolute-error comparison to that reference cannot close the remaining history
  budget. This is not a lower bound on actual affine or projected failure. The
  81 exact product-law cases and 80-digit interval bounds pass; the draw-16 raw
  coverage obstruction is rechecked. The next unresolved target is the selected
  projection's occupancy/collision statistic, or a stronger radius floor, rather
  than merely a higher moment order. No new selected-history probability is proved.
* **Part 263 (paper whole-flag identity; exact rational checks).**
  [flag_occupancy](research/wall1_flag_occupancy.md) gives finite half-open
  Gram--Schmidt cylinder representatives for the entire selected primitive flag.
  If projection loses k raw labels, each projected occupancy is repeated exactly
  k times: N=kN', J=kJ', h=kh'. The void fraction and N^2/(hJ) are unchanged.
  This removes positive-height and coprimality restrictions from the occupancy
  reduction, including horizontal branches and group losses. The sufficient
  certificate is 720 q^400 J_i<=1000 N_i^2 with raw graph collision tests.
  All 144 rational flag/radius cases pass, including kernel sizes 1, 3, and 5.
  The cylinder and radius remain design-dependent; fixed-candidate affine moments
  cannot be applied without addressing that dependence. No selected-history
  probability bound or full BKZ completion is claimed; not Lean-formalized.
* **Part 264 (paper conditional collision moments; exact finite checks).**
  [flag_collision_law](research/wall1_flag_collision_law.md) conditions on the
  containment equations AY=X of a fixed flag. Consistent input rank t costs
  q^(-mt), leaving a uniform map on d-t input dimensions. Normalizing residual
  pair equations by their input direction gives exact collision mean and variance,
  including repeated equations and mutually exclusive outputs. A one-sided
  variance bound supplies an explicit summand in a flag-weighted union bound.
  All 26 fixtures and 392 residual-map enumerations pass. The union must still
  cover the actual selected flags and moving radii; its width-506 numerical value
  is unbounded here. Containment is not selection, and the 3.922e-12 allowance
  remains open. Not independently audited or Lean-formalized.
* **Part 265 (paper saturation weights; exhaustive finite checks).**
  [flag_saturation](research/wall1_flag_saturation.md) first excludes proposed
  flags Gamma not containing q times their ambient saturation Lambda. For the
  remaining flags, finite subspaces F=Gamma/qLambda and E=Lambda/qLambda express
  exact saturation as E intersect graph(A)=F. Its conditional probability is an
  explicit full-rank product. Augmenting F by one or two collision differences
  gives exact joint probabilities and both collision moments under saturation.
  All 511 nested-space cases and 14468 joint-moment terms match direct enumeration.
  Flags with no label loss have E=F and saturation probability one; this correction
  alone does not bound their selected-history contribution. Shortestness and the
  width-506 flag sum remain open. Not independently audited or Lean-formalized.
* **Part 266 (paper selected moments; exact planar checks).**
  [selected_flag_moments](research/wall1_selected_flag_moments.md) encodes the
  chronological shortest-vector and signed-tie comparisons by a finite forbidden
  competitor list, using reduced raw lifts with an explicit norm bound. Combined
  with Part 265, inclusion--exclusion yields exact selected collision moments.
  Even truncations weighted by (J-c)^2 are pointwise upper bounds, giving a selected
  tail certificate without assuming independence. All 102 planar flag/radius cases
  pass selection, three moment identities, and every even-cutoff tail check.
  This restores shortestness to the finite flag formula, but its enormous subset
  and flag sums remain unevaluated at width 506. No improvement on the remaining
  history allowance or full BKZ completion; not Lean-formalized.
* **Part 267 (exact evaluation improvement; finite regression checks).**
  [selected_flag_moments](research/wall1_selected_flag_moments.md) now groups
  inclusion--exclusion terms by generated subspace and subset degree. Keeping
  degree preserves the even Bonferroni bound; replacing it by rank would not.
  Non-graphic spans and spans contradicting saturation are pruned only because
  every extension has zero contribution. The reusable `span_exclusion.py` powers
  the selected-moment checker. Its 102 planar cases still pass, using 144 distinct
  span moment evaluations instead of the expression's 5364 subset evaluations.
  Another 4100 rank-three cases verify grouping, pruning, cutoffs and repeated
  events against direct enumeration. This is a finite evaluation improvement,
  not a width-506 complexity or probability bound; the full flag sum remains open.
* **Part 268 (selected-law validation and parity certificate).**
  [selected_flag_moments](research/wall1_selected_flag_moments.md) now includes
  three-dimensional fixtures whose containment leaves a nontrivial uniform
  residual map. All 96 flag/radius cases pass exact selected moments, every
  even-cutoff bound, and complete first-selection probability sums of one.
  Twenty cases show a collision-mean change after selection. The identity
  J=N mod 2 supplies the nonnegative certificate (J-a)^2-1 for opposite-parity
  integer centers a, with a rigorous strict-tail denominator. It closes the
  toy q=3,R^2=1 exit bound to zero where the variance bound is positive, but is
  not uniformly exact in the other fixtures. None of these low-dimensional
  checks supplies the unresolved width-506 history bound. Not Lean-formalized.
* **Part 269 (conditional-law evaluator without field-point enumeration).**
  [flag_saturation](research/wall1_flag_saturation.md) implements exact conditional
  graph equations using RREF bases after eliminating fixed input pivots. It
  evaluates joint collision and saturation probabilities on residual coordinates,
  and is wired into the selected three-dimensional moment calculation. All 511
  nested-space cases, 14468 joint terms and 96 selected flag/radius cases pass.
  A q=3329, raw-dimension-517, fixed-rank-12 fixture checks 37 degree-two states
  in residual dimension 505, including impossible equations and saturation.
  This removes field-point enumeration from that path, but the eight added
  constraints are artificial independent directions, not the restart's complete
  competitor set. State/candidate/flag counts and the actual probability bound
  remain unresolved; no BKZ completion or tractability claim.
* **Part 270 (Lean parity and selected tail-count certificate).**
  `Research/Wall1/SelectedCollisionCertificate.lean` proves occupancy parity,
  nonnegativity and upper-tail monotonicity of (J-a)^2-1, positivity of its
  denominator, and a finite selected-tail count bound. `selected_occupancy_tail`
  applies directly to `CosetOccupancy.collisionCount` with history-dependent label
  types. Selection remains in the numerator; no conditional independence is
  assumed. File checking, target build and eight printed axiom audits pass using
  only propext, Classical.choice and Quot.sound. This formalizes the parity
  certificate layer, not the geometric identification, RREF probability formulas,
  inclusion--exclusion law or width-506 selected-history estimate. BKZ remains open.
* **Part 271 (Lean weighted Bonferroni and selected parity tail).**
  `Research/Wall1/SelectedBonferroni.lean` proves the even alternating-binomial
  upper bound, identifies present-subset counts with binomial coefficients, and
  reorders nonnegative weighted sums into the actual intersection expression.
  `selected_parity_tail` composes this with Part 270, retaining forbidden-event
  absence and the collision tail at every even cutoff. The target build and all
  eight printed axiom audits pass with only propext, Classical.choice and Quot.sound.
  This closes the finite inequality layer of the selected bound; the BKZ competitor
  geometry, conditional graph evaluation and width-506 numerical flag sum remain
  outside this theorem. No conditional independence premise or full BKZ completion.
* **Part 272 (Lean conditional graph rank-increment law).**
  `Research/Wall1/ConditionalGraphProbability.lean` derives the probability of
  a refined linear system conditional on a consistent row restriction. It is
  q^(-m times the input-rank increment) for a consistent refinement and zero
  otherwise. Conditioning positivity and rank monotonicity are proved, with
  q^(-m) as the one-rank-increment corollary. The target build and four printed
  axiom audits pass using only propext, Classical.choice and Quot.sound.
  This connects Part 264's basic conditional incidence formula to the existing
  exact system count. Saturation, geometric competitor identification, RREF
  program correctness and the width-506 selected-history bound remain separate.
* **Part 273 (mixed square selection certificate; exact checks).**
  [mixed_void_square](research/wall1_mixed_void_square.md) replaces the competitor
  absence indicator by the normalized square kernel of Part 257 while retaining
  its joint moments with the collision polynomial. The exact expression is a
  signed sum of factorial-weighted subset moments through degree 2t; no independence
  of competitor and collision counts is assumed. All 288 actual finite-design
  mixed identities and tail bounds pass; 34 improve on same-degree Bonferroni
  numerators. Another 945 polynomial checks and 45 reference identities pass.
  The much smaller Poisson reference value is not a design-law estimate. Actual
  width-506 mixed moments and the aggregate flag sum remain open; no numerical
  improvement for draws 14--404 or full BKZ completion. Not Lean-formalized.
* **Part 274 (weighted mixed-square optimization; exact checks).**
  [optimal_mixed_square](research/wall1_optimal_mixed_square.md) constructs the
  PSD Gram matrix of falling-factorial competitor counts weighted by the collision
  polynomial. Rational stationarity equations certify the optimal normalized square
  at the fixed degree, including singular matrices. All 324 finite weighted-law
  checks and 288 actual small-design mixed evaluations pass; 245 of the latter
  strictly improve on the same-degree Charlier square. This optimizes a fixed
  collision polynomial against supplied exact moments; PSD validation does not
  establish their provenance. The width-506 moment matrix and aggregate selected
  flag bound are still missing, so no improvement on the draw-14--404 allowance
  or full BKZ completion is claimed. Paper derivation, not Lean-formalized.
* **Part 275 (joint two-variable square; exact optimization certificate).**
  [joint_tail_square](research/wall1_joint_tail_square.md) optimizes a square
  polynomial affine in collision count J and degree t in competitor count Z.
  Its value at Z=0 is normalized to 1+a(J-T), a>=0, so it bounds the selected
  tail pointwise. The required moment orders remain h<=2t and collision degree<=2.
  Rational PSD/stationarity/complementarity checks certify the optimum, including
  active-boundary and singular cases. All 243 finite joint-law tests and 288
  small-design evaluations pass; 94 improve on the optimized product at the same
  integer threshold. Actual width-506 moments and their flag sum remain open;
  no draw-14--404 numerical guarantee or BKZ completion. Not Lean-formalized.
* **Part 276 (actual draw-14 numerical frontier; remainder still open).**
  [draw14_frontier](research/wall1_draw14_frontier.md) uses q=3329, N=518 and
  the proven mean floor 58.15006220912. The degree-24 Charlier square has reference
  contribution <9.131e-13, Bernoulli correction <1.120e-289, and correction from
  all circuits/rank-two components plus other components through size eight
  <1.160e-15. Their sum is <9.143e-13. The full draw-14 bound still includes an
  explicit normalized remainder from larger higher-nullity connected supports
  through size 24. Extending the old envelope to size nine already yields >0.00185,
  an unusable upper-bound value, not an actual probability lower bound. Interval
  assertions pass; no completed draw-14 estimate or improvement to the unconditional
  history budget is claimed. Later projected histories remain unresolved.
* **Part 277 (full-incidence reduction; conditional draw-14 bound).**
  [full_incidence_reduction](research/wall1_full_incidence_reduction.md) bounds
  proper-subset errors through connected full-incidence counts F_h, retaining one
  redundant outer input's density instead of repeating the one-circuit completion.
  Under the still-unproved full-incidence transfer target T(F)<=3.01e-12, all
  density-error terms, including mixtures, contribute <4.107e-197. The auxiliary
  caps F_h<=mu^h follow from existing bounds through size nine and from that target
  above size nine. Thus P(b_14>.280)<9.131e-13+T(F) conditionally; a sufficient
  remaining requirement is T(F)+P(max_(15..404)b_i>.280)<=3.0088e-12. Exact finite
  checks and outward interval assertions pass. The full-incidence target and later
  histories are not proved; no unconditional draw-14 closure or Lean proof.
* **Part 278 (general two-relation full-incidence envelopes).**
  [general_two_relations](research/wall1_general_two_relations.md) extends the
  circuit-pair witness to every girth, including new points inside the first
  circuit span. A weighted three-direction Holder/rearrangement bound retains
  the direction multiplicity constraint in the Gaussian count. At draw 14 the
  transfer from all circuits/rank-two components and other components through
  size nine is <7.162e-19. Components of size 10--24 and their mixtures remain
  open; admitting size ten into this envelope already gives >3.13e-7, not a true
  contribution lower bound. The largest size-ten strata have girth four and
  ranks five/four. All 816 witness cases, 2248 exact weighted inequalities and
  interval assertions pass. No full draw-14, later-history or Lean certificate.
* **Part 279 (rank-sensitive witnesses; components through size eleven).**
  [general_two_relations](research/wall1_general_two_relations.md) now chooses the
  second circuit outside the first circuit's span whenever r>c-1. Connectedness
  guarantees this choice even if other inputs lie inside that span, so t=1 witness
  terms are unnecessary in those ranks. The actual draw-14 full-incidence transfer
  through sizes nine/ten/eleven is respectively <9.013e-25 / 8.292e-19 / 6.038e-13.
  Applying Part 277's density-error formula only to these known smaller sizes
  includes proper-subset errors and all mixtures without a global incidence cap;
  the complete covered correction remains <6.038e-13. Reference plus covered
  terms is <1.517e-12. Remaining: the normalized signed size-12--24 correction
  plus P(max_(15..404)b_i>.280)<=2.405e-12. The size-twelve two-relation envelope
  exceeds 7.52e-5; its largest strata have girth four and ranks six/five/three.
  Strengthened witness tests and interval checks pass. No full draw-14 closure,
  later-history theorem or Lean proof. This supersedes Part 278's size-ten limit.
* **Part 280 (fixed uniform-stratum anchors and circuit-group Holder bounds).**
  [general_two_relations](research/wall1_general_two_relations.md) fixes both
  circuit witnesses when girth c=r+1, removing unnecessary positional union
  factors, and retains the three circuit group sizes in an additional Holder
  bound. The covered draw-14 correction through size eleven, including density
  errors and mixtures, improves to <6.541e-17. Reference plus covered terms is
  <9.132e-13; the normalized size-12--24 remainder plus later-history probability
  must still be <=3.0088e-12. This is not an unconditional draw-14 bound. The
  size-twelve envelope remains >7.48e-5. Added 101 nonvacuous fixed-position and
  510 exact three-group checks; existing witness/Holder and interval checks pass.
  Component coverage remains through eleven; larger supports and BKZ completion
  are unresolved. The new constants supersede Part 279's numerical accounting.
* **Part 281 (factorial-cumulant transfer and connected-support error control).**
  [factorial_cumulants](research/wall1_factorial_cumulants.md) retains exact
  Poisson forward-difference cancellations before taking coefficient majorants.
  Multivariate logarithms cancel disconnected label supports, including repeated
  labels. Selecting a smallest partition block bounds |kappa_j-F_j| by a density
  error; all mixtures contribute <3.475e-121 under the desired C(F)<=3.01e-12
  target, which itself implies the needed incidence caps. The existing full-count
  envelopes through eleven/twelve yield C bounds <2.551e-21 / <2.232e-8. Size
  twelve is still insufficient and larger supports remain unresolved. Conditional
  conclusion: P(b_14>.280)<9.131e-13+C(F), with remaining history target
  C(F)+P(max_(15..404)b_i>.280)<=3.0088e-12. All 240 transfer identities, 1866
  connected/error checks and interval assertions pass. No full draw-14 or Lean
  certificate; this provides an alternative to the older central transfer.
* **Part 282 (unique-four-circuit theta bound; incidence coverage through twelve).**
  [unique_four_circuit](research/wall1_unique_four_circuit.md) confines short
  six-column relation-code words to a saturated real plane. A unique weight-four
  direction improves its theta bound to theta(4 alpha) theta(5 alpha), with
  explicit long-word and periodic tails. No-coloop contractions supply at least
  k+1 basis extensions; paired four-circuits supply two ordered anchor witnesses.
  After removing those multiplicities, the actual draw-14 cumulant transfer
  through size twelve is <4.871e-13 (through eleven <2.548e-21). Remaining mixed
  charge M comes from size-13--24 components. A sufficient open target is
  M+P(max_(15..404)b_i>.280)<=2.5217e-12, giving conditionally
  P(b_14>.280)<1.4002e-12+M. All new exact regressions and existing cumulant/
  interval checks pass. No full draw-14 bound, later-history theorem or Lean
  proof; this supersedes the earlier size-twelve envelope failure.
* **Part 283 (short-code stratification and direct pair-sum count; through thirteen).**
  [short_relation_shapes](research/wall1_short_relation_shapes.md) separates codes
  with zero, one or multiple norm-four directions and counts the latter using
  finitely many balanced sign rows. The nine six-column sign pairs split into
  five triangular and four orthogonal codes. An integer ball-intersection count
  bounds the triangular equal-pair-sum configurations, with explicit nonzero
  modular layers. The actual cumulant transfer through size thirteen is
  <2.175e-13 (through twelve <4.247e-30). Remaining mixed charge M now involves
  size-14--24 components; a sufficient open target is
  M+P(max_(15..404)b_i>.280)<=2.7913e-12, giving conditionally
  P(b_14>.280)<1.1306e-12+M. Short-shape, exact integer-count, cumulant and
  interval checks pass. No full draw-14, later-history or Lean certificate.
* **Part 284 (several equal pair sums; restricted families only).**
  [multiple_pair_sums](research/wall1_multiple_pair_sums.md) extends the direct
  integer count to k equal pair sums and bounds all modular layers using their
  coordinate range. At draw fourteen, the connected 14-point family containing
  a four-pair anchor of augmented rank five has family-only cumulant transfer
  <3e-42. The twelve-pair rank-thirteen family on 24 points has transfer <1e-237.
  The verifier passes 75 finite energy comparisons, 20 exact range checks and
  interval threshold assertions. Other configurations and mixed terms remain
  open: full-class coverage still stops at thirteen, and Part 283's M and
  later-history target are unchanged. Paper calculation only, not a Lean proof.
* **Part 285 (general ear coverage; overlap-blind bound fails numerically).**
  [ear_decomposition](research/wall1_ear_decomposition.md) uses matroid ear
  decompositions to cover every connected support by h-r independent circuit
  relations. A labelled-witness dynamic program and triangular Holder bound
  give a universal envelope, but its size-fourteen transfer has log10 about
  521.573 and does not improve the existing bound. This is a loose upper
  envelope, not a lower bound or a refutation of the target. The 2,592 complete
  decomposition, 6,106 rank-increment and 192 rational Holder checks pass.
  Next analytic work must retain cross-ear overlaps. Full-class coverage with
  a useful numerical bound still stops at thirteen; no new Lean certificate.
* **Part 286 (linear residual transfer; five size-fourteen strata remain).**
  [linear_remainder](research/wall1_linear_remainder.md) observes that two
  components of size >=14 cannot coexist below degree 25. Thus the unknown
  transfer is exactly sum L_h U_h, including every mixture with known
  components. Mean-floor coefficient evaluation is justified termwise; the
  mixed/direct coefficient increment is <2e-42. Existing size-fourteen
  rank/girth envelopes outside c=4, r=5..9 add <6e-18, so admitting them
  preserves the rounded known-transfer bound <2.175e-13. Only those five
  strata remain in U_14; the size-15--24 classes and later histories remain
  open. Forty-eight exact identities and actual-parameter interval assertions
  pass. This simplifies the missing estimate but does not establish it or
  improve the complete exit bound. No Lean certificate.
* **Part 287 (direct orthogonal pair count; triangle exclusion is insufficient).**
  [orthogonal_pair_sums](research/wall1_orthogonal_pair_sums.md) bounds the four
  orthogonal six-point codes using a ball-intersection product and a full
  modular-layer correction. The production two-relation bound takes the
  smaller of this and its previous Gaussian estimate. Twenty exact real/modular
  and four rational Gram--Schmidt checks pass. A separately labelled diagnostic
  excludes eligible triangular six-point anchors but still gives a size-fourteen
  residual envelope about 6.8386e-4. No such family is admitted to the successful
  budget: Part 286's five residual strata remain open. This is an upper-envelope
  limitation, not a lower bound on the actual error. No new Lean certificate.
* **Part 288 (seven-point codes; triangle-free size-fourteen strata admitted).**
  [seven_point_codes](research/wall1_seven_point_codes.md) identifies the dominant
  seven-point witnesses. Exactly nine balanced short codes fit each prescribed
  four-/four- or four-/six-circuit pair, replacing 11025. A direct squared
  triple-count bound, with explicit weighted Gaussian aliases, lowers the
  admitted transfer including triangle-free size-fourteen strata to <5.395e-13.
  The remaining U_14 consists only of girth-four, rank-5..9 supports containing
  an eligible triangular six-point anchor. The sufficient open target is now
  sum L_h U_h + P(max_(15..404)b_i>.280)<=2.4693e-12; larger residual classes
  are unchanged. Finite code/count tests and interval budget checks pass.
  Part 287's triangle-free envelope failure is superseded. No full draw-14,
  later-history or Lean certificate, and no complete BKZ proof.
* **Part 289 (Lean support-cutoff certificate for the factored remainder).**
  `Wall1/LinearRemainder.lean` proves lower-support addition under multiplication,
  vanishing of higher powers below twice the cutoff, and linearity of the
  weighted factorial exponential remainder through degree 24 when U starts
  at degree 14. Only degrees 0..10 of the known multiplier are needed.
  File compilation passes; eleven theorem audits use only `propext`,
  `Classical.choice`, `Quot.sound`, with no `sorry` or new axioms.
  [Scope](research/wall1_linear_remainder.md): this formalizes the factored
  finite correction, not exponential factorization, cumulant/probability
  transfer, mean-floor monotonicity, or numerical geometry. No change to
  Part 288's unresolved activities or later-history target; BKZ remains open.
* **Part 290 (rare triangular-anchor existence; conditioning gap explicit).**
  [rare_triangular_anchor](research/wall1_rare_triangular_anchor.md) bounds
  eligible triangular six-point anchor existence in the fixed draw-14 fresh
  affine-graph model by 5(G_3+Alias_3)/q^(4m)<3e-87. All modular layers are
  retained. This does not bound high-order extension counts or selected
  histories. An exact affine-square example shows that deleting a full
  incidence while retaining proper-subset moments can invalidate a void upper
  bound; absence conditioning changes those moments. Interval, finite example
  and 256 event-TV checks pass. A robust conditional void transfer is still
  needed before using the rare event to replace Part 288's residual target.
  No full draw-14 or BKZ certificate follows.
* **Part 291 (third crossing relation; large new groups and rank nine admitted).**
  [triangular_third_relation](research/wall1_triangular_third_relation.md)
  extracts a fundamental circuit crossing a fixed rank-four triangular anchor
  and its basis extension. For t new points, 2<=t<=r-3 and the union rank is
  t+3. Fourier/Holder bounds retain the old exact pair energy and count the
  new group with all modular layers. At size fourteen, all t>=3 witness
  families contribute <1.566e-25; rank-nine t=2 adds <1.484e-24. The enlarged
  known transfer stays <5.395e-13. Remaining U_14 is restricted to ranks 5..8
  with only two-new-point eligible crossings. The open activity/history
  target remains <=2.4693e-12. All 186 crossing and 196 finite group checks
  and interval assertions pass. Larger classes and later histories remain
  open; no full draw-14, Lean or BKZ certificate follows.
* **Part 292 (parallel contraction; only rank-five triangles remain at size fourteen).**
  [parallel_contraction](research/wall1_parallel_contraction.md) shows by a
  single basis pivot that absence of every eligible large crossing forces
  the contraction by the triangular anchor to be loops plus independent
  rank-one parallel classes, each of size at least two. Counting within these
  classes gives <3.219e-17 for residual ranks 6..8, hence enlarged known
  transfer <5.396e-13. Only rank-five triangular configurations remain in
  U_14; larger classes are unchanged. The sufficient residual/history target
  is <=2.4692e-12. All 2593 graph, 137 pivot, 256 parallel, 81 partition and
  interval/budget checks pass. This is a paper refinement, not a Lean, full
  draw-14 or BKZ certificate.
* **Part 293 (rank-three short code; complete component coverage through fourteen).**
  [rank_five_code](research/wall1_rank_five_code.md) retains the fixed triangular
  plane in the last rank-five eight-point witness. The old integer projection
  has minimum positive squared distance 2/3; the third lattice height is at
  least 8/3. The cutoff sqrt(12)*30^2<3329 confines short representatives to
  three dimensions, with explicit long-vector and periodic tails. The last
  rank-five charge is <1.151e-28, so all size-fourteen classes are covered
  with known transfer <5.396e-13. The main cumulant probe uses the refinement.
  Remaining residual sizes are 15..24; their linear charge plus later-history
  probability must still be <=2.4692e-12. Projection, interval and cumulant
  checks pass. No full draw-14 exit, selected-history or BKZ proof, and the
  new geometry is not Lean formalized.
* **Part 294 (larger triangular components; other girths now obstruct).**
  [larger_triangular_components](research/wall1_larger_triangular_components.md)
  extends the third-relation bounds to sizes 15..24 and connects the smaller
  full-stratum envelopes to the main cumulant probe. The size-fifteen
  triangular envelope is <3.06e-4 and the full residual envelope <4.51e7,
  still far above the needed budget. A diagnostic excluding double-short
  anchors is dominated by rank-eight girth-three configurations; girths four
  and five also remain. These are upper-envelope limitations, not lower
  bounds on actual errors. Interval and prior cumulant checks pass; complete
  admitted coverage stays through fourteen. No later-history or BKZ proof.
* **Part 295 (external support excludes short independent directions).**
  [external_support](research/wall1_external_support.md) proves that a second
  circuit with t new positions and a proper nonempty old overlap has at
  least t+1 nonzero positions in every direction independent of the first
  circuit. For t>=4 the norm-four candidate count is therefore zero in
  those directions; first-circuit candidates remain. The finite checks
  cover 74,112 coefficient pairs and 369,792 directions. The full size-15
  envelope still has weighted log10 about 7.654, so the residual budget is
  not closed. Complete admitted coverage remains through fourteen.
* **Part 296 (external support improves the second lattice minimum).**
  [external_minima](research/wall1_external_minima.md) uses the support lower
  bound and even squared norms to force the second minimum to be at least
  E=2 ceil((t+1)/2). Gauss reduction gives height at least 3E/4, or E-1
  when the first vector has squared norm four. The full size-15 residual
  weighted log10 decreases to 7.62645; the no-double-short diagnostic drops
  to 4.82972 and is now dominated by rank-seven girth-four. All tail and
  periodic contributions remain. The necessary residual target and the
  full BKZ proof remain open; this geometry is not Lean formalized.
* **Part 297 (third circuits for orthogonal and shared-point anchors).**
  [other_short_anchors](research/wall1_other_short_anchors.md) extends the
  crossing-circuit cover to the other eligible double-short types, with
  180 six-point and 630 seven-point witnesses checked exactly. Adding these
  and triangular envelopes to the no-double-short remainder gives a full
  cover, now connected to the main probe. Its size-15 candidate has weighted
  log10 6.37057, still far above the residual budget. No selected-history
  or full BKZ proof is obtained.
* **Part 298 (four-circuit projection parity).**
  [four_projection](research/wall1_four_projection.md) proves perpendicular
  height >=t+3/4 for a second short direction outside a balanced four-row,
  and >=t+2 for even t with a three-position overlap. Exact checks cover
  6,561 old-coordinate tuples. The full size-15 residual weighted log10
  improves to 6.35668; the no-double-short diagnostic falls to 1.94692 and
  is now dominated by girth five. A first-ball/new-group alternative is
  retained where smaller. All tails remain. Neither the residual budget,
  selected-history bound, nor the full BKZ proof is complete.
* **Part 299 (three-row codes retaining the other short planes).**
  [other_third_codes](research/wall1_other_third_codes.md) proves positive
  old projection minima 1/2 for the orthogonal plane and 3/5 for the
  shared-point plane. With two new coordinates, the third heights are
  5/2 and 13/5. The cutoffs 28 and 29 retain all long and periodic tails.
  Exact checks cover 93,750 integer vectors and full cumulant regressions
  pass. The full size-15 residual weighted log10 drops to 1.94693, now
  close to the no-double-short remainder and dominated by girth five.
  This is still insufficient; larger sizes, selected histories, and the
  full BKZ proof remain open. The new geometry is not Lean formalized.
* **Part 300 (girth-five codes split by norm-six directions).**
  [six_short_lines](research/wall1_six_short_lines.md) shows that two
  independent balanced norm-six rows can span a full-support girth-five
  code only on eight positions. Short-line coefficient counts and separate
  theta bounds improve the full size-15 residual weighted log10 to 1.40954.
  The 1,278 finite-field classifications pass, with 144 eligible cases
  all of size eight. Girth-five strata no longer dominate; girth-four
  remains. The required residual and selected-history bounds, and hence
  full BKZ, are still unproved. No Lean formalization is claimed.
* **Part 301 (norm-six split inside the girth-four no-norm-four term).**
  [four_six_split](research/wall1_four_six_split.md) shows that two balanced
  norm-six rows in this restricted class force seven total positions.
  Separate zero/one/two-line theta terms retain all tails and improve the
  full size-15 residual weighted log10 slightly, to 1.40187. Exact finite
  classifications find 72 eligible girth-four cases, all size seven.
  Rank-seven girth-four remains dominant; this is not a residual-budget,
  selected-history, or full BKZ proof.
* **Part 302 (rare second short lines beside a norm-four circuit).**
  [rare_second_line](research/wall1_rare_second_line.md) counts independent
  norm-six and norm-eight witnesses beside the fixed first balanced row;
  their absence forces second squared minimum at least ten. All three
  cases retain cutoff-40 and periodic tails. Exact checks cover 14,465
  short-line cases and 175 prescribed-support uniqueness cases. The full
  size-15 residual weighted log10 drops to -3.28929, still far above the
  necessary residual budget. Triangular extensions and girth-six terms
  now dominate. Full BKZ and selected-history proofs remain open.
* **Part 303 (parallel contractions for larger short-anchor supports).**
  [larger_parallel_contraction](research/wall1_larger_parallel_contraction.md)
  extends the no-large-crossing partition cover to all three short-anchor
  types and sizes 15..24. The weighted recurrence is checked in 760 cases,
  alongside the existing partition and pivot checks. At size fifteen the
  triangular weighted log10 falls to -5.44209 and the full residual to
  -3.67322. The budget is still unmet; girth-six remainder terms dominate.
  Full BKZ and selected-history proofs remain open.
* **Part 304 (girth-six short lines including the first circuit).**
  [girth_six_lines](research/wall1_girth_six_lines.md) retains the ten
  balanced first-six-circuit patterns and counts independent short lines
  separately. Two-short-line Gram heights improve on supports of sizes
  eight, ten and eleven. Exact checks cover 948 girth-six pair cases.
  The full size-15 residual weighted log10 falls to -4.86704, still far
  above the required budget. Girth-three/four and triangular extensions
  remain, as do larger sizes and selected histories. Full BKZ is unproved.
* **Part 305 (fixed short planes with arbitrary crossing size).**
  [larger_third_codes](research/wall1_larger_third_codes.md) retains the
  three-row short-code count for every t>=2. The crossing's nonzero old
  row is supported in an independent anchor basis, so it cannot lie in
  the old relation plane. Third heights are t+2/3, t+1/2, and t+3/5 for
  the three anchor types. Exact checks cover 112,918 modular old parts.
  The full size-15 residual weighted log10 is -4.90099, still insufficient.
  No-large-crossing parallel completions, the no-double-short remainder,
  larger sizes and selected histories remain open; full BKZ is unproved.
* **Part 306 (one retained pair in a parallel class).**
  [marked_parallel_class](research/wall1_marked_parallel_class.md) retains
  the specialized two-new-position joint bound in one quotient class and
  counts remaining marked/unmarked classes separately. The 306 marked
  recurrence checks pass. The size-15 triangular weighted contribution
  is <1.88e-13; the full residual weighted log10 remains -5.00138 because
  the no-double-short remainder dominates. This family bound does not
  prove the full residual, exit, selected-history or BKZ statement.
* **Part 307 (girth-three short rows and exact five-point codes).**
  [three_six_split](research/wall1_three_six_split.md) includes both balanced
  six-support and (2,-1,-1) norm-six shapes, retaining short first-circuit
  rows. This gives only a tiny improvement. The subsequent
  [five_point_short_codes](research/wall1_five_point_short_codes.md) exhausts
  all 105 pairs of balanced norm-four lines on five positions and finds
  exactly six eligible codes over F_3329 for the prescribed three/four
  supports. The coefficient count drops from 225 to six; all geometric
  tails remain. No full residual, selected-history or BKZ proof is claimed.
* **Part 308 (rare second lines at arbitrary first-short support).**
  [general_rare_second](research/wall1_general_rare_second.md) bounds code
  counts by K4*K6 and K4*K8 without assuming the unique norm-four line is
  the prescribed first circuit. All specialized anchors use the refined
  one-short-line term. The 4,590 additional proper-support checks pass.
  The full size-15 residual weighted log10 improves to -7.04224, but
  girth-three five-point configurations still dominate and the residual
  budget is unmet. No full BKZ or selected-history proof is claimed.
* **Part 309 (weighted full-modular five-point count).**
  [five_point_weighted](research/wall1_five_point_weighted.md) uses unequal
  point weights and an exact square completion for the midpoint/shared-difference
  five-point code. All integer congruence layers are included. There are
  3,125 exact completion checks and eight full-modular small-ball checks;
  full cumulant regressions pass. The full size-15 residual weighted log10
  is -10.00541, still about forty times the entire residual budget.
  Girth-four terms, larger sizes and selected histories remain unresolved;
  full BKZ is unproved.
* **Part 310 (exact short-pair counts on seven and eight positions).**
  [four_six_seven](research/wall1_four_six_seven.md) derives the 23/4
  second height for the seven-point four/six pair and enumerates prescribed
  overlaps. This alone has little effect. Exact eight-point code counts
  for independent norm-six/eight rows lower the full size-15 residual
  weighted log10 to -11.30167 (about 4.99e-12), still about twice the
  entire residual budget before larger sizes and selected histories.
  Exhaustive actual-field classifications and full cumulant regressions
  pass; complete BKZ remains unproved.
* **Part 311 (dependent-point cover and other-anchor multiplicities).**
  [same_rank_extension](research/wall1_same_rank_extension.md) extends the
  fixed-plane third-code bound to one dependent new point and restores
  the justified e+1 quotient-basis multiplicity for other anchors.
  Exact checks cover 21,090 contractions. Full regressions pass, but the
  size-15 envelope remains about 4.99e-12. A new family/rank diagnostic
  identifies the shared-anchor rank-five same-rank term at about 2.65e-12;
  the new dependent-point cover does not beat its old bound. The residual,
  larger sizes, selected histories and complete BKZ proof remain open.
* **Part 312 (variance-based cube enlargement).**
  [cube_variance](research/wall1_cube_variance.md) uses the exact uniform-cube
  covariance and a one-sided second-moment inequality in the shared-point
  triple and outer ball counts. A positive radius-margin tradeoff improves
  the half-cube bound while retaining all modular layers. Exact small-ball
  checks and full cumulant regressions pass. The full size-15 residual
  weighted log10 improves to -11.47301 (about 3.37e-12), still above the
  updated residual budget. The admitted transfer through fourteen is now
  <3.419e-13, giving a sufficient remaining allocation of 2.6669e-12 for
  sizes 15..24 plus later-history probability. That target is unproved.
  Larger sizes, selected histories, and full BKZ
  remain open; this argument is not Lean formalized.
* **Part 313 (Gram strata; component admission through fifteen).**
  [eight_gram_strata](research/wall1_eight_gram_strata.md) stratifies the
  exact eight-point short-pair codes by integer Gram determinant. Unit
  minors justify the corresponding plane heights D/4, with all tails
  retained. The full size-15 weighted log10 is -11.61856; the admitted
  cumulant transfer through all size-fifteen classes is <2.750e-12 and
  is explicitly checked by the main probe. The remaining sufficient
  target is sizes 16..24 plus later-draw (15..404) bad-history probability
  <=2.588e-13. This target remains unproved; no complete draw-14 exit,
  selected-history or full BKZ theorem is claimed, and the new geometry
  is not Lean formalized.
* **Part 314 (determinant-twenty anchors and their extensions).**
  [twenty_plane](research/wall1_twenty_plane.md) proves that positive integer
  squared projection off the norm-four/norm-six plane of determinant twenty
  is at least 7/10. It counts 3360 such planes on eight labeled positions,
  and uses the resulting third-height bound with all tails and modular
  layers in the existing crossing/parallel-class cover. Exact checks cover
  6561 projection identities and the two-to-one witness multiplicity at
  three moduli. The cumulant transfer through fifteen is <1.654e-12;
  the sufficient remaining budget for sizes 16..24 plus later-history
  probability is now 1.3548e-12. This budget remains unproved. The size-16
  refined envelope is now dominated by rank-six girth-four components
  (weighted log10 about 3.53935), still far above the target. No full
  draw-14 exit, selected-history or BKZ theorem follows, and this geometry
  is not Lean formalized.
* **Part 315 (third-short-line split).**
  [third_short_split](research/wall1_third_short_split.md) splits the
  orthogonal/shared anchor extensions according to whether a new balanced
  norm-four line occurs. There are at most 3*choose(s,4-t) exceptional
  codes on a fixed t-new-position support. On the complement, the old
  planes' squared covering radii 2 and 8/5 give third squared heights at
  least 4 and 22/5. Both branches retain all tails and modular layers.
  The split is connected to dependent, crossing and marked-pair covers.
  Exact checks cover 4246 integer-vector reductions and eight exceptional
  line counts, in addition to the existing projection checks. For size16,
  rank6, the shared-anchor small-crossing unweighted log10 drops from
  31.11807 to 15.30519. Other anchor families and rank strata still leave
  the total far above its target. The cumulant probe passes 2106 exact
  checks and gives transfer through fifteen <1.557e-12, with sufficient
  remaining allocation 1.4518e-12 for sizes16..24 plus later histories.
  This remaining bound is unproved. This is not a full draw-14, adaptive
  selected-history or BKZ proof, and is not Lean formalized.
* **Part 316 (determinant-twenty third-short-line split).**
  [twenty_plane](research/wall1_twenty_plane.md) extends the exceptional
  line split to the determinant-twenty anchor. Its squared covering
  radius is at most 9/5, giving third squared height at least 21/5 in
  the absence of a new norm-four line. There are at most
  3*choose(8,4-t) exceptional lines. The split is used for all dependent,
  crossing and marked-pair branches; tails and modular layers remain.
  The regression passes 13199 exact vector checks and twelve line counts.
  It leaves the displayed full bound essentially unchanged; the next
  dominant rank8 terms have c=4,t=5. No residual budget is established.
* **Part 317 (nine-position Gram strata).**
  [nine_gram_strata](research/wall1_nine_gram_strata.md) exhaustively
  counts the c=4,t=5 norm-six/eight planes by prescribed old overlap.
  The Gram determinants are 23 and31, and duplicate determinant23
  witnesses are removed by equality of canonical plane sets. Unit minors
  justify the heights D/4; the nonexceptional coefficient count and all
  tails remain. Counts pass at q=7,17,3329 and the full cumulant probe
  passes all 2106 exact regressions. The size16 weighted log10 is now
  0.98644, dominated by rank5,girth4 at 0.93470, then rank8,girth4 at
  0.02345. Transfer through fifteen remains <1.557e-12. The remaining
  sufficient allocation 1.4518e-12 is still unproved, and the through24
  envelope remains about 3.97e236. Neither selected histories nor the
  full BKZ theorem have been proved; these refinements are not in Lean.
* **Part 318 (girth-filtered dependent shared-anchor extension).**
  [shared_dependent_codes](research/wall1_shared_dependent_codes.md)
  enumerates all105 additional balanced norm-four lines on the eight
  positions and checks all56 complementary supports per line. The
  girth-four survivors have Gram determinants 36,44,56,60 with witness
  counts24,28,24,5. Unit minors give primitive bases and third heights
  D/15; minors of absolute value below7 make the rank test exact at
  q=3329. The exceptional branch uses these strata and retains the
  nonexceptional bound and all tails. The full probe passes2106 exact
  regressions, with transfer through fifteen <5.295e-13. The sufficient
  remaining budget is2.4793e-12 for sizes16..24 plus later histories,
  still unproved. The size16 envelope log10 is0.04119, dominated by
  rank8/girth4, and the through24 envelope remains about3.97e236.
  This is not a full exit/selected-history/BKZ proof or Lean formalization.
* **Part 319 (determinant-twenty-three anchor cover).**
  [twenty_three_plane](research/wall1_twenty_three_plane.md) proves
  positive integer projection >=15/23 off the nine-position norm4/norm6
  plane and counts15120 labeled anchors. Its squared covering radius
  <=48/23 gives third height >=90/23 without an additional norm4 line;
  exceptional lines are retained separately. All dependent, crossing
  and parallel-class extensions and Gaussian tails are covered. Checks
  pass19683 projection identities,120 witness pairs,38852 plane-rounding
  identities, sixteen rare-line counts and2106 cumulant regressions.
  The size16 weighted log10 is -1.37896, now dominated by rank6/girth4
  and rank5/girth4. Transfer through fifteen remains <5.295e-13, but the
  residual allocation2.4793e-12 is unproved; the through24 envelope is
  still about1.71e233. Selected histories and the full BKZ proof remain
  open. The new geometry and counting are not Lean formalized.
* **Part 320 (both balanced determinant20 dependent types).**
  [twenty_dependent_codes](research/wall1_twenty_dependent_codes.md)
  checks both same-sign and mixed-sign overlaps of the norm4/norm6
  anchor. Girth filtering enumerates336 short lines and84 complementary
  supports each; unit minors establish primitive bases. The surviving
  third squared heights are D/20>=11/5. Per-stratum maxima across the
  two affine sign types give a uniform upper cover; all nonexceptional
  terms, Gaussian tails and modular layers remain. The cumulant probe
  passes2106 exact checks and retains transfer through fifteen <5.295e-13.
  Size16's weighted log10 is -1.76129, now led by rank5/girth4, then
  rank8/girth3 and rank7/girth4. The residual allocation2.4793e-12 is
  unproved and the through24 envelope remains about1.71e233. No complete
  draw14 exit, adaptive selected-history or BKZ proof follows; the new
  argument is not Lean formalized.
* **Part 321 (triangular third-short-line split).**
  [triangle_short_split](research/wall1_triangle_short_split.md) uses
  original balanced generators for every triangular sign pattern. Their
  squared covering radius is <=4/3, giving third height >=14/3 without
  an additional norm4 line. The exceptional line count is retained in
  dependent/crossing/marked-pair covers and the size14 rank5 baseline.
  Exact checks pass41066 plane reductions,24 rare-line counts and2106
  cumulant regressions. Transfer through fifteen is about5.28304e-13,
  below the retained5.295e-13 cap. Size16's weighted log10 is -2.18750,
  now led by rank8/girth3 and rank7/girth4. The remaining2.4793e-12
  allocation is unproved and the through24 envelope remains about1.71e233.
  The adaptive selected-history and full BKZ obligations remain open;
  this new geometry is not Lean formalized.
* **Part 322 (exact rare planes for girth3 on six positions).**
  [three_circuit_six_codes](research/wall1_three_circuit_six_codes.md)
  counts prescribed c=3,t=3 short planes, including the norm6 three-support
  shape. Each old overlap has3 determinant20 and6 determinant23 planes;
  all eligible norm8 planes already occur in the norm6 set. Counts and
  primitive unit-minor checks pass at q=7,17,3329. All residual families
  and Gaussian tails remain in the general two-relation cover. The full
  probe passes2106 exact regressions and keeps transfer through fifteen
  <5.295e-13. Size16's weighted log10 is -2.46811; rank8/girth3 is now
  -5.53603 and the leading stratum is rank7/girth4. The residual budget
  2.4793e-12 is unproved and the through24 envelope is about3.34e232.
  Selected histories, the full BKZ theorem and Lean formalization of
  these new counting/geometry arguments remain open.
* **Part 323 (determinant23 dependent-code girth filter).**
  [twenty_three_dependent_codes](research/wall1_twenty_three_dependent_codes.md)
  enumerates252 additional norm4 lines and all120 complementary supports
  per line. Unit minors give primitive row bases; minors below7 make
  the girth test valid over F_3329. Surviving third heights are D/23>=56/23.
  All exceptional Gram strata, the nonexceptional family and full tails
  remain in the dependent cover. The full probe passes2106 regressions
  and retains transfer through fifteen <5.295e-13. Size16's weighted
  log10 is -3.09089, led by rank4/girth4 and rank8/girth4. The remaining
  allocation2.4793e-12 is still unproved and the through24 envelope
  remains about3.34e232. Full selected-history and BKZ proofs remain
  open; the new counting/geometry argument is not Lean formalized.
* **Part 324 (all triangular dependent sign patterns).**
  [triangle_dependent_codes](research/wall1_triangle_dependent_codes.md)
  checks all5 balanced triangular patterns,300 short lines and35
  complementary supports per line. Girth-four survivors have Gram
  determinant32 or48; primitive unit minors give third heights D/12>=8/3.
  Uniform counts24 and6 cover all sign patterns with harmless overcounting.
  The full probe passes2106 exact checks and gives transfer through
  fifteen <3.419e-13. The sufficient remaining allocation is2.6669e-12,
  still unproved. Size16's triangular contribution has weighted log10
  -14.40256, but the full residual is -3.40933, led by rank8/girth4.
  The through24 envelope remains about3.34e232; adaptive histories,
  full BKZ and Lean formalization of these new arguments remain open.
* **Part 325 (girth-filtered four-circuit planes on six positions).**
  [four_circuit_six_codes](research/wall1_four_circuit_six_codes.md)
  enumerates one-norm4 planes with prescribed c=4,t=2 supports, rejects
  all support<=3 codewords, and retains exact Gram strata24,28,31,32.
  Determinant20/23 candidates belong to the excluded girth-three family;
  its separate cover remains. Unit minors and counts pass at q=7,17,3329.
  All other families and Gaussian tails remain in the general evaluator.
  The full probe passes2106 regressions and transfer through fifteen
  stays <3.419e-13. Size16's weighted log10 is -5.53071, dominated by
  rank8/girth3, whereas rank8/girth4 is -9.84777. The residual allocation
  2.6669e-12 remains unproved and the through24 envelope is about1.63e232.
  Full selected-history, BKZ and Lean formalization obligations remain.
* **Part 326 (girth-three determinant20 anchor cover).**
  [girth_three_twenty](research/wall1_girth_three_twenty.md) proves
  positive old projection >=3/10 for the six-position norm4/(2,-1,-1)
  plane and counts180 witness anchors. The full extension cover includes
  old supports of size2 for dependent points and size1 for marked pairs,
  as required at girth three. All short-line exceptions and tails remain.
  Checks pass15625 projection identities,180 witnesses, coverage of all
  removed plane keys at three moduli, and2106 cumulant regressions.
  Size16's weighted log10 is -9.84269, now led by rank8/girth4. Transfer
  through fifteen stays <3.419e-13, but the residual allocation2.6669e-12
  is still unproved and the through24 envelope is about1.61e232.
  Later selected histories, full BKZ and new-argument Lean proofs remain open.
* **Part 327 (orthogonal norm4/norm6 determinant24 anchors).**
  [twenty_four_plane](research/wall1_twenty_four_plane.md) proves the
  all-integer positive projection bound7/12 by rounding in the old plane
  and exhaustively checking all577 integer vectors of squared norm<=3.
  It counts5880 eight-position anchors and retains all third-code tails
  and short-line exceptions in their extension cover. Both affine
  dependent sign types are checked on336 lines and84 complements each;
  surviving third heights are D/24>=9/4. All2106 cumulant regressions pass.
  Size16's residual is about3.17e-12, still above its2.6669e-12 allowance.
  The explicitly computed transfer through sixteen is3.5070600055e-12,
  exceeding3.01e-12: size16 is NOT admitted. The dependent refinement
  leaves this total essentially unchanged. Through fifteen remains
  <3.419e-13, while through24 is about1.61e232. Later histories, full BKZ
  and new-argument Lean formalization remain open.
* **Part 328 (seven-position determinant23; admission through sixteen).**
  [seven_twenty_three](research/wall1_seven_twenty_three.md) distinguishes
  the seven-position short plane from the earlier nine-position type.
  Rounding and all99 integer vectors of squared norm<=2 prove positive
  projection >=11/23;84 pairs per first support give2940 anchors. The
  full extension cover keeps all exceptions and tails. The full probe
  passes2106 exact regressions and gives transfer through sixteen
  <9.583e-13, superseding Part327's failed admission. The remaining
  sufficient condition is sizes17..24 plus later-draw (15..404) bad-history
  probability <=2.0505e-12. That condition remains unproved; through24
  still has an ineffective envelope about1.61e232. No full draw14 exit,
  selected-history or BKZ theorem is claimed. New geometry is not in Lean.
* **Part 329 (norm-six pair strata on nine positions).**
  [six_six_nine_codes](research/wall1_six_six_nine_codes.md) addresses
  the new size17 girth6 obstruction. Prescribed overlap counts for
  determinants27/35 are28/72 at overlap3,0/96 at4, and0/240 at5.
  Unit minors and girth tests pass at q=7,17,3329. The full short-plane
  bound retains all other families and tails. All2106 cumulant checks
  pass, and through sixteen stays below9.583e-13. Size17 remains open.
* **Part 330 (girth-eight eleven-position geometry).**
  [eight_eight_eleven](research/wall1_eight_eight_eleven.md) proves that
  two norm8 rows with eleven-position support and girth8 have inner
  product of absolute value one, hence second squared height63/8.
  The other reduced-minimum case uses heights10,15/2; both full tails
  remain. All1960 partners and2106 cumulant regressions pass. Through
  sixteen is about8.79745e-13, below the retained9.583e-13 cap. Size17's
  weighted log10 is8.62756, now led by rank8/girth4 and rank8/girth3.
  The remaining2.0505e-12 allocation is unproved; through24 remains
  about1.61e232. Full selected-history, BKZ and Lean obligations remain.
* **Part 331 (five- and ten-position rare-plane counts).**
  [five_ten_gram_strata](research/wall1_five_ten_gram_strata.md) removes
  duplicate determinant23 planes on five positions and counts the
  determinant28/32 ten-position planes for each prescribed overlap.
  Exact enumeration passes at q=7,17,3329; all2106 cumulant checks pass.
  Through sixteen is about8.78533e-13, below the retained9.583e-13 cap.
  Size17's weighted log10 improves from8.62756 to7.21025, now led by
  rank9/girth7. The remaining2.0505e-12 allocation is still unproved;
  through24 remains about1.61e232. No full BKZ or Lean proof is claimed.
* **Part 332 (girth-seven short-plane geometry).**
  [girth_seven_geometry](research/wall1_girth_seven_geometry.md) uses
  projective column-group sizes to show that norm8 pairs on H positions
  satisfy |dot|<=3H-30. At H<=9 such pairs cannot occur; at H=10,11
  their second squared heights are at least8,55/8 respectively. The
  remaining reduced-minimum case and all tails are retained. All3254
  partner checks and2106 cumulant regressions pass. Through sixteen
  remains below9.583e-13. Size17's weighted log10 is6.56746, now led by
  rank9/girth4. The residual allocation and full BKZ proof remain open;
  this new geometry is not Lean formalized.
* **Part 333 (eleven-position rare counts and full norm-eight shapes).**
  [eleven_gram_strata](research/wall1_eleven_gram_strata.md) counts105
  determinant31 planes for each prescribed overlap1 or3, and zero for2.
  Separately, norm-eight reduced pairs covering eleven positions have
  |dot|<=3 even when one row has support five and a coefficient2. This
  improves the no-four/no-six second height to55/8, retaining the
  other minimum case and every tail. Modular counts and2718 full-shape
  checks pass, as do2106 cumulant regressions. Through sixteen stays
  below9.583e-13; size17 weighted log10 is6.56131. The gain is small and
  does not meet the residual allocation. Next separate the selected
  cover's short-anchor charges from raw two-relation terms. Full BKZ
  and Lean obligations remain open.
* **Part 334 (selected-cover diagnosis and norm-ten split).**
  [norm_ten_split](research/wall1_norm_ten_split.md) reconstructs the
  selected cover and identifies the one-norm-four term as the dominant
  size17 rank9/girth4 loss. On eleven positions, independent norm-ten
  rows have ten unit entries. Inner product +/-3 produces a previously
  counted norm-eight row; otherwise determinant39 applies. At most1512
  witnesses suffice; the remaining second squared height is at least11.
  All tails remain. The1512 witness checks and2106 cumulant regressions
  pass. Size17 weighted log10 is6.24900, now led by rank8/girth3; through
  sixteen stays below9.583e-13. The residual allocation, adaptive bridge,
  complete BKZ proof and new Lean formalization remain open.
* **Part 335 (five-position girth-three determinant20 anchor).**
  [five_twenty_anchor](research/wall1_five_twenty_anchor.md) derives
  an all-integer projection formula with positive minimum1/5 for the
  five-position rank3 anchor. Thirty primitive affine witnesses cover
  the family. Its complete girth-three extension cover is added back
  before excluding that family from the exact five-position table.
  All3125 projection checks,30 witness checks and2106 cumulant checks
  pass. Through sixteen remains below9.583e-13; size17 weighted log10
  is6.15469, now led by rank8/girth6. The residual allocation, adaptive
  bridge and full BKZ proof remain open; this geometry is not in Lean.
* **Part 336 (nine-position girth-six determinant27 anchor).**
  [nine_twenty_seven](research/wall1_nine_twenty_seven.md) identifies
  the dominant two-norm-six family and proves projected minimum2/3
  from a three-group integer identity. Covering radius squared2 and
  girth six give third squared height max(t+2/3,4). A complete rank7
  extension cover with47040 witnesses is added back before excluding
  determinant27 from the exact table. All19683 projection checks,
  560 witness checks and2106 cumulant regressions pass. Through sixteen
  stays below9.583e-13; size17 weighted log10 is5.96277, now led by
  rank8/girth4 and rank8/girth3. Residual, adaptive BKZ and new Lean
  obligations remain open.
* **Part 337 (ten-position determinant28 anchor; target remains open).**
  [ten_twenty_eight](research/wall1_ten_twenty_eight.md) proves projected
  minimum1/2 and covering radius squared16/7 for the rank8 anchor.
  Balanced-sign enumeration gives330 witnesses per first support and
  69300 overall; an initial smaller count was rejected and corrected.
  All59049 projection checks,330 witness checks and2106 cumulant
  regressions pass. The complete new cover helps other strata but does
  not improve the target rank8/girth4 bound: same-rank extensions remain
  too costly. Size17 weighted log10 is5.95115; through sixteen stays
  below9.583e-13. Residual, adaptive BKZ and new Lean obligations remain.
* **Part 338 (girth-filtered one-point determinant28 extensions).**
  [ten_dependent_codes](research/wall1_ten_dependent_codes.md) enumerates
  720 norm-four rows across both affine sign types. Primitive minors
  and165 complementary-column tests per row give exact girth-filtered
  Gram strata68..112. Complete D/28 kernels replace the unrestricted
  rare-line bound while retaining the no-new-four remainder and tails.
  All checks and2106 cumulant regressions pass. Size17 weighted log10
  is5.69665; rank8/girth4 is no longer in the five largest strata.
  Through sixteen stays below9.583e-13. Rank8/girth3, the remaining
  allocation, adaptive BKZ and new Lean obligations remain open.
* **Part 339 (five-position two-four determinant15 anchor).**
  [five_fifteen](research/wall1_five_fifteen.md) isolates the remaining
  five-position two-four family. A covering-radius reduction to11
  integer representatives proves projected minimum1/3. Sixty primitive
  affine witnesses and squared covering radius8/5 give a complete
  rank3 extension cover, added back before excluding the family.
  Geometry, witness checks and2106 cumulant regressions pass. Size17
  weighted log10 is5.06404, now led by rank10/girth3. Through sixteen
  remains below9.583e-13. The residual allocation, adaptive BKZ bridge
  and new Lean obligations remain open.
* **Part 340 (large-support three-circuit geometry).**
  [three_large_support](research/wall1_three_large_support.md) proves
  that for t>=6 a norm-six row lies on the first three-circuit; its
  integer projected minimum1/3 gives second height>=t+1/3. For t>=8
  no norm-eight row exists, giving the no-six kernel heights10,15/2.
  All coefficient counts and tails remain. The729 projection checks,
  short-shape checks and2106 cumulant regressions pass. Size17 weighted
  log10 is4.90208, now led by rank8/girth8; rank10/girth3 leaves the
  five largest strata. Through sixteen stays below9.583e-13. The
  residual allocation, adaptive BKZ bridge and new Lean work remain open.
* **Part 341 (girth-eight exclusions on small supports).**
  [girth_eight_ten](research/wall1_girth_eight_ten.md) rules out
  eight/eight pairs on at most ten positions, and eight/ten or ten/ten
  pairs on at most eleven, by cancelling a shared sign class. Complete
  kernels split minima8,10,>=12 with all tails retained. The2519 new
  pair checks, prior geometry checks and2106 cumulant regressions pass.
  Size17 weighted log10 is4.65646, now led by rank8/girth5; through
  sixteen remains below9.583e-13. Residual, adaptive BKZ and new Lean
  obligations remain open.
* **Part 342 (norm-six pairs with a prescribed five-circuit).**
  [five_six_pair_codes](research/wall1_five_six_pair_codes.md) proves
  that the eight-position two-six family has determinant32 and second
  squared height16/3. Exact prescribed-overlap counts are0,36,36 for
  overlaps2,3,4, checked at q=7,17,3329 with primitive minors. The
  one-six/no-six families and all tails remain. All2106 cumulant checks
  pass. Size17 weighted log10 is4.46209, now led by rank6/girth4;
  through sixteen stays below9.583e-13. The residual allocation,
  adaptive BKZ bridge and new Lean obligations remain open.
* **Part 343 (shared-anchor two-point Gram strata; tighter admitted cap).**
  [shared_two_point_codes](research/wall1_shared_two_point_codes.md)
  identifies the shared seven-position anchor's small crossing as the
  rank6/girth4 bottleneck. All63 new norm-four lines pass the girth test;
  exact determinant counts44:20,50:14,54:13,56:8,60:8 improve the third
  heights. All tails and unrestricted-family remainders remain. The
  admitted transfer through sixteen is now below3.459e-13, with the
  remaining sufficient allocation updated to2.6629e-12. That allocation
  remains unproved. Size17 weighted log10 is4.18599, now led by
  rank8/girth3; adaptive BKZ and new Lean obligations remain open.
* **Part 344 (two norm-six lines with a prescribed three-circuit).**
  [three_six_pair_codes](research/wall1_three_six_pair_codes.md) proves
  that the eight-position family contains a three-position norm-six
  row and a six-unit row. Each prescribed overlap admits10 determinant32
  and20 determinant35 planes, with primitive minors and exact modular
  checks. Complete kernels replace the broad two-six count; all other
  families and tails remain. All2106 cumulant checks pass. Size17
  weighted log10 is3.72392, now led by rank9/girth6. Through sixteen
  stays below3.459e-13. The2.6629e-12 residual allocation, adaptive BKZ
  bridge and new Lean obligations remain open.
* **Part 345 (large-support girth-six strata and no-six geometry).**
  [six_six_large_codes](research/wall1_six_six_large_codes.md) counts
  exact norm-six pairs on10/11 positions and six/eight pairs on11,
  preserving the longer-minimum remainder. Those refinements alone
  barely affect the total. Girth-six cancellation then strengthens
  the no-six kernels, with second heights8,15/2,55/8 on supports<=9,10,11.
  All finite classifications and2106 cumulant checks pass. Size17
  weighted log10 is2.86969; rank9/girth6 leaves the five largest strata.
  Through sixteen stays below3.459e-13. The2.6629e-12 residual allocation,
  adaptive BKZ bridge and new Lean obligations remain open.
* **Part 346 (six-position girth-three determinant23 anchor).**
  [six_twenty_three](research/wall1_six_twenty_three.md) proves projected
  minimum7/23 by nearest-plane rounding and73 bounded integer cases.
  The360 primitive affine witnesses give a complete rank4 anchor cover;
  excluded determinant23 planes are added back with all tails retained.
  Geometry, witness checks and2106 cumulant regressions pass. Size17
  weighted log10 is2.57349, now led by rank8/girth4; through sixteen
  stays below3.459e-13. The2.6629e-12 allocation, adaptive BKZ bridge
  and new Lean obligations remain open.
* **Part 347 (triangular norm-six extensions).**
  [triangle_six_extensions](research/wall1_triangle_six_extensions.md)
  identifies the triangular t=4 crossing as the rank8/girth4 bottleneck.
  Exact norm-six strata on t=3,4,5 are counted across all five affine
  patterns, excluding planes already carrying new norm-four rows.
  The no-four/no-six remainder has third height>=20/3 by rounding;
  all tails and coefficient remainders remain. Classification checks
  and2106 cumulant regressions pass. Size17 weighted log10 is1.99228,
  now led by rank10/girth4; through sixteen stays below3.459e-13.
  The residual allocation, adaptive BKZ and new Lean work remain open.
* **Part 348 (twelve-position short-pair exclusions).**
  [twelve_small_circuit](research/wall1_twelve_small_circuit.md) classifies
  reduced norm-eight/ten pairs for girth four/six with proper crossing.
  All49638 full-support checks pass, including coefficient-two shapes.
  The three minimum-length cases give squared GS lower bounds(8,10),
  (10,42/5),(12,9), with existing tails and periodic terms retained.
  All2106 cumulant regressions pass. Size17 weighted residual log10 falls
  from1.99228 to1.52078; this is an upper envelope, not a probability.
  Through sixteen remains below3.459e-13. Sizes17..24, the2.6629e-12
  residual allocation, adaptive BKZ bridge and new Lean proofs remain open.
* **Part 349 (twelve-position girth-five refinement).**
  The same [short-pair classification](research/wall1_twelve_small_circuit.md)
  now checks girth five. Unlike girths four/six, it permits(8,8) and(8,10),
  but their Gram determinants are at least60 and64; no(10,10) pair qualifies.
  The exhaustive minimum-length cases give(8,15/2),(10,19/2),(12,9).
  The complete-kernel refinement retains all tails and coefficient counts.
  All49638 classification checks and2106 cumulant regressions pass.
  Size17 weighted residual log10 decreases from1.52078 to1.40866;
  through sixteen remains below3.459e-13. This does not admit size17,
  meet the2.6629e-12 residual budget, or resolve adaptive BKZ or Lean work.
* **Part 350 (norm-four/ten planes on twelve positions).**
  [Twelve-position classification](research/wall1_twelve_small_circuit.md)
  now counts the unique-four-line norm-ten extensions: overlap2 has196
  determinant36 and182 determinant40 planes; overlap3 has546 determinant40
  planes; overlap1 has none. Exact checks agree for q=7,17,3329.
  The no-norm-ten remainder has second squared GS height at least11;
  complete kernels retain cutoff40 tails and periodic layers.
  All2106 cumulant regressions pass. Size17 residual weighted log10
  decreases from1.40866 to1.14821, now dominated by rank8/girth4.
  Through sixteen remains below3.459e-13. Size17 admission, the residual
  budget, adaptive BKZ bridge and new Lean formalization remain open.
* **Part 351 (triangular norm-eight cover and empty four-new exception).**
  [Triangular extensions](research/wall1_triangle_six_extensions.md) now
  classifies norm-eight witnesses for t=3,4,5 over all five affine patterns,
  including coefficient-two rows, with shorter-plane exclusions and unit-minor
  checks. The no-four/six/eight remainder has squared height at least26/3.
  Also, t=4 norm-four rows would be new-only, incompatible with a crossing
  whose nonzero old coefficients use an independent anchor basis; their
  previous conservative exception count3 is replaced by0.
  Classification and2106 cumulant checks pass, with all tails retained.
  These changes have negligible numerical effect: size17 weighted log10
  remains1.14820799686 and through sixteen remains below3.459e-13.
  Thus the unclassified norm-eight remainder and that norm-four exception
  are not the effective bottleneck. The residual budget, adaptive BKZ bridge
  and new Lean obligations remain open.
* **Part 352 (weighted triangular norm-four Gaussian).**
  [Weighted four-extension](research/wall1_triangle_four_weights.md) identifies
  the t=3 norm-four crossing as the effective triangular bottleneck.
  Weights5/8 on the attached old coordinate,1 on other old coordinates,
  and9/8 on new coordinates preserve total weight9. All90 affine witnesses
  have weighted squared GS lengths23/5,72/23,32/9; the determinant product
  improves from44 to729/16. Tail and periodic bounds use the conservative
  scale8/9, retaining every correction. Exact Gram checks and2106 cumulant
  regressions pass. Size17 weighted residual log10 decreases from1.14821
  to0.576616; the triangular contribution is at-1.54867. Through sixteen
  remains below3.459e-13. These are upper envelopes, not probabilities;
  size17 admission, the residual budget, adaptive BKZ and Lean work remain open.
* **Part 353 (norm-ten refinement on ten positions).**
  [Four/ten classification](research/wall1_four_ten_ten.md) isolates the
  post-weighting rank8/girth4 residual at t=6, overlap3. Norm-ten witnesses
  have determinant36/39 for overlaps1,3 (counts45/270 each), and
  determinant40 for overlap2 (count46). Checks agree at q=7,17,3329,
  including coefficient-two shapes. The remaining second squared height
  is at least11; existing norm-eight covers, tails and periodic terms remain.
  All2106 cumulant regressions pass. Size17 weighted residual log10 falls
  from0.576616 to-1.440839, now led by rank5/girth4. Through sixteen
  remains below3.459e-13. The size17 envelope still exceeds the required
  residual allocation; adaptive BKZ and new Lean obligations remain open.
* **Part 354 (triangular two-new norm-four determinant counts).**
  [Two-new classification](research/wall1_triangle_two_four.md) replaces
  the45-times-worst-kernel cover by componentwise determinant counts
  {32:6,36:24,44:18,48:6} across all five affine patterns. All225
  witnesses and unit-minor checks pass. Ordinary and marked parallel
  completion paths both use the refinement, with unchanged remainder,
  tail and periodic terms. All2106 cumulant regressions pass.
  Transfer through sixteen is about3.42413830e-13 (the existing asserted
  cap3.459e-13 and residual allocation are conservatively retained).
  Size17 weighted residual log10 falls from-1.440839 to-1.892886,
  again led by rank8/girth4. Size17 admission, the remaining residual
  budget, adaptive BKZ and new Lean obligations are still open.
* **Part 355 (weighted six-position determinant24 kernel).**
  [Six-position weights](research/wall1_six_d24_weights.md) treats the
  dominant remaining rank8/girth4 c=4,t=2,overlap2 family with weights
  5/6 on old coordinates and4/3 on new ones. All12 exact rational checks
  give squared GS lengths24/5,63/10 and determinant product700/27>24.
  The complete kernel includes prefactor27/25 and tail/periodic scale3/4.
  All2106 cumulant regressions pass. Size17 weighted residual log10
  falls from-1.892886 to-2.080222, now led by rank5/girth4.
  Through sixteen remains about3.42413830e-13. The existing conservative
  cap and budget are retained; size17 admission, adaptive BKZ and new
  Lean formalization remain unproved.
* **Part 356 (four equal pair sums at determinant32).**
  [Two-new triangular classification](research/wall1_triangle_two_four.md)
  now verifies all27 determinant32 witnesses have four projective column
  directions of multiplicity two, with unit determinants for every triple.
  Coordinate sign changes therefore turn their equations into four equal
  pair sums. The existing k=4 intersection-count bound plus modular alias
  correction replaces the Gaussian kernel when smaller. All225 witness
  checks,27 structural checks and2106 cumulant regressions pass.
  Through sixteen is about3.418861513e-13. Size17 weighted residual log10
  falls from-2.080222 to-2.327239, led by rank8/girth3 and rank8/girth4.
  Existing conservative caps and allocation remain unchanged. Size17
  admission, the residual target, adaptive BKZ and new Lean work remain open.
* **Part 357 (three-circuit extension on ten positions).**
  [Three/six/eight analysis](research/wall1_three_six_eight_ten.md) counts
  norm-six/eight planes with determinant44/47 (35/70 witnesses for each
  overlap) at q=7,17,3329, and gives the remaining one-six height17/2.
  This alone is negligible. In the no-six family, proportional new parts
  and affine balance exclude reduced(8,8),(8,10),(10,10) pairs; a direct
  argument and105 finite pair checks give cases(8,10),(10,19/2),(12,9).
  All tails remain and2106 cumulant regressions pass. Size17 weighted
  residual log10 falls from-2.327239 to-2.434815; through sixteen stays
  about3.418861513e-13. Existing conservative caps remain. Size17 admission,
  the residual target, adaptive BKZ and new Lean formalization remain open.
* **Part 358 (twelve-position exact-girth-seven exclusion).**
  [Twelve-position analysis](research/wall1_twelve_small_circuit.md) excludes
  two independent norm-eight rows at exact girth seven: their projective
  column groups have size at most four, so all row supports have size at
  least eight. The exhaustive minimum cases give squared GS heights(8,8)
  and(10,15/2), with all cutoff14 tails and periodic terms retained.
  All49638 pair checks and2106 cumulant regressions pass. Size17 weighted
  residual log10 decreases from-2.434815 to-2.538231; rank10/girth7 leaves
  the top five strata. Through sixteen stays about3.418861513e-13.
  Existing conservative caps remain; size17 admission, the residual target,
  adaptive BKZ and new Lean formalization remain open.
* **Part 359 (seven-position short-family refinements).**
  [Seven-position analysis](research/wall1_seven_eight_codes.md) counts
  norm-four/eight planes by determinants23,28,31,32, respecting the
  determinant23 norm-six overlap and separate anchor exclusion. Checks
  agree at q=7,17,3329. This alone has small effect. In the no-four family,
  girth four forces two reduced norm-six rows to have inner product+/-1,
  giving determinant35 and height35/6. All360 pair checks and2106
  cumulant regressions pass, with counts and all tails retained.
  Size17 weighted residual log10 falls from-2.538231 to-2.570977;
  through sixteen stays about3.418861513e-13. Existing conservative caps
  remain; size17 admission, adaptive BKZ and new Lean obligations are open.
* **Part 360 (determinant44 anchor projection certificate).**
  [Nine-position projection](research/wall1_d44_projection.md) prepares a
  full-anchor treatment of the remaining triangular three-new norm-four
  crossing. Its positive integer projection minimum is exactly6/11.
  Squared rounding radius8/3 reduces any putative smaller projection to
  integer norm below106/33<4; all835 possible vectors are checked exactly.
  All90 affine witnesses have the same signed-permutation column geometry.
  Thus this is an all-integer geometric lemma, not a bounded-search guess.
  Fourth-relation modular/tail and completion accounting are not yet
  connected. No new numerical residual bound or Lean formalization is
  claimed; size17 admission and the adaptive BKZ bridge remain open.
* **Part 361 (determinant44 fourth-relation cover connected).**
  [Fourth-relation extension](research/wall1_d44_extension.md) connects the
  nine-position rank-six anchor, with113400 witnesses, to the full envelope.
  Cutoff20 satisfies44*20^4<3329^2; squared fourth height is at least
  t+6/11, or additionally10/3 when new norm-four rows are excluded.
  Coefficient, tail, periodic, dependent and parallel completion terms are
  retained. Removing the triangular t=3 norm-four class is paired with a
  complete anchor addback, and the old envelope is retained as an alternative.
  The835 projection and90 geometry checks and2106 cumulant regressions pass.
  Size17 weighted residual log10 falls from-2.570977 to-2.835101;
  the triangular contribution falls to-7.399184. Through sixteen stays
  about3.418861513e-13. Size17 admission, the full residual target,
  adaptive BKZ and new Lean formalization remain open.
* **Part 362 (eleven-position norm-eight crossing bound).**
  [Four-circuit/eleven-point analysis](research/wall1_four_eleven_eight.md)
  uses proportionality on seven new coordinates to give second squared
  height19/2 when the first minimum is eight. All1680 reduced-pair checks
  and2106 cumulant regressions pass. Numerical effect is negligible:
  size17 weighted log10 stays about-2.835101. An explicit primitive
  norm-ten pair attains determinant75 and height15/2 at girth four,
  ruling out a uniform increase for that remaining class. Isolating its
  rare planes is a further obligation. Full residual, adaptive BKZ and
  new Lean obligations remain open.
* **Part 363 (eleven-position norm-ten pairs isolated).**
  [Eleven-position analysis](research/wall1_four_eleven_eight.md) now proves
  every reduced norm-ten pair admits a norm-ten generator on the four-circuit,
  and enumerates its prescribed-support planes at q=7,17,3329. Complete
  rare kernels plus remainders(10,19/2),(12,9) retain all tails. All2106
  cumulant regressions pass, but size17 weighted log10 remains about-2.835101.
  New split diagnostics identify the reason: at overlaps1 and3 the one-four
  kernel exceeds the no-four kernel by about48 and41 decimal orders before
  the common normalization. The next target is that one-four family, not
  a further uniform improvement to the norm-ten remainder. Full residual,
  adaptive BKZ and new Lean obligations remain open.
* **Part 364 (weighted eleven-position determinant31 kernel).**
  [Eleven-position weights](research/wall1_eleven_d31_weights.md) uses
  weights55/72,11/12,77/72 on the attached old, other old, and new coordinates.
  All420 exact checks give squared GS lengths252/55,576/77 and weighted
  determinant product greater than31. Complete cutoff40 tails and periodic
  layers use the conservative scale72/77. The change applies only to the
  counted determinant31 class, with the existing remainder retained.
  All2106 cumulant regressions pass. Size17 weighted residual log10 falls
  from-2.835101 to-3.050645; rank9/girth4 leaves the top five strata.
  Through sixteen remains about3.418861513e-13. Size17 admission, the
  full residual target, adaptive BKZ and new Lean formalization remain open.
* **Part 365 (seven-position three-circuit short families).**
  [Three-circuit/seven-point analysis](research/wall1_three_seven_short.md)
  counts two-six planes by determinants27,32,35,36, with agreement at
  q=7,17,3329. In the no-six family exhaustive reduced-pair checks exclude
  (8,8), give Gram>=76 for(8,10) and Gram>=91 for(10,10), yielding complete
  squared-height cases(8,19/2),(10,91/10),(12,9). All coefficient remainders,
  cutoff tails and periodic terms remain. Classification checks and2106
  cumulant regressions pass. Size17 weighted residual log10 falls from
  -3.050645 to-3.485263, now led by rank10/girth6. Through sixteen stays
  about3.418861513e-13. Size17 admission, the remaining residual target,
  adaptive BKZ and new Lean formalization remain open.
* **Part 366 (twelve-position one-six refinement).**
  [Six/eight twelve-position analysis](research/wall1_six_twelve_eight.md)
  first confirms the one-six family dominates rank10/girth6. Norm-eight
  extensions have determinants44,48, with exact prescribed-overlap counts
  agreeing at q=7,17,3329. The remaining second squared height is at least
  17/2. All coefficient remainders, cutoff36 tails and periodic layers stay.
  Classification and2106 cumulant regressions pass. Size17 weighted residual
  log10 falls from-3.485263 to-4.047737; rank10/girth6 leaves the top five.
  Through sixteen stays about3.418861513e-13. Size17 admission, the full
  residual target, adaptive BKZ and new Lean formalization remain open.
* **Part 367 (weighted eight-position determinant28 kernel).**
  [Eight-position weights](research/wall1_eight_d28_weights.md) converts
  every norm-four/eight determinant28 witness to a sparse second row by
  a unimodular change. Weights1/8,7/8,21/16 give squared GS lengths80/7,
  1328/105 and determinant product37664487/1048576>28. All96 exact
  checks and2106 cumulant regressions pass. The complete cutoff40 tail
  and periodic corrections use scale16/21, with all counts retained.
  Size17 weighted residual log10 falls from-4.047737 to-5.079907;
  through sixteen stays about3.418861513e-13. Size17 admission, the
  full residual target, adaptive BKZ and new Lean formalization remain open.
* **Part 368 (weighted ten-position determinant32 kernel).**
  [Ten-position weights](research/wall1_ten_d32_weights.md) uses weights
  5/8(shared),1(old-exclusive),9/8(new) for orthogonal norm-four/eight
  rows. Squared GS lengths26/5,128/15 give determinant product
  2302911/65536>32. All300 exact Gram/unit-minor checks and2106 cumulant
  regressions pass. Cutoff40 tails and periodic corrections use scale8/9;
  both short-pair splits and diagnostics use the complete improved kernel.
  Size17 weighted residual log10 changes from-5.079907384 to-5.079964574,
  only about0.013% improvement. Thus this raw-term diagnosis does not
  identify a major improvement in the selected complete cover. Through
  sixteen remains about3.418861513e-13. Size17 admission, the full residual
  target, adaptive BKZ and new Lean formalization remain open. Next inspect
  the selected residual's internal contributions before choosing a new family.
* **Part 369 (exclude reduced norm-eight pairs on ten positions).**
  [Ten-position no-four analysis](research/wall1_four_ten_eight_pairs.md)
  identifies the selected two-relation residual: t6/overlap3 contributes
  about97.8% of rank8/girth4, dominated by the no-four kernel rather than
  Part368's one-four family. Two norm-eight rows must have identical new
  unit parts and disjoint old supports, giving dot6 and contradicting
  Gauss reduction. All165 eligible pairs are checked exactly. The new
  complete GS kernel cases(8,8),(10,15/2) retain cutoff14 tails and periodic
  terms. All2106 cumulant regressions pass. Size17 weighted residual log10
  falls from-5.079965 to-5.417096 (about2.17-fold improvement); through
  sixteen stays about3.418861513e-13. New stratum-candidate diagnostics
  retain both one- and two-relation alternatives. Size17 admission, the
  full residual target, adaptive BKZ and new Lean formalization remain open.
* **Part 370 (rare norm-eight pair cover for five-circuit planes).**
  [Five-circuit ten-position split](research/wall1_five_ten_eight_split.md)
  identifies the no-six kernel at t5/overlap4 as the leading rank8/girth5
  contribution. There are6615 balanced norm-eight lines of support>=5,
  hence at most21875805 unordered pair witnesses. Charging these with
  the old complete(8,6) GS kernel divided by the coefficient count leaves
  complete cases(8,8),(10,15/2). All tails and periodic terms remain.
  The6615 exact line checks and2106 cumulant regressions pass. Size17
  weighted residual log10 falls from-5.417096 to-6.253230. Rank8/girth3
  now leads, followed by rank10/girth8 and rank8/girth4. Through sixteen
  remains about3.418861513e-13. Five-circuit split diagnostics are retained.
  Size17 admission, the full residual target, adaptive BKZ and new Lean
  formalization remain open.
* **Part 371 (weighted seven-position determinant27 kernel).**
  [Seven-position weights](research/wall1_seven_d27_weights.md) identifies
  the two-six family at t4/overlap2 as the rank8/girth3 bottleneck. Weights
  1/8,23/16,23/16 on C and1 on the four new positions give squared GS
  lengths768/23,100/23 and weighted determinant product75/2>27. All36
  exact Gram checks and2106 cumulant regressions pass. The complete
  cutoff36 tail and periodic corrections use scale16/23; other classes
  and counts remain. Size17 weighted residual log10 falls from-6.253230
  to-6.405900. Rank8/girth3 leaves the top five; rank10/girth8 now leads.
  Through sixteen remains about3.418861513e-13. Size17 admission, the
  full residual target, adaptive BKZ and new Lean formalization remain open.
* **Part 372 (short-pair cover for twelve-position girth-eight planes).**
  [Twelve-position girth-eight split](research/wall1_eight_twelve_pairs.md)
  identifies t4/overlap7 as the rank10/girth8 bottleneck. Count at most
  150069150 unordered pairs among17325 unit norm-eight lines for the
  exceptional(8,8) family. Projective sign groups have size<=4, giving
  |dot|<=2 for(8,10) and dot0 for(10,10). The complete residual GS cases
  are(8,19/2),(10,19/2),(12,9), with all cutoff14 and periodic terms.
  All6638 eligible representative-pair checks,17325 line counts and2106
  cumulant regressions pass. Size17 weighted residual log10 falls from
  -6.405900 to-6.536332. Rank10/girth8 leaves the top five; rank8/girth4
  now leads. Through sixteen remains about3.418861513e-13. Size17 admission,
  the full residual target, adaptive BKZ and new Lean formalization remain open.
* **Part 373 (norm-ten split for nine-position four-circuit planes).**
  [Nine-position norm-ten split](research/wall1_nine_norm_ten_split.md)
  locates the t5/overlap3 bottleneck in the generic second-minimum>=10
  remainder rather than the counted determinant31 class. There are5292
  balanced norm-ten lines on nine positions and at most15876 witnesses
  paired with the three first norm-four lines. Charge these with the
  complete height9 kernel, leaving height11 for the higher remainder.
  All5292 line checks and2106 cumulant regressions pass, with cutoff40
  tails and periodic terms retained. Size17 weighted residual log10 falls
  from-6.536332 to-6.713969. Rank8/girth4 leaves the top five; rank9/girth7
  now leads. Through sixteen remains about3.418861513e-13. Size17 admission,
  the full residual target, adaptive BKZ and new Lean formalization remain open.
* **Part 374 (rare norm-eight pairs on eleven positions at girth seven).**
  [Eleven-position girth-seven split](research/wall1_seven_eleven_eight_split.md)
  identifies t4/overlap6 as the rank9/girth7 bottleneck. There are5775 unit
  norm-eight lines and at most16672425 unordered pair witnesses. Charge
  these with the complete(8,55/8) kernel divided by the coefficient count;
  retain complete cases(8,8),(10,15/2) for the remainder. All cutoff14 tails
  and periodic corrections remain. The5775 line checks,624 eligible
  representative-pair checks and2106 cumulant regressions pass. Size17
  weighted residual log10 falls from-6.713969 to-6.917041. Rank9/girth7
  leaves the top five; rank11/girth4 and rank5/girth4 now lead. Through
  sixteen remains about3.418861513e-13. Size17 admission, the full residual
  target, adaptive BKZ and new Lean formalization remain open.
* **Part 375 (four-circuit planes on thirteen positions).**
  [Thirteen-position analysis](research/wall1_four_thirteen_ten.md)
  identifies t9/overlap3 as the rank11/girth4 bottleneck. With a norm-four
  row, at most1512 norm-ten extension witnesses have determinant39;
  the remaining second height is>=11. Without norm four, no norm-six/eight
  row fits C or covers nine new positions. Two outside norm-ten rows
  cannot have a full C difference, leaving complete GS cases(10,19/2),
  (12,9). All7560 exact Gram/inner-product checks and2106 cumulant
  regressions pass. All respective cutoff40/14 tails and periodic terms
  remain. Size17 weighted residual log10 falls from-6.917041 to-7.100985;
  rank11/girth4 leaves the top five, and rank5/girth4 now leads. Through
  sixteen remains about3.418861513e-13. The through24 envelope remains
  ineffective at about7.03e226; this is not a failure probability. Size17
  admission, the full residual target, adaptive BKZ and new Lean work remain open.
* **Part 376 (exact marked-pair multiplicity for the rank-one quotient).**
  [Single-class multiplicity](research/wall1_single_class_multiplicity.md)
  weights each marked pair by1/choose(k,2), where k is its nonloop class
  size. For a rank5 triangular support there is exactly one such class;
  the weights sum pointwise to1. Exact rational completion counts retain
  every loop/nonloop split and all existing joint-kernel corrections.
  The correction is connected to the size14 baseline and sizes15..24.
  All1981 subset checks,114 weighted count identities and2106 cumulant
  regressions pass. Size17 triangular weighted log10 falls from-7.399184
  to-9.138110; full residual log10 becomes-7.396911 from-7.100985. Through
  sixteen is about3.418861456e-13, with prior conservative caps retained.
  Rank8/girth6 and rank9/girth4 now lead. Size17 admission, the full
  residual target, adaptive BKZ and new Lean formalization remain open.
* **Part 377 (six-circuit refinements on ten positions).**
  [Six-circuit ten-position analysis](research/wall1_six_ten_refinement.md)
  splits the one-six family by at most3307500 norm-six/eight witnesses,
  leaving second height>=17/2. For two-six determinant32 planes, weights
  11/12(shared),49/48(exclusive) give squared GS lengths3288/539,
  35712/6713 and weighted determinant product4719878935541/146767085568>32.
  All2100/1575 line counts,780 weighted Gram/unit-minor checks and2106
  cumulant regressions pass. All cutoff36 tails and periodic corrections
  remain; weighted corrections use scale48/49. Size17 weighted residual
  log10 falls from-7.396911 to-7.695059; rank9/girth4 now dominates.
  Through sixteen remains about3.418861456e-13. Size17 admission, the full
  residual target, adaptive BKZ and new Lean formalization remain open.
* **Part 378 (all-integer projection lemma for the determinant31 anchor).**
  [Eleven-position projection certificate](research/wall1_eleven_d31_projection.md)
  proves projected squared minimum21/31 for the norm-four/eight plane.
  Nearest-plane rounding has squared radius47/16; a smaller positive
  projected value would give an integer vector of squared norm<1793/496<4.
  All1563 resulting vectors are checked exactly, with minimum positive
  projection numerator21. All420 balanced witnesses are certified signed
  coordinate permutations of the canonical plane. This is an all-integer
  paper proof supported by exact enumeration, not merely a search claim.
  It supplies projected height t+21/31 under a nonzero old-projection
  premise, and height49/16 when new norm-four exceptions are removed.
  No extension cover is yet connected and no class is newly excluded;
  numerical residual bounds remain those of Part377. The next obligation
  is a complete added-back extension cover, followed by the global residual,
  adaptive BKZ bridge and Lean work.
* **Part 379 (complete determinant31 extension cover connected).**
  [Eleven-position anchor cover](research/wall1_eleven_d31_anchor.md)
  adds the rank9 anchor with138600 witness patterns, including same-rank
  dependent extensions, larger crossing circuits and parallel completions.
  New norm-four exceptions are explicitly added back, with projected
  height49/16 on their complement and full cutoff24/40 corrections.
  The exclusion flag and production add-back cover are connected; selected
  cover reconstruction and2106 cumulant regressions pass. At size17/rank9
  the new complete cover has weighted log10 about-3.543690, worse than
  the preceding-7.743732, so the preceding bound remains selected. The
  overall size17 log10 changes only negligibly to-7.695059283. This is a
  completed mathematical cover, not a meaningful numerical improvement.
  Next classify the additional norm-four relations by their actual Gram
  determinant rather than the generic projected minimum. Full residual,
  adaptive BKZ and Lean obligations remain open.
* **Part 380 (girth-filtered one-point determinant31 extensions).**
  [One-point Gram classification](research/wall1_eleven_dependent_codes.md)
  checks495 balanced norm-four extensions and220 nine-column complements
  per line. Unit minors prove saturation; all minors have absolute value<7,
  so the girth filter is also valid modulo3329. All420 anchors map to the
  balanced representative by permutations and row signs. Determinants52,54
  are excluded by girth; the retained minimum is84. Exact determinant counts
  replace the one-point exceptional term with complete cutoff24 kernels.
  All classification checks and2106 cumulant regressions pass. The D31
  added-back contribution at size17/rank9 has weighted log10-41.279008,
  and the new complete cover is now selected. Full size17 residual log10
  falls from-7.695059 to-8.666684. Rank5/girth4,rank8/girth4,rank8/girth6
  now lead. Through sixteen remains about3.418861456e-13. Size17 admission,
  the full residual target, adaptive BKZ and new Lean formalization remain open.
* **Part 381 (four-pair anchor projection and affine patterns).**
  [Four-pair projection](research/wall1_four_pair_projection.md) identifies
  determinant32 as the rank5 triangular bottleneck. Its orthogonal
  complement splits into four pair-difference directions and the all-ones
  direction, proving projected squared minimum1/2 for ALL integer vectors.
  Nearest-plane squared radius29/12 supplies the independent cutoff35/12<3
  certificate; all129 short vectors satisfy the exact projection identity.
  Affine balance permits nine signed patterns per pairing, giving945
  patterns, checked as distinct row spaces at q=7,3329. These prerequisites
  support a proposed eight-point/rank5 anchor extension cover. No new class
  is excluded yet; numerical bounds remain those of Part380. The complete
  add-back cover, global residual target, adaptive BKZ and Lean work remain open.
* **Part 382 (complete rank-five four-pair extension cover).**
  [Four-pair extension cover](research/wall1_four_pair_extension.md)
  connects the945-pattern rank5 anchor at sizes14..24. One-point norm-four
  extensions have two affine types;336 exact lines with unit four-column
  minors and84 complement tests per line exclude determinant52 by girth.
  Retained determinant counts are{84:96} and{84:72,116:24}. Complete
  cutoff24 kernels and the height43/12 no-new-four complement cover every
  dependent-point case. The D32-restricted triangular remainder receives
  the full anchor add-back before comparison with the preceding bound.
  All classification checks and2106 cumulant regressions pass. Size17
  triangular weighted log10 becomes-14.455814; full residual log10 becomes
  -8.845650 from-8.666684. Through sixteen is about3.418861455e-13; prior
  conservative caps remain. Rank8/girth4,rank8/girth6,rank8/girth3 now lead.
  Size17 admission, the full residual target, adaptive BKZ and Lean work remain open.
* **Part 383 (sign-sensitive nine-position determinant31 weights).**
  [Nine-position weights](research/wall1_nine_d31_weights.md) weights the
  two agreeing shared coordinates5/6, the opposing shared coordinate5/12,
  the old-exclusive coordinate13/12 and five new coordinates7/6. The
  weighted rows are orthogonal with squared lengths372/65,318/35 and
  determinant product19724215/559872>31. All300 exact Gram checks and2106
  cumulant regressions pass. Complete cutoff40 and periodic corrections
  use scale6/7; counts and added-back families remain. Size17 weighted
  residual log10 falls from-8.845650 to-8.969919. Rank8/girth6 now leads,
  followed by rank8/girth3 and rank8/girth4. Through sixteen remains
  about3.418861455e-13. Size17 admission, the full residual target,
  adaptive BKZ and new Lean formalization remain open.
* **Part 384 (rank-eight two-six determinant32 anchor cover).**
  [Ten-position rank-eight cover](research/wall1_six_ten_anchor.md) proves
  projected squared minimum3/4 using radius17/6 and1161 exact short-vector
  checks. All780 anchors map to two balance-preserving affine types.
  Their5040 one-point norm-six extensions are classified by unit minors
  and462 six-column complements per line; retained determinants start120.
  Complete cutoff24 kernels and the height31/6 complement give a full
  same-rank cover with163800 anchor witnesses. It is added back to the
  D32-restricted c6 residual ONLY at rank8, alongside the existing D27 cover.
  All classification checks and2106 cumulant regressions pass. Size17
  weighted residual log10 falls from-8.969919 to-9.239619. Rank8/girth6
  leaves the top five; rank8/girth3 and rank8/girth4 now lead. Through
  sixteen remains about3.418861455e-13. Size17 admission, the full residual
  target, adaptive BKZ and new Lean formalization remain open.
* **Part 385 (parallel approach: exact five-position two-six classification).**
  [Eight prescribed charts](research/wall1_three_five_six_pairs.md) proves
  that C=012, S=0134 in the no-four family has four determinant32 and four
  determinant35 planes. Exclusive unit minors prove saturation; an integer
  quadratic-form argument proves minimum squared norm6. Exact enumeration at
  q=7,17,3329 and an independent nine-choice construction agree. The complete
  counted kernels, including tails and periodic corrections, now refine the
  c3/H5/overlap2 two-six contribution in the production envelope. All2106
  cumulant regressions pass. The full size17 residual remains log10
  -9.239618750774848 at displayed precision: local classification alone does
  not improve the selected full envelope. The full H5 anchor is dominated
  by one-four; the improved no-four subfamily has relative size about4.76e-38.
  Through24 remains about7.03e226,
  an ineffective upper bound, not a failure probability.
* **Part 386 (parallel approach: integer-polynomial certificate duality).**
  [Alternative global remainder route](research/wall1_global_remainder_alternative.md)
  tests lowering the required moment order. At the exact rational reference
  mean58.15006220912, positive rational quadrature matching all moments through
  degree22 proves that every polynomial P nonnegative on the nonnegative
  integers with P(0)>=1
  and degree<=22 has E_Poisson[P]/0.280 >=4.36531830216e-12, above3.922e-12.
  Adjacent-root polynomials attain this bound. This is a fixed-reference
  certificate obstruction, not a lower bound on actual failure or a result
  for the unknown larger true mean. Degree24 improves the reference by about
  3.7 percent; its high-order weights remain too large to remove the current
  huge remainder envelopes. No new production probability bound is claimed.
* **Part 387 (parallel approach: adaptive complete transcripts).**
  [Adaptive bridge audit](research/wall1_adaptive_bridge_audit.md) proves that
  adaptive full linear-query transcripts, including stopping, have affine
  fibers and a uniform unused complementary map. Compressing to a selected
  winner preserves the old law exactly when its selection likelihood is
  constant in that map. A shortest-vector example exhibits the bias, and
  359 transcript fibers,2680 fresh-direction laws and168 event inequalities
  pass exact checks. Fresh-column randomness does not control the retained
  selected geometry. The width506 history sum, sizes17..24 certification,
  new Lean formalization and the complete BKZ proof remain open.
* **Part 388 (odd-degree extension of the polynomial obstruction).**
  The [integer-polynomial audit](research/wall1_global_remainder_alternative.md)
  now also covers degree23. Interpolation at zero and the paired integer roots
  leaves c*x*product_i((x-a_i)(x-a_i-1)); the product is nonnegative on
  nonnegative integers, and c>=0 for every admissible odd-degree polynomial.
  The degree22 positive quadrature therefore still supplies the same lower
  bound at degree23. Exact rational interpolation-defect checks pass for
  degrees17,19,21,23,25. This rules out dropping size24 merely by using an
  odd-degree certificate at the fixed mean floor; it does not bound the
  actual dependent-law failure probability or resolve the full BKZ goal.
* **Part 389 (six-position two-six coefficient classification).**
  [H6 classification](research/wall1_three_six_six_pairs.md) enumerates all
  2415 pairs of70 balanced norm-six lines and proves completeness by their
  support types. Prescribed overlap1 has one determinant36 chart; overlap2
  has18 determinant32 and one determinant36 charts. Unit minors establish
  saturation, and the excluded determinant20 charts contain norm-four rows.
  Counts agree at q=7,17,3329. Complete counted kernels replace only the
  two-six subfamily, with all tails and other families retained. Alone this
  changes the size17 full-envelope log10 to-9.239826543832959; the larger
  five-position one-four term still dominates its rank8/girth3 stratum.
* **Part 390 (effective five-position determinant23 weighting).**
  [H5 weighted kernel](research/wall1_five_d23_weights.md) assigns weights
  3/20 to two shared positions and47/30 to three exclusive positions.
  The squared GS lengths2060/141 and149730/4841, prefactor squared
  1200000/103823, and tail/periodic scale30/47 are checked exactly for60
  balanced pairs. Norm-eight presentations reduce to the same norm-six
  planes. The complete kernel, not merely its determinant, improves the
  D23 term and is minimized with the old bound in production. The whole
  one-four split improves by log10 -4.787209; D24 then dominates locally.
  All2106 cumulant regressions and standalone classification checks pass.
  Combined with Part389, full size17 residual log10 is-9.422463228182312
  (about3.7804e-10). Rank8/girth4, rank6/girth4 and rank9/girth6 now lead.
  The through16 transfer remains about3.418861455e-13; through24 is still
  about7.029876163e226 and unusable. Sizes17..24, later selected histories,
  new Lean formalization and the complete BKZ theorem remain open.
* **Part 391 (eleven-position six-circuit excludes two eight minima).**
  [Six-support exclusion](research/wall1_six_eleven_no_eight_pair.md) proves
  that two unit-eight rows covering eleven positions and containing a
  six-support codeword have inner product magnitude5. Their difference
  has norm squared6, so they cannot occur in the no-six family. The complete
  no-six kernel now uses (8,8) or (10,15/2), with its original tails.
  All3920 balanced full-support pairs are checked; all304 eligible cases
  have the asserted short difference. No coefficient family is discarded.
* **Part 392 (shared anchor with four new positions).**
  [Norm-six split](research/wall1_shared_four_new_six.md) classifies210
  balanced lines into determinants74,80,84,86,90 with counts64,46,44,28,28.
  Unit minors give saturated third GS heights D/15. The complementary
  family has height32/5 by the old covering radius8/5. Every counted kernel
  retains cutoff29 and periodic corrections; the full split is minimized
  with the previous bound. This directly targets the rank8 other-two-four
  addback's four-new-position term. The production path and diagnostic
  both use the complete bound.
* **Part 393 (triangular containment removes a duplicate D44 cover).**
  [D44 containment](research/wall1_shared_two_d44_reorder.md) proves that
  all20 determinant44 two-point extensions contain a six-position triangular
  anchor. `other_envelopes(exclude_triangular=True)` now bounds only the
  no-triangle subfamily, omitting these complete code terms. Both production
  callers explicitly retain the full triangular cover; the default remains
  unrestricted. All tails of retained families remain. The three changes
  in Parts391--393 pass2106 cumulant regressions and their exact local checks.
  Full size17 residual log10 is-10.110085037002284 (about7.761e-11).
  Leading strata are rank8/girth4 (-10.44865), rank9/girth6 (-10.51841),
  and rank6/girth4 (-10.98284). Through16 remains about3.418861455e-13;
  through24 remains about7.029876163e226. The2.6629e-12 remaining allocation,
  the selected-history bridge, new Lean work and complete BKZ proof are open.
* **Part 394 (seven-position D28 complete weighted kernel).**
  [D28 weighting](research/wall1_seven_d28_weights.md) uses old weights1,
  new coefficient-two weight1/5 and other new weights7/5. Squared GS lengths
  (4,157/7), prefactor squared125/49 and tail/periodic scale5/7 are verified
  for108 witnesses and18 prescribed charts. The complete kernel is minimized
  with the prior D28 kernel, retaining all other code families.
* **Part 395 (D20 one-point cover outside earlier two-four families).**
  [Conditional D20 cover](research/wall1_twenty_no_two_four.md) reduces the
  one-point norm-four rare count to at most9 determinant76 witnesses. All
  removed configurations contain a six- or seven-position two-four anchor.
  `twenty_envelopes(exclude_two_short=True)` is used only where the complete
  triangle and other-two-four covers are already added; the default remains
  unrestricted. Their combined coverage is sufficient even though `other`
  itself is restricted to no-triangle events. Retained tails are unchanged.
* **Part 396 (rank-nine D32 crossing cover and independent audit).**
  [Rank-nine extension](research/wall1_six_ten_rank_nine.md) classifies4200
  two-point norm-six extensions of the two D32 affine types; each retains1908
  girth-six witnesses. Unit minors and all minor magnitudes below7 justify
  saturation and the finite-field rank filter. The complete crossing cover
  includes coefficient sum sum_(a=4)^8 choose(8,a)q^a and every completion
  factor; the complement has GS height31/6. Production removes D32 at rank9
  only when adding this full cover and the required D27 cover. Independent
  audit found no missing crossing, coefficient or addback. Parts391--393
  also received a separate [proof audit](research/wall1_parts391_393_audit.md).
  All2106 cumulant regressions and dedicated checks pass. Full size17 residual
  log10 is-10.997859079851332 (about1.005e-11), with rank8/girth4 now dominant.
  The through16 transfer remains about3.418861455e-13 and through24 about
  7.029876163e226. The shared remaining allowance2.6629e-12 is still unproved.
  No attack-cost bit gap from the heuristic BKZ prediction is certified:
  these are local probability envelopes, and the full selected-history and
  cost theorems remain open. The obsolete440-bit comparison above is removed.
* **Part 397 (uniform ball-constrained dependent completions).**
  [Affine-slice bound](research/wall1_ball_slice_completion.md) proves
  M_d=min(q^d,V_d(R+sqrt(d)/2)^d) for centered ball inputs in any affine
  d-plane, by injective coordinate pivots and disjoint unit cubes. The two
  final input-completion factors in the general one/two-relation cover now
  use M_(r-1)^k; coefficient and probability factors are unchanged. All1164
  finite pivot checks pass. This improves high-rank bounds but does not
  resolve the high-order remainder or selected-cylinder distribution.
* **Part 398 (six-position D24 full anchor cover; through17 milestone).**
  [D24 anchor](research/wall1_six_d24_anchor.md) proves integer projected
  minimum1/3 by nearest-plane radius5/2 and73 exhaustive short representatives.
  All180 balanced affine witnesses have unit minors. Complete same-rank and
  crossing covers retain every cutoff26 tail and periodic correction; the
  no-new-four complement has height7/2. Production removes D24/H6 only while
  adding this full cover and all previous required covers. An independent
  [audit](research/wall1_ball_slice_d24_audit.md) checks both new arguments.
  All2106 cumulant regressions pass. The full-incidence cumulant transfer
  through17 is below1.077e-12 (evaluated1.076402696610603e-12). Together with
  the reference/error cap9.131e-13, this leaves a conservative1.9318e-12
  allocation for sizes18..24 and later bad histories; their bound is open.
  The size17 weighted residual itself is about7.35e-13. Through24 remains
  about3.818709584e223, an ineffective upper envelope, not a probability.
* **Part 399 (high-order diagnosis and checkpoint).**
  [High-order frontier](research/wall1_high_order_frontier.md) records the
  Part396 snapshot: sizes18/19 are led by rank11/girth5 on13 positions,
  size24 by rank12/girth4 on14 positions. Their anchors already span the
  full rank; free completion of the remaining inputs loses the simultaneous
  ball constraints. The note identifies the weighted conditional completion
  moment needed to improve this step. Its witness-multiplicity ceiling is
  limited to that specific counting method, not a lower bound on failure.
  [Checkpoint scope](research/wall1_checkpoint_2026_11_24.md) separates these
  paper/computational results from the existing Lean lemmas and open BKZ goal.
* **Part 400 (weighted completion and its full-anchor limitation).**
  [Weighted completion](research/wall1_weighted_completion.md) expresses
  the actual span-law chi-square as a weighted same-span rank-collision
  energy and bounds arbitrary completion moments by reference moments plus
  their variance/chi-square penalty. It includes fixed-anchor quotient-rank
  formulas up to the required higher orders; a first-moment bound cannot
  simply be raised to a power. The leading H=r+2 branches have no extra
  basis: conditioning on their full anchor makes the reference a singleton,
  so this version gives an identity, not an improvement. Averaging over
  the actual weighted anchors remains open.
  [Pinned distinct completions](research/wall1_pinned_distinct_completion.md)
  proves the falling-factorial refinement and explains why it alone is
  negligible at the current large caps. Its2172 exact checks pass.
* **Part 401 (a conditional stopped-potential route).**
  [Selected histories](research/wall1_selected_history_alternative.md)
  proves a finite stopped-drift bound without enumerating all flags.
  A graph-lattice collision counterexample shows that fixed-time mean
  bounds alone do not justify a martingale maximum bound. Exact checks
  cover204 collision identities and12 stopped-tree cases. The actual
  selected-cylinder high-order potential and conditional drift remain
  unproved; no new selected-history probability follows.
* **Part 402 (7000-witness H11 cover; improved through17 bound).**
  [Norm-eight pair cover](research/wall1_five_eleven_eight_pairs.md)
  exhausts the girth-five H11 two-short-row family by20 inside times350
  outside lines. Unit minors certify saturation; the complete complement
  retains the original cutoff14 tails and periodic terms. Independent review
  and all7000 pair checks pass. Production and the standalone complete
  kernel agree within relative1e-60. The local bound improves15.65 decimal
  orders and rank9/girth5 totals at sizes17/18 improve1.9655 orders.
  The integrated through17 cumulant correction is now below8.048e-13
  (evaluated8.047489906106801e-13). All2106 exact regressions pass.
  With the reference/error cap9.131e-13, a conservative remaining
  allocation2.204e-12 for sizes18..24 plus later histories would keep the
  total below3.922e-12; that remaining estimate is still unproved.
  Through24 stays about3.818709584e223: this is an ineffective upper
  envelope, not an actual probability. Full BKZ remains open.
* **Part 403 (actual fresh-column power drift).**
  [Two-layer power drift](research/wall1_two_layer_power_drift.md)
  proves E[(p')^k | incoming history] <= p(B)^k p(sqrt(B^2-1))
  for k>=1 and a predictable lower bound B on every outgoing radius.
  It follows from an exact two-layer miss-set inclusion and does not
  assume independence of the chosen winner. Independent audit and3276
  nested-set plus104 shortest-winner branch checks pass. The resulting
  stopped-power criterion still needs the actual moving-radius shell
  estimate and an initial power bound. Fresh unexposed columns are
  essential; this is not a theorem for arbitrary reused-column BKZ tours.
* **Part 404 (anchor collision energy via connected unions).**
  [Anchor collision energy](research/anchor_collision_energy.md)
  bounds same-span energy by a common-map second moment, then by
  sum_i binomial(H,i)^2 i! F_(2H-i,r). Individual pairwise probability
  gluing is false; aggregate Jensen is valid. Exact finite checks include
  actual ball fibers. The reduction needs degrees up to2r+4 for H=r+2,
  beyond24 when r>=11, and can lose substantially through variance.
  No small collision energy or new high-order global bound is inferred.
* **Part 405 (H13/H14 long-crossing refinements, integrated).**
  [H13 girth five](research/wall1_five_thirteen_short_pairs.md) excludes
  outside norm-eight rows and independent norm-ten pairs, then counts
  25200 saturated (8,10) witnesses.
  [H14 girth four](research/wall1_four_fourteen_long_crossing.md) proves the no-four
  GS bound(10,9) for all overlaps and counts norm-twelve crossings in
  the overlap-three one-four family, retaining its full complement.
  Both arguments passed independent review and exact finite checks;
  integrated kernels match independent reconstructions. All original
  tails, periodic corrections and outer coefficient factors remain.
  The final all-overlap run passes2106 exact cumulant regressions.
  Through17 is8.047466717798704e-13, still below8.048e-13; through24
  is about4.816712268e216. The latter remains an ineffective upper
  envelope, not a failure probability. Sizes18..24, selected-history
  shell control, and the complete BKZ theorem remain unproved.
* **Part 406 (girth-seven H13 excludes two norm-eight rows).**
  [H13 girth seven](research/wall1_seven_thirteen_no_eight_pair.md)
  proves that every norm-eight row uses all six new and two old
  coordinates. Two independent such rows would yield a nonzero old
  row of support at most four, contradicting girth seven. The complete
  GS cases(8,8) and(10,15/2) retain cutoff14 tail power13/2 and all
  periodic terms. Independent audit and11760 pair checks pass; the
  integrated selected kernels match independent evaluation within1e-60.
  The full cumulant run passes2106 exact regressions. Through17 is
  8.047466639505124e-13; through24 remains about2.747742353e215,
  an ineffective upper envelope. No completed high-order or BKZ
  probability certificate follows from this local refinement.
* **Part 407 (girth-six H13 counted short pairs).**
  [H13 girth six](research/wall1_six_thirteen_short_pairs.md) counts
  2100 saturated norm6/norm8 witnesses with determinant47 and retains
  the one-six complement with GS(6,17/2). In the no-six family,
  norm-ten rows must be unit on seven new and three old coordinates.
  Differences exclude independent(8,8),(8,10),(10,10) pairs, yielding
  complete GS cases(8,10),(10,19/2),(12,9). Independent proof audits
  approve the split with unchanged cutoff36/14 tails and power6.
* **Part 408 (girth-three H9 counted short pairs).**
  [H9 girth three](research/wall1_three_nine_short_pairs.md) counts
  315 saturated norm6/norm8 witnesses with determinant at least39,
  retains the full one-six complement, and excludes independent
  norm-eight pairs in the no-six family. All195 proportional-new
  pair checks and an independent audit pass. The integration retains
  all existing excluded-family addbacks and coefficient normalizers.
  The relevant improvement is in the restricted residual; an
  unrestricted stratum comparison would obscure the actual effect.
* **Part 409 (girth-four H12 norm-twelve crossing cover).**
  [H12 crossing classification](research/wall1_four_twelve_ten_pairs.md)
  retains the exact546 norm-ten charts, counts at most7434 norm-twelve
  pair witnesses with Gram at least44 for overlap three, and bounds
  the remaining one-four family by GS(4,13). Independent enumeration
  confirms saturation and the D44/D47 chart counts over7,17,3329.
  A separate no-four improvement was numerically negligible and was
  not substituted for this effective one-four refinement. Original
  cutoff40 tails, periodic corrections and complete complements remain.
* **Part 410 (integrated three-family verification).**
  The complete run after Parts407--409 passes240 Poisson/cumulant and
  1866 connected-support regressions. The through17 correction is
  6.902542020700491e-13, hence below6.903e-13. Together with the
  reference/error cap9.131e-13, a conservative remaining allocation
  2.3185e-12 for sizes18..24 and later histories would keep the total
  below3.922e-12; this allocation is a target, not a proved estimate.
  Through24 is still about1.803622374e213. The full frontier diagnostic
  also completes and verifies all18 selected-cover/remainder comparisons.
  Its leading size18 stratum is rank9/girth5, size19 rank10/girth6,
  and size24 rank13/girth4. The upper envelopes remain ineffective
  for those high orders; no full BKZ or selected-history proof follows.
* **Part 411 (H9 girth-five short-pair chart covers).**
  [H9 refinement](research/wall1_five_nine_refinement.md) enumerates
  all eligible norm6/8 and norm8/8 normalized charts. Their rare terms
  retain the old uniform complete kernels; the complementary GS bounds
  are(6,17/2) and(8,8),(10,15/2). Independent enumeration over7,17,3329
  and a proof audit pass. All4 integrated kernels match independent
  formulas within1e-60. The full size18 rank9/girth5 residual improves
  5.1445268404 decimal orders, limited by unchanged t3/t5 families.
* **Part 412 (H15 girth-four long-crossing cover).**
  [H15 refinement](research/wall1_four_fifteen_long_crossing.md) counts
  5544 norm4/12 witnesses with Gram47 and retains the full one-four
  complement. The no-four cases are(10,23/2),(12,45/4),(14,25/2),
  (16,12): independent outside12/14 and14/14 pairs are excluded by
  their short old-supported differences. All original tails remain.
  Independent audit and finite checks pass; all3 integrated selected
  kernels match the independent interval reconstruction.
* **Part 413 (complete rank-ten D32 cover).**
  [Rank-ten cover](research/wall1_six_ten_rank_ten.md) uses connectivity
  of the fundamental-circuit graph to cover both t2 and t3 crossings.
  The former needs one additional independent basis point; the latter
  needs none. Both leave h-13 completions in affine dimension9.
  All2400 new norm-six witnesses and an independent coverage audit
  pass. Production retains the D27 addback and the entire D32 cover
  when using the residual excluding both families. The standalone
  complete rank10/girth6 envelope improves5.8020122293 decimal orders.
  [Weight diagnostic](research/wall1_six_ten_frontier_refinement.md)
  separately documents a much smaller weight adjustment; that optional
  adjustment is not integrated or needed for this coverage theorem.
* **Part 414 (rank-ten integrated verification checkpoint).**
  All2106 exact cumulant regressions pass after Parts411--413.
  Through17 is6.143361028426690e-13, below6.144e-13. With the
  reference/error cap9.131e-13, a conservative2.3944e-12 allocation
  for sizes18..24 and later histories would keep the total below
  3.922e-12; that remaining allocation is still unproved. Through24
  remains about6.573520003e212, an ineffective upper envelope.
  All18 frontier selected-cover/remainder comparisons pass, including
  the new rank-ten D32 addback. Current leading strata at sizes18,
  19,24 are respectively rank9/girth4,rank11/girth4,rank12/girth5.
  This checkpoint contains paper proofs and interval/exact computations;
  these new results have not been formalized in Lean. The complete
  BKZ cost/probability theorem remains open.
* **Part 415 (all-rank D32 coverage and integrated checks).**
  [Higher ranks](research/wall1_six_ten_higher_rank.md) and
  [all ranks](research/wall1_six_ten_all_rank.md) cover all fundamental
  crossings through rank21 where r<=h-3. Production retains the earlier
  special covers, D27 addbacks, periodic corrections and tails. All2106
  cumulant checks and all18 frontier reconstructions pass. Through17
  remains below6.144e-13; through24 remains ineffective. The optional
  all-t projection bonus is not enabled in production.
* **Part 416 (completion and initialization obstructions).**
  [Uniform occupancy](research/wall1_uniform_completion_obstruction.md)
  is exactly maximized by a coordinate plane. Improving this cap alone
  cannot close the displayed leading terms. [Girth-four completion](research/wall1_girth_four_completion_obstruction.md)
  retains almost all candidates in a large span; its concrete anchor is
  not certified to survive every residual exclusion. [Raw initialization](research/wall1_initial_small_radius_obstruction.md)
  has small-radius void nearly one. [Smoothed potentials](research/wall1_smoothed_void_potential.md)
  and [marked lattice shells](research/wall1_lattice_radial_profile.md)
  specify the scope of the resulting obstacles, without claiming a
  reachable-history or BKZ failure counterexample.
* **Part 417 (conditional drift with additional geometry).**
  [Multiple heights](research/wall1_multi_height_drift.md) give an optimized
  pairwise-independent second-moment bound, verified by2289 exact tests.
  [Overlap energy](research/wall1_overlap_energy_drift.md) gives a sharp
  mean/variance-to-power bound for k>=2. Its1411 assertion groups and
  strengthened variance feasibility checks pass. [Actual winner projection](research/wall1_winner_projection_gain.md)
  proves power contraction for a planar, rank-one-marked subclass by
  exhaustive winner evaluation. None supplies the required profile/energy
  law for actual selected histories or reused columns.
* **Part 418 (mixed-fiber weighted completion reduction).**
  [Independent maps](research/wall1_independent_map_energy.md) avoid the
  common-map Jensen loss with normalization q^(-2mr) and doubled shared
  input weights. A direct pinned-completion alternative uses19 input
  positions with input nullity8, output-anchor nullity2, and q^(-mr).
  It avoids degree25/26 energy moments but requires a new asymmetric
  kernel bound; ordinary19-point joint-ball estimates would undercount.
  Sixty exact identities/majorants pass. This is a reduction, not a
  numerical improvement to the remaining global residual or a Lean proof.
* **Part 419 (mixed-kernel coefficient and alias accounting).**
  [Shared charts](research/wall1_mixed_chart_sum.md) keep the same affine
  completion coefficients in all118 input rows; interchanging their sum
  with the coordinate power can undercount. Fixed-matrix coordinate
  multiplicities give a conditional weighted-ball improvement, with no
  estimate of those multiplicities under the actual anchor law.
  [Gram kernels](research/wall1_mixed_gram_kernel.md) separate a discrete
  Gram theta factor from modular aliases via a Schur complement;1337
  exact algebra checks and432 joint-dual inverse checks pass. The joint
  dual prefactor is coefficient-invariant; its nonzero terms retain the
  modular dependence. Dropping the aliases is not justified.
  [Completion temperature](research/wall1_mixed_completion_temperature.md)
  certifies the globally optimal universal pivot-Gaussian bound at the
  actual radius; it remains weaker than the existing volume cap.
  [Finite mixed fixture](research/wall1_mixed_kernel_fixture.md) verifies120
  fixed-chart majorants and shows the temperature derivative can change
  sign with anchor weighting. No production residual is improved here;
  the coupled coefficient sum with aliases remains the substantive target.
* **Part 420 (anchored dual completion, integrated full-anchor cases).**
  [Coefficient rank](research/wall1_dual_coefficient_rank.md) gives exact
  fibers of the shared affine coefficient map. [Gaussian rank tails](research/wall1_dual_frequency_rank.md)
  retain the actual dual temperature, not a uniform residue model.
  [Weighted pivots](research/wall1_dual_rank_pivot_bound.md) and its
  [anchored strengthening](research/wall1_anchored_dual_completion.md)
  keep the same anchor theta on nonpivot coordinate rows. The resulting
  multiplier includes every rank stratum and infinite Gaussian tail.
  Production now minimizes a separate common-theta completed candidate
  against the old completed bound, only when no free basis points remain.
  Direct-ball and anisotropic anchor minima are not multiplied by it.
  All2106 cumulant checks and frontier reconstructions pass. Through17
  is below6.143e-13; through24 is about4.2321e208, still ineffective.
  Free-basis terms and selected histories remain open. No new Lean
  formalization or completed BKZ guarantee is claimed.
* **Part 421 (independent-basis extension of anchored completion).**
  [Extended completion](research/wall1_extended_dual_completion.md)
  retains the original anchor beta on added independent basis points,
  with exact factor exp(beta R^2)theta(beta)^518/q^400 per point.
  The extended code theta factors, and the coloop-free contraction
  preserves the f+1 witness division. The original beta is included
  in cache keys; theta-only completed candidates are minimized against
  the existing completed bounds. Independent implementation audit,
  all2106 exact cumulant checks and all18 reconstructions pass.
  Through17 is below2.752e-13. Through24 is about2.5742e194 and remains
  ineffective. The size24 leader is now rank12/girth3 with9 free basis
  points. Different temperatures for those points need a further
  anisotropic proof. Actual selected histories and the BKZ theorem remain open.
* **Part 422 (separate Gaussian weights for independent points).**
  [Anisotropic extension](research/wall1_anisotropic_dual_completion.md)
  retains the original anchor weight while giving independent basis
  points their own positive weight. Fourier positivity and coordinate
  hyperplane sums yield two drop-coordinate eta candidates. The exact
  extended theta factorization preserves all input/output normalizers;
  every rank tail is retained. The old and same-weight candidates remain.
  Independent proof/implementation review,81 exact anisotropic coefficient
  sums,2106 cumulant checks and18 frontier reconstructions pass.
  Through17 is below2.666e-13; through24 is about1.96044e153, still an
  ineffective envelope. The size24 leader is rank9/girth3 with a six-point
  anchor and5 free basis points. The selected-history law remains open.
* **Part 423 (six-point common-theta snapshots).**
  [Six-point bridge](research/wall1_six_point_theta_bridge.md) retains
  refined common-beta envelopes separately from selected weighted/direct-ball
  minima. Unsafe six-point branches use a complete isotropic bad/one/none
  decomposition. Independent integration audit, 2106 exact cumulant checks
  and 18 frontier interval comparisons pass. Through17 stays below2.666e-13;
  through24 is below1.034e140, still ineffective against the3.01e-12 target.
  The size24 leader is rank9/girth3, now a seven-point t4/overlap2 anchor
  with4 independent extensions. Selected histories and full BKZ remain open.
* **Part 424 (girth-three common-theta extension).**
  [Seven-point bridge](research/wall1_seven_point_theta_bridge.md) replaces
  the weighted D27 contribution by a separately retained isotropic counterpart
  for theta completion; H8/H10/H11 final common-beta bounds are also retained.
  Independent branch audit,2106 exact cumulant checks and18 frontier interval
  comparisons pass. Through17 stays below2.666e-13; through24 is below2.258e136,
  still ineffective. The size24 leader is now rank8/girth4 with a seven-point
  t3/overlap3 anchor and3 independent extensions. The full transfer target,
  selected-history law and BKZ theorem remain open.
* **Part 425 (four-circuit seven-point theta bridge).**
  [Seven-point bridge](research/wall1_seven_point_theta_bridge.md) retains
  an isotropic D28 counterpart and the complete bad/one/none decomposition
  before shared-four direct-ball replacements. Independent audit,2106 exact
  cumulant checks and18 frontier comparisons pass. Through17 is below2.665e-13;
  through24 is below8.203e133 and still ineffective. The size24 leader is
  rank8/girth4, now t2/overlap2 with4 independent extensions. The six-point
  two-four family needs a sharper complete bound or a stronger cover with
  its addback; larger-anchor snapshots alone do not remove this term.
  The full transfer target, selected histories and BKZ remain unproved.
* **Part 426 (two-four common-theta determinant split).**
  [Six-point bridge](research/wall1_six_point_theta_bridge.md) preserves
  the orthogonal Gaussian before its direct-ball replacement, charging five
  triangular and four orthogonal codes separately with all exclusions.
  Independent audit,2106 exact checks and18 interval comparisons pass.
  Through17 is below1.526e-14; through24 is below4.557e133, still ineffective.
  The rank8/girth4 six-point leader persists. A Poisson zero-layer lower
  bound on the triangular Gaussian explains why anchor-only tightening
  cannot remove its leading term. Joint completion constraints remain open.
* **Part 427 (joint completion via disjoint frequency bases).**
  [Holder lemma](research/wall1_disjoint_basis_holder.md): if a rank-t
  dual-frequency matrix contains L disjoint column bases, the normalized
  coefficient average is at most eta_L^t, where eta_L is the maximal
  hyperplane average of (psi/psi(0))^L. Constant fibers and Holder prove
  the bound including fixed offsets;48 exact finite checks pass. To use
  it numerically requires an anchor-specific eta_L bound and a certified
  distribution of base packing under the auxiliary Gaussian law. Rank
  alone is insufficient. No production improvement or actual-history
  independence is asserted from this lemma.
* **Part 428 (auxiliary Gaussian basis-packing tail).**
  [Sequential exposure](research/wall1_disjoint_basis_holder.md) bounds
  failure to obtain L disjoint k-bases by a binomial lower tail: every
  fresh column escapes the current proper span with probability at least
  1-M, where M is the maximal residue atom. Independent audit and2688
  exact finite checks pass. An interval diagnostic at q3329,n118,k14,L2,
  gamma1.25e-6 gives packing failure below5.40e-11. This is an auxiliary
  event only. The rank-deficient contribution is retained explicitly when
  joining this bound to the Holder moment. Anchor-specific eta_L bounds
  remain open; the production completion envelope is unchanged.
* **Part 429 (free-coordinate Holder moment integration).**
  [Disjoint-basis extension](research/wall1_disjoint_basis_holder.md) bounds
  higher moments of the independent free-coordinate factors, including
  Gaussian aliases, and joins them to packing and rank tails. Mathematical
  and implementation audits,48 Holder checks,72 factorization checks,
  2688 packing cases,2106 cumulant checks and18 frontier comparisons pass.
  Through17 remains below1.526e-14 and through24 below4.557e133: the main
  residual does not improve substantially. The rank8/girth4 diagnostic is
  dominated by rank-tail t11 rather than its full-rank term. Sharper rank
  tails or deficient-rank joint moments are required; full BKZ remains open.
* **Part 430 (actual generating-row rank tail).**
  [Generating rows](research/wall1_generating_row_rank_tail.md) replace
  ambient-subspace counting by a union over actual t-row generators,
  yielding Pr(rank<=t)<=binom(k,t)M^((n-t)(k-t)). Independent audits,
  28 finite rank cases,154 helper cases,2106 cumulant checks and18 frontier
  comparisons pass. Through17 is below3.389e-17; through24 is below7.427e73,
  still ineffective against the full target. The size24 leader is now
  rank12/girth4, six-point t2/overlap2 with8 independent extensions.
  All rank tails remain; selected histories and full BKZ remain unproved.
* **Part 431 (full-coordinate joint completion).**
  [Full coordinates](research/wall1_full_coordinate_completion.md) derive
  a separate candidate directly from F_h, retaining dependent output-ball
  constraints as well as input constraints. The dual frequency matrix has
  518 columns, with one completion Chernoff factor and the original q^(-400r).
  This does not upper-bound the input-only mixed relaxation. Two scope
  audits, implementation review,12 exact fixtures,5 scalar checks,2106
  cumulant checks and18 frontier comparisons pass. Through17 is below
  3.219e-17; through24 is below1.336e37 and still ineffective. The size24
  leader is rank10/girth4, six-point t2/overlap2 with6 free extensions;
  several rank8/9 strata are nearby. Selected histories and full BKZ are open.
* **Part 432 (higher Holder orders and canonical normalizer research).**
  The518-coordinate candidate retains additional Holder orders through32
  and intermediate gamma choices, with all old candidates preserved.
  144 exact factor tests,48 Holder tests,2106 cumulant checks and18 frontier
  comparisons pass. Through17 is below3.219e-17; through24 below1.913e31
  remains ineffective. The size24 leader is now rank8/girth3, H9 t6/overlap2
  with one free extension. Separately, the [two-four normalizer lemma](research/wall1_two_four_normalizer.md) supplies canonical unit-minor charts
  and an improved dual normalizer for five triangular/four orthogonal codes;
  all9 charts pass exact checks. This family-specific lemma is not yet
  integrated and cannot be applied to an unsplit general anchor envelope.
* **Part 433 (complete girth-three theta snapshot scope).**
  Independent branch audit permits final common-beta snapshots for all
  c3 anchors with8<=H<=24; the H7 special reconstruction is retained.
  [Integration checkpoint](research/wall1_seven_point_theta_bridge.md):
  2106 exact cumulant checks and18 interval comparisons pass. Through17
  stays below3.219e-17; through24 is below1.438e27 and remains ineffective.
  Size24 is led by rank9/girth4, six-point t2/overlap2 with5 free extensions.
  The canonical two-four normalizer design is audited but not integrated;
  its4 exact hyperplane/convolution tests and9 unit-minor chart tests pass.
  The full transfer target and selected-history law remain unproved.
* **Part 434 (integrated canonical two-four normalizer).**
  [Family-specific completion](research/wall1_two_four_normalizer.md)
  separates five triangle/four square theta masses from the one/no-four
  remainder, applying D12/D16 normalizers only to their certified charts.
  Independent audit,9 chart tests,4 convolution identities,6 scalar cases,
  2106 cumulant checks and18 frontier reconstructions pass. Through17 is
  below3.219e-17; through24 below5.931e25 remains ineffective. Size24 is
  now led by rank8/girth4, H8 t4/overlap3 with2 free extensions. The exact
  hyperplane convolution refinement remains unused. Full BKZ is unproved.
* **Part 435 (complete audited theta snapshot catalogue).**
  [Common-weight reconstruction](research/wall1_eight_nine_theta_bridge.md)
  covers c4 H8..24 and all c>=5, separately reconstructing weighted c4
  H8..11 and c6 H10 branches. All prior candidates and exclusion flags
  remain. Independent branch/implementation audits,2106 cumulant checks
  and18 frontier comparisons pass. Through17 stays below3.219e-17;
  through24 is below2.170e16 and still ineffective. Size24 is now led by
  rank9/girth4 H7 t3/overlap1,3 with4 free extensions. This shared-four
  family needs its own normalizer proof; the H6-specific boost cannot be
  reused silently. Selected histories and full BKZ remain unproved.
* **Part 436 (general Gaussian hyperplane convolution).**
  [Affine convolution](research/wall1_general_hyperplane_convolution.md)
  retains the exact coordinate-sum constraint across all r+2 dual Gaussian
  factors, using a mixed-weight Fourier/theta upper bound with full aliases.
  Independent audits,4 exact mixed-weight identities,12 interval cases,
  2106 cumulant checks and18 frontier comparisons pass. Through17 remains
  below3.219e-17; through24 is below2.981e10 and still ineffective. The
  rank9/girth4 H7 leader persists. A separate [D15 chart proof](research/wall1_shared_four_normalizer.md) passes18 exact chart checks
  but is not integrated. Selected histories and full BKZ remain open.
* **Part 437 (integrated H7 shared-four normalizer).**
  [D15 split](research/wall1_shared_four_normalizer.md) applies the certified
  canonical normalizer only to the nine shared-four codes for overlaps1/3,
  keeping the isotropic remainder under the generic cap. Independent audit,
  18 chart tests,6 scalar cases,2106 cumulant checks and18 frontier comparisons
  pass. Through17 stays below3.219e-17; through24 is below5.627e5 and remains
  ineffective. Size24 is now led by rank10/girth4 H6 t2/overlap2 with6 free
  extensions. Higher moments of the canonical anchor are the next candidate;
  actual selected histories and full BKZ remain open.
* **Part 438 (canonical anchor higher moments).**
  [Completion-square spectral moments](research/wall1_canonical_anchor_moments.md)
  retain anchor correlations using certified H6/H7 charts. Raw Gaussian moments
  are not clipped; no extra normalizer boost is used. Independent mathematical
  and implementation audits,3645 exact identities,raw/normalized regression,
  existing Holder and normalizer tests,2106 cumulant checks and18 frontier
  reconstructions pass. Through17 is below3.219e-17; through24 is below0.666
  (computed envelope0.6654023307944522), still above the3.01e-12 target.
  The size24 leader is rank11/girth4. These are upper envelopes, not measured
  probabilities. Selected-history transport and full BKZ remain unproved;
  no new Lean theorem is claimed.
* **Part 439 (weighted diagonal anchor majorizers).**
  Positive row weights yield a diagonal majorizer by an exact sum of squares.
  [Canonical moments](research/wall1_canonical_anchor_moments.md) retain all prior
  scalar candidates. All27 charts and19116 weighted-square fixtures pass;
  independent audit and complete cumulant/frontier runs pass. Through24 is
  below0.007831. This remains above the target.
* **Part 440 (correlated canonical anchor moments).**
  [Correlated moments](research/wall1_correlated_anchor_moments.md) expand integer
  powers, bound all fractional shifts by centered lattice theta, and use exact
  LDL pivots. All27 charts are maximized over before minimizing other bounds.
  Two independent proof/implementation audits,405 exact square identities,
  normalizer regression checks,2106 cumulant checks and18 frontier interval
  reconstructions pass. Through17 is below3.219e-17; through24 is below3.924e-4
  (computed envelope0.00039232861950197982), still above3.01e-12.
  The size24 leader is rank10/girth3, with the c3/H5 anchor now dominant.
  H5 adaptation is derived but not integrated. These are analytic upper
  envelopes, not measured probabilities or new Lean results. Actual selected
  histories and the full BKZ theorem remain unproved.
* **Part 441 (H5 exceptional correlated completion).**
  [H5 normalizer](research/wall1_five_point_normalizer.md) separates the six
  D15 codes from the isotropic remainder, before weighted D23/ball refinements.
  Exact enumeration at q7,17,3329 verifies canonical unit minors and LDL
  profiles; H5/H7 dimension/cache separation and old-family regressions pass.
  Independent implementation/provenance audit,2106 cumulant checks and18
  frontier reconstructions pass. Through17 remains below3.219e-17; through24
  is below2.025e-8 (computed envelope2.0248575735038707e-8), still above3.01e-12.
  The size24 leader is again rank11/girth4,H6 t2/overlap2 with7 free extensions.
  This is an analytic upper envelope, not a measured probability. Adaptive
  selected histories and full BKZ remain unproved; no new Lean result claimed.
* **Part 442 (base-packing criterion closes the draw-14 transfer).**
  [Matroid packing](research/wall1_matroid_packing.md) bounds absence of
  disjoint auxiliary frequency bases by deficient flats, with either ambient
  subspace counts or actual generating-column counts. Independent audits,
  2246 finite configurations,308 CDF checks,nonuniform weighted checks,
  2106 cumulant checks and18 frontier reconstructions pass. Through24 is
  below1.058e-12, meeting the3.01e-12 target. Independent bootstrap audit finds
  no circularity: this implies temporary caps before the error bound is used.
  Baseline plus transfer plus error is below1.971e-12, bounding b14>.280 under
  the original uniform matrix law via pointwise projection domination.
  This includes the actual projection but is not conditional on history.
  [Winner-coupled replicas](research/wall1_winner_coupled_replicas.md) supplies
  a deterministic witness and exact shared-winner expansion, with270 branch,
  216 replica and27 quotient-kernel checks. Its quantitative stopped drift
  and selected-state initial moment remain open. Full BKZ remains unproved;
  no new Lean theorem is claimed.
* **Part 443 (capped history potential closes initialization).**
  [Capped potential](research/wall1_capped_history_potential.md) uses
  Phi(P)=min(1,(P/.280)^24)<=P/.280. The Part442 certificate controls the
  expected void fraction before Markov, so the matching actual draw14
  initial potential is below1.9704509e-12 under the original matrix law.
  Independent provenance/stopping audit and452 exact rational checks pass.
  Initial exits are included once. The remaining sufficient budget for
  normalized stopped charges (and any additional gate exits) is1.9515491e-12.
  The capped winner-coupled target is weaker than the raw-power target.
  Its small conditional charge remains unproved; full BKZ remains open.
* **Part 444 (actual-winner drift obstruction and gain/loss reduction).**
  [Rank-two drift](research/wall1_rank_two_capped_drift.md) gives an exact
  low-dimensional example with initial void0 but positive expected capped
  potential after actual shortest-vector selection and projection. It persists
  strictly inside the incoming radius, and independent algebra verifies the
  complete coset minima. The66-case finite search agrees. This refutes only
  a universal zero-drift assertion for that q3,dimension3 model with exponent506;
  production-state reachability and a506-dimensional counterexample are not
  established. [Gain/loss accounting](research/wall1_projection_gain_loss.md)
  gives an exact witness-void identity and a capped increment envelope that
  offsets lost coverage by gained coverage;39762 exact checks pass. The
  required small stopped charge on actual reachable histories remains unproved.
* **Part 445 (determinant-consistent model checks).**
  [Orthogonal embedding](research/wall1_determinant_consistent_embedding.md)
  shows that matching the rank-two fixture to detM=V506 g506 creates an
  unmarked vector of length<1. Its actual radius cannot shrink and that
  embedding has zero outgoing void. Exact rational certificates also exclude
  restoration of the old diagonal winner under common marked scaling.
  [Dimension-three marking](research/wall1_dimension_three_marking.md) proves
  by AM-GM that every determinant-coupled q3 rectangular model has incoming
  void>=4/9, outside the pre-exit regime;56 finite grid checks pass.
  These results constrain use of the earlier counterexample, not the actual
  q3329,rank400 selected-state law. No new history probability is obtained.
  The required stopped gain/loss estimate and full BKZ proof remain open.
* **Part 446 (multheight contraction for the400-marked rectangle).**
  [Rectangular multheight bound](research/wall1_rectangular_multheight.md)
  treats33 heights jointly with the actual winner bounded by the unmarked
  axis c. The shared-mark24th moment factorizes across400 coordinates.
  All11082241 scalar pairs are enclosed by exact fixed-point Taylor sums;
  final geometry uses outward intervals. The outgoing capped potential is
  below5.105e-27. The existing iid Berry–Esseen input supplies a positive
  incoming lower bound, proving strictly negative expected capped drift for
  this fixed q3329,g550 rectangular state. Independent mathematical and
  integer-arithmetic audits plus9 exact finite checks pass. This resolves
  the earlier rectangle's one-step transition, not general selected histories.
  No claim that subsequent states remain rectangular is made; full BKZ is open.
* **Parts 447–450 (reachability correction and conditional refinements; paper only).**
  The [Gram obstruction](research/wall1_gram_multheight.md) proves the Part446
  rectangle cannot be an actual cubic projection: its unit-length vectors
  do not generate all505 directions. More generally the proposed Gram102
  family forces g<212.241, contradicting g>=549. Its abstract local bound
  remains valid but is unusable as an actual-history gate. The
  [linear-section obstruction](research/wall1_linear_section_obstruction.md)
  also excludes the fixed-positive-tilt unprojected relaxation with
  anisotropic or redundant generators at the conservative radii considered.
  [Capped convolution](research/wall1_two_height_convolution.md) and
  [winner bins](research/wall1_winner_bin_convolution.md) give conditional
  refinements, checked in3276 and18660 exact finite cases. They still require
  actual-history nearest-distance tails. The
  [radius check](research/wall1_draw14_radius_sensitivity.md) proves a0.024%
  shrink exhausts the existing degree12 reference-term budget, without
  claiming any actual failure lower bound. Independent audits and exact or
  outward-interval certificates support these statements. No new later-history
  failure bound, full BKZ proof, or Lean formalization is claimed.
* **Parts 451–453 (transport refinement and genuine q-ary toy obstruction; paper only).**
  [Shared winner-bin budgets](research/wall1_winner_bin_convolution.md)
  prevent repeated use of the same convolution moment, with11110 additional
  exact checks. [Linear capped transport](research/wall1_linear_capped_transport.md)
  uses the existing draw14 first-moment seed without a24th-power requirement:
  a conditional multiplier1.0017 for390 steps would give total<3.821716e-12.
  The multiplier is not proved for production histories. The
  [Hamming-type construction](research/wall1_hamming_zero_void.md) shows why
  it cannot follow from generic q-ary structure and shortest selection alone.
  Correctly normalized cubic-grid states at(q,width)=(2,16),(3,14),(5,13)
  have zero initial void but positive outgoing void on every nonzero fresh
  mark. All68 winner branches are exactly checked and independently audited.
  These examples do not refute the q3329,width506 claim; their unit-cover
  construction cannot fit that width. The central selected-history estimate
  and the full BKZ theorem remain unproved. No new Lean result is claimed.
* **Parts 454–456 (mixed moments and frozen-fiber Gaussian weights; paper only).**
  [Mixed cumulants](research/wall1_mixed_cumulant_identity.md) isolate the
  negative weighted competitor term, prove auxiliary-mark first-covariance
  cancellation, and express the next covariance by signed constraint buckets.
  [Correlated packing](research/wall1_correlated_packing.md) extends the
  auxiliary bound to unrestricted joint discrete Gaussians with bounded
  precision diagonal. [Periodization](research/wall1_gaussian_periodization.md)
  removes a fixed loss per frozen dimension and preserves distinct-fiber
  factorial moments; conditional thinning gives an integer void witness.
  Exact checks cover20 joint laws,60 auxiliary-shift cases,1049 constraint
  pairs,10 correlated packing cases, and a rational precision audit.
  General lemmas received independent mathematical review, not Lean
  formalization. Matrix reformulation and low-moment shortcuts do not
  supply the missing selected-history moments. No improvement to the
  later-history probability bound or full BKZ completion is claimed.
* **Coset-exit audit note (no new probability bound).**
  [coset_ideas](research/wall1_coset_ideas.md) distinguishes the reachable draw-2 exceptional
  family from the full exit event. Bounding that family's probability does not bound its
  complement. Its zero-exit sampling calculation is a statistical benchmark, not an experiment.
* **Lean (table sampler accuracy, W1-L95; rechecked 2026-11-23).** ShiftedTableAccuracy:
  `shifted_table_excess` and `shifted_table_pmf_excess` prove the 2⁻⁹²³ one-draw bound for
  every integer 127×511 matrix and target, at the concrete run-zero table parameters.
  `shifted_table_coupling` constructs the corresponding coordinate-PMF coupling without
  a sampler-accuracy premise. File compilation and all four printed axiom audits pass with
  only `propext`, `Classical.choice`, `Quot.sound`. This discharges the analytic TV obligation
  listed in earlier progress entries below; transporting and connecting this coupling to the
  complete concrete solver and its execution-level cost is a separate obligation. It does not
  resolve the width-506 selected-history estimate.
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
* **Lean (γ₇ closed).** `Seven.intrinsic_rank_seven`, `Seven.sharp_seven` and `rank_seven` prove
  γ₇⁷ = 64 and λ₁¹⁴ ≤ 64·covol² for every rank-seven lattice. The proof bounds the determinant
  throughout each residue-code chart by comparing a normalized form with the integral orbits of
  33 representatives. The stronger marked-vertex classification `Seven.Coverage` remains open.
  * Lean checks 657 positive-step pivot congruences. Contact-coordinate identities certify 17
    simplicial cones, and proofs about positive contact supports certify the other 16.
  * At E₇ the certificate uses 63 contact lines and 157 pivot directions. For a nonzero feasible
    displacement, a symmetry image of one of these directions has positive support contained
    in the displacement's positive support. Lean checks the geometric reasons for 21,690 clauses
    and an 81,153-step reverse-unit-propagation refutation to prove this assertion.
  * The generator uses the published total of 79,900,912 facets to stop its orbit search.
    Lean checks the resulting witnesses independently. [Jaquet-Chiffelle (1992), §4, p. 278](https://www.numdam.org/article/JTNB_1992__4_2_273_0.pdf).
    The targeted build is
    `lake build SigabaNeo.Lib.Lattices.Research.Wall1.WatsonHigherChartBounds`.
* **Lean (Hermite budget for Part 192).** HermiteSevenTwentyFour (axiom-clean) proves the unconditional caps
  g₇ = (64/3)^{1/5} ≈ 1.84422 (Mordell, from γ₆), g₈ = (64/3)^{7/30}, and g₂₄ = (2/π)(13!)^{1/12} ≈ 4.16937 (Blichfeldt).
  Script: docs/research/scripts/wall1_hermite_budget.py.
  * These are too weak: with both substitutions the prefix flag sum is 3.78·10⁻¹⁴, against an allowance of
    6.54·10⁻¹⁵.
  * Thresholds (one cap varied, the other sharp), after reevaluating the three late sums: g₇ < 1.816489 and
    g₂₄ < 4.086149. With Lean's current rounded late bounds: 1.816034 and 4.078315. Sharp values are 1.811447 and 4.
  * Rogers' center-density bound gives g₂₄ ≈ 4.0811. That fits the reevaluated budget but is not formalized.
* **Lean (late enclosures, rank-24 attempts).** ControlledLateEnclosures / HermiteSphereBudget24 / RogersSimplex24
  (axiom-clean).
  * Tightened late sums: positive 394 draws < 2.066876811·10⁻¹², radius 30 < 7.189180962·10⁻¹⁵, horizontal 406 draws
    < 1.037844738·10⁻¹³. This leaves 6.679534238·10⁻¹⁵ for the prefix, so g₂₄ = 4.086149 (with sharp g₇) or
    g₇ = 1.816489 (with sharp g₂₄) fits.
  * The rank-506 sphere/lens certificate family reaches only 4.37201 in rank 24. Coefficient 4.09 is excluded for that
    polynomial family (scripts wall1_sphere24.py).
  * Rogers' simplex bound gives g₂₄ < 4.0811164, which fits. Lean proves `IntrinsicHermite 24 4.08114` conditional on
    Rogers' packing comparison and the simplex moment identities (wall1_rogers24.py). Still open: an unconditional
    rank-24 cap, a near-sharp rank-7 cap, and the terminal theorem parameterized by both caps.
* **Lean (prefix-explicit terminal theorem).** ControlledTerminalCaps (axiom-clean).
  * Unconditional: Pr(A₄₀₆) < Pr(Z₁) + Pr(Z₂) + Pr(Prefix) + 6.508320465762·10⁻¹². So Pr(Prefix) ≤ 6.679534238·10⁻¹⁵
    suffices for the 6.515·10⁻¹² remainder.
  * `terminal_bound_of_numeric_caps` takes any certified caps with g₇⁷ ≤ 64 and g₂₄ ≤ 4.
  * With the unconditional Mordell/Blichfeldt caps the flag majorant is 3.7817·10⁻¹⁴, and the raw term is only
    6.29·10⁻³⁴. Open: a different suffix split, or a transfer of ≈ 3.1·10⁻¹⁴ from elsewhere in the ledger.
* **Lean (Part 192 terminal theorem UNCONDITIONAL).** ControlledTightRaw / ControlledProvedProfile /
  ControlledProvedFlags / ControlledProvedFlagSum / ControlledTerminalUnconditional (axiom-clean).
  * `terminal_bound_unconditional`: Pr(A₄₀₆) < Pr(Z₁) + Pr(Z₂) + 4.652·10⁻¹², with no Hermite hypotheses. A corollary gives
    the original 6.515·10⁻¹² remainder.
  * Ingredients: raw250_tight (< 2.35454·10⁻¹²); initial raw term at radius 2896 (< 7·10⁻³⁴); sum of all 12,089 flag
    charges ≤ 3.781668308231·10⁻¹⁴; prefix_bound_mordell_blichfeldt (< 3.782·10⁻¹⁴).
  * Hermite inputs: sharp γ₅ and γ₆, Mordell at ranks 7–8, Blichfeldt at rank 24. γ₇ and γ₂₄ are no longer needed.
  * The terminal probability is now reduced in Lean to exactly the two research residuals Z₁ and Z₂.
* **Lean (Z_rem conditional chain).** LongWinnerCrossing / AdaptedBinomialTail / LongWinnerProbability /
  LongWinnerFourthMoment / LongWinnerRawMoments / LongWinnerRawTail (axiom-clean).
  * Deterministic crossing (Part 216): if at most 99 of the first 405 winners exceed 1.10gᵢ, then gᵢ > 34.807 on draws
    8–406.
  * Adapted binomial domination for finite weighted laws, allowing dependent draws.
  * Ceiling 0.126 on all 405 draws gives crossing < 2.5881467826·10⁻¹¹ (exact integer tail certificate).
  * Fourth-moment (B) on draws 11–405 gives < 2.69977·10⁻¹¹. (B) on 54–405 plus Part 222's raw-graph tail premise
    (draws 1–53, not yet in Lean) gives < 2.4681·10⁻¹¹.
* **Lean (raw-graph winner tail).** RawGraphVoid / RawGraphWitness / LongWinnerRawDirections (axiom-clean).
  * Unconditional matrix void bound under the uniform matrix law: Pr[sⱼ > r] ≤ 3329⁴⁰⁰/(3329⁴⁰⁰ + Dⱼ(r)). Here Dⱼ(r) is the
    number of projective integer directions in the ball whose newest input coordinate is nonzero mod 3329. The proof uses
    pair incidences plus survival of raw witnesses through the earlier projections.
  * Draw 1 is fully proved. Draws 2–53 are proved through certified radii (r ≤ 3307 on draw 2, ... , r ≤ 1932 on draw 53);
    the period cap covers r = 3329.
  * Still open: the deterministic count V_N r^N ≤ 4(3329⁴⁰⁰ + Dⱼ(r)) on the remaining radii. With it and (B) on draws
    54–405, the crossing bound is < 2.4681·10⁻¹¹.
* **Lean (width-638 success certificate, Part 236/238).** Width638Graph / Geometry / Groups / Arithmetic / Numeric /
  Averaging / Certificate (axiom-clean; no sorry/admit/native_decide).
  * `recovery_std`: for a uniform 512×511 design mod 3329, independent CBD(3) secret and errors, and EVERY exact-CVP
    oracle, the four-group width-638 algorithm returns the planted secret with probability > 0.643162094166.
  * Components: rank-638 graph oracle; translated-ball first moment (ties charged, zero-residue competitors excluded);
    factorization over the four groups given the shared secret; validation charge 4(7/3329)⁴; centered lifting; exact
    CBD shell convolution and the final rational inequality.
  * The CVP execution cost (< 2^778.825, Part 238) is not formalized.
* **Lean (early-winner tail completed).** RawBallCount / RawBallRounding / RawCenteredCount / RawDirectionCountBounds /
  RawDirectionMultiplicity / RawScalarMajorant / RawScalarWeights / LongWinnerDirectionCount (axiom-clean).
  * V_N r^N ≤ 4·Dⱼ(r) for 1 ≤ j ≤ 52, N = 506 + j, 1690 ≤ r ≤ 3329.
  * The small-g crossing bound < 2.4681·10⁻¹¹ now has the conditional fourth-moment hypothesis (B) on draws 54–405 as its
    only hypothesis.
* **Lean (Part 238 cost and solver).** Width638Cost / ShiftedGaussianPair / ShiftedGaussianHistory / ShiftedGaussianPeak /
  ShiftedGaussianSchedule / ShiftedGaussianError / PoissonOverflow / IntegralMidpointCount / IntegralMidpointMass /
  IntegralShiftedGaussianCVP (axiom-clean; 37 public theorems).
  * Word budget: < 2^776.825 per call, < 2^778.825 total including validation, peak space < 2^766 words (768-bit
    word-RAM charges).
  * Shifted combiner pair law, with Part 140's joint coupling reused (stable pairing).
  * Single-call exact CVP: after 36 pairing levels, the first minimum-energy member is a closest point except with
    probability < 2⁻¹⁶⁸. Empty lists count as failure; ties accept any minimizer. Remaining hypothesis: `initial_sampler`,
    a one-draw coupling with an exact shifted Gaussian at mismatch ≤ 2⁻⁹²³.
  * `four_event_transfer`: credit > 0.643162094166 survives four dependent 2⁻¹⁶⁸ errors (> 0.6431620941).
  * Still uninstantiated: the concrete graph-coordinate instance, the table sampler's coupling, and the
    credited-event-implies-success link for the randomized calls plus validation.
* **Lean (one-draw coupling).** OneDrawCoupling (axiom-clean). For any PMFs P, Q (including on infinite lattices), a
  coupling with mismatch ≤ ε exists iff Σₓ (P(x) − Q(x))₊ ≤ ε, and one attains equality. So `initial_sampler` reduces to
  the analytic bound Σₓ(P−Q)₊ ≤ 2⁻⁹²³ for the table law.
  * Remaining for the end-to-end width-638 theorem:
    * the concrete coordinate contract;
    * that sampler TV bound;
    * the event inclusion for randomized outputs (ties: two exact outputs may differ, and validation checks the chosen
      one);
    * an execution-level work bound.
* **Lean (closest-point selection, integer coordinates).** UniqueClosestSelection / IntegerGridGeometry (axiom-clean).
  * `selected_of_not_bad`: on a good block, any selector returning a feasible minimizer returns the planted point.
  * `exists_disagreeing_first_closest`: a counterexample on 2ℤ. On an earlier tied block, two exact selectors can disagree,
    which changes the first accepted candidate. So `recovery_std` (fixed oracle) does NOT transfer to arbitrary selectors
    as stated. The four-group statement must be reproved for selector families (e.g. charge ties on every queried block,
    or fix the order of validation).
  * Integer-submodule realization with the squared-residual identity, a basis, and parity labels.
  * Remaining: the concrete rank-638 instance, and `samplerTV` (Σ(P−Q)₊ ≤ 2⁻⁹²³) as an explicit hypothesis.
* **Lean (selector-uniform validation).** SelectorUniformValidation / ClosestSelectionEvents (axiom-clean).
  * `any_selection_failure_le`: Pr[some closest-point choice gives a wrong output] ≤ Pr[all blocks bad] + E|C|·ε, where C
    is the set of distinct wrong candidates over all blocks. This covers choices made after seeing validation.
  * `minima_validation_le`: C is built from all tied minimizers, with ε = (7/q)^v.
  * `transfer_four`: common event > 0.643162094166 plus four 2⁻¹⁶⁸ solver errors gives > 0.6431620941 (samplerTV
    explicit).
  * Remaining: a numerical bound on E|C|. It should follow from the translated-ball first moment already in the
    certificate.
* **Lean (candidate count).** MinimumCandidateCount (axiom-clean): E|C| ≤ Σᵢ E Nᵢ, where Nᵢ counts the non-planted feasible
  points in block i's closed residual ball. It allows arbitrary dependence and counts repeated answers once. The existing
  translated-ball theorem bounds Pr[Nᵢ ≥ 1], not E Nᵢ, so a numerical constant for E|C| is still needed.
* **Lean (expected competitor count).** Width638Expected (axiom-clean): `expected_competitors` gives
  Σ_A |competitors p A| · q^r ≤ (ballCount − 1)·#designs when 4·normSq p < q². This is the first-moment form of
  `translated_ball`, so E Nᵢ obeys the same numerical bound as Pr[Nᵢ ≥ 1]. Remaining for the tie-robust constant:
  combine it with MinimumCandidateCount and the CBD averaging.
* **Lean (randomized solvers, tie gap closed).** Width638Randomized (axiom-clean).
  * `recovery_randomized`: let S be any family of solvers indexed by seeds ω (finite seed law w, independent of the
    sample). Suppose that for every input the probability over seeds of a non-closest answer is ≤ δ. Then the
    width-638 recovery probability is > 0.643162094166 − 4δ.
  * Proof: for each seed, wrong answers are patched by a fixed exact oracle; `recovery_std` applies to the patched
    oracle; the raw and patched runs agree unless one of the four queries is wrong (`agree`); and `seed_average_le`
    swaps the seed average with the sample law.
  * This supersedes the E|C| route; no count of tied minimizers is needed.
  * Remaining for the concrete solver: instantiate the per-input error δ = 2⁻¹⁶⁸ from IntegralShiftedGaussianCVP (the
    rank-638 coordinate contract plus the samplerTV hypothesis).
* **Lean (PMF seeds, Euclidean realization).** PMFSeedAveraging / IntegerGridCoordinates (axiom-clean).
  * `lweProb_pmf_seed_average_le` (with 0 ≤ δ): the seed-averaging bound for an arbitrary PMF seed law.
  * Block joining preserves normSq. The Euclidean image of an integer submodule is discrete, and a Euclidean closest
    point pulls back to an integer-residual minimizer. `IntegralCoordinates` exists for any integer submodule in
    dimension 638 and any integral target.
  * Remaining: the PMF form of `recovery_randomized`, and the graph-specific `Correct` link to the shifted-Gaussian
    solver output.
* **Lean (randomized solvers, arbitrary seed law).** Width638RandomizedPMF (axiom-clean). `recovery_randomized_pmf`:
  for any seed PMF μ independent of the sample, if every input has μ{ω | ¬ Correct (S ω) A t} ≤ δ, then
  Σ' μ(ω)·Pr[recovery with S ω] ≥ 0.643162094166 − 4δ. With δ = 2⁻¹⁶⁸ this is the Part 238 success bound for randomized
  solvers. Remaining: connect `closest_point_failure` (IntegralShiftedGaussianCVP, via IntegerGridCoordinates) to
  `Correct` on the rank-638 graph; samplerTV stays a hypothesis.
* **Lean (finite product of PMFs).** FiniteProductPMF (axiom-clean). The product of PMFs over a finite index has
  coordinate marginals ν i and cylinder outer measures equal to those of ν i. `finiteProductPMF_uniform_bound` turns
  per-input error bounds into the single-seed uniform bound that `recovery_randomized_pmf` needs. Remaining width-638
  link: instantiate F x with the shifted-Gaussian selector on the rank-638 graph (via IntegerGridCoordinates and
  `closest_point_failure`) and show Good = Correct.
* **Lean (integer-grid selection).** IntegerGridSelection (axiom-clean). If the selector returns a Euclidean closest point,
  its pullback minimizes the integer squared residual, including ties; the pullback returns 0 on `none`. For any PMF,
  the probability of a nonminimal pullback is at most the selector's failure probability. The per-input specialization
  to `Width638.Correct` is not done.
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
