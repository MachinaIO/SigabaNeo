# High-order production frontier and completion counting

The companion `wall1_high_order_frontier.py` captures the actual return locals
of `wall1_larger_triangular_components.actual_parameters`, rather than
substituting a different cap, an excluded-family diagnostic, or a handpicked
anchor. It reconstructs every competing cover for each reported stratum,
checks that the selected interval agrees with `refined_strata`, and reports
all selected-cover components. It separately reconstructs the underlying
one/two-relation remainder candidates and their actual leading terms.
No production source is edited.

The current capture uses private in-memory copies of the two production
functions, with a hook inserted only at their own return statements. Return
expressions are evaluated once and their original objects are returned.
Nested functions and loaded module bindings are untouched. Small checks cover
early returns, object identity, nested-return exclusion, and private globals.
This replaces global Python tracing; the numerical cover reconstruction and
its interval-agreement assertions are unchanged. The earlier traced
post-H13/H14 run was intentionally interrupted before producing a result,
so that run supplies no numerical evidence.

## What the completion factor means

In the two-relation remainder at support size h and rank r, after selecting
an anchor and enough additional free basis points, there remain

    k=h-r-2

points assigned freely in an affine span of dimension d=r-1. The present
count uses q^(d*k). The script prints d*k and d*k*log10(q) exactly as a
positive contribution to the logarithmic upper bound. This is not the
logarithm of the entire bound: anchor membership, the free-basis ball masses,
the witness choice factor, and the signed-moment transfer coefficient remain
separate. For a three-relation extension the analogous unrestrained
completion count is q^((r-1)*(h-r-3)).

A uniform affine-slice bound C_d <= q^d immediately replaces the two-relation
factor by C_d^k, since each dependent point must still lie in the ball.
If the certified per-point log10 ratio is g_d=log10(C_d/q^d), the maximum
change supplied by this replacement in a fixed two-relation term is k*g_d.
The minimum among valid covers can be recomputed afterward; the improvement
of a non-selected candidate alone is not a global reduction.

## Why basis witness multiplicity alone cannot close a very large deficit

For the existing two-circuit/basis witness format, a witness is determined by
three subsets of the h labels: its first circuit support, second circuit
support, and chosen extra basis labels. There are at most 2^(3h)=8^h such
triples. On an actual configuration, normalized circuit coefficients and
basis coordinates are determined, so the q-power counts alternative point
assignments, not additional witnesses of that fixed configuration.

Consequently the specific method of dividing the existing witness upper
bound by a justified uniform multiplicity of these label-subset witnesses
cannot improve it by more than 3h*log10(2) decimal orders.
At h=24 this generous absolute ceiling is about 21.675 orders, even before
accounting for divisions already present. It cannot by itself remove an
upper-bound excess of more than two hundred orders. This is a ceiling for
that particular division method, not an impossibility theorem for more
powerful geometric, probabilistic or differently structured counting methods.
The large residual numbers are coarse upper bounds, never lower bounds on
actual incidences. Sharpening the Gaussian estimate itself or reweighting
witnesses using geometry is not constrained by this multiplicity argument.

## Concrete next lemma: weighted completion mass

Let X be the random/free anchor-and-basis data in a fixed witness branch,
with its existing nonnegative weight w(X), including the indicator of every
anchor ball constraint. Let A_X be the resulting r-1 dimensional affine
slice over F_q, and let B_R be the centered-residue Euclidean ball. Define

    C(X) = | A_X intersect B_R |.

The required replacement at this branch is the weighted bound

    integral w(X) * C(X)^k dX <= M_{h,r,anchor},

instead of

    q^((r-1)*k) * integral w(X) dX.

A uniform bound uses C(X)<=C_d and is already sufficient for a valid local
improvement. To obtain stronger averaged savings, the expectation must use
the same weighted distribution of X that includes the anchor constraints.
A statement for a uniform, independently sampled affine slice cannot simply
be substituted: short-anchor conditioning changes that distribution.
Distinctness and exact rank restrictions may be retained in the completion
count for further savings, or dropped for a conservative bound. Existing
covered-family addbacks and every theta/periodic tail remain necessary.

This is a precise new quantitative obligation, not a proved small bound for
M. It identifies the place where simultaneous geometry of the many dependent
points has to enter, rather than counting all field coordinates freely.

## Captured production result (Part396 snapshot)

The completed run `/tmp/wall1_high_order_frontier.log` used the production
functions imported before the subsequent uniform ball-completion and D24-six
changes. It reproduces total logs 17.1698920070702, 51.2341232389501 and
226.846947674638 for h=18,19,24 respectively. Every reported selected cover
agreed with its actual `refined_strata` interval. These are upper bounds,
not actual error estimates.

| h | Leading rank/girth | Nullity h-r | Leading stratum log10 | Leading (c,t,a) | Extra free basis points |
|---|---|---:|---:|---|---:|
| 18 | 11/5 | 7 | 17.1667894118343 | (5,8,4) | 0 |
| 19 | 11/5 | 8 | 51.2325715205191 | (5,8,4) | 0 |
| 24 | 12/4 | 12 | 226.846923049576 | (4,10,3) | 0 |

For h18 and h19 the original cover wins: there is no special addback hiding
the leading girth-five bound. Its two-relation minimum wins over the
one-relation logs 145.7925 and 179.7913. The next rank/girth stratum is 11/7,
with logs 14.6952465 and 48.7610286. At h18 the next two are 9/5 and 9/4;
at h19 they are 11/6 and 10/4.

For h24 the D31-eleven cover wins, but its remaining two-relation term is
226.8469230 while the largest addback, other-two-four, is only 186.5259539.
Thus another local addback improvement would not address this leading term.
The next strata are 12/5 (222.3278268), 13/4 (222.2658317), 12/7
(219.8562837), 11/5 (219.8229137), and 12/6 (218.6351584). The dominant ranks
are near half the support size, and nullity is large.

| h | Anchor union H=c+t | Affine dimension d=r-1 | Unconstrained points k=h-r-2 | Old q exponent dk | log10(q^(dk)) |
|---|---:|---:|---:|---:|---:|
| 18 | 13 | 10 | 5 | 50 | 176.115689757833 |
| 19 | 13 | 10 | 6 | 60 | 211.338827709400 |
| 24 | 14 | 11 | 10 | 110 | 387.454517467233 |

In all three leading branches H=r+2. The two circuits already span the
entire rank, leaving no extra free-basis points. Nevertheless the final
5,6,10 points are charged by all affine-span coefficients. This specifically
identifies the weighted-completion lemma above as a useful next target.

Using the separately proved `wall1_ball_slice_completion.completion_bound`
with the same parameters gives fixed-branch shifts -0.702307901833,
-0.842769482200 and -3.265022123906. Thus the resulting leading branch logs
are approximately 16.46448151, 50.38980204 and 223.58190093. These are
branch diagnostics, not a recalculation of the global sum. The uniform
improvement is valid but far too small to close these particular bounds.
For example the h24 branch alone needs a gain above 226.8469 orders just to
fall below one; its current ten-point uniform gain is 3.2650 orders.

The diagnostic script has subsequently been made compatible with D24-six
and the captured `completions` dictionary, and disables line tracing while
retaining return-local capture. The full numerical log above belongs to the
prior snapshot; these compatibility edits passed a Python compilation check
but were not used to claim a second complete production run.

## Completed Part406 snapshot

The private-return-hook diagnostic completed successfully after the H13/c5,
H14/c4 and H13/c7 integrations. Log: `/tmp/wall1_c7_h13_frontier.log`.
All18 selected-cover and remainder reconstructions pass their interval
agreement assertions. The reported weighted total logarithms are13.2572609301
at size18,46.6972229094 at size19, and215.4389760078 at size24. These are
logarithms of upper envelopes, not measured probabilities.

The leading size18/19 stratum is now rank11/girth6, with the H13 anchor
c=6,t=7,overlap5 and no extra free basis points. The leading size24 stratum
is rank12/girth6 with that same H13 anchor and one extra basis point.
The D27-nine cover wins in all three cases, but the leading contribution
is its remaining two-relation term, not the D27 addback. Thus the next
specific local target is the c6/H13 crossing geometry. At size18 several
other strata are comparable (rank9/girth3, rank9/girth5 and rank10/girth4),
so a gain in the leading c6 term alone will not settle that whole size.

This snapshot supersedes the Part396 leading-stratum identification for
the current production evaluator. The historical figures above are retained
as dated evidence, not presented as the current frontier.

## Completed Part410 snapshot

After the c6/H13, c3/H9 and c4/H12 integrations, the full diagnostic again
completes, including all18 selected-cover/remainder interval checks.
Log: `/tmp/wall1_c6_c3_c4_frontier.log`. Weighted total logarithms are
12.6161089160 at size18,42.1007482855 at size19,213.2561456141 at size24.
These remain upper-envelope logarithms, not probabilities.

The current leading strata are rank9/girth5 at size18, rank10/girth6 at
size19, and rank13/girth4 at size24. Thus the Part406 leading c6/H13
identification is superseded; its improvement has exposed other terms.
The cumulant evaluator separately reports through17 below6.903e-13 and
through24 about1.803622374e213. The full high-order target and the actual
selected-history shell estimate remain open.

## Completed Part414 snapshot

The H9/c5 and H15/c4 refinements and the full rank-ten D32 cover are
integrated. Log `/tmp/wall1_rank10_d32_frontier.log` completes all18
selected-cover/remainder interval comparisons, including the rank-ten
D32 addback. Weighted total logarithms at sizes18,19,24 are respectively
11.5648055378,40.1484938201,212.8177979888. Their leading strata are
rank9/girth4,rank11/girth4,rank12/girth5. These supersede Part410's
leading-stratum identification.

The separate cumulant log `/tmp/wall1_rank10_d32_cumulants.log` passes
all2106 exact regressions and evaluates through17 at6.143361028426690e-13
and through24 at6.573520003e212. No probability interpretation is assigned
to the latter ineffective envelope. Higher-rank D32 extensions under
investigation are not part of this snapshot.

## Part422: anisotropic anchored completion checkpoint

The common-theta completed candidates now include separate free-point weights.
All18 selected-cover/remainder interval reconstructions pass in
`/tmp/wall1_anisotropic_dual_frontier.log`. Size24 has a rank9/girth3 leader,
with crossing t3/overlap2 and5 independent extension points. The dominant
cover is now original rather than an excluded-anchor addback cover.

The matching cumulant run `/tmp/wall1_anisotropic_dual_cumulants.log` passes
all2106 exact checks. Through17 is2.66530650507442e-13 (below2.666e-13);
through24 is1.96043337689968e153. The latter remains an ineffective upper
envelope, not an actual probability. The earlier Part414/420/421 snapshots
remain historical records; this checkpoint supersedes their current frontier.

## Part 423: six-point common-theta checkpoint

The audited six-point theta snapshots are integrated; all2106 exact cumulant
checks and18 frontier interval comparisons pass. Through17 is below2.666e-13,
while through24 is below1.034e140 and remains ineffective. The current size24
leader is rank9/girth3, t4/overlap2, with4 independent extensions (a seven-point
anchor). This supersedes Part422's six-point leader. Sizes18 and19 are led by
rank8/girth4 under the D23-seven cover. See `wall1_six_point_theta_bridge.md`
for the proof boundary, logs and next snapshot candidates. Actual selected
histories and full BKZ remain unproved.

## Part 424: girth-three common-theta checkpoint

The c3 seven-point isotropic counterpart and H8/H10/H11 snapshots pass
independent branch review,2106 exact cumulant checks and18 frontier interval
comparisons. Through17 stays below2.666e-13; through24 is below2.258e136 and
remains ineffective. Size24 is now led by rank8/girth4, t3/overlap3, with3
independent extensions, under the original cover. This supersedes Part423's
leader. The next anchor family is c4 H7; its shared direct-ball bounds must
be kept separate from common-theta snapshots. See
`wall1_seven_point_theta_bridge.md` for proof scope and run provenance.

## Part 425: four-circuit seven-point checkpoint

Independent audit,2106 exact checks and18 interval comparisons pass for the
c4 H7 common-theta bridge. Through17 is below2.665e-13; through24 is below
8.203e133, still ineffective. The size24 leader remains rank8/girth4, but
now uses t2/overlap2 (six points) with4 independent extensions. This
supersedes Part424's seven-point leader. The next obligation is a sharper
complete two-four theta bound or cover including its addback; further
larger-anchor snapshots alone cannot remove this term. See
`wall1_seven_point_theta_bridge.md` for logs and exact scope.

## Part 426: two-four determinant split

The common-theta snapshot now separates five triangular and four orthogonal
codes, preserving all exclusions. Independent audit,2106 exact checks and18
interval comparisons pass. Through17 is below1.526e-14; through24 is below
4.557e133, still ineffective. The size24 rank8/girth4 t2/overlap2 leader
persists. The triangular Gaussian has a Poisson zero-layer lower bound
with the same continuous leading term as the current estimate. The next
substantive direction is joint completion control, not merely a tighter
upper bound on that same anchor Gaussian. See `wall1_six_point_theta_bridge.md`.

## Part 429: integrated Holder candidate

The free-coordinate higher-moment candidate is integrated and audited.
All2106 cumulant checks and18 frontier comparisons pass. The through24
bound stays below4.557e133 with no substantial improvement. The rank8/girth4
six-point leader persists. Its auxiliary rank-tail t11 term dominates the
full-rank contribution, so a full-rank-only Holder improvement cannot
resolve it. The next target is sharper auxiliary rank tails or joint
moments for deficient-rank strata. See `wall1_disjoint_basis_holder.md`
and `scripts/wall1_holder_rank_bottleneck.py` for proof scope and evidence.

## Part 430: generating-row rank tail

The actual-row generator bound is integrated and independently audited.
All2106 cumulant checks and18 frontier comparisons pass. Through17 is
below3.389e-17; through24 is below7.427e73, still ineffective. The size24
leader is now rank12/girth4 with a six-point t2/overlap2 anchor and8 free
extensions, superseding the rank8 leader. The former rank8 rank-tail
obstruction is no longer dominant in its local diagnostic. The new
rank12 leader needs separate diagnosis. See `wall1_generating_row_rank_tail.md`.

## Part 431: full-coordinate joint-incidence candidate

The new candidate retains all518 coordinates directly in F_h; the old
input-only mixed relaxation is not its target. Independent scope and
implementation audits,12 exact fixtures,5 scalar checks,2106 cumulant checks
and18 frontier comparisons pass. Through17 is below3.219e-17; through24
is below1.336e37, still ineffective. The size24 leader is now rank10/girth4,
six-point t2/overlap2 with6 free extensions, with nearby rank8/9 strata.
This supersedes Part430. See `wall1_full_coordinate_completion.md`.

## Part 432: extended Holder grid

The larger finite Holder/gamma grid passes all2106 cumulant checks and18
frontier comparisons. Through17 is below3.219e-17; through24 is below1.913e31,
still ineffective. The size24 leader is rank8/girth3, H9 t6/overlap2 with
one free extension, superseding Part431. Its common-theta snapshot needs
branch audit. A separate canonical two-four normalizer lemma is recorded
in `wall1_two_four_normalizer.md` but has not entered production.

## Part 433: complete c3 common-theta snapshots

All c3 final common-beta snapshots with8<=H<=24 are now retained after
independent branch audit. All2106 cumulant checks and18 comparisons pass.
Through17 stays below3.219e-17; through24 is below1.438e27, still ineffective.
The size24 leader is rank9/girth4, t2/overlap2 with5 free extensions, with
a significant eight-point t4/overlap3 term. This supersedes Part432. The
next six-point normalizer candidate must split triangle/square/remainder;
its audited design is in `wall1_two_four_normalizer.md` and is not yet used.

## Part 434: canonical two-four split completion

The D12/D16 family-specific normalizers are integrated with a generic
one/no-four remainder. Independent audit,2106 cumulant checks and18 frontier
reconstructions pass. Through17 stays below3.219e-17; through24 is below
5.931e25, still ineffective. The size24 leader is rank8/girth4, H8 t4/overlap3
with2 free extensions, superseding Part433. The next H8/H9 isotropic
counterparts have a read-only branch audit but are not yet integrated.
See `wall1_two_four_normalizer.md` for the implemented and pending scopes.

## Part 435: complete audited theta snapshot catalogue

The c4 H8..24 and c>=5 common-theta reconstructions pass independent audits,
2106 cumulant checks and18 frontier comparisons. Through17 remains below
3.219e-17; through24 is below2.170e16, still ineffective. The size24 leader
is rank9/girth4, H7 t3/overlap1,3 with4 free extensions. It supersedes
Part434's H8 leader. This shared-four family requires a separate chart and
normalizer proof; the H6 boost is not applicable as currently certified.
See `wall1_eight_nine_theta_bridge.md` for the complete checkpoint.

## Part 436: general hyperplane convolution

The mixed-weight affine convolution candidate passes independent audits,
2106 cumulant checks and18 frontier comparisons. Through17 remains below
3.219e-17; through24 is below2.981e10, still ineffective. The rank9/girth4
H7 shared-four leader persists. Its D15 chart normalizer has a separate
proof audit and18 exact checks, but is not in production yet. See
`wall1_general_hyperplane_convolution.md` and `wall1_shared_four_normalizer.md`.

## Part 437: H7 shared-four split

The D15 canonical H7 split passes independent audit,2106 cumulant checks
and18 frontier comparisons. Through17 stays below3.219e-17; through24 is
below5.627e5, still ineffective. The size24 leader is rank10/girth4 H6
t2/overlap2 with6 free extensions, superseding the H7 leader. Higher moments
of the canonical anchor itself, rather than only its free factors, are a
candidate for further improvement. See `wall1_shared_four_normalizer.md`.

## Part 438: canonical anchor higher moments

Completion-square cancellation and spectral majorants are documented in
[canonical anchor moments](wall1_canonical_anchor_moments.md). Both independent
audits passed. Full cumulant/frontier runs exited successfully, with 2106 exact
cumulant checks and 18 interval reconstruction checks. Through17 remains below
3.219e-17; through24 is below0.666 (envelope0.6654023307944522). The size24
leader is rank11/girth4, log10 envelope −0.2900398457. The 3.01e-12 target,
selected-history transport, and full BKZ proof remain open. Logs:
`/tmp/wall1_spectral_cumulants.log`, `/tmp/wall1_spectral_frontier.log`.

## Parts 439–440: diagonal and correlated anchor moments

[Canonical moments](wall1_canonical_anchor_moments.md) give the diagonal
refinement; [correlated moments](wall1_correlated_anchor_moments.md) retain the
full Gram matrix via exact LDL pivots. Both complete runs pass. The final
through24 envelope is0.00039232861950197982 (<3.924e-4), with through17<3.219e-17.
The size24 leader is rank10/girth3 (log10 −3.4859477485), dominated by the
H5 anchor. H5 needs explicit dimension scoping and a common-theta split before
using the same lemma; those steps are documented but not integrated. Target
3.01e-12, selected-history transport, and full BKZ remain open. Logs:
`/tmp/wall1_correlated_cumulants.log`, `/tmp/wall1_correlated_frontier.log`.

## Part 441: H5 exceptional correlated completion

The [H5 split](wall1_five_point_normalizer.md) uses explicit anchor-size scope
for D15. Exact chart recovery, cache separation, independent provenance audit,
2106 cumulant checks and18 frontier reconstructions pass. Through24 is now
below2.025e-8 (envelope2.0248575735038707e-8), with through17<3.219e-17.
Size24 is led by rank11/girth4,H6 t2/overlap2 with7 free extensions,
log10 −7.7881732232. Target3.01e-12 and actual-history transport remain open.
Logs: `/tmp/wall1_h5_correlated_cumulants.log` and
`/tmp/wall1_h5_correlated_frontier.log`.

## Part 442: complete transfer target met

[Matroid packing](wall1_matroid_packing.md) gives through24<1.058e-12,
below3.01e-12. The independent bootstrap audit confirms no circularity in
temporary caps. Baseline+transfer+error<1.971e-12 bounds the draw14 event
under the original uniform matrix law, including its actual projection by
pointwise domination. It does not condition on that projection or history.
Size24 is now led by rank7/girth4. The later-history bound remains open;
a sufficient rounded remaining budget is1.951e-12. See the winner-coupled
replica formulation for the unproved conditional estimate.
