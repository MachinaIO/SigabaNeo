# Full-coordinate completion for connected joint incidences

The full-incidence reduction defines F_h as the sum of P(T), the joint
incidence probability of every point of a distinct connected input support.
Proper-subset discrepancies are handled separately by density_errors.
Thus this target retains output-ball conditions on dependent positions;
it is stronger than the input-only relaxation used by the earlier dual cap.

Fix a valid extended input basis of augmented rank r. Its r output values
are uniform with normalization q^(-mr). A dependent input with affine
coefficient column v has output given by the same v. For the raw full ball,
its indicator is bounded by

    exp(gamma R^2) exp(-gamma(||input||^2+||output||^2)).

The prefactor occurs once, not separately for input and output. For a fixed
coefficient matrix V the Gaussian coordinate kernel is identical in the
n input and m output coordinates, so the joint kernel has exponent n+m.
Only after applying q^(-mr) on eligible input bases may eligibility be
relaxed in this nonnegative count. All integer aliases can then be summed
as in the earlier proof. This gives a new candidate by replacing the frequency column count
118 by518, with the same anchor normalization and coefficient count:

    F_full = q^((r-1)k) exp(k gamma R^2)
               theta(q^2 gamma)^(518k) E[eta^rank(B)],

where B has k rows and518 independent auxiliary Gaussian frequency columns.
The eta, Holder moments and original anchor/free-point factors are unchanged.
The rank tails and basis-packing failure bounds use518 columns.

This replacement is restricted to full joint-incidence bounds. It is not
valid for a mixed proper-subset term whose other outputs lack incidence
constraints, or for actual selected histories. Input-only candidates remain
available. Two independent scope audits approved the derivation and its production
application. The candidate directly bounds F_h; it does not bound the old
mixed-fiber relaxation T_k. The unchanged positive density/cumulant transfer
then consumes the new F_h upper bounds.

The helper defaults to118 coordinates. The three production dictionaries
request518 and retain the118 candidate through a one-step minimum. The
cache includes the coordinate count and gamma grid. The518 branch also
tests gamma in{.2,.25,.3,.35,.4}e-6 in addition to the previous grid; no
global optimization is claimed. The audited API retains0<=k<=118 for both
branches, so the fallback always lies in its domain.

Independent implementation review checked all three dictionaries, the
prefactors, cache keys and scalar non-worsening cases. Twelve exact-rational
fixtures over F5/F7 verify the affine-map normalization, rank-eligible
Gaussian majorant, relaxed tensor-square count, and input-only comparison.
These fixtures complement the general proof; they are not a complete BKZ
certificate. Full production run results follow below when available.

## Part 431 numerical checkpoint

Both full runs exited0: `/tmp/wall1_full_coordinate_cumulants.log` and
`/tmp/wall1_full_coordinate_frontier.log`. All2106 exact cumulant checks and
18 selected-cover/remainder comparisons pass. Twelve exact full-coordinate
fixtures and five scalar non-worsening/cache cases pass; the API also rejects
k119 consistently in either coordinate mode. The post-launch domain fix only
restricts unsupported k>118 and does not affect any production call (h<=24).

Through17 is below3.219e-17; through24 is below1.336e37 and remains ineffective
against the3.01e-12 target. It is not a failure probability. Weighted total
base-ten logarithms at sizes18,19,24 are approximately-12.5054437633,
-4.7177761036,37.1257676479. The size24 leader is rank10/girth4, t2/overlap2,
with6 free extensions. Rank9/girth4, rank9/girth3 and rank8/girth3 are nearby
terms, so controlling only the first stratum will not settle the full target.
This supersedes the Part430 rank12 frontier. Actual selected histories and
full BKZ remain unproved; no new Lean theorem is asserted.
