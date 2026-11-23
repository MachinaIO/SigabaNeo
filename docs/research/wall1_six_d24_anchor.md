# A complete six-position determinant-24 anchor cover

This is a new rank-four anchor, distinct from the existing eight-position
D24 anchor. It covers the H6 one-four determinant-24 family that controls the
size-17/rank-8 remaining term after Part 396. The comparison below uses the
actually selected D28-ten exclusions, without the unselected D31-eleven
exclusion. No production family was removed by this worker.

## Affine anchor family and integer projection

A representative is

    a=(1,1,-1,-1,0,0),
    b=(1,-1,1,-1,1,-1).

Both rows are balanced, with squared norms 4 and 6 and dot product zero.
Their Gram determinant is 24. For any fixed four-support there are twelve
balanced unit-six lines orthogonal to a balanced four-line. Thus
`binomial(6,4)*12=180` is a valid witness upper count for all labelled
anchors on six positions.

Every witness is a permutation of this affine representative, up to global
row signs. To see this, orient a and split its four positions by sign.
Orthogonality says the sum of the b entries in each two-element group is
the same. Balance of the full unit-six row then forces these sums to be zero,
and the two outside entries of b to be opposite. The old columns are exactly
(1,1),(1,-1),(-1,1),(-1,-1), and the new columns are (0,1),(0,-1).
No arbitrary coordinate sign changes are used to transport affine balance.
These give three distinct projective column classes, each of multiplicity
two, so the plane has girth four over every odd field under consideration.
An old column and a new column give a unit minor, proving saturation.

For an integer vector v, let x=<a,v> and y=<b,v>. Its squared projection onto
the orthogonal complement of the old plane is

    p(v)=||v||^2 - x^2/4 - y^2/6.

Every positive p(v) is at least 1/3. Here is an all-integer proof from the
finite check. Round the two orthogonal plane coefficients independently to
integers and subtract the resulting integer combination of a,b. The squared
plane component remaining is at most 4/4+6/4=5/2. If 0<p(v)<1/3, the rounded
integer vector therefore has squared norm less than 17/6<3, hence at most 2.
There are exactly 73 such integer vectors in six dimensions. Exact rational
calculation on all of them gives p=0 or p>=1/3, a contradiction. The bound is
attained, for example by (-1,0,0,1,0,0). This is not an extrapolation from a
bounded enumeration: the rounding argument reduces all integers to it.

## Complete local code bounds

For t new positions, let H=6+t, ell=2 if t=0 and ell=3 otherwise, and
r0=H-ell. Use beta=r0*N/(2H*R^2), alpha=pi^2/(beta*q^2).
The short theta product is

    theta(4 alpha) theta(6 alpha)                       (t=0),
    theta(4 alpha) theta(6 alpha) theta((t+1/3) alpha)   (t>0).

The latter requires the existing crossing-code premise: its nonzero old
coefficient vector is supported on an independent anchor basis. Such a vector
cannot lie in the old relation plane, so its old projection is nonzero. Every
new coordinate is also nonzero, giving squared projected length >=t+1/3.

If there is no additional balanced norm-four line outside the old plane,
replace t+1/3 by max(t+1/3,7/2). Indeed the old rounding radius is 5/2; a
smaller projected length than 7/2 could be rounded to a balanced nonzero
integer row of squared norm less than 6. Evenness of balanced squared norms
and girth four leave only a norm-four row, excluded by the premise. The
rounded row is balanced because its sum is zero modulo q and its norm makes
the absolute sum strictly less than q. Subtracting old balanced rows preserves
this property and all new coordinates.

The module retains the complete Fourier bound: cutoff L=40 for t=0, L=26
for t>0, tail

    exp(-L^2 alpha/2) theta(alpha/2)^ell,

and the full periodic sum with
`delta=2 exp(-pi^2/(4 beta))/(1-exp(-2 pi^2/beta))`.
In particular `24*26^4 < 3329^2` is checked for the three-row lifting, and
`2*40^2 < 3329` for the two-row lifting. No determinant-only approximation
or omitted modular tail is used. Denote the resulting full ball/incidence
bound by J_t and its no-new-four version by J_t^nf.

For C coefficient choices set

    W_t(C) = min(C J_t, 3 binomial(6,4-t) J_t + C J_t^nf)  (1<=t<=4),
    W_t(C) = C J_t                                         (t>4).

A new norm-four row has all t new coordinates nonzero, chooses 4-t old
positions, and has three balanced sign lines per support. Each fixes at
most one normalized extension code, so the first summand is a witness cover.
The second covers its full complement. Double-counting only enlarges the
upper bound.

## Full same-rank and crossing cover

These are the same complete extension counting formulas used for the
existing D20 and D23 anchors, now with size 6, rank d=4, pattern bound P=180,
and the preceding local bounds. Write Q=binomial(h,6)P.

For whole rank four, use the minimum of

    Q J_0 q^(3(h-6)),
    Q W_1(sum_{a=3}^4 binomial(4,a) q^(a-1)) q^(3(h-7)).

The second selects the least labelled outside point; no extra outside-point
choice is required. Girth four gives at least three old basis coefficients.

For rank r>4, a crossing relation using t>=2 new positions leaves
`e=r-4-t+1` independent additional positions. Set

    C_t = sum_{a=max(1,4-t)}^4 binomial(4,a) q^(t+a-2),
    A_t = Q binomial(h-6,t) binomial(h-6-t,e)
          W_t(C_t) mu^e q^((r-1)(h-r-3))/(e+1).

The lower limit on a imposes a nonzero old part and girth at least four.
The basis-choice correction e+1 is the existing connected-contraction
count: the contracted outside part has no coloops. Sum A_t for t>=3.
For t=2 use the minimum of A_2 and the two complete parallel-class bounds
already implemented in `parallel_completion_count` and
`marked_parallel_completion_count`, with anchor rank four. Both bounds
include the same required local crossing factor in the marked case; neither
is used to discard the t>=3 cases.

If r=h-2, a proper nullity-two anchor would leave every outside element a
coloop, impossible in a connected support; assign zero. The module only
uses this case for h>6. All addbacks are complete for their stated whole
rank, including arbitrary further dependent positions.

The function `envelopes(s)` returns bounds for all sizes 15--24 and ranks
4,...,h-2. Parent integration may remove the D24 term **only from the H6
one-four split** and add this full cover to the existing complete cover,
then take the minimum with the previous complete bound. The existing H8
D24 exclusion is a different family and flag.

## Numerical decision and validation

The initial complete-envelope probe at size 17, rank 8 gives

    log10(new complete H6D24 anchor / current (8,4,2,2) term)
        = -43.94622688599....

The individual crossing contributions relative to that same old term are

| t | log10 ratio |
| --- | ---: |
| 2, after complete parallel/marked minimum | -86.01265967236 |
| 3 | -43.94622688599 |
| 4 | -55.76788319270 |
| 5 | -68.65912906086 |

Thus even the generic third-row cover is much smaller than the currently
charged D24 family. Further short-third-row classification is unnecessary
for this integration decision. The original term includes tiny non-D24
parts; the full production comparison must retain them and recompute all
selected covers, rather than report this 43.95-order local ratio as a global
improvement.

Reproduce with `wall1_six_d24_anchor.py` for 73 exact projection checks and
180 balanced saturated witnesses, and `wall1_six_d24_anchor_probe.py` for the
complete interval diagnostic. Observed log:
`/tmp/wall1_six_d24_anchor_probe.log`. No production source was edited by this
worker. The selected-history bridge and complete BKZ proof remain open.
