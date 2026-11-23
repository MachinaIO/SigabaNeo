# A separate cover for determinant-twenty-three anchors

After Part 318 the size16, rank8, girth4 upper bound is dominated by
c=4,t=5 overlaps1 and3 in the family with no earlier short anchor. These
are Part 317's determinant23 planes. This note retains a third relation
when extending these nine-position, rank-seven anchors.

## Integer geometry

Coordinate sign changes put the short rows in the form

    a=(1,1,1,1,0,0,0,0,0), b=(1,0,0,0,1,1,1,1,1).

Their Gram matrix is [[4,1],[1,6]]. They span a primitive plane, since
exclusive unit coordinates recover both coefficients integrally. Put
S_a=v1+v2+v3 and S_b=v4+...+v8. Orthogonal decomposition gives

    D(v) = sum_(1<=i<j<4)(vi-vj)^2/3
           +sum_(4<=i<j<9)(vi-vj)^2/5
           +(15v0-5S_a-3S_b)^2/345.

A nonconstant triple contributes at least2/3 and a nonconstant five-group
at least4/5, both larger than15/23. If both groups are constant, the last
numerator is divisible by225 and a positive D is at least15/23. Thus
positive integer projection satisfies D(v)>=15/23. The zero case is
precisely the integer plane: the two group constants add to v0.

For a crossing supported on a fixed independent old basis, the old part
cannot be in this relation plane. With t new positions, the third squared
height is at least t+15/23. Take cutoff26, since 23*26^4<3329^2. The same
saturation/minor argument as for the other fixed planes retains all
short code representatives in three dimensions, with squared old heights
4 and23/4. Include the complete long Gaussian tail and periodic terms.

In balanced coordinates a=(1,1,-1,-1,0,0,0,0,0) and
b=(1,0,0,0,1,1,-1,-1,-1), the fundamental triangle's circumcenter is
(9/23)a+(10/23)b and its squared circumradius is48/23. Triangulation and
the barycentric squared-distance identity prove this covering-radius
bound on the whole plane. Part315's reduction argument then gives third
squared height at least90/23 when there is no new balanced norm-four line.
Use the maximum of this and t+15/23. Exceptional lines are counted by
3*choose(9,4-t); each fixes at most one normalized fundamental relation.
No exclusion is applied without adding its exceptional branch.

## Counting and full component cover

For a fixed first four-support, the exhaustive balanced norm-six witness
enumeration gives120 pairs with five new nonzero entries and dot product
of absolute value one. The saturated plane's squared norm form is
4m^2+2mn+6n^2=4(m+n/4)^2+(23/4)n^2. Hence it has exactly one norm-four
line and one norm-six line. No pair multiplicity divisor is needed.
There are choose(9,4)*120=15120 anchors on nine labeled positions.

Use the earlier anchor extension cover with size9 and rank7: dependent
one-point extensions at rank7, every crossing size allowed by the rank,
and the parallel and marked-pair alternatives. The coloop-free quotient
basis divisor e+1 is used only for crossing completions, as before.
The old Gaussian-only anchor bound is retained as an alternative.

Partition girth-four components into the earlier short-anchor families,
the family with a determinant23 anchor, and those with none. Only the
last family's two-relation estimate removes determinant23 summands.
Add all the anchor covers, then take the minimum with the former full
bound. All terms are positive, so overlapping witness families are safe.

The regression enumerates all19683 vectors in {-1,0,1}^9 for the exact
projection identity and checks all120 short-pair witnesses. The preceding
proof, rather than the finite cube alone, establishes the all-integer
projection inequality. The Gaussian and covering-radius bounds also keep
their complete analytic arguments. None of this is yet Lean formalized.

## Outcome

The covering-radius regression, including this plane, passes38852 exact
integer-vector checks and sixteen exceptional-line counts. The full
cumulant probe passes2106 exact regressions and keeps transfer through
fifteen below5.295e-13. The sufficient residual allocation remains
2.4793e-12 for sizes16..24 plus the later selected-history probability.

Size16's full weighted residual log10 is now -1.3789629709, still far
above that allocation. The leading rank/girth strata are (6,4) at
-1.6115400964, (5,4) at -1.9660001176, and (8,3) at -2.5148446833.
The rank8/girth4 determinant23 extension no longer dominates. The
through24 envelope is approximately1.71e233 and remains ineffective.
The residual condition and the adaptive selected-history law are open;
no complete draw14 exit or BKZ theorem follows.
