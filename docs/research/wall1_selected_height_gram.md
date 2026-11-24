# Selected shared-mark Gram matrix for unequal-height witnesses

The existing [scalar-orbit certificate](wall1_scalar_collision_certificate.md)
uses a common candidate radius and a spectral relaxation. The
[selected pair evaluator](wall1_selected_pair_collision.md) retains exact
mixed gates at height one. Here we retain exact mixed gates across several
heights, allowing different candidate families at their respective radii.
This is a computation of the required moments, not a production bound on them.

## Exact gated moments

Fix a frozen-space/syndrome-image stratum and its actual quotient mark group
H, of size h>1. Let E be a gate decided before the fresh uniform U in H.
Write Q(C) for the joint probability of E and the quotient equations C,
under the conditioned stratum law. Its base stratum probability must not
be multiplied twice. Full and quotient equations in E remain distinct.

For each integer height j not divisible by q, fix a finite candidate multiset
S_j, with quotient-coordinate data x and label lambda(x). Define

    X_j(U)=sum_(x in S_j) 1{lambda(x)=jU}.

All heights use the SAME U. Put

    M0 = (h-1)Q()/h,
    b_j = (1/h) sum_(x in S_j) [Q()-Q(x)],
    G_jk = (1/h) sum_(x in S_j,y in S_k)
               [Q(kx-jy)-Q(kx-jy,x)].

These are the joint gated nonzero-mark mass, first moments, and ordinary
second moments, respectively. They are not conditional moments divided by
P(E). The equation lambda(kx-jy)=0 is necessary and sufficient for the
same mark U to serve both witnesses. Because j is invertible it determines
one U; the anchored second term removes exactly U=0. Diagonal terms are
included. For identical occurrences their contribution is [Q()-Q(x)]/h.
No independence of candidates, heights, or selection events is assumed.

Equivalently replace each x in S_j by j^(-1)x modulo q. The constraints
then become x'-y' and (x'-y',x'), so the existing grouped-difference machinery
applies. This normalization is only for labels: the geometric height remains
the actual integer j, not its residue representative. Repeated residues,
points and heights retain their multiplicity. Negative heights are allowed.

## Coverage and winner tail

For fixed nonnegative weights w, let Y=sum_j w_j X_j. Weighted
Cauchy--Schwarz on the joint event E,U!=0 gives

    P(E,U!=0,some witness) >= (w^T b)^2/(w^T G w).

If the denominator is zero, the numerator is zero and we use bound zero.
Thus the gated nonzero-mark void mass is at most M0 minus this expression.
G is symmetric positive semidefinite because it is a genuine Gram matrix.
One may optimize w using the fixed stratum's exact gated moments. If the
families or weights depend on the hidden map, that dependence must instead
be retained inside the expectations; the fixed-data Q formulas cannot be
used as if they were independent.

If every candidate is a genuine point of K with ||x||²+j²<=r², and r>=1,
a witness rules out a strict long winner S>r; the zero mark has its unit
height-one witness. Therefore the same upper bound controls P(E,S>r).
For an inclusive tail S>=r, use strict geometric inequalities and r>1,
or a separate no-ties result. On a fixed geometric stratum unequal radii
sqrt(r²-j²) may be used directly, rather than shrinking every family to
the radius belonging to the largest height.

This applies before the fresh draw. It does not supply the needed selected
moment bounds and does not justify conditioning U on future gate survival.

## Exact signed affine-square optimization

For the void event, nonnegative weights are an unnecessary restriction.
For every real vector w, pointwise

    1{X=0} <= (1-w^T X)^2.

The expectation under the same joint gated nonzero-mark measure is

    M0-2w^T b+w^T G w.

Apply the existing [weighted square optimizer](wall1_optimal_mixed_square.md)
to the augmented Gram matrix [[M0,b^T],[b,G]]. This is an application of that
existing method, not a new general optimization theorem. Its exact rational
solver produces Gw=b and returns the upper certificate M0-b^T w. PSD of
the augmented matrix ensures b is orthogonal to ker G, so the system is
consistent even when G is singular. For any perturbation z, the objective
increases by z^T G z>=0. Thus this is the best affine-square certificate
using these counts and moments, including all signed coefficients.

For any proposed nonnegative weights v, optimizing the scale w=tv yields
M0-(v^T b)^2/(v^T G v). Therefore the signed optimum dominates every
nonnegative weighted second-moment certificate. No nonnegative-support
claim for the signed sum is needed: the square equals one when all counts
vanish and is nonnegative everywhere else. The zero-denominator case
again has zero first moment.

The improvement can be strict. Under the uniform law on count vectors
(0,0),(1,1),(2,3), the exact data are

    M0=1, b=(1,4/3), G=((5/3,7/3),(7/3,10/3)).

The signed weights (2,-1) give void certificate 1/3, which equals the true
void probability in this fixture. For nonnegative weights (a,c), coverage
is at most 3/5: cross multiplication reduces this claim to
6ac+10c²>=0. Hence the best nonnegative-weight void certificate is 2/5.
This is an abstract count-law example, not a production lattice example.

The optimizer coefficients depend on the fixed gated moment law, not on the
realized hidden map or fresh mark. Normalizing only some of M0,b,G by gate
mass would invalidate the calculation. The true winner implication still
requires the preceding geometric witness conditions. None of this controls
the actual width506 moment entries.

## Reproduction and scope

Run `python3 docs/research/scripts/wall1_selected_height_gram.py`.
The evaluator accepts mixed signed exclusion states and additional positive
full or quotient equations. It keeps the zero-anchor corrections even when
the exclusion gate is incomplete. Its Gram matrix includes ordinary diagonal
terms, unlike a second factorial moment.

The exact fixtures enumerate every residual map and every nonzero fresh
mark for q=3,5,7, with syndrome-image dimension zero and one. They include
unequal families, a zero candidate, repeated residues, negative heights,
repeated height residues at q=3, an old full exclusion, and positive quotient
constraints. Across 24 fixtures, 1536 rational nonnegative weight choices
satisfy the coverage bound; in 20 fixtures a tested combination improves on
the best individual-height second-moment certificate. These are algebraic
fixtures, not geometric models of reachable width506 histories.

Independent mathematical review verified the collision equation, anchoring,
normalization, selection dependence, and strict-versus-inclusive tail boundary.
The production geometry and selected Gram entries remain unbounded. No
full-history probability improvement or Lean formalization is claimed.

The checker additionally evaluates the optimized affine square directly on
every enumerated map and mark, checks that it dominates all 1536 sampled
nonnegative weight bounds, and tests empty, zero-mass and singular families.
The signed strict-improvement fixture has an exact certificate of the best
nonnegative bound as well. Independent review confirmed the signed extension
and its joint-measure normalization.

## Geometric one-step check with a complete old-minimum gate

The algebraic fixtures above do not enforce candidate lengths. A separate
checker now does so in genuine low-dimensional q-ary lattices. For
q in {7,11}, take K=Z^3 and, for uniform a=(a1,a2) in F_q^2,

    M_a={(x,y,z) in Z^3: x=a1*z and y=a2*z modulo q}.

The quotient K/M_a is F_q^2 and det(M_a)=q². Use r²=11/2. The exact old
minimum gate is the exclusion of all nonzero integer points of norm²<=5.
Integer squared lengths make this equivalent to lambda1(M_a)>r.
Set S_1=Z^3 intersect B_2 and S_2=Z^3 intersect B_1, including zero.
Every occurrence satisfies ||x||²+j²<=5<r². On the old gate zero-labeled
candidates other than zero are excluded, while the general anchored formulas
handle the zero candidate without an additional assumption.

For each fresh U in F_q^2, the actual appended graph lattice is

    L_(a,U)={(x,j) in Z^3 x Z: lambda_a(x)=jU}.

Its strict-long event lambda1(L_(a,U))>r is evaluated independently by
checking every nonzero integer vector in the four-dimensional ball of squared
radius 5. On the old gate, height zero contributes nothing; |j|>=3 is too
large; symmetry of S_j accounts for negative heights. Therefore this exact
short-vector test agrees with absence of both witness families. The zero
mark always has its height-one unit vector.

The checker enumerates all q² old maps and q² fresh marks, and compares
first and second moments, and the optimized square expectation, against the
mixed-equation evaluator. Their common unconditioned denominator is q^4.
There are 32 surviving old maps at q=7 and 104 at q=11. Conditional on the
old gate, the exact strict-long probabilities are respectively 61/196 and
1093/1573. The optimized two-height upper bounds are 3376/8659 and
231360/325127. In both cases they improve the corresponding height-one
moment upper bound, while remaining strictly above the exact probability.
The checker prints the unnormalized joint values as well, so the conditioning
factor is explicit.

Run `python3 docs/research/scripts/wall1_selected_height_geometry.py`.
This verifies actual witness geometry and a complete old-minimum gate in a
one-step finite experiment. Uniform a conditioned only on its old minimum
is NOT asserted to be the law induced by a preceding BKZ tour. Thus these
results do not supply the width506 selected-history moments or a production
failure bound. No geometric gate-preservation or chronological-law claim is
inferred from the finite checks.

Independent review reran the geometric checker and confirmed the complete
short-vector enumeration, gate equivalence, signed-height reduction and both
joint and conditional normalizations.

The [chronological projection check](wall1_chronological_height_gram.md)
adds actual first shortest-vector selection and rational projected geometry
before the fresh append. Its miniature winner strata reveal the entire old
matrix, so it does not resolve production residual selection bias.
