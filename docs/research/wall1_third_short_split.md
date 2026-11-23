# Splitting off a third norm-four direction

The fixed old plane has balanced integer generators a,b of squared length
four. Their inner product is zero (orthogonal six-position anchor) or has
absolute value one (shared seven-position anchor). Both planes are
primitive. In the orthogonal case the fundamental square gives squared
covering radius two. For the shared case change one row's sign if needed
to make the inner product one, and triangulate the fundamental rhombus
into triangles (0,a,b) and (a,b,a+b). The first triangle's circumcenter
is (2/5)(a+b), of squared distance 8/5 from its three vertices. For any
point x in the triangle, the barycentric average of its squared distances
to the vertices is 8/5-||x-circumcenter||^2<=8/5. Thus at least one vertex
is within squared distance 8/5; the second triangle is its reflection.
Subtracting a nearest lattice vertex leaves squared in-plane error at most

    C=2 (orthogonal), C=8/5 (shared).

Let z be an integer vector in the saturated short
three-dimensional lattice, outside the old plane. Subtract the chosen
integer combination of a,b. The resulting integer vector w has

    ||w||^2 <= ||projection_off_plane(z)||^2+C.

Its reduction belongs to the three-row relation code. That code is affine
(coordinate sum zero modulo q) and comes from distinct points of girth
at least four. If ||w||^2<6, then its coordinate sum is zero over the
integers: |sum w|<=sqrt(H)||w||<q, since q^2>6H. Its squared norm is
therefore even. It cannot have norm zero because z is outside the plane.
It cannot have norm two because that would be a weight-two relation
between distinct points. Thus it has norm four and is a balanced
four-support line outside the old plane.

Consequently, on codes with no additional balanced norm-four line, every
nonzero quotient vector has squared height at least 6-C: four for the
orthogonal anchor and 22/5 for the shared anchor. Take the maximum with
the previously established t+delta bound. This argument applies to
every vector of the saturated short lattice, not merely to its chosen
fundamental generator. The old-plane basis, saturation, cutoff, long
Gaussian tail and periodic terms remain exactly as in the fixed-plane
bound. Only its third short theta factor changes.

## Counting exceptional codes

Fix the old anchor basis X and a set of t new positions. The third
fundamental relation has nonzero coefficients on all new positions and
old coefficients supported on X. Every codeword outside the old plane
has new part proportional to this relation, so an independent norm-four
line must use all t new positions. For 1<=t<=4 there are at most

    K_t = 3 choose(s,4-t)

such balanced sign lines, where s is the old anchor size. Each line
determines one three-dimensional code after adjoining the old plane.
For a fixed independent X, subtracting old-plane rows and normalizing
one new coordinate gives a unique fundamental relation. Therefore K_t
bounds the number of exceptional normalized coefficient assignments
across all old supports, rather than separately for each support size.
Multiple lines defining one code only cause overcounting.

If Q is the old coefficient-count bound, J the unrestricted fixed-plane
bound, and J_no4 its strengthened version, replace the aggregate Q*J by

    min(Q*J, K_t*J + Q*J_no4).

The unrestricted bound is used for every exceptional code. The total
coefficient bound Q also bounds the nonexceptional family. Both terms
include complete tails and modular layers. In the implementation the
first Q*J can retain any independently justified, smaller joint bound.
For t>4 the current code simply retains the previous bound.

Apply this split to dependent extensions (t=1), all crossing terms, and
marked parallel pairs (t=2). Their position counts, completion bounds
and basis multiplicity factors are unchanged. The parallel alternative
without a retained pair is also unchanged. The minimum of the three
small-crossing covers remains valid.

This is a paper argument with exact rational regression checks and
interval evaluation, not a Lean formalization or a completed BKZ proof.

## Diagnostic result

At component size16 and rank6, the shared-anchor small-crossing envelope
has unweighted log10 about 15.30519, down from 31.11807. These are the
same component units before multiplying by the linear-remainder weight;
neither number is a probability. The orthogonal-anchor large and small
crossing terms have log10 approximately -24.75337 and -21.47479.
The full component envelope still includes determinant-twenty anchors,
triangular anchors and the family with no such short anchors. Improving
this one family therefore does not prove the size16 or remaining budget.

Validation: 4246 exact rational reductions verify the covering-radius
inequality and the norm-two-or-four alternative; eight exact line counts
verify K_t for both anchor types and t=1,2,3,4. The earlier 15625
orthogonal and 78125 shared-plane projection checks also pass. These
finite checks supplement the all-integer arguments above.

The complete cumulant probe passes its 240 transfer checks and 1866
connected-support/error checks. The outward interval for transfer through
fifteen is approximately 1.556871908218055e-12 from above, hence below
the new cap 1.557e-12. With reference and error below 9.131e-13, the
sufficient residual condition becomes

    sum_(h=16)^24 L_h^* U_h + Pr(max_(i=15)^404 b_i>.280) <= 1.4518e-12.

The allocated total is exactly 3.9219e-12<3.922e-12. The residual condition
is not established: the complete through-24 upper envelope remains about
5.83e238. It is an ineffective upper bound, not evidence that the event
has large probability. Adaptive later-history estimates also remain open.
