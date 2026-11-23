# Seven-position determinant23 anchor extensions

The leading size16 rank8/girth4 terms after Part327 have c=4,t=3 and
overlaps2,3. Their rare norm-four/norm-six plane has seven positions,
not the nine positions of Part319. It needs a separate component cover.

## Integer geometry

After coordinate isometries use

    a=(1,1,1,1,0,0,0), b=(1,-1,0,1,1,1,1).

Their Gram matrix is [[4,1],[1,6]]. Exclusive unit coordinates give a
primitive plane. Its fundamental triangles have squared circumradius
48/23, as for every primitive basis with this Gram matrix. This proves
the same squared covering-radius upper bound for the plane lattice.

Suppose an integer vector had positive squared perpendicular projection
D<11/23. Subtract a nearest old-plane lattice point. The resulting
integer vector w has the same projection and squared norm at most
D+48/23<59/23<3, hence integer squared norm at most two. There are
exactly99 such vectors in seven dimensions. Exhaustively evaluating

    ||w||^2-(6<a,w>^2-2<a,w><b,w>+4<b,w>^2)/23

gives zero or a value at least11/23 for every one, a contradiction.
This is a bounded exact certificate for the all-integer statement.

For a crossing with t new positions and nonzero old coefficients in
an independent anchor basis, the third squared height is at least
t+11/23. Retain old heights4 and23/4, cutoff26, the complete long tail
and all periodic layers. The no-additional-norm-four branch also has
third height at least90/23 from the covering-radius argument in original
balanced coordinates. Count all exceptional norm-four lines separately.

## Counting and component cover

For a fixed four-support, enumerate its three balanced norm-four lines
and all balanced norm-six lines with nonzero entries on the other three
positions and dot product of absolute value one. There are84 pairs,
so choose(7,4)*84=2940 labeled anchors. The primitive plane norm form
4m^2+2mn+6n^2 has unique norm-four and norm-six lines, so these witness
counts suffice without a multiplicity divisor.

Use the size7, rank5 extension cover with all dependent-point, crossing,
parallel and marked-pair branches. Girth remains four; none of the
smaller old supports permitted only at girth three is assumed here.

Split the full girth-four family into the previous short-anchor families,
the family with an eligible seven-position determinant23 anchor, and
the family containing none. Only the last family's c=4,t=3 rare norm-six
count is set to zero. Retain its norm-eight term and all other bounds;
add the complete anchor covers and take the minimum with the earlier
full envelope. No norm-eight family or modular tail is discarded.

Both the99-vector projection certificate and84-pair enumeration pass
exactly. The finite certificate, analytic envelope and full component
cover are not yet Lean formalized. The remaining selected-history and
BKZ claims require more than this individual component refinement.

## Size16 admission and remaining condition

The complete cumulant probe passes2106 exact regressions and its outward
interval for transfer through sixteen is below9.583e-13 (approximately
9.582432310768002e-13 from above). The main probe now asserts this cap.
This supersedes Part327's failed size16 admission. Transfer through
fifteen remains below3.419e-13.

Using the exact linear remainder for unknown components of size at
least17, a sufficient remaining condition is

    sum_(h=17)^24 L_h^* U_h + Pr(max_(i=15)^404 b_i>.280) <= 2.0505e-12.

Here h is component size; i is the later selected-draw index. The L_h^*
are the positive linear-remainder weights with the admitted components
through sixteen. The b_i remain the smaller-radius void quantities,
not direct conditional exit probabilities. Together with the existing
reference/error cap9.131e-13, the allocation is exactly

    (0.9583+0.9131+2.0505)e-12=3.9219e-12<3.922e-12.

The remaining condition is unproved. The through24 envelope is still
about1.61e232, and later selected-history estimates remain open. This
admission is an intermediate component bound, not a completed draw14
exit bound or a complete BKZ theorem.
