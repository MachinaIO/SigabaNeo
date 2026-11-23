# Norm-ten split for nine-position four-circuit planes

The rank8/girth4 residual after Part372 is led by t5/overlap3. Its one-four
kernel dominates the no-four part. Within the one-four split the generic
second-minimum>=10 remainder exceeds the counted short-line contribution
by over two decimal orders. Therefore a refinement of the already-counted
norm-eight determinant31 kernel alone cannot resolve this term.

There is a unique norm-four line in this family, on C. There are three
balanced such lines on its prescribed four positions. On nine positions,
a balanced norm-ten integer line, up to sign, has shape

    (2,1,1,-1,-1,-1,-1) or (2,-2,1,-1).

The unit support-ten shape does not fit. A coefficient of absolute value3
would leave only one unit entry and could not be balanced. Thus the list
is exhaustive. For the first shape, choose the doubled coordinate and
then the two other positive coordinates, obtaining7 choose(6,2)=105 per
support-seven set. For the second, there are4!/2=12 lines per support-four
set. Hence there are105 choose(9,7)+12 choose(9,4)=5292 lines, or at most
15876 witnesses paired with the three possible norm-four lines on C.

Every relevant independent row is nonzero on all five new coordinates.
Its norm-ten shape therefore has a unit new entry. Together with any old
unit coefficient of the norm-four row this gives a unit minor; the pair
is saturated and remains independent modulo3329. For fixed prescribed
supports it determines at most one normalized coefficient chart. The
witness count is an upper bound, including supports and pairs that are
not eligible; it need not equal the number of distinct eligible planes.

Gauss reduction against the first norm-four row gives |dot|<=2. For a
second row of squared norm10 this yields second GS squared length>=9.
After charging this finite family, a second squared norm>=12 gives height
at least11. Keep the previous norm-six/eight determinant cover and replace
its generic remainder by

    min(one_count,15876)/Q K(4,9)^N + one_count/Q K(4,11)^N.

All cutoff40 tails and periodic corrections are inside K, and the complete
new split is minimized with the previous bound. Existing removed-anchor
covers, coefficient counts and the no-four family remain. Diagnostics
report both the previous generic remainder and the new split.

The exact script verifies all5292 balanced line representatives, their
support counts, and the unit-new-entry property whenever applicable.
This is a paper-level bound, not new Lean formalization or a proof of the
full residual budget or adaptive BKZ distribution bridge.
