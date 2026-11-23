# Complete rank-five four-pair extension cover

This connects the four-pair projection lemma to the rank5 triangular
residual at sizes14..24. Only rank5 uses the new exclusion; larger ranks
retain their prior complete covers.

A four-pair anchor has eight positions, augmented rank5, three independent
relations, and945 balanced patterns. Fix such an anchor in a larger rank5
support. The least-labelled outside point is dependent on an independent
five-point anchor basis. Its nonzero old coefficient vector has nonzero
projection modulo the anchor relation plane, so the previous projected
minimum gives fourth squared GS length at least1+1/2=3/2. The first three
squared GS lengths are4,3,8/3. Use the complete nine-position, rank5 kernel
with relation dimension4 and cutoff24;32*24^4<3329^2 and9*24^2<3329^2.
The complementary Gaussian tail and all periodic-coordinate corrections
are retained.

For additional norm-four rows, there are two affine sign types: all pair
sums have equal signs within their pairs, or every pair has opposite signs.
Internal swaps of pairs and global row signs map the eight mixed patterns
to a representative without changing affine balance. For each type there
are168 balanced norm-four lines using the new position. Their determinants
before filtering are52,84,116. Compute all126 four-column minors for each
line. Unit minors prove saturation; every minor has absolute value<7.
Every six-column complement must have rank4 to exclude a relation with
support<=3, over both Q and F_3329. Checking all84 complements gives

    equal-sign type: {84:96},
    mixed-sign type: {84:72,116:24}.

In particular all determinant52 candidates violate girth four. Use the
uniform witness upper counts{84:96,116:24}, with fourth squared GS height
D/32 and the complete cutoff24 kernel for each D. These are line counts,
not a claim that the witnesses determine distinct extended planes.

On the complement of new norm-four relations, nearest-plane rounding has
squared radius29/12, and a balanced nonzero relation outside the anchor
plane has squared norm at least6. Thus fourth squared GS length is at least
43/12. With C=sum_(a=3)^5 choose(5,a) q^(a-1), the complete dependent-point
bound W is the minimum of C times the unrestricted kernel and

    96 K(84/32) + 24 K(116/32) + C K(43/12).

After this distinguished outside point, each further point has at mostq^4
affine-slice choices. The complete anchor envelope is the minimum of

    choose(h,8)*945*J0*q^(4(h-8))

and

    choose(h,8)*945*W*q^(4(h-9)),

where J0 is the existing four-equal-pair-sum ball bound including modular
aliases. No factor for choosing the least outside point is needed.

The triangular rank5 remainder removes only determinant32 from its
explicit two-new-point norm-four cover. All other determinants, the
no-new-four term, and every tail remain. Its old completion bound and the
pair-multiplicity-corrected bound remain valid on this restricted family.
Add the ENTIRE four-pair anchor envelope to that restricted remainder,
then take the minimum with the previous full rank5 bound. This is done
both for the size14 baseline and for sizes15..24. No restricted-only
quantity is substituted for a full bound.

The finite check covers336 balanced extension lines across the two types,
with their unit minors and girth tests. The earlier129 projection checks
and945-pattern check supply the geometric and counting prerequisites.
This is a paper-level extension cover with exact checks; it is not new
Lean formalization or a completion of the global residual or adaptive
BKZ distribution bridge.
