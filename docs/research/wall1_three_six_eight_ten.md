# Ten-position extension of a norm-six three-circuit

The current rank8/girth3 residual is led by c=3,t=7,overlap2. In the
no-norm-four family, a norm-six relation must lie on the first three
positions: every independent relation uses all seven new positions. Its
shape is a permutation of (2,-1,-1), up to overall sign. There are three
normalized first lines.

An independent row of squared norm eight must be unit on all seven new
positions and one old position. The other norm-eight shapes have too few
positions. The exact script `scripts/wall1_three_six_eight_ten.py` enumerates
all balanced rows, normalizes modulo the first row using a unit old pivot
and a unit new pivot, and deduplicates each prescribed-support plane.
For either old overlap1 or2, the counts are35 at Gram determinant44 and70
at determinant47. They agree at q=7,17,3329. An old unit pivot and a new
unit entry give a unit minor, so the rows generate the saturated integer
plane and provide second squared Gram--Schmidt height D/6.

In the complement, reduce the second basis row against the norm-six row.
Its squared norm is at least ten, and its inner product with the first row
has absolute value at most three. Its squared perpendicular height is at
least10-9/6=17/2. The balanced affine lift makes squared norms even; the
existing cutoff and modulus conditions justify that lift.

Add the two complete rare kernels with their exact counts and the full
previous one-six coefficient count times the height17/2 remainder. Keep
the previous cutoff-36 tail and every periodic correction in each kernel,
then take the minimum with the previous one-six bound. The two-six and
no-six classes are untouched. This classification is not Lean formalized
and does not establish the complete residual or adaptive BKZ estimate.

## No-six family: short reduced pairs are impossible

The preceding rare-eight split alone has negligible numerical effect. The
no-six family is improved using the rank-one restriction on the seven new
coordinates. Every nonzero relation either lies on C or is nonzero on all
seven new coordinates. A balanced row supported on C has neither squared
norm eight (the only such balanced shape has support two) nor ten. A row
outside C of norm eight is unit on seven new and one old coordinates; at
norm ten it is unit on all ten. Other norm-eight/ten shapes have support
at most seven and cannot cover seven new plus an old coordinate.

For two independent such rows, the new parts are proportional. Orient them
to agree there. Their old difference is a nonzero relation on C and must
be nonzero at all three old positions, by girth three.

* Two norm-eight rows differ on at most two old positions: impossible.
* A norm-eight and norm-ten row have inner product seven plus or minus one,
  violating the Gauss bound |dot|<=4 for the shorter row.
* Two norm-ten rows can differ at all three old positions only by having
  opposite signs on all three. Their old sums would then be opposite nonzero
  odd integers, whereas agreement on the new coordinates and balance force
  those old sums to be equal: impossible.

Consequently a reduced basis in the no-six family has exhaustive squared
GS lower-bound cases (8,10), (10,19/2), or (12,9). These follow from second
squared norm at least twelve in the first two cases and the general Gauss
inequality in the last. The script `scripts/wall1_three_ten_pairs.py` checks
all105 candidate pairs with full old-difference support as an independent
finite verification of these exclusions. The production bound sums the
three complete kernel powers with unchanged cutoff-14 tails and periodic
terms, and takes the minimum with the preceding no-six bound.
