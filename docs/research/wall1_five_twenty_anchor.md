# Five-position determinant-twenty anchor

The size17 rank8/girth3 diagnostic shows the six-position anchor charge
is negligible relative to the remaining two-relation term. Its largest
configurations add two positions to a first three-circuit. At overlap one
the one-norm-four term dominates; at overlap two the two-four family is
also substantial. The present refinement only addresses the determinant20
part of the one-four family and does not remove the two-four family.

Up to coordinate signs and permutation, a five-position norm-four/six
pair of determinant20 is

    a=(1,1,1,1,0), b=(1,1,0,0,2).

The affine rows before this isometry can be taken as
(1,1,-1,-1,0), (1,1,0,0,-2). Geometry may use the signed version;
balanced-line counting uses the original affine rows. A unit minor
establishes that the rows generate their primitive integer plane.

For every integer vector v, squared distance to this plane is exactly

    ((v0-v1)^2+(v2-v3)^2)/2
      +(v0+v1-v2-v3-v4)^2/5.

Every nonzero distance is therefore at least1/5: each numerator is an
integer square and every summand is nonnegative. This is an all-integer
proof, independently checked on3125 vectors in [-2,2]^5. It replaces
the different lower bound3/10 for the six-position anchor.

The Gram matrix is [[4,2],[2,6]], with basis heights4,5. Fundamental
triangles have squared circumradius4*6*6/(4*20)=9/5. In the absence of
additional norm-four rows, the nearest representative of a third relation
has squared norm at least six, hence projected squared length at least
6-9/5=21/5. With t new nonzero coordinates, also retain the lower bound
t+1/5. The existing cutoff27 third-code tail remains valid because
20*27^4<3329^2. All periodic layers remain.

There are30 affine witness pairs on a fixed five-position set. The
norm-six row must have support three and overlap the norm-four support
in two positions; its coefficient of absolute value two is at the
exclusive fifth coordinate. The two shared coefficients have the same
relative sign, giving the canonical geometry above. Enumeration checks
all30 witnesses and their unit minors. Counting witnesses is a safe
upper bound even if a plane has multiple representations.

The anchor has rank3. Reuse the proved girth-three extension cover with
size5, rank3,30 patterns and the new projection minimum. Dependent-point
coefficients start at old support2, crossing coefficients at max(1,3-t),
and marked-pair coefficients at old support1. The parallel/marked covers,
crossing divisor and no-coloop exclusion are unchanged. Extra norm-four
third codes are covered explicitly before using the restricted kernel.

Only `exclude_five_twenty` removes the determinant20 term from the exact
five-position table. The complete candidate adds both the existing
six-position anchor cover and this five-position cover back, and is then
minimized with the previous complete candidates. All other short-plane
families are retained. This is not a Lean formalization or a full BKZ proof.

The full interval probe passes2106 exact cumulant regressions. Transfer
through sixteen is about8.78531642171e-13, below the retained9.583e-13 cap.
Size17's weighted residual log10 is6.1546901715; the leading strata are
now rank8/girth6, rank8/girth4, and rank8/girth3. The latter is5.5854684520.
Through24 remains about1.61354e232, so the remaining2.0505e-12 allocation
and the adaptive BKZ bridge remain unproved. These are upper envelopes,
not actual failure probabilities. Logs: `/tmp/wall1_five_twenty.log` and
`/tmp/wall1_five_twenty_cumulants.log`.

Implementation checks also cover the five-position extension through
t=19, needed at size24. Equal rational height thresholds are compared
as integer numerators before interval conversion, avoiding undecidable
comparisons of overlapping enclosures of the same rational number.
