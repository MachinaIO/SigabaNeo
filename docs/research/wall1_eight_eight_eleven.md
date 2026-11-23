# Girth-eight planes with eleven-position support

After the exact norm-six pair refinement, the size17 rank9/girth8 term
c=8,t=3 is the largest remaining two-relation envelope. Improve its
short-plane geometry without assuming random directions or omitting tails.

At girth eight every short nonzero integer relation has squared norm
at least eight. The affine condition forces even squared norms below
the cutoff. A norm-eight row must have eight +/-1 entries: the other
integer shape has support five and is forbidden by girth. Use the
existing saturated short-plane argument and a Gauss-reduced basis.

If both basis rows have norm squared eight, they must jointly cover all
eleven coordinates: their reductions span the full two-dimensional
code, which has full support. Their overlap has five positions and
their inner product is an odd integer of absolute value1,3 or5. The
exclusive groups have three positions each. In the shared group the
ratios of coefficients are +/-1; the larger equal-ratio group has
(5+|dot|)/2 positions. A row combination cancelling that group has
support11-(5+|dot|)/2. Girth eight excludes |dot|=3 and5, which give
support seven or six. Therefore |dot|=1 and the squared second height
is (64-1)/8=63/8.

If the first squared minimum is eight but the second is at least ten,
Gauss reduction gives |dot|<=4 and second squared height at least
10-16/8=8, also at least63/8. If the first squared minimum is at least
ten, both are at least ten and the standard Gauss-reduced second height
is at least(3/4)*10=15/2. Short-span dimension zero or one is covered by
the same products since unused theta factors are at least one.

Use two complete envelopes with short products

    theta(8 alpha) theta((63/8) alpha),
    theta(10 alpha) theta((15/2) alpha).

Both retain the previous cutoff14 tail and every periodic layer. Each
code falls into one of the two cases. Their Nth powers may be added as
a conservative upper bound for all codes, with the full old coefficient
count retained. Take the minimum with the former complete bound. This
changes only c=8,t=3 and imposes no new assumptions on other strata.

The regression fixes one balanced first row (all others are coordinate
permutations), enumerates all1960 balanced norm-eight partners with the
three new coordinates nonzero, and computes the exact minimum support
from projective column-group sizes. It verifies girth>=8 exactly when
|dot|=1 and Gram determinant63. The analytic argument above supplies
the universal implication; the enumeration is a finite cross-check.

This strengthens a component envelope, not the complete adaptive
selected-history or BKZ theorem. It is not Lean formalized.

The complete cumulant probe passes2106 exact regressions and retains
transfer through sixteen below9.583e-13 (actual envelope about8.79745e-13).
Size17's full weighted residual log10 is8.6275560787, now led by
rank8/girth4 at8.3771479994 and rank8/girth3 at8.1862542466. Thus the
girth-eight refinement removes the intended dominant term, but the
remaining positive envelope is still vastly above2.0505e-12. The
through24 envelope remains about1.61e232. These are ineffective upper
bounds for the remaining families, not actual failure-probability estimates.
