# Weighted eight-position determinant28 kernel

The current rank8/girth4 remainder is led by c=4,t=4,overlaps1 and3.
Split diagnostics show the one-four kernel exceeds the no-four kernel
by more than twenty decimal orders. Within the counted norm-eight cover,
determinant28 is the smallest retained determinant in these overlaps.

Let a be the unit norm-four row on the first four coordinates and v a
norm-eight row nonzero on the four new coordinates. Determinant28 means
|<a,v>|=2. If v has eight unit entries, subtract the signed a, obtaining
another norm-eight row with one old entry of absolute value two and four
unit new entries. Otherwise v already has that shape: its coefficient two
cannot be new, since that would give inner product of absolute value one.
The basis change is unimodular and preserves the relation plane.

On this sparse representation give the attached old coordinate weight1/8,
the other three old coordinates weight7/8, and the four new ones weight21/16.
The sum of weights is8. Weighted Gram--Schmidt in metric diag(1/w) gives
squared lengths80/7 and1328/105. The coordinate-weight determinant product
is37664487/1048576>28. The script `scripts/wall1_eight_d28_weights.py` checks
all96 balanced witnesses, including the basis changes, with rational
arithmetic. A unit old/new minor proves the integer plane is saturated.

The complete Poisson kernel has prefactor

    ((1/8)*(7/8)^3*(21/16)^4)^(-1/2)

and the theta product at the weighted squared lengths. Since max(w)=21/16,
use16/21 times the unweighted Gaussian parameters in the original cutoff-40
tail and periodic-coordinate corrections. The Markov exponential is unchanged
because the total weight is8. Both the short-plane lift and the complementary
tail remain covered. Each witness may choose its own attached coordinate
before the union bound.

Only the determinant28 kernel for union size eight uses this refinement,
and only when smaller than its preceding complete kernel. Coefficient counts,
other determinant families and the unclassified remainder are unchanged.
This local result is not yet Lean formalized and does not prove the complete
size17 residual or adaptive BKZ claim.
