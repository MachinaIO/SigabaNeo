# Three-circuit short families on seven positions

The leading rank8/girth3 term has c=3,t=4. Refine the two-norm-six and
no-norm-six families separately, retaining the one-six family.

## Two norm-six rows

Every such plane contains a norm-six generator on the first circuit C.
A norm-six row on C is a permutation of(2,-1,-1). If both independent
rows initially lie outside C, each must be unit on four new and two old
positions. Orient their proportional new parts to agree. Their old supports
cover C and share one coordinate; their inner product is3 or5. Gauss
reduction forces3, so their difference has squared norm12-6=6 on C.
This is a unimodular basis change.

Fix the norm-six row on C and enumerate the balanced norm-six second rows.
Unit old and new entries give a unit minor. The exact normalized plane
counts in `scripts/wall1_three_seven_six.py` are

    overlap1: {32:4};
    overlap2: {27:18,32:4,35:24,36:18}.

Keys are Gram determinants. All counts agree at q=7,17,3329. Use squared
heights6,D/6 and the existing cutoff-36 tails and periodic corrections,
with the exact counts divided by the full coefficient count. Compare with
the previous complete two-six cover.

## No norm-six row

Balanced norm-eight or norm-ten rows cannot have full support on C: the
norm-eight shape on at most three positions has support two, and there is
no balanced norm-ten row on three positions. Thus these short rows must
be nonzero on all four new coordinates. The exact enumeration
`scripts/wall1_three_seven_pairs.py` runs over every balanced integer row
of squared norm8 or10 (including coefficient-two shapes), imposes
proportional new coordinates, full support of the old difference and
Gauss reduction2|dot|<=first_norm. It obtains

    squared norms(8,8): no pairs;
    squared norms(8,10): determinant76,24 pairs;
    squared norms(10,10): determinant91,48 pairs; determinant96,18 pairs.

The row generator exhausts square partitions within the stated norms and
normalizes only overall sign. The proportionality and support checks use
integer cross-products. Their absolute values are below3329, so the small
row conditions forced modulo3329 also hold over the rationals. This is a
finite classification of all vectors at these norms, not a sample from
an unbounded search.

If the first minimum is8, the second is at least10; determinant76 gives
height19/2 when it is10, and the Gauss bound gives at least10 when it is
at least12. If the first minimum is10, the second height is at least91/10
when both norms are10, or at least19/2 otherwise. When the first minimum
is at least12 the generic heights12,9 apply. Sum complete kernel powers
for(8,19/2),(10,91/10),(12,9), retaining cutoff-14 tails and periodic terms,
and take the minimum with the preceding no-six kernel. Counts of all other
families remain. The whole residual and adaptive BKZ bridge remain open;
these refinements are not yet Lean formalized.
