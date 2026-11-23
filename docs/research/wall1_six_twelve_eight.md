# Norm-six/eight planes on twelve positions

The rank10/girth6 residual is led by c=6,t=6,overlap5. Split diagnostics
show that its one-six contribution dominates the no-six contribution by
about48 decimal orders before common normalization. This identifies the
one-six family as the target of the following refinement.

A norm-six row must be unit on six positions, since girth six excludes
the support-three coefficient-two shape. It must lie on the first circuit
C. Otherwise it would use all six new positions and no old coordinate,
contradicting the nonzero old projection of a proper crossing. The first
norm-six line is therefore one of ten balanced unit lines on C.

Any independent norm-eight row must be unit on eight positions: its other
balanced shape has support five and violates girth six. It uses all six
new and two old positions. Its inner product with the first row is0 or+/-2,
giving Gram determinant48 or44. An old unit entry and a new unit entry
give a unit minor. The generated integer plane is saturated, with squared
second Gram--Schmidt height D/6.

`scripts/wall1_six_twelve_eight.py` normalizes second rows modulo the first
row and by the first new entry, deduplicates planes and checks the prescribed
old support at each cancellation scalar. The counts at q=7,17,3329 agree:

    overlap1: none;
    overlap2: {44:180,48:170};
    overlap3: none;
    overlap4: {44:180};
    overlap5: {48:850}.

In the remaining one-six family a reduced second row has squared norm at
least ten. Its inner product with the first row has absolute value at most
three, so its squared perpendicular height is at least10-9/6=17/2. Sum the
counted complete kernels and the full previous one-six coefficient count
times this remainder kernel. Retain cutoff-36 tails and every periodic
layer, and compare with the previous complete one-six bound. The no-six
family and all other covers remain in place. This local refinement is not
yet formalized in Lean and does not prove the complete adaptive BKZ claim.
