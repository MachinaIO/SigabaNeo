# Six-circuit refinements on ten positions

The rank8/girth6 residual after Part376 is led by t4/overlap5, where the
one-six family dominates. Overlaps4 and2 follow, dominated by two-six
planes of determinant32. Both sources are refined here.

In girth six a norm-six row is unit on six positions, and a norm-eight
row is unit on eight positions; all non-unit balanced shapes have smaller
support. There are2100=10 choose(10,6) norm-six lines and1575=35 choose(10,8)
norm-eight lines up to sign. Hence at most3307500 witnesses cover a plane
containing both lengths. Independent short pairs stay independent modulo
3329, since some nonzero integer minor has absolute value less than7.
For prescribed circuit supports each pair determines at most one normalized
coefficient chart. This witness bound overcounts ineligible pairs.

Within the one-six family, retain the old complete GS kernel(6,13/2)
for this counted exception. Outside it the second squared norm is at least
10, so Gauss reduction gives height>=10-3^2/6=17/2. Use the counted kernel
plus the full one-count times the(6,17/2) kernel, minimized with the old
complete bound. Both kernels retain cutoff36 tails and periodic corrections.
No saturation claim for a counted six/eight pair is needed.

For two norm-six rows on ten positions, both rows are unit and their
supports share two coordinates. Determinant32 forces inner product+/-2.
Give the two shared coordinates weight11/12 and the eight exclusive ones
weight49/48. The sum is10. In metric diag(1/w), the squared GS lengths are
3288/539 and35712/6713. Their product times the weight product is

    4719878935541/146767085568 > 32.

Each row has exclusive unit coordinates, so a unit minor certifies the
integer-plane basis. The prescribed six-circuit is one of these row
supports: the projective groups have sizes4,4,2, and only cancelling a
size4 group leaves a six-support row. Thus the exact check fixing the
first row on C covers every determinant32 geometry up to interchanging
the two rows and coordinate permutations.

Use prefactor ((11/12)^2(49/48)^8)^(-1/2), the weighted theta lengths,
and scale48/49 in the original cutoff36 tail and periodic corrections.
This bounds the complementary tail because max(w)=49/48. Take the minimum
with the preceding complete determinant32 kernel. Determinant36, the
no-six family, and all coefficient counts remain unchanged.

The script verifies the2100 and1575 line counts and780 exact weighted
Gram/unit-minor checks. The proof is paper-level with exact arithmetic
checks; the full residual budget, adaptive BKZ bridge and Lean work remain
open.
