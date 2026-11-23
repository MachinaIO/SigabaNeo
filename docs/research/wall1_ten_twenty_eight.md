# Ten-position determinant28 anchor

The remaining size17 rank8/girth4 term is dominated by c=4,t=6,a=2.
Within its one-norm-four bound, the norm-eight family dominates the
height-nine remainder. Logs: `/tmp/wall1_rank8_four.log` and
`/tmp/wall1_ten_parts.log`. This motivates an anchor cover of determinant28.

The norm-four and norm-eight rows cover ten positions, so their overlap
has size two. Determinant28 means dot product of absolute value two;
the shared coefficient ratios agree. After coordinate signs and permutation,
use a=(1,1,1,1,0,0,0,0,0,0), b=(1,1,0,0,1,1,1,1,1,1).
The shared, first-exclusive and second-exclusive groups have sizes2,2,6.
Exclusive columns give a unit minor, establishing primitivity.

Let S1,S2,S3 be the group sums. For every integer v its squared distance
to the plane is

    sum over groups G of [sum over i<j in G (vi-vj)^2/|G|]
       +(3S1-3S2-S3)^2/42.

If a group is nonconstant, its variance contribution is at least1/2
for the two-position groups and5/6 for the six-position group. If all
are constant, the last term is (6/7) times an integer square. Thus every
positive squared distance is at least1/2. This proves the all-integer
bound; all59049 ternary vectors independently check the identity.

The Gram matrix is [[4,2],[2,8]], with squared heights4,7. Fundamental
triangles have squared sides4,8,8, hence squared circumradius16/7.
When additional norm-four relations are absent, nearest-plane rounding
and the affine even-norm condition give third squared height at least
6-16/7=26/7. Also retain t+1/2 for t new coordinates. Additional norm-four
relations are covered by the existing rare-line split before applying
the restricted bound. Third-code tails use cutoff25 because28*25^4<3329^2;
all periodic layers and anchor tails remain.

Counting uses the original balanced affine signs, not the isometric
all-positive representative. For each first balanced four-line, two old
pairs have matching signs and contribute15 second lines each; four old
pairs have opposite signs and contribute20 each. Thus there are
3*(2*15+4*20)=330 witnesses per first support and69300 per ten-position
set. Enumeration verifies this count and the unit minors. An initial
count omitting opposite-sign pairs was rejected by this check and is
not used in the final evaluation.

Use the complete girth-four extension cover at size10, rank8 and69300
witnesses, with the new projection and covering-radius constants. Only
the determinant28 entries at union10 are excluded from the exact table;
the new cover and all previous removed families are added back. The
diagnostic reconstruction includes the new candidate and checks overlap
with the interval selected by the production path. All other families,
including determinant32, remain covered.

This is not a completed BKZ proof and is not Lean formalized.

The corrected complete probe passes2106 cumulant regressions. Transfer
through sixteen remains below9.583e-13 (about8.78530122974e-13). Size17's
weighted residual log10 is5.9511534546. Crucially, rank8/girth4 stays at
5.5983265652: the new complete candidate does not beat the old one for
that target stratum. The small aggregate gain comes from other strata;
it must not be reported as closing the targeted obstruction. At rank8,
the ten-position anchor has the full rank already, so its same-rank
extension bound must be sharpened before this cover can help there.
Through24 remains about1.61354e232 and the2.0505e-12 allocation remains
unproved. Logs: `/tmp/wall1_ten_twenty_eight.log` and
`/tmp/wall1_ten_twenty_eight_cumulants.log`.
