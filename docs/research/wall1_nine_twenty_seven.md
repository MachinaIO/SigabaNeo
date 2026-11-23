# Nine-position determinant27 anchor at girth six

The size17 rank8/girth6 diagnostic is dominated by c=6,t=3,a=3.
Its two-norm-six part dominates the one-six and no-six parts. The exact
nine-position table splits it into determinants27 and35; this refinement
covers the determinant27 family by an additional third relation.

Two norm-six rows at girth six have unit entries on six positions each.
If their union has nine positions, their shared and two exclusive groups
each have size three. Determinant27 means inner product of absolute
value three, so the coefficients have a constant relative sign on the
shared group. After coordinate signs, permutation and a row sign, use

    a=(1,1,1,1,1,1,0,0,0),
    b=(1,1,1,0,0,0,1,1,1).

An exclusive-coordinate minor is a unit, so the pair spans its primitive
integer plane. Write S1,S2,S3 for the sums in the three groups. For every
integer vector v, its squared projected length is

    sum over groups G of [sum over i<j in G (vi-vj)^2/3]
      +(S1-S2-S3)^2/9.

If any group is nonconstant, its within-group contribution is at least2/3.
Otherwise Si=3ki, and the last contribution is an integer square. Thus
every nonzero projected length squared is at least2/3. The formula and
minimum are cross-checked on all19683 vectors in {-1,0,1}^9, while the
argument proves the bound for all integer vectors.

The Gram matrix is [[6,3],[3,6]], with squared basis heights6,9/2.
The fundamental parallelogram splits into equilateral triangles of
squared side6 and squared circumradius2. Round a third relation in the
old plane using this covering radius. If its projected squared length
were below4, the rounded integer representative would have squared norm
below6. Its modular affine equation lifts to the integer affine equation
since q^2>6H. Girth six forbids such a nonzero independent relation.
Consequently, with t new positions, the third height is at least
max(t+2/3,4). Signed coordinates do not affect this argument: the affine
normal after the isometry still has squared norm H.

Enumerating the original balanced affine rows gives560 witness pairs per
fixed first six-support, each with a unit minor. Therefore47040 witnesses
cover all placements on a fixed nine-position set. This may overcount
planes, which is safe. Use size9, rank7 and this witness bound in the
complete extension cover. Girth-six coefficients start at old support5
for a dependent point, max(1,6-t) for a crossing, and4 for a marked pair.
Retain the existing crossing divisor, parallel covers and no-coloop case.

Third-code tails use cutoff25, with27*25^4<3329^2; anchor tails use cutoff40.
All periodic layers remain. Only the determinant27 entries in the exact
c=6,H=9 table are removed under an explicit exclusion flag, and the
complete anchor cover is added back before taking the minimum with the
previous bound. Determinant35 and all other families remain present.

This is not a complete BKZ proof and is not Lean formalized.

The complete interval run passes2106 cumulant regressions. Transfer through
sixteen remains below9.583e-13 (about8.78530122993e-13). Size17's weighted
residual log10 is5.9627712508, now led by rank8/girth4 and rank8/girth3;
rank8/girth6 is no longer among the five largest strata. Through24 remains
about1.61354e232. The remaining2.0505e-12 allocation and adaptive projected
BKZ bridge are still open. Logs: `/tmp/wall1_nine_twenty_seven.log` and
`/tmp/wall1_nine_twenty_seven_cumulants.log`. These envelopes do not estimate
the actual failure probability.
