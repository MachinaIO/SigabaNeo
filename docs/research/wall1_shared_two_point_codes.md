# Two-point extensions of the shared four/four anchor

The size17 rank6/girth4 selected-cover diagnostic shows that the
remaining two-relation term is negligible. The dominant contribution
is the shared seven-position two-four anchor's small crossing. The
orthogonal anchor's contributions are about40 decimal orders smaller
within this particular sum. Logs: `/tmp/wall1_rank6_cover.log` and
`/tmp/wall1_rank6_other.log`.

Use affine representatives on nine positions

    a=(1,1,-1,-1,0,0,0,0,0),
    b=(1,0,0,0,1,-1,-1,0,0).

The last two positions are new. The shared coefficient can be made
positive in each row by row signs; each exclusive triple then has one
positive and two negative entries. Permutations cover every other
affine sign choice. Enumerate all63 balanced norm-four lines v nonzero
at both new positions: choose two of seven old positions and one of
three balanced sign patterns.

For x=<a,v>, y=<b,v>, the rank-three Gram determinant is

    D=60-4x^2+2xy-4y^2.

Exact counts are {44:20,50:14,54:13,56:8,60:8}. Every row triple has a
unit minor, establishing primitivity, and all minors have absolute value
below7. Every six-column complement has rank three, so no nonzero
codeword has support at most three. These84 complementary-column tests
per line verify girth four over Q and every prime field q>=7. No line
is excluded: the improvement is in the exact third heights, not in a
smaller total count.

The old Gram determinant is15, so each third squared height is D/15,
at least44/15. Replace the63-fold generic kernel at height13/5 by the
sum of complete kernels for these determinant strata. Retain the full
coefficient count times the no-new-norm-four kernel, and every cutoff29
tail and periodic layer. This covers both the crossing and marked-pair
production paths; the minimum with the old complete bound remains.

This is not a Lean formalization or a full adaptive BKZ proof.

The complete interval run passes2106 cumulant regressions. Transfer through
sixteen is about3.45843824783e-13; the asserted admitted-component cap is
now3.459e-13. Together with the unchanged baseline/error cap9.131e-13,
the remaining sufficient allowance is2.6629e-12 for sizes17..24 plus the
later-history event, because

    (0.3459+0.9131+2.6629)e-12=3.9219e-12<3.922e-12.

This replaces the old2.0505e-12 allocation; it does not prove that the
remaining families fit the new budget. Size17's weighted residual log10
is4.1859947994, now led by rank8/girth3; rank6/girth4 is no longer among
the five largest strata. Through24 remains about1.05489e232, an ineffective
upper envelope rather than an actual failure probability. Logs:
`/tmp/wall1_shared_two_point.log` and
`/tmp/wall1_shared_two_point_cumulants.log`.
