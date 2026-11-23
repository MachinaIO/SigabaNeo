# Shared seven-point anchor: the four-new-position norm-six split

This targets the addback actually selected for size 17, rank 8, girth 4.
In the Part 390 snapshot the selected cover is D28-ten. Its other-two-four
addback has weighted log10 -9.80196347695; its remaining non-anchor part has
log10 -10.45171972594. These are upper-envelope values.

The diagnostic `wall1_rank_eight_other_anchor_diagnostic.py` decomposes that
addback. Relative to the whole other-two-four addback, the orthogonal
six-position anchor's large-crossing part is 10^-14.57822 and both
small-crossing parts are smaller still. The shared seven-position anchor's
large-crossing part is decisive. Its t=4 contribution accounts for about
99.84% of the addback; t=3 has relative log10 -2.79821379189. This identifies
t=4, rather than the raw two-relation remainder, as the target below.

## Uniform geometry and complete short-vector classification

After permuting positions within the supports and independently negating the
two balanced rows to put +1 at their shared coordinate, every shared anchor
has the representative

    a = (1,1,-1,-1,0,0,0; 0,0,0,0),
    b = (1,0,0,0,1,-1,-1; 0,0,0,0).

This transformation preserves affine balance. The old Gram matrix is
[[4,1],[1,4]], of determinant 15, with squared GS lengths 4 and 15/4.
The semicolon separates four new positions. A crossing direction outside
the old plane is nonzero on all four new positions and has a nonzero old
projection. The latter is the existing `code_ball_bound` premise: its old
coefficient vector is supported on an independent anchor basis and is
nonzero. A nonzero vector supported there cannot belong to the old relation
plane. This premise is essential; a disjoint new-only four-circuit is not
covered by the crossing argument.

A balanced norm-six integer vector with these four new coordinates nonzero
must be a unit vector on six positions. The other balanced norm-six shape,
(2,-1,-1), has only three positions. Thus precisely two old coordinates are
nonzero, and there are

    binomial(7,2) * (binomial(6,3)/2) = 210

possible norm-six lines. For each line c, put x=<a,c> and y=<b,c>. The
three-row determinant is

    D = 90 - 4x^2 + 2xy - 4y^2.

Exact enumeration gives the witness counts

| D | Number of lines |
| --- | ---: |
| 74 | 64 |
| 80 | 46 |
| 84 | 44 |
| 86 | 28 |
| 90 | 28 |

These are witness upper counts, not distinct coefficient-chart counts. Each
line fixes at most one normalized crossing code relative to a fixed anchor
basis. Multiple witnesses for the same code cause only overcounting.
An a-only old coordinate, a b-only old coordinate, and any new coordinate
have a 3x3 minor of magnitude one. Thus a,b,c are a saturated basis of the
integer lattice in their real span, and the exact third squared GS length
is D/15. In particular its minimum is 74/15, improving the previous generic
23/5 = 69/15.

## The complement with no new norm-six line

The old shared plane has covering radius squared 8/5, as used in the
existing no-new-four argument. For any integer vector outside the old plane,
subtract a nearest vector of the old integer plane. This preserves its new
coordinates, affine balance, and its component perpendicular to the old
plane, while leaving an old-plane component of squared norm at most 8/5.

If the squared perpendicular norm were less than 32/5, the resulting
nonzero balanced integer row would have squared norm less than 8. Balanced
integer squared norms are even. All four new coordinates are nonzero, and
the old projection is nonzero, so a norm-four row is impossible. A norm-six
row is excluded in the complement. Hence the third squared GS length in
this complement is at least 32/5.

This argument excludes only new rows outside the old plane. It does not
exclude the original norm-four lines of the anchor. Modular short rows are
integer balanced rows because their coordinate sum is a multiple of q with
absolute value less than q. The existing cutoff/lifting inequalities are
unchanged.

## Complete-kernel bound and integration point

Let J(h) be the existing rank-three complete ball bound with size 11, rank 8,
GS squared lengths (4,15/4,h), cutoff 29, and all tail/periodic terms intact.
In particular `15*29^4 < 3329^2`. The new module implements J directly with
the same beta, prefactor, Markov factor, and q normalizer as
`wall1_orthogonal_third_code.code_ball_bound`.

For C crossing coefficient choices, a valid complete replacement is

    64 J(74/15) + 46 J(80/15) + 44 J(84/15)
      + 28 J(86/15) + 28 J(6) + C J(32/5).

Take its minimum with the prior complete coefficient-weighted bound. It
covers both the norm-six family and its entire complement; no family is
removed without an addback. The function
`wall1_shared_four_new_six.refined_bound(s, C, old)` returns that minimum and
the two split parts. It applies to the shared size-seven, t=4 branch in
`other_envelopes` after its existing `weighted_joint` calculation. It also
applies at other whole-support ranks for the same local crossing geometry;
this note's quantitative diagnosis is specifically rank 8.

## Validation and scope

The 210 exact rational determinant checks pass. The complete-kernel
calculation gives

    log10(new t=4 bound / old t=4 bound) = -30.71976253679...,
    log10(new whole rank-8 other-two-four addback / old) = -2.798213791888....

The rare-six part exceeds its complement by about 6.4265 decimal orders.
After this change t=3 controls that addback. The non-anchor remainder of the
selected rank-8 cover remains a larger obstacle; one must not report a
30-order improvement of the full rank-8 or size-17 bound.

Reproduce:

    python3 docs/research/scripts/wall1_shared_four_new_six.py
    python3 docs/research/scripts/wall1_rank_eight_other_anchor_diagnostic.py

Observed diagnostic log:
`/tmp/wall1_rank_eight_other_anchor_diagnostic.log`.
Only new research scripts and this note were created by this worker. Parent
integration, full regression, and the global BKZ proof remain separate.
