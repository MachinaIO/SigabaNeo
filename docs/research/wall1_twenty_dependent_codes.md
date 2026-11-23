# Girth filtering for determinant-twenty dependent extensions

Part319 leaves a rank6,girth4 contribution at size16. The relevant
determinant20 anchor has eight positions and rank6; retaining one
dependent outside point gives a three-row code on nine positions.
Refine Part316's additional norm-four branch by imposing girth four.

## Both balanced anchor types

Let a=(1,1,-1,-1,0,0,0,0,0). After choosing row signs so the dot product
is two, the two overlapping coordinates of b have the same signs as a.
Those two signs may be equal or opposite. Permutations within the common
and exclusive coordinate groups, and simultaneous sign reversal, reduce
the balanced possibilities to

    b_same=(1,1,0,0,1,-1,-1,-1,0),
    b_mixed=(1,0,-1,0,1,1,-1,-1,0).

Both cases must be checked: arbitrary coordinate sign changes would
preserve lengths but would not preserve the affine sum condition used
in the norm-four enumeration.

For each representative enumerate all168 balanced norm-four lines v
nonzero on coordinate nine. Write x=<a,v>, y=<b,v>. The Gram determinant is

    D=80-6x^2+4xy-4y^2.

Test every complementary six-coordinate support for rank three. A
failure means the relation code contains a nonzero vector on at most
three coordinates and is forbidden by girth four. All three-column
minors have absolute value below seven, so this is the exact same rank
test over Q and every prime field q>=7. A unit minor also occurs in
every case, establishing a primitive three-row integer basis.

| D | Same-sign overlap | Mixed-sign overlap | Uniform upper count |
| --- | ---: | ---: | ---: |
| 44 | 9 | 12 | 12 |
| 50 | 24 | 20 | 24 |
| 56 | 32 | 24 | 32 |
| 60 | 2 | 8 | 8 |
| 64 | 12 | 12 | 12 |
| 66 | 12 | 20 | 20 |
| 74 | 36 | 32 | 36 |
| 76 | 25 | 16 | 25 |
| 80 | 4 | 12 | 12 |

In particular, all determinant34 candidates fail girth four. The
remaining third squared heights are D/20, at least11/5. For every
anchor use the coordinatewise maximum of the two witness-count columns.
These maxima sum to181, exceeding168, which is harmless: this is an
upper bound per Gram stratum, not a claimed exact number of codes.

## Connection to the full envelope

Let J_D be the complete fixed-plane Gaussian bound with old squared
heights4 and5 and third squared height D/20. The cutoff, long tail and
periodic layers remain unchanged. Replace the generic exceptional
term168*J by the sum of the uniform stratum counts times J_D, and retain
the existing Q*J_no4 bound for the nonexceptional coefficient choices.
Take the minimum with the old unpartitioned cover. This replacement is
used only for the one-point dependent branch of the determinant20
anchor; all other crossings and alternatives remain as before.

A short witness fixes at most one normalized fundamental relation for
the independent old basis. Multiple witnesses for a code overcount and
do not invalidate the upper bound. A unit minor makes the short rows
the full integer basis of their plane, so D/20 is its actual third
Gram--Schmidt squared length. The finite enumeration covers336 lines
and84 complementary supports per line, with exact integer arithmetic.

This strengthens a component envelope. It is not a Lean proof, a proof
of the full residual budget, or a proof of adaptive BKZ selected histories.

## Verified outcome

The complete cumulant evaluation passes2106 exact regressions. Transfer
through fifteen remains below5.295e-13 (about5.2945316774e-13), so the
sufficient remaining allocation stays2.4793e-12. The size16 full weighted
residual log10 becomes -1.7612915378. Its leading strata are now
rank5/girth4 at -1.9660001176, rank8/girth3 at -2.5148446833, and
rank7/girth4 at -2.5826350936. The previously dominant rank6/girth4 term
is no longer among the largest five. The rank5 term still contains the
triangular-anchor extension, which has not yet received the same
short-line/girth refinement.

The residual envelope is still far above the allocated budget, and the
through24 envelope remains about1.71e233. These positive upper bounds
do not establish either large actual failure probability or the required
small failure probability. The selected-history and full BKZ obligations
remain open.
