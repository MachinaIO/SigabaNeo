# Gram-determinant strata for eight-point rare short pairs

Refine Part 310's exact eight-point code counts using the integer Gram
determinant of the first norm-four row C and its independent norm-six/eight
row v. Put D=4||v||^2-<C,v>^2. The second squared Gram--Schmidt height for
this pair is D/4, rather than the worst-case height five or seven.

Each new coordinate of v is nonzero. At squared norm six or eight, at
least one of the four new coordinates has magnitude one. An old coordinate
of C has magnitude one and C vanishes at every new position; those two
coordinates give a two-by-two minor of magnitude one. Thus C,v generate
the saturated integer lattice in their real plane. The theta product
theta(4 alpha) theta((D/4) alpha) consequently bounds the plane sum by
iterated shifted Gaussian summation, without requiring that v be a
shortest reduced basis vector.

The fixed norm-four row and cutoff 40 still confine all short representatives
to this real plane. Retain the same long-vector tail and periodic terms.
The overlap-specific geometric lower heights remain available as well;
take their maximum with D/4.

The exact finite-field enumeration retains the same normalized code keys
as Part 310 and groups them by the integer Gram determinant:

| Squared norm of v | Old overlap | D | Code count |
|---|---|---|---|
| 6 | 2 | 20 | 16 |
| 6 | 2 | 24 | 14 |
| 6 | 3 | 24 | 42 |
| 8 | 1 | 28 | 12 |
| 8 | 1 | 31 | 48 |
| 8 | 2 | 32 | 13 |
| 8 | 3 | 28 | 12 |
| 8 | 3 | 31 | 48 |

All counts are exhaustively verified at q=3329; q=7 and q=17 provide
additional regressions. If a code had appeared in more than one group,
summing the group bounds would still be a safe overcount. Norm-eight
groups may include codes also counted by norm six; their bounds are used
only to cover the no-norm-six branch, so this also only overcounts.
The branch with neither independent norm six nor eight retains its
previous height-nine bound and full coefficient count.

This is a paper refinement with exact finite counting and outward interval
evaluation. It does not by itself prove the higher-size, selected-history,
or complete BKZ statements, and is not Lean formalized.

## Admission through component size fifteen

The full size-fifteen residual weighted log10 is -11.61856, about
2.407e-12. Adding it to the previously admitted components gives a
positive cumulant transfer through all size-fifteen classes below
2.750e-12. The main cumulant probe now explicitly checks this cap.

Retaining the reference/error allowance 9.131e-13, the sufficient remaining
condition becomes

    sum_(h=16)^24 L_h^* U_h + Pr(max_(i=15)^404 b_i>.280) <= 2.588e-13.

Here h denotes component size in the draw-14 moment calculation, while i
denotes the later selected draw. They are different indices. The budget
identity is (2.750+0.9131+0.2588)e-12=3.9219e-12<3.922e-12.
Since two unknown components of size at least sixteen cannot fit below
degree twenty-five, their transfer is still linear in their activities.
Only known coefficients through degree eight can mix with them, so
admitting size fifteen does not alter those linear coefficients.

The remaining condition is unproved. In particular, this admission is
not a complete draw-14 exit-probability bound, a proof for later selected
histories, or a full BKZ theorem. The current full-size-24 envelope remains
far above the required budget.
