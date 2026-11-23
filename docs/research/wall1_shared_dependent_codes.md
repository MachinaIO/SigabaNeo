# Girth filtering for a shared anchor's dependent extension

The size16 rank5 diagnostic after Part 317 is dominated by the same-rank
seven-position shared anchor. Part 315 splits its one-point dependent
extension into codes having an additional norm-four line and codes with
no such line. The latter already have third squared height at least 22/5.
This note refines the former using the existing girth-four requirement.

After row signs and coordinate permutations, the balanced anchor rows are

    a=(1,1,-1,-1,0,0,0,0), b=(1,0,0,0,1,-1,-1,0).

These operations preserve the affine condition. Every balanced shared
anchor has this form: make the common entry positive in each row, then
each exclusive triple contains one positive and two negative entries.

Enumerate the 105 balanced norm-four lines v nonzero on the eighth
coordinate. For x=<a,v>, y=<b,v>, the three-row Gram determinant is

    D = 60-4x^2+2xy-4y^2.

The exact witness counts before and after imposing girth four are:

| D | All witnesses | Girth-four witnesses |
| --- | ---: | ---: |
| 24 | 2 | 0 |
| 26 | 6 | 0 |
| 36 | 24 | 24 |
| 44 | 28 | 28 |
| 50 | 4 | 0 |
| 54 | 8 | 0 |
| 56 | 28 | 24 |
| 60 | 5 | 5 |

For a three-row generator matrix, a nonzero codeword supported on at most
three coordinates exists exactly when some complementary five-column
matrix has rank less than three. For every witness, the enumerator checks
all 56 complementary supports and all their three-column minors. It also
checks that every minor has absolute value less than seven and at least
one minor is a unit. Thus the rank test is identical over the rationals
and every prime field q>=7, in particular q=3329. This is a complete finite
enumeration, not a random test or an assumption on typical codes.

The unit minor makes a,b,v a primitive integer basis of its real plane.
After the old Gram--Schmidt squared lengths 4 and 15/4, the third squared
length is exactly D/15. All surviving witnesses therefore have height
at least 12/5. The cutoff argument in the existing fixed-plane bound
keeps every short lift in this plane. Its integer lattice is generated
by a,b,v, so the corresponding three theta factors give the short bound.
The full long tail and periodic aliases are unchanged.

Replace the exceptional term 105*J_generic by

    24*J_36 + 28*J_44 + 24*J_56 + 5*J_60,

where J_D uses third squared height D/15. A witness determines at most
one normalized fundamental relation for the fixed independent anchor
basis. Different witnesses may define the same code; retaining them
only overcounts. The nonexceptional term Q*J_no4 is unchanged. Apply this
only to the shared anchor with one new dependent point; other crossing
and parallel alternatives remain as before.

The proof uses finite exact counting and the previously established
Gaussian envelope; it is not a Lean formalization. Larger components
and the adaptive selected-history estimates still need proof.

## Outcome

The full cumulant probe passes its 2106 exact regressions. Transfer
through fifteen is about 5.294539486477022e-13 from above, hence below
the new checked cap 5.295e-13. Together with the reference/error cap
9.131e-13, the sufficient remaining condition is now

    sum_(h=16)^24 L_h^* U_h + Pr(max_(i=15)^404 b_i>.280) <= 2.4793e-12.

The allocation sums exactly to 3.9219e-12<3.922e-12. The residual
condition remains unproved. Size16's full weighted envelope has log10
0.0411928902; its rank5/girth4 part is now -1.9660001176, while rank8/girth4
dominates at 0.0234528635. The through24 bound remains about 3.97e236.
These are upper envelopes, not probability lower bounds. The refinement
does not establish a complete draw14 exit probability or the BKZ theorem.
