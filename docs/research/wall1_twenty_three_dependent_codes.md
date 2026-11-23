# Girth-filtered determinant23 dependent extension

The size16 rank7/girth4 diagnostic after Part322 is dominated by the
same-rank determinant23 anchor extension. The anchor has nine positions
and rank7. Retaining one dependent outside point gives a rank-three
relation code on ten positions. Refine its additional norm-four branch.

Use balanced rows

    a=(1,1,-1,-1,0,0,0,0,0,0),
    b=(1,0,0,0,1,1,-1,-1,-1,0).

Every eligible anchor has this form up to permutations and whole-row
signs: the single common entry is made positive; the exclusive groups
then have respectively one positive/two negative and two positive/three
negative entries. No individual-coordinate sign change is used in this
affine classification.

Enumerate the252 balanced norm-four lines v nonzero on the last position.
For x=<a,v>, y=<b,v>, the three-row Gram determinant is

    D=92-6x^2+2xy-4y^2.

For every candidate check all120 complementary seven-column supports.
Girth at least four is equivalent to each such complement having rank
three. This equivalence follows by testing whether a nonzero row
combination can be supported on the other three positions. Every
three-column minor has absolute value below seven, so this is the same
rank test over Q and every prime field q>=7. A unit minor exists for
every candidate and makes the integer row lattice primitive.

The surviving witness counts are:

    D:      56  60  66  68  74  76  80  84  86  88  92
    count:  18  26  25  24  23  11   7  14  42  41   9

All determinant38 and40 candidates fail girth four. Some candidates
of determinants80,84,86 also fail. The surviving third squared heights
are D/23, at least56/23. Witnesses are not asserted to be distinct codes;
any duplication is retained as harmless overcounting.

Replace the generic exceptional term252*J by the displayed weighted
sum of J_D, where J_D retains the old squared heights4 and23/4 and uses
third squared height D/23. The unit-minor primitive basis justifies this
height for the full integer plane containing the short representatives.
Keep the cutoff26, full long tail, all modular layers, the nonexceptional
coefficient bound and all completion factors. This changes only the
one-point dependent branch; other crossings and parallel alternatives
retain their bounds. Take the minimum with the old complete cover.

The finite classification uses exact integer arithmetic and all supports.
It supplements the existing analytic Gaussian argument; it is not a
Lean theorem or a completed proof of the adaptive BKZ history law.

## Verified outcome

The exact classification and complete cumulant probe pass, including
2106 transfer and connected-support regressions. Transfer through
fifteen remains below the retained cap5.295e-13. The sufficient remaining
allocation2.4793e-12 is unchanged and remains unproved.

Size16's full weighted residual log10 is -3.0908897720. The rank7/girth4
stratum is now -5.3286127922; the leading strata are rank4/girth4 at
-3.3751772138 and rank8/girth4 at -3.4179345089. The through24 bound is
still about3.34e232, so neither the complete residual condition nor the
adaptive selected-history law is established. These are positive upper
envelopes, not estimates or lower bounds on actual failure probability.
