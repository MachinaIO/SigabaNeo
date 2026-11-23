# Girth-seven short-plane geometry

In the existing saturated short-plane argument, girth seven and the affine
condition imply that each nonzero short integer row has even squared norm
at least eight. Every norm-eight row has eight unit entries: the alternative
integer shape has support five and is excluded.

Suppose two independent norm-eight rows span a code with full support H.
Their shared support has size16-H, and each exclusive group has size H-8.
The shared coefficients have ratios +1 or -1. If their inner product is d,
the two shared ratio groups have sizes (16-H+d)/2 and (16-H-d)/2.
Cancelling either group produces a codeword, so each group has at most
H-7 elements. Consequently

    |d| <= 3H-30.

For H<=9 this is impossible. For H=10 it forces d=0, giving second
squared height8. For H=11 it gives |d|<=3, giving second squared height
at least (64-9)/8=55/8. This argument only uses girth and integer shapes;
the finite enumeration is an independent check, not its justification.

If the first reduced minimum is eight and the second at least ten,
Gauss reduction gives |d|<=4, so the second squared height is at least
10-16/8=8. If the first minimum is at least ten, the usual reduced-basis
bound gives heights10 and15/2. Thus for c=7,H<=11 use the sum of the
Nth powers of two complete envelopes with short products

    theta(8 alpha) theta(h alpha),
    theta(10 alpha) theta((15/2) alpha),

where h=55/8 for H=11 and h=8 otherwise. Short-span dimensions zero
and one are covered by these products as well. Retain the old cutoff14
tail, all periodic layers, and the full coefficient count. Take the
minimum with the old bound; no family is removed.

`wall1_eight_eight_eleven.py` checks all3254 eligible partner candidates
on8..11 positions. Accepted determinant counts are empty at8 and9,
{64:288} at10, and {55:624,63:1184} at11. Its existing1960 girth-eight
checks also pass. This is not a Lean formalization or a complete BKZ proof.

The full interval calculation passes all2106 cumulant regressions. Transfer
through sixteen remains below9.583e-13 (about8.78532709167e-13). Size17's
weighted residual log10 is6.5674552429, with rank9/girth4 now the largest
stratum at6.2768968929. The through24 envelope remains about1.61354e232.
Thus the targeted girth-seven term is no longer dominant, but the
sizes17..24 plus later-history allocation2.0505e-12 is still unproved.
Logs are `/tmp/wall1_girth_seven.log` and
`/tmp/wall1_girth_seven_cumulants.log`. These upper envelopes are not
actual failure probabilities. Adaptive selected-history, projected-block,
and full BKZ obligations remain open.
