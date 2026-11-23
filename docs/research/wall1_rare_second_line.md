# Rare second short lines beside a fixed norm-four circuit

Consider c=4 and t>=4 in the existing two-circuit cover. Part 295 implies
that any norm-four line is the first circuit itself; there are three
balanced choices for that line. Instead of using one worst-case second
height for every coefficient pair, split according to independent short
representatives of squared norms six and eight.

Under girth four, a norm-six affine row is balanced on six positions,
giving K6=10 choose(H,6) projective integer lines. A norm-eight affine row
is either balanced +/-1 on eight positions, or has one entry of magnitude
two and four of magnitude one. In the latter case choose the magnitude-two
entry positive to fix projective sign; one of the four others is positive
and three are negative. Thus

    K8 = 35 choose(H,8) + 20 choose(H,5).

The remaining norm-eight possibility has two entries of magnitude two
and is excluded by girth. Odd squared norms cannot occur for affine
integer rows of sum zero.

Fix the first balanced circuit and one independent short line. Their span
determines the entire code. A prescribed second circuit misses at least
one old position; vanishing at that position determines its projective
direction uniquely, since the first circuit is nonzero there. Hence the
number of normalized coefficient pairs with an independent norm-six line
is at most 3*K6, and similarly at most 3*K8 for norm eight. Cap these by
the existing count for first-circuit norm-four pairs. External support
makes the norm-six count zero for t>=6 and norm-eight count zero for t>=8.

Split into (i) codes with an independent norm-six line, (ii) those with
norm eight but no independent norm six, and (iii) neither. With a
Gauss-reduced first vector of squared norm four, the second squared
minimum is at least 6, 8, or 10. Its squared perpendicular height is
therefore at least 5, 7, or 9. Take the maximum with Part 298's support,
parity, and overlap-specific height in each case.

For each class retain the same cutoff 40, long-vector tail, and positive
periodic expansion as the previous one-norm-four bound. The first two
Gaussian powers receive the rare coefficient-count weights; the last
receives the full first-norm-four count. This positive overcount covers
all eligible coefficient pairs. Take its minimum with the previous bound
and with the separate first-ball/new-group alternative.

Exact enumeration verifies 14,465 short-line cases in dimensions four
through ten and 175 prescribed-support uniqueness cases. The all-dimension
counts and uniqueness proof are above; finite checks are regressions.

The full size-fifteen residual weighted log10 decreases from 1.40187 to
-3.28929 (about 5.14e-4). This is approximately a 49,000-fold improvement,
but remains over eight orders of magnitude above the entire residual
budget. The triangular extension and girth-six terms now dominate.
Full cumulant regressions preserve the admitted bound through fourteen.
Sizes 15..24 and selected histories still need proof; this is not a
complete BKZ proof or a Lean formalization.
