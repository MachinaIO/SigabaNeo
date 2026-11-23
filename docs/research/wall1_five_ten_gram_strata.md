# Five- and ten-position rare-plane counts

This refines the one-norm-four part of the existing two-relation envelope.
The two-norm-four and no-norm-four parts are unchanged. Counts below are
for a fixed prescribed overlap, not a sum over choices of positions.

For a first three-circuit and five-position union, enumerate all balanced
norm-four lines and all affine integer rows of squared norm six or eight.
Include the support-three shape (2,-1,-1). Require the first circuit to
have exactly the prescribed three-position support, and the second circuit
to have the prescribed old overlap and both new positions. Remove planes
containing two norm-four lines. Normalize the first circuit at coordinate
zero and eliminate that coordinate from the second row to deduplicate planes.

The resulting (Gram determinant, count) lists are:

| Prescribed overlap | Norm six | Norm eight |
| --- | --- | --- |
| 1 | (20,1) | empty |
| 2 | (20,1), (23,6), (24,6) | (23,6), (31,12) |

The six determinant-23 planes in the two columns are identical; count them
once. Every retained row pair has a unit minor, establishing primitivity.
The script `wall1_three_circuit_five_codes.py` checks these statements at
q=7,17,3329. Only the concrete q=3329 case is needed here.

For a first four-circuit and ten-position union, the unique norm-four line
is the first circuit: an independent row must cover all six new positions.
A norm-six row cannot also meet the old positions. A norm-eight row must
have eight unit entries, six new and two old. Its inner product with the
first row is zero or plus/minus two, so its determinant is32 or28. An
old-exclusive and a new position give a unit minor. Enumerating balanced
rows and deduplicating normalized planes gives:

| Prescribed overlap | (determinant, count) |
| --- | --- |
| 1 | empty |
| 2 | (28,55), (32,50) |
| 3 | (32,150) |

`wall1_four_six_seven.py:ten_point_counts` checks this at q=7,17,3329.
The production bound uses second squared height D/4 for each counted
plane and retains the full remaining one-four coefficient count at height9.
All previous cutoff tails and periodic layers remain. Thus the refinement
does not discard the planes whose second minimum exceeds eight.

The completed interval runs report transfer through sixteen of about
8.78532719193e-13, below the retained9.583e-13 cap. All2106 exact cumulant
regressions pass. Size17's weighted residual log10 falls from8.6275560787
to7.2102479362. Its leading stratum is now rank9/girth7, at7.0980790820.
The through24 envelope is still about1.61354e232. These ineffective upper
bounds are not actual failure-probability estimates.

Logs: `/tmp/wall1_five_ten_exact.log` and
`/tmp/wall1_five_ten_exact_cumulants.log`.
The remaining sizes17..24 and later-history allocation of2.0505e-12 is
unproved. This is computer-assisted component analysis, not a completed
BKZ proof or a Lean formalization.
