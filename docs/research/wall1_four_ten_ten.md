# Norm-ten extension of a four-circuit on ten positions

The post-weighting size17/rank8/girth4 cover is dominated by its remaining
two-circuit term, specifically c=4, t=6, overlap3. The earlier cover counted
norm-eight witnesses individually, but bounded all other planes with second
squared Gram--Schmidt height nine.

Fix a balanced norm-four first row on C={0,1,2,3}. An independent row is
nonzero on all six new coordinates. At squared norm ten it can be a unit
row on ten positions or a coefficient-two row on seven positions; the
support-four coefficient-two shape cannot cover six new positions. The
script `scripts/wall1_four_ten_ten.py` enumerates all balanced integer rows,
so includes both admissible shapes. There is at least one unit new entry;
together with an old entry of the first row this gives a unit minor and
proves saturation of the integer plane.

Normalize the second row by its first new entry and modulo the first row,
then deduplicate planes for each prescribed overlap and Gram determinant.
Every possible proper old support is attained at a cancellation scalar
`-second[i]/first[i]`. Exact computations at q=7,17,3329 agree:

| Old overlap | Determinant | Plane witnesses |
|---|---|---|
| 1 | 36 | 45 |
| 1 | 39 | 270 |
| 2 | 40 | 46 |
| 3 | 36 | 45 |
| 3 | 39 | 270 |

Each determinant supplies squared height D/4. The existing norm-eight
cover, including any anchor exclusions and their separate addbacks, is
retained. Add the above norm-ten kernels without subtracting possible
overlap from other covers. In the remaining family, a Gauss-reduced second
row has squared norm at least twelve and inner product at most two with
the norm-four first row, giving projected squared length at least eleven.
Use the full previous coefficient count for this remainder. All cutoff-40
tails and periodic corrections are retained in every complete kernel, and
the old and refined upper bounds are compared by outward interval endpoints.

This improves a finite coefficient-family envelope; it is not a claim that
the size17 residual or the adaptive BKZ theorem is proved. No new Lean
formalization is provided here.
