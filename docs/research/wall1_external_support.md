# External support excludes short independent directions

Let C and D be circuit rows over a field. Suppose C has c nonzero
positions, D meets exactly a of them with 1 <= a < c, and D has t
additional nonzero positions. Every projective direction in their span
other than C has a representative D + lambda C.

All t additional positions remain nonzero. At least one old position also
remains nonzero: if lambda = 0, use an intersection position; otherwise
use a position of C outside D. Consequently every such direction has
Hamming weight at least t + 1. For t >= 4, it cannot be the reduction of
an integer vector of squared norm four, since such a vector has at most
four nonzero coordinates.

The two-relation envelope now omits the independent norm-four candidate
count when t >= 4. For c = 4 it retains the candidates on the first
circuit line. The no-short contribution, long-vector tails, periodic
terms, and other strata are retained.

`wall1_external_support.py` checks 74,112 coefficient pairs and 369,792
independent directions over fields of sizes three and five. These are
regression checks; the argument above applies to any field.

This improves a candidate count but does not improve the reported full
size-fifteen envelope at the displayed precision: its weighted logarithm
remains about 7.654. Complete admitted coverage remains through size
fourteen. The size 15..24 residual and later selected-history probability
are still unbounded at the required budget. This is not a complete BKZ
proof or a Lean formalization of this support argument.
