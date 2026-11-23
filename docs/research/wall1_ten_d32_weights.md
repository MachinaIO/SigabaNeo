# Weighted ten-position determinant-32 kernel

Let a be a balanced unit norm-four row on the first four positions, and b
an independent balanced norm-eight row nonzero on all six new positions.
Every non-unit balanced norm-eight shape has support at most five, so b must be unit
on eight positions, sharing exactly two positions with a. Determinant32
means their ordinary inner product is zero.

Give the two shared positions weight5/8, the two old-exclusive positions
weight1, and the six new positions weight9/8. Their sum is10. In the metric
diag(1/w), the rows remain orthogonal, with squared lengths26/5 and128/15.
The product of the coordinate weights and Gram determinant is

    (5/8)^2 (9/8)^6 (26/5) (128/15) = 2302911/65536 > 32.

An old-exclusive coordinate and any new coordinate form a unit minor, so
the two rows form a basis for the integer lattice in their rational plane.
The exact script `scripts/wall1_ten_d32_weights.py` checks all300 balanced
witnesses. This enumeration checks the identities; the support argument
above explains why the enumeration includes every relevant shape.

The complete Poisson kernel uses prefactor ((5/8)^2 (9/8)^6)^(-1/2) and
the theta product at the two weighted squared lengths. The total weight
preserves the exponential Markov factor for ten balls. Since max(w)=9/8,
the weighted quadratic form is at least8/9 times the unweighted form.
Thus the existing cutoff-40 complementary tail and periodic-coordinate
corrections remain valid after scaling their Gaussian parameters by8/9.
The short-plane lifting cutoff itself is unchanged.

The implementation takes the smaller of the preceding complete kernel and
this complete kernel only for union10, determinant32. Both the norm-eight
split and the combined norm-eight/norm-ten split use it, as do diagnostics.
All coefficient counts, other determinant classes, and unclassified
remainders are retained. Weights may depend on the witness before the
union bound. This is a paper-level bound with exact arithmetic checks,
not a Lean formalization or a proof of the adaptive BKZ claim.
