# Weighted seven-position determinant27 kernel

The rank8/girth3 residual after Part370 is led by t4/overlap2. Within its
no-four split, the two-six family dominates: the one-six bound is roughly
10^-28 of that kernel, and the no-six bound roughly10^-78.

The existing seven-position classification supplies a norm-six row a on
C, of shape(2,-1,-1), and an independent norm-six row b nonzero on all four
new positions. For determinant27, |dot(a,b)|=3. The row b must have unit
entries on four new and two old positions; a support-three norm-six row
cannot cover the new positions. One shared old entry is the coefficient-two
position of a, and the other is one of its unit positions. Their signs
must make the two contributions to the inner product agree.

Give the coefficient-two old position weight1/8, the other two old
positions weight23/16 each, and the four new positions weight1 each.
The weight sum is7. In metric diag(1/w), the squared GS lengths are

    768/23, 100/23,

and their product times the coordinate-weight product is75/2>27.
The second row can have either inner-product sign. A unit old coefficient
of a and any new unit coefficient of b give a unit minor, so these rows
form an integer basis in their rational plane. The exact script checks
all36 balanced witnesses and both inner-product signs.

Use prefactor ((1/8)(23/16)^2)^(-1/2), these weighted theta lengths, and
scale16/23 for the existing cutoff36 tail and periodic-coordinate terms.
Indeed the weighted quadratic form is at least16/23 of the unweighted
form. The unweighted lifting cutoff and the Markov exponential remain
valid, since the weights sum to7. Only determinant27 in the c3, union7
exact two-six cover receives this kernel, and only when the full weighted
bound is smaller. Counts and the other determinants32,35,36 are retained.

This is a paper-level strengthening with exact arithmetic verification.
It does not close the size17..24 residual, adaptive BKZ distribution bridge,
or their Lean formalization.
