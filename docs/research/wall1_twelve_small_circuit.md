# Twelve-position short reduced pairs

Consider a full-support rank-two affine integer relation lattice on twelve
positions, of girth c=4 or c=6, with the prescribed second circuit crossing
a proper nonempty subset of the first circuit. Suppose its minimum squared
length is at least eight. A Gauss-reduced basis has squared lengths A<=B
and inner product d satisfying 2|d|<=A.

Every balanced integer row of squared length eight and support at least four
is, up to permutation and overall sign, either four +1 and four -1, or
(2,1,-1,-1,-1). For squared length ten the shapes are five +1 and five -1,
(2,1,1,-1,-1,-1,-1), and (2,-2,1,-1). These lists follow by partitioning
the squared norm into squares and imposing zero coordinate sum.

For two independent rows a,b covering all twelve positions, group coordinate
pairs (a_i,b_i) by rational projective direction. The nonzero row-space
supports are exactly twelve minus the group sizes, together with twelve.
Consequently a necessary condition is that these supports have minimum c,
contain c, and contain some integer in [13-c,11]. The last condition is the
proper crossing requirement; it excludes, in particular, disjoint support-eight
and support-four rows, which would otherwise invalidate an exclusion claim.

The exhaustive integer check `scripts/wall1_twelve_small_circuit.py` fixes
each first-row shape and enumerates every balanced second row, imposing full
support and Gauss reduction. No (A,B)=(8,8) or (8,10) pair passes these
necessary conditions. Every eligible (10,10) pair has 100-d^2>=84.
Permutation and overall sign symmetry justify fixing the first-row shapes.
For these small coefficients distinct rational projective directions remain
distinct modulo q=3329 (their nonzero two-by-two determinants have absolute
value at most eight). Thus the support test also applies to the short-plane
finite-field lift used in the existing bound.

The three exhaustive minimum-length cases therefore have squared
Gram--Schmidt lower bounds

* A=8: B>=12, hence (8,10);
* A=10: if B=10 use (10,42/5); if B>=12 the height is at least 19/2;
* A>=12: Gauss reduction gives (12,9).

The implementation sums the three complete kernel powers and takes the minimum
with the preceding bound. Cutoff-14 tails, periodic layers and coefficient
counts are retained. This is a computer-assisted local refinement, not a Lean
proof or a proof of the adaptive BKZ claim.

## Girth-five extension

For c=5 the previous exclusions are false. The same exhaustive check finds
eligible (8,8) determinants 60 and 63, and eligible (8,10) determinants
64,71,76,79,80. It finds no eligible (10,10) pair. The diagnostic counts
fix one representative of each first-row shape: they certify the possible
determinants, and are not used as counts of all coefficient planes.

Thus the exhaustive cases now give (8,15/2), (10,19/2), and (12,9).
In the first case B=8 gives height at least 60/8, B=10 gives at least
64/8, and B>=12 gives at least 10. In the second case B=10 is excluded,
so B>=12 and height is at least 12-25/10. The third case is unchanged.
The girth-five no-six contribution uses the sum of these three complete
kernel powers, capped by its previous bound, with all existing tail terms.

## A unique norm-four line and a norm-ten extension

For c=4 on twelve positions, the unique norm-four line lies on the first
four-coordinate circuit C. Every independent row is nonzero on all eight
new positions and on at least one old position. Its squared norm is even,
so is at least ten. At norm ten all entries are units, with precisely two
old positions: a coefficient of absolute value two on a new position would
already make the squared norm at least eleven before including old entries.

The script `scripts/wall1_four_ten_twelve.py` enumerates all three balanced
first lines and all balanced unit second lines on eight new and two old
positions. It normalizes modulo the first row and by the first new entry,
deduplicates the resulting planes, and checks each prescribed old overlap.
For q=7,17,3329 it obtains the same counts:

| Prescribed overlap | Gram determinant | Planes |
|---|---|---|
| 1 | any | 0 |
| 2 | 36 | 196 |
| 2 | 40 | 182 |
| 3 | 40 | 546 |

An old coordinate and a new coordinate give a unit two-by-two minor, so
these pairs generate their saturated integer plane. Their second squared
Gram--Schmidt heights are determinant/4. In the complement there is no
independent row of squared norm at most ten. Reduce a second basis vector
against the norm-four row: its inner product has absolute value at most
two, hence its projected squared length is at least 12-4/4=11.

The implementation adds the counted complete kernels with heights 9 and 10,
and the full coefficient-count remainder with height 11. It retains the
cutoff-40 tail and periodic corrections of the original norm-four bound,
and takes the minimum with that bound. The remainder is deliberately not
reduced by the rare counts, so overlapping covers cannot cause undercounting.

## Girth seven on twelve positions

At girth seven, a squared-norm-eight row must be unit on eight coordinates:
the coefficient-two shape has support five and is forbidden. Two independent
unit-eight rows spanning a full-support plane on twelve positions overlap
on exactly four coordinates. Each exclusive projective column group has
size four, and each shared projective group has size at most four. Every
nonzero row of their plane therefore has support at least eight. This
contradicts the existence of the prescribed seven-coordinate circuit.

Thus, if the first squared minimum is eight, the second is at least ten.
Gauss reduction gives second squared height at least10-16/8=8. If the first
minimum is at least ten, the usual heights(10,15/2) apply. Sum the complete
kernels for(8,8) and(10,15/2), and cap by the old bound. Here(8,8) denotes
Gram--Schmidt squared heights, not the excluded pair of squared norms.
The cutoff-14 tail and periodic terms stay unchanged. The finite twelve-point
classifier now checks this exclusion as well; the proof uses exact girth
seven, not merely a lower bound of seven on girth.
