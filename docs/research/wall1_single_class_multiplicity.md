# Removing marked-pair multiplicity in a rank-one quotient

Fix a triangular anchor of size6 and rank4. For a connected rank5 support,
the contraction by its span has rank1: it consists of one nonloop parallel
class and loops. The nonloop class has size at least2, since otherwise
its only member is a coloop. Distinct augmented points ensure that any
pair in this class gives a crossing relation with a nonzero old part;
girth four forces at least two old basis coefficients. Thus the same
two-new-point kernel applies to every pair in the class, as in the
existing marked-class argument.

If the nonloop class has size k, the preceding pair-marked cover counts
it choose(k,2) times. Assign each marked pair weight1/choose(k,2).
For every fixed configuration and anchor the sum of these weights is
exactly1. This is a pointwise identity, so it remains true after averaging
and permits application of the same uniform joint-kernel upper bound.
It requires neither independence of pair events nor disjoint events.

After marking two points, let n be the remaining number of positions and
j the number belonging to their class. The other n-j are loops. With an
anchor of rank d, each class member has at most q^d affine-slice choices,
and each loop at most q^(d-1). The corrected completion factor is

    M*(n,d,q) = sum_(j=0)^n choose(n,j)
                  q^(d*j+(d-1)*(n-j)) / choose(j+2,2).

Multiplying by the outer choose(n+2,2) gives the exact combinatorial
identity

    choose(n+2,2) M* = sum_(k=2)^(n+2) choose(n+2,k)
                              q^(d*(k-2)+(d-1)*(n+2-k)).

The powers still count completions with upper bounds; the identity is
exact for these weights. Loop/nonloop membership is fixed by the original
anchor, so changing the marked pair does not change k. Overlaps between
different anchor choices are left as an upper bound; no anchor multiplicity
is divided out.

The implementation uses exact fractions for M*, converting to interval
arithmetic only when multiplying the joint kernel. It applies to the
rank5 triangular term at sizes15..24 and to the size14 entry in the earlier
baseline. It retains the minimum with previous bounds. Other quotient
ranks and anchor families are unchanged. All joint-kernel tails, periodic
corrections, and coefficient counts stay inside the existing kernel.

Checks enumerate1981 subsets and their pair weights, and verify114 exact
weighted identities against direct class-size sums at q=3,7,3329 and
anchor ranks4,5. These are combinatorial checks, not a Lean proof or a
verification of the full BKZ claim. The complete residual budget and the
adaptive selected-block distribution bridge remain open.
