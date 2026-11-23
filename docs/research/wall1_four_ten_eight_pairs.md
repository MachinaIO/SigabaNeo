# Ten-position four-circuit planes without norm-four relations

The selected rank8/girth4 residual is the two-relation sum, rather than the
one-relation alternative. Its t=6, overlap3 term accounts for about97.8%
of that sum. Within this term the no-four family dominates; after Part368
the one-four part is less than10^-14 of the selected kernel. Improving the
norm-four/eight determinant32 kernel therefore has little global effect.
These are shares of upper bounds, not frequencies of actual configurations.

Consider the lifted rank-two integer relation plane on ten positions with
a circuit C supported on four positions. Every vector outside C is nonzero
on all six new positions, and any two such vectors have proportional new
parts. Work in the family with no norm-four or norm-six row.

A balanced norm-eight integer row is unit on eight positions, has one
entry of absolute value2 and four unit entries, or is the support-two
shape(2,-2). The support-two shape contradicts girth four. The support-five
shape cannot cover the six new positions. None of these shapes can lie
on the full four-position circuit C. Hence every norm-eight row is unit on all six new positions and
exactly two old positions.

Suppose two independent norm-eight rows form a Gauss-reduced basis. Change
one sign so their new parts agree. Their difference is a nonzero vector
on C, and therefore must be nonzero on each of its four positions. The
two old supports must consequently be disjoint. Their inner product is
then6, contradicting the reduced-basis inequality |dot|<=8/2=4.
This excludes every reduced(8,8) pair. The exact finite check examines
all165 pairs with proportional new parts and full four-position difference.

If the first squared minimum is8, the second squared norm is at least10.
Gauss reduction then gives second squared GS length at least
10-4^2/8=8. If the first squared minimum is at least10, the general
Gauss bound gives squared GS lengths at least10 and15/2. Thus use the
sum of complete kernels with pairs(8,8) and(10,15/2), and take its minimum
with the preceding complete kernel. Here the pairs denote GS lengths,
not the excluded pair of row norms. The original cutoff14 tail and all
periodic terms are retained in both kernels. Coefficient counts and
all norm-four and norm-six contributions remain unchanged.

The classification is a paper proof supported by exact checks. It does
not close the size17..24 remainder, the adaptive BKZ distribution bridge,
or its Lean formalization.
