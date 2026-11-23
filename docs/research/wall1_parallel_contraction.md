# Parallel classes after excluding large crossing circuits

This paper refinement admits the remaining rank-six through rank-eight
size-fourteen triangular families. Their additional weighted charge is below
3.219e-17, and the total admitted transfer is below 5.396e-13. At size fourteen
only the rank-five triangular family remains. The higher-size activities and
later selected histories are still open; BKZ is not proved.

## A single basis pivot forces a larger crossing

Use Part 291's rank-four anchor A and fixed basis X=B_A. Extend X to a basis
X union Y of a connected representable matroid M. Express every nonbasis
column in these basis coordinates. A mixed column has nonzero coordinates in
both X and Y. A mixed column with at least two nonzero Y coordinates gives
Part 291's eligible crossing with at least three points outside A.

Suppose no such crossing exists for any basis extending X. Then every mixed
column has exactly one nonzero Y coordinate. Consider the graph on basis
positions obtained by joining positions that occur in the support of a
nonbasis column. This graph is connected: otherwise every column lies in one
of the complementary spans of its components, contradicting connectedness
of M.

On Y, pure-Y columns connect their support positions. Each component of this
graph must touch a mixed column to connect to X. If any component has at
least two vertices, take a mixed column e at a vertex b incident to a pure-Y
column f with another Y coordinate. Replace basis vector b by e. This is a
valid basis exchange since e_b is nonzero. In the new coordinates,

```
f = (f_b/e_b)e + [f - (f_b/e_b)e],
```

where the bracket has b-coordinate zero. Its X part is nonzero, and f retains
at least one other Y coordinate. Together with the nonzero e-coordinate this
is a mixed fundamental circuit with at least three new points, a contradiction.
The exchange retains the fixed basis X, so the resulting witness is exactly
within Part 291's covered class.

Consequently every column has at most one nonzero Y coordinate. In M/A the
nonloops therefore form a direct sum of rank-one parallel classes. Loops
are precisely the positions in span(A). Since M has no coloops, neither does
M/A; a singleton parallel class would be a coloop. Every class thus contains
at least two positions.

This implication is used only for the residual family with no eligible large
crossing in **any** basis extension of the fixed X. Checking just one basis
would not suffice; the pivot is essential.

## Count by parallel classes rather than the whole span

Put k=r-4 and h=14. There are eight positions outside A. If l are loops,
partition the remaining 8-l positions into k nonempty classes of size at
least two. Let S_2(n,k) count these partitions. Its recurrence is

```
S_2(n,k) = k S_2(n-1,k) + (n-1) S_2(n-2,k-1),
S_2(0,0)=1.
```

Choose the least labelled position in each class as its representative.
Their quotient directions are independent, so their full-incidence weighted
sum is at most mu^k after fixing A. No factor for alternative representatives
is needed. Every other point in a class lies in the affine slice of
span(A,representative), giving at most q^4 choices. Each loop lies in the
affine slice of span(A), giving at most q^3 choices. The candidate clipping
and rank restrictions may be dropped only after the independent evaluations
have supplied the density factors.

With A_3=(G_3+Alias_3)/q^(4m), the rank-(k+4) activity is at most

```
choose(14,6) * 75 * A_3 * mu^k
 * sum_(l=0)^(8-2k) choose(8,l) S_2(8-l,k)
                     q^(4(8-l-k)+3l).
```

The factor 75 accounts for the pairings and affine-compatible signs as before.
Multiple anchors may count the same configuration, safely enlarging this bound.
No assumption about conditional independence after excluding a rare event is
used. This is a direct configuration count.

The activity is a positive constant times mu^k. Multiplying it by the linear
transfer coefficient from Part 286 leaves negative mu-powers termwise, so
the existing mean-floor evaluation is valid.

## Numerical result and open target

For ranks six, seven and eight, the weighted envelopes are respectively below
3.21842e-17, 6.271e-29 and 6.359e-42. Their sum is below 3.219e-17.
Adding them to Part 291's admitted baseline gives

```
known transfer < 5.396e-13.
```

The rank-five envelope remains about 5.72e-7 and is not admitted. Thus U_14
can be restricted to rank-five, girth-four configurations containing an
eligible triangular six-point anchor. Their quotient has rank one, so the
parallel-class statement alone does not give enough suppression.

The sufficient remaining condition is now

```
sum_(h=14)^24 L_h^* U_h + Pr(max_(15..404) b_i>.280) <= 2.4692e-12.
```

This remains unproved. The slight decrease in the available residual budget
reflects the newly admitted positive contributions, not a new complete
failure-probability bound. The reference allowance 9.131e-13 and these two
rounded budgets still total less than 3.922e-12.

Validation: `wall1_parallel_contraction.py` checks 2,593 connected fundamental
graphs, 137 explicit pivot witnesses, 256 parallel cases, and 81 partition
counts against exact set partitions. Actual-parameter interval assertions
and exact rational budget arithmetic pass. No part of this new structural
or numerical argument is Lean formalized yet.
