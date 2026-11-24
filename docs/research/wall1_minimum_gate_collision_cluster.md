# The old-minimum gate does not suppress all high-order collisions

Part 472 matches the first reference moment on a genuine old-minimum gate.
The same gate does not imply small relative errors in the higher moments.
The following exact q=3329 lattice example has 24 short candidates in one
nonzero quotient coset, while retaining the strict height-one witness margin.
It is not shown reachable in the production process and does not refute
that process's desired probability bound.

## An explicit lattice and its marked quotient

Work in the seven-dimensional subspace x_1=x_2 of R^8. Put

    D_6 = {z in Z^6 : sum_i z_i is even},
    M_0 = Z*(1,1,0^6) orthogonal-sum D_6,
    M = 3*M_0,     K = (3/q)*M_0,     q=3329.

Then qK=M and K/M has order h=q^7. Every nonzero vector of M_0 has squared
norm at least two: a nonzero first component contributes 2*a^2, and a
nonzero D_6 vector cannot be a signed coordinate unit. The bound is attained,
so lambda_1(M)^2=18.

Let k=(1/2,1/2,e_1) and let P consist of the 24 points

    p=(s/2,s/2,t*e_j),   s,t in {-1,1}, j=1,...,6.

Define the candidate list C={3*(p-k/q):p in P}. For each point,
q*(p-k/q)=q*p-k belongs to M_0: its equal first coordinates are integers,
and the sum of its last six coordinates is q*t-1, an even integer.
Thus C lies in K. Differences p-p' belong to M_0, so all candidates have
the same quotient label. The label is nonzero because the first coordinate
(s-1/q)/2 is not an integer.

The point p=-k belongs to P and attains the maximum distance from k/q.
Cauchy--Schwarz supplies the matching upper bound for all other p. Hence

    max_{x in C} ||x||^2 = (27/2)*(1+1/q)^2
                         =149700150/11082241 <14.

Take R^2=14 and c^2=18. These candidates satisfy R<c and the strict
height-one margin R^2+1=15<18=c^2, while the old minimum is exactly c.
Every pair difference is a nonzero vector of M and has squared norm at
least 18. The real affine span of C has dimension seven: P is the product
of a segment with the six-dimensional cross-polytope vertex set, and
translation and nonzero scaling preserve affine dimension.

## First moment exact; higher reference moments need not be close

Let U be a uniform fresh mark in H=K/M and use height one. All 24 candidate
indices hit if U equals their common label v; none hits otherwise. In the
notation of Part 472, with the old state deterministic and already satisfying
the minimum gate,

    M_0=(h-1)/h,
    M_j=(24)_j/h,       1<=j<=24.

For the first-moment-matching binomial reference p=1/(h-1), the ratio is

    M_j / [M_0*(24)_j*p^j] = (h-1)^(j-1).

It equals one at j=1 and is large at every higher order. The example therefore
rules out a uniform small-relative-error conclusion from q-ary marking,
the old minimum, and the witness margin alone. Likewise those geometric
conditions alone cannot discard every 24-point low-dimensional collision
tuple. A quantitative selected-history estimate must use additional structure
or correctly charge the states and tuples where this behavior occurs.

The candidate mean here is only 24/(h-1), not the reference mean 58 of the
production-motivated benchmark. The candidate list is not asserted to be
all short projected points. Its void is not identified with the actual
next-winner tail: additional witnesses can cover other marks. This example does not rule out a theorem with
additional density, full-list, determinant, or reachability hypotheses.
In particular its real affine rank seven must not be identified with a
production component's finite-field input rank: that identification requires
a separate correspondence with the actual raw graph representation.

## Verification

`scripts/wall1_minimum_gate_collision_cluster.py` checks all 24 memberships,
nonzero labels, all 276 pair differences, the exact rational radius and the
strict height margin. It computes real affine rank by rational elimination
and checks the factorial-moment ratios through order 24. The minimum proof
is the integer parity argument above, not an incomplete shortest-vector
search. The parent reran this checker successfully; independent review approved
the lattice construction, moment ratios and scope. No production failure
probability, reachable flag, or Lean formalization is claimed.
