# H13, girth five: short-pair exclusions and a counted (8,10) cover

Assume the existing rank-two coefficient-code setting: first support
C={0,...,4}, eight new coordinates J={5,...,12}, and a prescribed second
support J union A, with empty != A strictly contained in C. The code has
girth at least five. The relevant c5/H13 branch has no norm-six rows.
All bounds below keep the original cutoff-14 tail and periodic correction.
No production evaluator was edited by this worker.

## Every outside row meets the old support

Every code direction outside the C direction is nonzero on all of J.
Moreover it cannot be zero on all of C. If such a new-only direction existed,
it and the C direction would span the code; every code row would then have
old support either empty or all of C. That contradicts the prescribed proper
nonempty overlap A. This argument is over the finite field and does not
assume any short C vector exists.

A balanced integer norm-eight row outside C would have to be a unit row on
exactly the eight new positions, hence new-only, which is impossible. A
norm-eight row is therefore in C and has the shape (2,1,-1,-1,-1) up to sign
and permutation. There are twenty such lines. In particular two independent
norm-eight rows are impossible.

The balanced norm-ten possibilities have supports 10, 7, or 4: respectively
unit ten, (2,1,1,-1,-1,-1,-1), and (2,-2,1,-1), up to signs and permutations.
No norm-ten row fits inside C with girth five. Outside C, the requirement of
eight new positions eliminates the support-seven and support-four shapes.
Thus every norm-ten row is a unit row on J and two old coordinates.

Two independent norm-ten rows cannot coexist. Their new unit restrictions
are proportional modulo q, and therefore agree up to an integer sign for
q=3329. Their signed difference is a nonzero row on at most four old
positions. Its entries have magnitude at most two, so it remains nonzero
modulo q and violates girth five. This excludes the reduced-minima case
(10,10), not merely a particular presentation.

## Complete rank-two cases

For a Gauss-reduced integer basis, distinguish its first squared norm.

* If it is eight and the second is ten, the first vector is on C and the
  second has exactly two old unit entries. Their inner product has magnitude
  at most three. The squared GS lengths are at least (8,71/8).
  If the second squared norm is at least twelve, Gauss reduction gives
  second GS length at least 12-8/4=10, which is stronger.
* If the first squared norm is ten, a second norm-ten vector was excluded,
  so the second squared norm is at least twelve. GS lengths are at least
  (10,19/2).
* If the first squared norm is at least twelve, the usual reduced-basis
  inequality gives GS lengths at least (12,9).

The resulting three complete cases are therefore

    (8,71/8), (10,19/2), (12,9).

The affine parity used here is exact: an integer vector with coordinate sum
zero has even squared norm. Short modular affine rows have integer sum zero
because the absolute sum is less than q.

## Count the exceptional (8,10) case

There are twenty possible C-supported norm-eight lines and

    binomial(5,2) * binomial(10,5)/2 = 1260

possible outside norm-ten lines. Their 25200 pairs give a witness upper
count. Each pair determines a coefficient plane and at most one normalized
chart for any fixed prescribed second support. Counts need not be counts of
distinct planes for this upper bound.

Let a,b be such a pair. Among the three old coordinates where b vanishes,
at least two have |a_i|=1. Such an old coordinate and any new unit coordinate
of b give a unit minor. Hence the pair is saturated in its rational plane,
and its exact Gram determinant is 80-<a,b>^2. Enumeration verifies

    {71:5320, 76:7560, 79:4760, 80:7560}.

All 25200 pairs satisfy the unit-minor argument and |<a,b>|<=3. The script
also groups outside norm-ten lines by their signed new restriction and checks
all 9170 resulting pairs; each has the forbidden nonzero old difference.
The 35 candidate new-only norm-eight lines are checked separately.

After covering (8,10), the remaining norm-eight case has second squared norm
at least twelve, giving (8,10) as its **GS lower bounds**. Here the second
10 denotes projected squared length, not a second vector of norm ten.
The other two cases above remain unchanged.

## Short spans of rank zero or one and saturation

These cases must not be silently assumed to have a reduced rank-two basis.
If the span of cutoff-short rows has rank zero, its Gaussian sum is just one,
which is bounded by the (12,9) theta product because each theta factor is at
least one. If it has rank one, use its shortest primitive generator. Its
squared norm is eight, ten, or at least twelve. Its one-dimensional theta
bound is dominated by, respectively, the (8,10), (10,19/2), or (12,9) product,
again because the additional theta factor is at least one. The norm-eight
rank-one case belongs to the complement of the counted two-row family.

For rank two use the saturated integer lattice in the real span. It reduces
into the coefficient code: two independent cutoff-short rows have a
nonzero 2x2 minor of absolute value at most 14^2<q, so q does not divide their
index in the saturated lattice. The reduction of the latter therefore has
the same two-dimensional span. Its short vectors are subject to exactly the
same girth, support, and balance restrictions. The explicit (8,10) family
has the stronger unit-minor saturation certificate described above.

The existing `14^3<q` lifting proves that all cutoff-short code rows lie in
real rank at most two. Everything outside that cutoff remains in the full
tail. Thus the case split covers ranks zero, one, and two without asserting
an unproved lower bound for a missing second short row.

## Complete kernels and proposed insertion

Put beta=11N/(26R^2), a0=pi^2/beta, alpha=a0/q^2, and

    delta=2 exp(-a0/4)/(1-exp(-2a0)),
    T=exp(-98 alpha) theta(5 alpha/2)^2,
    E=sum_{j=1}^13 binomial(13,j) delta^j,
    K(u,v)=(pi/beta)^(13/2)
           * ((theta(u alpha) theta(v alpha)+T)/q^2 + E).

The existing unweighted lifting checks `14^3<3329` and
`13*14^2<3329^2` hold. No tail, periodic term, or zero vector is omitted.
For overlap o, Q=q^(9+o). Both following complete bounds are valid:

    B_direct = K(8,71/8)^N + K(10,19/2)^N + K(12,9)^N,

    B_counted = min(25200,Q)/Q * K(8,71/8)^N
                + K(8,10)^N + K(10,19/2)^N + K(12,9)^N.

Production can add a `c == 5 and union == 13` branch in the existing no-six
section, before `two_term` is assembled:

```python
from wall1_five_thirteen_short_pairs import EIGHT_TEN_WITNESSES
tail8 = iv.exp(-98*alpha)*half_sum
rare = six_plane(8, I(71)/8, tail8)**n
higher = (six_plane(10, I(19)/2, tail8)**n
          +six_plane(12, 9, tail8)**n)
direct = rare+higher
counted = (I(min(coefficient_count, EIGHT_TEN_WITNESSES))/coefficient_count
           *rare + six_plane(8, 10, tail8)**n+higher)
none_term = min((none_term, direct, counted), key=lambda v: v.b)
```

The existing outer minima remain. This is a complete local cover, requiring
no new exclusion or global anchor addback.

## Measured local and selected gains

The standalone diagnostic records the actual selected kernels and actual
one- versus two-relation choices for rank 11 at sizes 18 and 19. In its
pre-integration run the counted local improvement is 37.5097 to 42.5097
orders, depending on overlap; the direct three-case bound improves 25.4464
to 30.4464 orders. These values include every correction above.

Recomputing the rank-11/girth-five selected sums while changing only t=8
terms gives the same gain at both component sizes:

    log10(new selected sum / old selected sum) = -20.5014701836973....

The old leading family is t=8, overlap four. The new sum retains all other
families, so the 42-order kernel gain is not a 42-order full-stratum gain.
Raw selected activity logs change from 47.1137503389 to 26.6122801552 at
size 18, and from 82.6970290606 to 62.1955588769 at size 19. These are raw
activity upper envelopes, not probabilities or weighted transfer values.

Reproduce with `python3 docs/research/scripts/wall1_five_thirteen_short_pairs.py`.
The pre-integration measured log is preserved at
`/tmp/wall1_five_thirteen_short_pairs.log`. After parent integration, the
standalone diagnostic reconstructs the previous selected kernel as the
minimum of the unchanged generic Gaussian envelope and the original
no-six K(8,6) kernel. It checks production against the standalone counted
replacement within relative tolerance 1e-60, and reconstructs the old whole
sum by undoing only the changed t=8 factors. The post-integration log is
`/tmp/wall1_five_thirteen_short_pairs_integrated.log`. Parent-wide regression
and independent review remain separate. This result alone does not certify
the complete high-order budget or the adaptive BKZ bridge.
