# H11, girth five: a counted norm-eight pair cover

The rank-nine/girth-five diagnostic identifies the same controlling family
at component sizes 17 and 18: first circuit C={0,...,4}, six new positions,
and second-support overlap four. Its contribution is approximately 98.86%
of the selected two-relation sum. The local one-six and two-six terms are
zero; the actual selected kernel is the no-six bound. The current second
largest family is H9, four new positions and overlap four, at relative
log10 -1.96579620888.

This note gives a complete finite-witness split for the controlling H11
family. It changes neither the event nor the circuit coefficients and needs
no excluded-family addback.

## Assumptions and all possible norm-eight rows

Use exactly the existing short-plane setup: a two-dimensional relation code
on eleven coordinates has girth at least five, contains a line with support
C, and contains a second line supported on all six new coordinates and a
proper nonempty subset of C. Integer short rows are balanced. In the family
under study there is no independent norm-six line; the shortest squared
integer norm is at least eight. All restrictions are the existing c=5,H=11
no-six branch, not new distributional assumptions.

A balanced norm-eight integer line of support at least five has one of two
shapes:

* eight unit entries with four plus and four minus signs;
* five entries of magnitudes 2,1,1,1,1, with signs equivalent to
  (2,1,-1,-1,-1).

The support-two shape (2,-2) violates girth five. These are all possibilities
by partitioning the squared norm eight into integer squares.

A row outside the C direction has all six new coordinates nonzero: its new
restriction is proportional to that of the prescribed crossing row. It must
therefore be a unit-eight row, supported on the six new coordinates and two
old ones. There are

    binomial(5,2) * binomial(8,4)/2 = 350

such balanced lines. A norm-eight line in the C direction has the second
shape above, and there are 5*4=20 possible lines.

Two distinct outside norm-eight lines cannot coexist in a girth-five code.
Their six new unit restrictions must be proportional modulo q. For q=3329
(and the tested q=7,17), this proportionality is exactly +1 or -1 as integer
rows. Their corresponding difference is a nonzero old-supported row on at
most four coordinates. Its entries have magnitude at most two, so it stays
nonzero modulo q. This contradicts girth five.

Consequently every code with two independent norm-eight rows is witnessed
by one of the 20 C rows and one of the 350 outside rows: at most 7000 pairs.
This is a witness upper bound, not a claim of 7000 distinct coefficient
charts. Each pair fixes one modular plane and hence at most one normalized
chart for any fixed prescribed second support.

## Gram bound and saturation

Let a be the C row and b the outside unit-eight row. Only two old entries
contribute to their inner product, and at most one entry of a has magnitude
two. Thus |<a,b>|<=3 and

    det Gram(a,b) = 64-<a,b>^2 >=55.

There are three old coordinates where b vanishes; at least two of these
have |a_i|=1. Together with any new unit coordinate of b they give a unit
minor. Therefore a,b generate the saturated integer lattice in their real
plane. Their exact squared GS lengths are 8 and `(64-<a,b>^2)/8`, so the
uniform bound (8,55/8) is valid. The two rows are also Gauss reduced since
2|<a,b>|<=6<8.

Exact checks enumerate all 7000 witnesses and obtain determinant counts
`{55:1500,60:2100,63:1300,64:2100}`. They also check all 2575 pairs of outside
rows with proportional new restrictions, each producing the forbidden
old row. Normalizing the prescribed second supports at q=7,17,3329 gives
chart counts `{1:0,2:700,3:210,4:1960}` by overlap. Production may safely use
the simpler uniform witness bound 7000; none of the sharper counts is needed
for this result.

## The full complement and Gaussian tails

There are two remaining possibilities for a Gauss-reduced basis of the
short integer plane:

1. Exactly one independent norm-eight line exists. The second squared norm
   is at least ten. Its squared GS projection is at least `10-8/4=8`.
2. There is no norm-eight line. The first squared norm is at least ten and
   the second squared GS length is at least `3*10/4=15/2`.

Thus the complete split uses GS lower bounds (8,55/8), (8,8), and (10,15/2).
These exhaust the existing no-six class. No saturation claim about an
arbitrarily chosen complement pair is required: the complement uses a
Gauss-reduced basis of the full integer lattice, as in the existing bound.
If the cutoff-short real span has rank zero or one, the added theta factor
is at least one, so these same complement bounds also cover that case.

Let beta=9N/(22R^2), a0=pi^2/beta, alpha=a0/q^2, and

    delta = 2 exp(-a0/4)/(1-exp(-2a0)),
    T = exp(-98 alpha) theta(5 alpha/2)^2,
    E = sum_{j=1}^11 binomial(11,j) delta^j,
    K(u,v) = (pi/beta)^(11/2)
             * ((theta(u alpha) theta(v alpha)+T)/q^2 + E).

These are the complete existing cutoff-14 kernels, including the full
periodic correction. The existing lifting inequalities `14^3<3329` and
`11*14^2<3329^2` are checked. There is no omitted long-vector, alias, or
zero-vector term.

For overlap o, put Q=q^(7+o), the coefficient chart count already used in
this branch. A valid replacement upper bound for `none_term` is

    min(7000,Q)/Q * K(8,55/8)^N
       + K(8,8)^N + K(10,15/2)^N.

The first term covers the counted pair family, and the other two cover its
whole complement. Minimize this complete sum with the previous `none_term`.
The unchanged Markov and q-normalizing factors outside the kernel are
preserved. This is a local complete cover, so no new exclusion flag or
anchor addback is needed.

## Exact production insertion

Inside the c in (5,6) section of `wall1_general_two_relations.py`, after the
existing H11 refinement of `none_term`, add a separate branch for
`c == 5 and union == 11`:

```python
from wall1_five_eleven_eight_pairs import PAIR_BOUND
tail8 = iv.exp(-98*alpha)*half_sum
counted_eight = (
    I(min(coefficient_count, PAIR_BOUND))/coefficient_count
    *six_plane(8, I(55)/8, tail8)**n
    +six_plane(8, 8, tail8)**n
    +six_plane(10, I(15)/2, tail8)**n)
none_term = min((none_term, counted_eight), key=lambda v: v.b)
```

This worker has not edited the shared production evaluator; the parent subsequently integrated the displayed branch.

## Verified gain and limits

`wall1_five_eleven_eight_pairs.py` checks the exact witnesses and compares
against `five_circuit_anchor_parts[6,overlap]['selected']`, not an unused
internal kernel. The complete local kernel improvement has log10 about
-15.65285786 for every overlap. Replacing these terms in the full rank-nine,
girth-five two-relation sums gives, at both sizes 17 and 18,

    log10(new sum / old sum) = -1.9655321794015....

The diagnostic separately confirms that the two-relation candidate is the
selected rank-nine/girth-five candidate at size 17. It also reports the
actual size-18 candidate and raw terms; parent integration must still
recompute the complete selected envelopes. The next local bottleneck is
H9, not the tiny remaining H11 norm-eight pair term.

Reproduce:

    python3 docs/research/scripts/wall1_five_eleven_eight_pairs.py

The pre-integration measured log is preserved at
`/tmp/wall1_five_eleven_eight_pairs.log`. After parent integration the script
reconstructs the old complete H11 branch, checks that the production selected
kernel agrees with the standalone new kernel within relative tolerance 1e-60,
and reconstructs the old aggregate from the changed H11 terms. This avoids
applying the same improvement twice. The post-integration regression log is
`/tmp/wall1_five_eleven_eight_pairs_integrated.log`.
The raw controlling-family diagnostic is
`wall1_rank_nine_five_diagnostic.py`. All gains here concern upper envelopes,
not actual failure probabilities. This does not close sizes 18--24 or the
adaptive BKZ selection bridge.
