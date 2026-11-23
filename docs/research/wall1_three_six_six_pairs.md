# Exact H6 two-six planes for a prescribed three-circuit

Fix C={0,1,2}, S_a={0,...,a-1,3,4,5}, a=1 or 2, and q=3329.
Among full-support balanced rank-two coefficient codes with girth three,
no balanced norm-four integer row in the modular preimage, and two
independent balanced integer rows of squared norm six, the exact normalized
chart counts are:

| Prescribed overlap a | Gram determinant D | Count | Squared GS lengths |
|---|---:|---:|---|
| 1 | 36 | 1 | (6,6) |
| 2 | 32 | 18 | (6,16/3) |
| 2 | 36 | 1 | (6,6) |

This is a local coefficient classification, not a completed BKZ theorem.

## Exhaustiveness of the generating forms

Every balanced norm-six integer row on six positions is either a shape-three
row (2,-1,-1) on three positions, up to sign, or a unit-six row with three
+1 entries and three -1 entries. The first kind has 60 unoriented lines and
the second has 10.

Choose two independent such rows spanning the code. Their combined support
must be all six positions. If both have support three, their supports are
disjoint. Their linear combinations have support three or six, so they
cannot contain the required second circuit of support four or five.

If both are unit-six rows u,v, a combination vanishing on positions 3,4,5
forces their entries there to agree up to an overall sign. Adjust that sign
so they agree. To obtain support exactly C, their old entries must all be
opposite. Balance then forces the sum of their three old entries to be zero,
which is impossible for three signs. These cancellation implications hold
also modulo q>=7: the only relevant entry differences are 0 or +/-2.

Therefore one row is shape-three, call it a, and the other is unit-six,
call it b. A combination with nonzero b coefficient can vanish at all three
new positions only if a is supported exactly on those new positions. But
its values (2,-1,-1) cannot be proportional to three unit entries over any
field of characteristic >=7. Thus the unique C direction must be a itself.
We have reduced every eligible plane to a shape-three row on C and a
balanced unit-six row b on all six positions.

## Exact count without enumeration

Orient a with its +2 entry at d in C and its other entries -1. Orient b so
that its majority sign on C is +1. There are two cases.

1. All three old entries of b are +1. All three new entries are -1. Then
   <a,b>=0 and D=36. The old ratios b_i/a_i have one exceptional value 1/2
   at d and the common value -1 at the other two positions. Cancelling the
   common value leaves exactly the old position d; cancelling the exceptional
   value leaves its complement. Thus a=1 requires d=0, and a=2 requires
   d=2. Each prescribed support admits precisely one such plane.

2. Exactly one old entry of b is -1; call its position e. The new entries
   have sum -1, so there are precisely three choices (the position of the
   unique new +1). If e=d, the scalar product is -4 and a+b has norm squared
   four, so this plane is excluded. If e!=d, the scalar product is +2 and
   D=32. The three old ratios are 1/2,-1,+1, all distinct. Cancellation
   removes precisely one old position, so overlap one is impossible and
   overlap two with old positions 0,1 is always available by cancelling
   position 2. There are 3 choices of d, 2 of e!=d and 3 new sign choices:
   exactly 18 planes.

There is no duplicate count. In every retained plane the quadratic-form
bound below shows that its only integer norm-six lines are a and b. In
particular b is the unique unit-six line; C recovers a. This remains a
statement about distinct modular charts: if two retained planes agree
modulo q, normalize their common C row and compare their unit-six rows at a
new coordinate. Their difference has coordinates 0 or +/-2 and is a scalar
multiple of a. The two old unit coordinates of a determine this scalar in
{0,+/-2}; comparing the distinguished coefficient 2 shows a nonzero choice
would require a difference +/-4 instead of 0 or +/-2, impossible modulo
q>=7. Therefore their unit-six rows coincide up to sign.

The chart normalization is f_0=1 for the C row, v_0=0,v_3=1 for its
independent complement, precisely the normalization used in the coefficient
sum. The excluded D=20 cases yield three charts for each prescribed overlap:
e=d=0 for overlap one, and e=d=2 for overlap two, with three new sign choices.

## Saturation, girth, minima and modular validity

Take an old position i with a_i=+/-1 and any new position j. The minor
on columns i,j is a_i*b_j=+/-1. Consequently Za+Zb is saturated in its
rational plane. In the retained cases |<a,b>|<=2, so for integers u,v both
nonzero,

    ||ua+vb||^2 = 6u^2+6v^2+2uv<a,b> >= 4(u^2+v^2) >= 8.

If one coefficient is zero, the least nonzero squared norm is six. Thus
both successive minima squared are six, the only norm-six lines are the
generators, and no norm-four vector exists in the saturated plane. The
basis is Gauss reduced, with exact squared GS lengths 6 and D/6.

The three new columns form one projective class. The old column classes
have sizes 2,1 when D=36 and 1,1,1 when D=32; all differ from the new class.
The maximum class size is three. Therefore the minimum support of a nonzero
codeword is exactly three, establishing the girth condition.

For a norm-four integer vector w in the modular preimage, a new coordinate
fixes an integer lift |v|<=2. An old unit coordinate fixes a lift |u|<=4.
The discrepancy w-ua-vb has coordinate magnitudes at most 12. When q>12,
being divisible by q forces it to vanish. This contradicts the planar
norm-four exclusion. In particular q=3329 is covered. Direct exhaustive
checks also verify the result at q=7; the hand counting and rank arguments
are valid for every prime q>=7. No identification of the entire modular
preimage with the planar lattice is used: periodic tails remain necessary.

## Formula for integration

Let K(x,y) be the existing no-four planar theta bound, retaining its
short-vector remainder and periodic-plane term. In the c=3,t=3 two-six
family, coefficient chart denominators are Q=q^(a+2). Replace only that
family's current contribution by its minimum with:

- overlap 1: K(6,6)^N / q^3;
- overlap 2: [18*K(6,16/3)^N + K(6,6)^N] / q^4.

Retain the one-six and no-six families and their existing coverage. Existing
overcounting in their weights does not invalidate this refinement. A
separate numerical evaluation is needed to measure the global effect.

## Exact executable verification

`python docs/research/scripts/wall1_three_six_six_pairs.py` enumerates every
unordered pair of the 70 norm-six lines (2415 pairs), extracts the prescribed
supports, deduplicates normalized charts, verifies unit minors and girth,
and excludes all 45 balanced norm-four lines from each retained modular code.
The run saved at `/tmp/wall1_three_six_six_pairs.log` gives, for each
q=7,17,3329:

```
retained={(1,36):1, (2,32):18, (2,36):1}
excluded={(1,20):3, (2,20):3}
```

Only the new script and this note were changed for this classification.
