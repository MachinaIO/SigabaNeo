# Splitting girth-five codes by norm-six directions

In an affine integer row of squared norm six, either six entries are
+/-1, or one entry has magnitude two and two have magnitude one. Girth
five excludes the latter support-three case. The former has three plus
and three minus signs, hence 10 projective sign patterns on a prescribed
six-support. Write K=10 choose(H,6) for the number of such lines on H
positions. A five-support first circuit cannot be one of them.

## Two norm-six directions force eight positions

Two independent balanced six-support rows spanning the relation code have
union equal to its full H-position support. Their overlap has size 12-H;
their exclusive positions number 2H-12. On the overlap, coefficient
ratios are +/-1. The two mixed directions which can cancel coordinates
cancel respectively p and 12-H-p positions. Every other mixed direction
has weight H.

If H<=7, one of those two mixed directions has weight at most
H-ceil((12-H)/2)<=4, contradicting girth five. If H>=9, every mixed
direction has at least 2H-12>=6 exclusive nonzero positions, so none
can be the prescribed five-circuit. Thus H=8 is necessary. This argument
applies over every odd field; the evaluation uses q=3329.

## Coefficient counts and Gaussian factors

The prescribed first and second circuits have c=5, t new positions, and
a overlapping old positions. There are at most Q=q^(t+a+1) normalized
coefficient pairs. Fixing a first circuit (at most q^3 choices) and a
norm-six line determines the code; the prescribed missing old coordinate
then determines the second circuit direction. Thus at most K*q^3 pairs
have a short line. For t>=6 there are none, by Part 295's support bound.
Two short lines determine the entire code and both prescribed directions,
so K^2 is a valid upper count for the two-independent-short-line class,
which is empty unless H=8. Counts are capped by Q.

Split the average into no norm-six line, exactly one, and at least two.
Their short theta products are respectively

    theta(8 alpha) theta(6 alpha),
    theta(6 alpha) theta((13/2) alpha),
    theta(6 alpha) theta((9/2) alpha).

The first follows from Gauss reduction and even squared norms. In the
second, the shortest vector has squared norm six and an independent one
has squared norm at least eight, so its perpendicular height is at least
8-6/4=13/2. The last uses the general reduced height 3*6/4.

For codes with a norm-six row, cutoff 36 is valid because
sqrt(6)*36^2<3329. The same minor and saturation argument as Part 283
confines short representatives to a plane. Retain the tail
exp(-648 alpha) theta(p alpha/2)^2. In the no-short class, retain cutoff
14 and its tail exp(-98 alpha) theta(p alpha/2)^2. Include the positive
periodic expansion in all three factors. Weight the latter two factors
by their coefficient-count bounds divided by Q, and the no-short factor
by one; overcounting is harmless. Take the minimum with the old bound.

## Verification and remaining gap

There are 1,278 exact finite-field classifications in the regression, with
144 eligible cases, all on eight positions. First-support and balanced-sign
symmetry are fixed in that enumeration. The unbounded-field argument is
given above; the finite enumeration is a regression, not its replacement.

The full size-fifteen residual weighted log10 improves from about 1.94693
to 1.40954. Girth-five strata leave the five largest terms; rank-seven
girth-four now dominates. The full envelope still misses the required
residual budget. Sizes 16..24 and later selected histories also remain
open. These are paper bounds and interval checks, not a Lean proof or
completion of BKZ.
