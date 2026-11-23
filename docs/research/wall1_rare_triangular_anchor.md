# Rare triangular anchors: first moment and conditioning boundary

In the fixed draw-14 candidate ball and **fresh uniform affine-graph model**,
the probability that an eligible triangular six-point anchor occurs is below
3e-87. This concerns existence of an anchor, not its extensions to high-order
moments, and is not a selected-history or full BKZ bound.

## First-moment estimate

An eligible anchor has six distinct input positions, augmented input rank
exactly four, and one of the triangular two-row balanced-sign codes. Partition
the six coordinates into three pairs. The pair forms must have equal sums
of coefficients because the relations are affine. Up to common sign reversal,
there is one ordinary-sum type and four oriented-difference types. Thus five
signed patterns suffice after ordering the six points.

For each pattern, drop the rank/distinctness restrictions and coordinate
clipping only **after** using augmented rank four to obtain the incidence
factor q^(-4m). Sign changes preserve the enlarged integer ball, so the
number of compatible lifted tuples is bounded by the same modular equal-pair
energy G_3+Alias_3 from Part 284. The count includes all nonzero modular layers.
Each actual witness is included among these ordered tuples. No symmetry
divisor is needed for the following safe union/first-moment bound:

```
Pr(exists eligible triangular anchor)
 <= 5 (G_3+Alias_3) / q^(4m)
 < 2.848e-87 < 3e-87.
```

The interval calculation gives 2.84783583244745e-87 rounded upwards, at
q=3329, m=400, N=518 and the existing draw-14 radius. The bound is for the
unconditioned random graph underlying that fixed geometry. It does not assert
the same bound after arbitrary BKZ history conditioning, nor union it over
later selected projections.

## Why this does not yet close the residual transfer

The residual moments count every extension of a six-point anchor to larger
connected configurations. Rare anchors can therefore have a much larger
moment envelope. An existence bound does not automatically bound those
weighted extension counts.

Conditioning on absence of anchors is also not a license to reuse the
unconditional independence and cumulant identities. Even proper-subset
incidences change under that conditioning. The following exact example
illustrates the issue independently of the large lattice parameters.

Take a uniformly random affine map F_2^2 -> F_2 and let its four zero-value
indicators be the hits. Every proper subset of the four inputs is affinely
independent, so those joint hit probabilities are 2^(-j). All four hit with
probability 1/8; no point hits with probability 1/8. After conditioning on
not all four hitting, a given hit has probability 3/7 and two prescribed hits
have joint probability 1/7, instead of 1/2 and 1/4.

The unconditioned factorial moments of the number of hits are
(1,2,3,3,3), through order four. Setting only the full four-point moment to
zero while retaining the lower moments makes the even inclusion-exclusion
sum equal zero, although the actual void probability is 1/8. Thus naive
deletion can even destroy an upper bound. This example does **not** refute
all possible exceptional-event methods; it shows why such a method needs
its own transfer theorem.

At the event level, if Bad has probability delta, then for every event E,
abs(Pr(E | not Bad)-Pr(E))<=delta, by the two-component mixture identity.
For the void event specifically, Bad is impossible whenever there are no
hits, so Pr(void)=(1-delta)Pr(void | not Bad). A useful continuation would
bound the conditional void probability without assuming the original graph
independence under conditioning. Such a bound has not been proved here.

## Validation and remaining work

`wall1_rare_triangular_anchor.py` verifies the actual-parameter interval
bound, the exact affine-square example, and the event-level TV inequality
for all 256 events in that example. The first-moment geometric argument is
not Lean formalized. Part 288's residual activity/history target remains
unproved; the rare-anchor estimate is not substituted for it.
