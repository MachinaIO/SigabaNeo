# Triangular third-relation bounds at sizes fifteen through twenty-four

The third-relation method from Parts 291 and 293 extends to larger connected
components. The resulting valid upper envelopes improve the generic counts
but do not meet the residual budget. Complete admitted coverage remains
through size fourteen. The calculations identify other classes that cannot
be resolved by concentrating only on triangular anchors.

## General rank/size formula

Let h>=14 and consider a girth-four rank-r connected support containing an
eligible triangular six-point anchor A. Retain the fixed four-point basis of
A and the crossing fundamental-circuit argument from Part 291. For r>4,
the witness has t new points, a old basis positions, and union rank t+3.

Use the eight-point three-row code bound of Part 293, denoted B_8, when t=2;
this already includes the q^(-5m) full-incidence factor. For t>=3, use
A_3 K_t from Part 291. The resulting contribution is bounded by

```
choose(h,6) * 75 * choose(h-6,t) * choose(4,a)
 * choose(h-6-t,r-t-3) * q^(t+a-2)
 * joint_bound * mu^(r-t-3)
 * q^((r-1)(h-r-3)) / (r-t-2).
```

Sum max(1,4-t)<=a<=4 and 2<=t<=min(r-3,h-6). The basis-extension divisor
and the probability normalization are exactly those established in Part 291;
no new independence or uniform-history assumption is introduced.

For r=4 the old six-point anchor already spans the support, giving
choose(h,6)*75*A_3*q^(3(h-6)). For r=h-2 and h>6, such a connected support
is impossible: the anchor has nullity two, and equal nullity of the full
support would make all outside positions coloops. This stratum is set to
zero, rather than evaluating completion formulas with a negative exponent.

The third-code geometry at t=2 is unchanged by additional basis extensions:
it applies to the eight-point anchor of rank five before those extensions
are chosen. The resulting positive mu-polynomials remain valid under the
existing mean-floor transfer argument.

## Combine the complementary families

For each girth-four rank stratum, split into supports without a triangular
anchor and supports with one. Add their bounds, then take the smaller of
this sum and the prior full-stratum bound. Other girths retain their full
bounds. Circuits and rank-two components remain included. The main cumulant
probe now uses the resulting full-component envelopes at sizes 15--24.
This is an upper-bound improvement, not admission of these sizes to the
successful budget.

A separate diagnostic restricts girth-four supports to those with no eligible
two-circuit anchor whose row space has two independent balanced norm-four
directions. It removes only those explicitly counted short-code terms;
the positive terms for the other code classes may still overcount them.
Other girths are unchanged. This diagnostic is not substituted for the full
component envelope.

## Result and next obstruction

At h=15 the weighted triangular-family envelope is below 3.06e-4 and the
full residual envelope is below 4.51e7. Both are still too large for the
remaining 2.4692e-12 joint activity/history budget. Large values here are
upper bounds, not lower bounds on actual activity or failure probability.

The diagnostic excluding double-short anchors still has log10 charge about
6.4529. Its largest individual term has rank eight and girth three, with
log10 charge about 6.4424. Significant remaining terms also have girths four
and five. Thus eliminating triangular or double-short anchors alone cannot
make this particular envelope small; three-point circuit strata need their
own sharper counting argument.

`wall1_larger_triangular_components.py` implements the formulas, retains the
size-fourteen rank-five threshold as a regression, and checks the stated
size-fifteen bounds with interval arithmetic. The updated main cumulant
regressions preserve the complete size-fourteen bound. The higher-size
budget, later selected histories and full BKZ proof remain open; these new
counting arguments are not Lean formalized.
