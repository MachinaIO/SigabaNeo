# Exact selected pair collision evaluation

[Partial-gate certificates](wall1_partial_pair_certificate.md) extend this
evaluator to incomplete exclusions, retaining zero-anchor subtractions and
bounding the remaining weighted events.

The [full-family variance obligation](wall1_full_family_variance.md) now has
an evaluator using the existing mixed full/quotient incidence machinery.
It computes exact finite selected-gate moments, not a production upper bound.

## Fixed-stratum identity

Fix geometry, quotient order h>1, and A candidate points. Let Q_E(C) be
the unconditional probability of the fixed stratum, exact old-history gate E,
and quotient constraints C. Full chronological membership exclusions and
quotient old-minimum exclusions remain separate in its signed state expansion.
The base stratum mass is already included and must not be multiplied twice.

Assume Q_E({x})=0 for each candidate x. For ordered distinct points x,y,
simultaneous height-one hits require lambda(x−y)=0 and determine the unique
nonzero fresh mark lambda(x). Their joint mass is Q_E({x−y})/h.
Group the differences by their finite-field span l, with ordered-pair
multiplicity w_l. Retain the zero span when distinct points have equal residues.

    M0 = (h−1) Q_E(empty)/h,
    M1 = A Q_E(empty)/h,
    M2 = sum_l w_l Q_E(l)/h,
    mu = A/(h−1),
    E[1_E 1_{U!=0}(Z−mu)²] = M2+M1−M0 mu².

`selected_pair_moments` in the accompanying script evaluates these expressions,
checks the nonzero-label hypothesis, and caches grouped incidence queries.
It trusts that the supplied states encode an exact gate. Candidate families
must be fixed within each stratum; different geometries require separate
strata. Constructing and summing all production selected-history strata
remains unresolved. No unselected uniform-map law is substituted.

## Complete geometric fixtures

Take q=5, K=Z³, lambda(x)=(x_1−a_1 x_3,x_2−a_2 x_3) modulo 5.
Exclude all 26 nonzero integer vectors of squared norm at most 3 from the
old lattice: this is the complete old-minimum test at c²=7/2. The candidates
are all 18 nonzero vectors of squared norm at most 2, whose height-one lifts
have squared norm at most 3<7/2. Add the full exclusion (2,1,1).

A second fixture has one fixed image direction E=span(1,0,0,0), the same
projected quotient geometry, and full exclusion (0,2,1,1). This exclusion
also involves the image component of the map. The extra full exclusions
are explicit algebraic gates, not demonstrated chronological BKZ histories.

Each fixture reduces 306 ordered pairs to 31 constraints. Exact incidence
results agree with all map/nonzero-mark pairs (25*24 and 125*24 before gating).

| Fixed image dimension | Gate mass | M2 | Centered second moment |
|---|---:|---:|---:|
| 0 | 3/5 | 76/625 | 287/1250 |
| 1 | 79/125 | 396/3125 | 1503/6250 |

Replacing Q_E(l) by Q_E(empty) times the unselected incidence instead gives
M2=126/625 and 3318/15625. Although these totals overestimate the correct
ones, individual collision probabilities increase after the gate for 15
and 16 of the grouped constraints. Therefore an entrywise claim that an
old-minimum exclusion suppresses every collision is false in these fixtures.
The production weighted aggregate still needs its own estimate.

## Verification

Run `python3 docs/research/scripts/wall1_selected_pair_collision.py`.
Exact rational enumeration and an independent mathematical audit verify the
identities, mixed-gate distinction, and geometric vector-list completeness.
No production selected-history bound or Lean theorem is claimed.

The [selected multiheight Gram evaluator](wall1_selected_height_gram.md)
retains the same mixed gates for unequal candidate families at several signed
heights, including their shared-mark cross moments and zero-label corrections.
