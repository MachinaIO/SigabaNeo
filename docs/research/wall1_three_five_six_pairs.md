# Five-position two-six planes with prescribed supports

This is an exact finite-dimensional classification, not a proof of BKZ success.
Fix C={0,1,2}, S={0,1,3,4}, and a prime q>=7. Consider a balanced
rank-two coefficient code on all five positions that contains two independent
balanced integer rows of squared norm six. Its girth is three, and we restrict
to the no-norm-four family. At q=3329 there are exactly eight normalized charts:
four with Gram determinant 32 and four with determinant 35. Their squared
Gram--Schmidt lengths are respectively (6,16/3) and (6,35/6).

## Completeness and hand count

A balanced integer row of squared norm six in five positions necessarily has
three nonzero coordinates, with values (2,-1,-1) up to overall sign. Indeed,
the only other possible partition of six into nonzero squares is six ones,
which needs six positions; a single four and two ones must balance as stated.
There are 3*binomial(5,3)=30 unoriented lines.

For two such independent rows a,b spanning a full-support five-position code,
their supports intersect in exactly one position. The projective classes of
the five columns (a_i,b_i) have multiplicities 2,2,1: the two positions
exclusive to a, the two exclusive to b, and the shared position. These are
three distinct classes over every field of characteristic at least seven.
A nonzero linear combination can therefore vanish on at most two positions.
Its support has size three exactly when it is a scalar multiple of a or b.
Consequently the prescribed support C must be the support of one of the two
norm-six rows; rename that row a.

Write supp(b)={j,3,4}, with j in C. A combination with support S must have a
nonzero coefficient of b. If j!=2, vanishing at position 2 forces the
coefficient of a to be zero, and the resulting support is only supp(b), not
S. Thus j=2. Conversely, if j=2, cancellation at position 2 leaves all four
positions 0,1,3,4 nonzero. Every required plane therefore has generators
supported on C and B={2,3,4}.

Choose the representative of each generator with one coefficient +2 and the
other two coefficients -1. Let i in C be the +2 position of a, and k in B
that of b. There are nine choices. Their scalar product is a_2*b_2:

| Condition | Number | absolute scalar product | Gram determinant |
|---|---:|---:|---:|
| i=k=2 | 1 | 4 | 20 |
| Exactly one of i,k equals 2 | 4 | 2 | 32 |
| Neither equals 2 | 4 | 1 | 35 |

In the first case a-b has squared norm four, so it is excluded. Each other
case has girth exactly three. Distinct choices give distinct planes: each
plane has a unique line of support C and a unique line of support B, and
those lines recover i,k because 2!=-1 in the field. The chart normalization
is f_0=1 for the C row and v_0=0,v_3=1 for its independent complement. Hence
counting planes counts exactly the charts used in the coefficient sum.

## Saturation, minimum and Gram--Schmidt bounds

Each row has an exclusive position whose coefficient has absolute value one.
Taking one such position from each row gives a 2-by-2 minor of determinant
+/-1. Therefore Za+Zb is saturated in its rational span: the coordinates of
any integer vector ua+vb at these two positions force u,v to be integers.
This applies to all nine configurations, including the excluded one.

For either retained determinant, |<a,b>|<=2. If integers u,v are both nonzero,

    ||ua+vb||^2 = 6u^2+6v^2+2uv<a,b>
               >= 4(u^2+v^2) >= 8.

If only one coefficient is nonzero, the norm
squared is at least six. Thus this saturated lattice has first and second
successive minima squared equal to six, no norm-four vector, and a,b are
Gauss reduced. Orthogonalization gives squared lengths 6 and D/6 exactly.
In particular there is no unproved passage from a nonsaturated basis to a
larger planar integer lattice.

For q=3329 this also excludes a balanced norm-four vector in the modular
preimage. At the two exclusive unit positions, lift its coefficients u,v as
integers with absolute values at most two. The discrepancy between that
vector and ua+vb is coordinatewise at most 10, hence cannot be a nonzero
multiple of 3329. It would therefore be a norm-four vector of the saturated
plane, which was just excluded. The script additionally checks all fifteen
balanced norm-four lines directly for q=7,17,3329. This assertion does not
identify the whole modular preimage with the planar lattice; periodic
contributions in the existing theta estimate must still be retained.

## Integration formula

For c=3,t=2,overlap=2,H=5, the unrestricted coefficient-chart count is
Q=q^(c+t+overlap-4)=q^3. Let K(x,y) denote the existing `no_four_plane(x,y,tail)`
upper bound including its current short-vector remainder and periodic-plane
term. Replace the old two-six contribution by the smaller of itself and

    (4*K(6,16/3)^N + 4*K(6,35/6)^N)/q^3.

No one-six or no-six term is changed by this classification, and their counts
must retain their existing coverage. Keeping the old other-family weights
can overcount the total but remains a valid upper bound. This is a refinement
of the already isolated two-six family, not a replacement for the full
coefficient count or for the q-periodic tail.

## Reproducible exact check

Run `python docs/research/scripts/wall1_three_five_six_pairs.py`.
The script independently enumerates all 435 unordered pairs of the thirty
unoriented norm-six lines; 135 pairs have full support. It checks support
elimination, unit minors, column-class multiplicities, chart deduplication,
and exclusion of every balanced norm-four line in the modular preimage.

```
norm-six lines: 30 full-support pairs: 135 determinants: {20: 15, 32: 60, 35: 60}
q=7: no-four charts={32: 4, 35: 4}; excluded norm-four charts=1; GS squared lengths=(6,16/3) or (6,35/6)
q=17: no-four charts={32: 4, 35: 4}; excluded norm-four charts=1; GS squared lengths=(6,16/3) or (6,35/6)
q=3329: no-four charts={32: 4, 35: 4}; excluded norm-four charts=1; GS squared lengths=(6,16/3) or (6,35/6)
```

These checks and the counting proof establish this local classification only.
They leave larger supports, global probability accumulation and the adaptive
BKZ bridge to their separate arguments.

## Production integration and diagnostic correction

The counted kernel is integrated in `wall1_general_two_relations.py`, keeping
the old complete bound as a fallback. The full 2106 cumulant regression checks
pass (`/tmp/wall1_h5_parallel_cumulants.log`); the complete component run is
`/tmp/wall1_h5_parallel_components.log`. Size17 retains log10 upper envelope
-9.239618750774848 at displayed precision, and the through24 transfer remains
about 7.03e226. These are bounds, not observed failure probabilities.

The initial targeting diagnosis was incomplete: two-six dominates the
**no-four subfamily**, but the full H5 anchor is dominated by one-four.
After this change, log10(no-four/selected) is -37.3224332042. The full anchor
selects the split, and the enclosing rank8/girth3 stratum selects the two-relation
cover; neither minimum is hiding the change. Instead, its relative contribution
is only about 4.76e-38. Thus the next local target is the one-four family, not
further optimization of this already tiny subfamily. The independent diagnostic
is `/tmp/three_h5_mask_diagnostic.py` with the corresponding `.log` file.
