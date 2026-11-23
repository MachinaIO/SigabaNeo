# A third relation crossing a triangular anchor

This refinement bounds the size-fourteen triangular-anchor families whose
crossing witness introduces at least three new points, and also all remaining
rank-nine triangular families. Their combined charge fits inside Part 288's
rounded known-transfer bound 5.395e-13. Ranks five through eight with only
two-new-point crossing witnesses, larger components, and later histories
remain open. These are paper arguments with finite/interval checks, not Lean
proofs or a complete draw-14 certificate.

## A crossing fundamental circuit exists

Let T be a connected augmented-input matroid of rank r>4 containing an eligible
six-point triangular anchor A of rank four. Fix a basis B_A of A; for a fixed
signed pair representation, take both points of the first pair and one point
of each remaining pair. Extend it to a basis B of T.

There must be a fundamental circuit D, relative to B, meeting both B_A and
B outside B_A. Otherwise every nonbasis vector has its basis coordinates
entirely in one of these two parts. All vectors then split into two nonempty
sets in complementary spans, contradicting connectedness. A nonbasis point
of A cannot supply a crossing circuit, so the extra point of D is outside A.

Put t=|D outside A| and a=|D intersect A|. Then

```
2 <= t <= r-3,  1 <= a <= 4,  rank(A union D)=t+3.
```

Indeed D outside A consists of its extra point and t-1 points of B outside
B_A. Those t-1 points are independent modulo span(A). The extra point is
dependent on them and the old part, so the rank increment is t-1.
Since the residual family has girth four, t+a>=4 as well.

The counting below uses D intersect A contained in the fixed B_A. It is not
an assertion that every possible third circuit has that property. A valid
witness of this form exists for every basis extension, which suffices for
the covering argument.

## Preserve the old exact count while bounding the new group

Let H_3=G_3+Alias_3 be the full modular equal-pair energy from Part 284.
Apply finite Fourier inversion only to the third relation, whose t new
coefficients are all nonzero. The Fourier transform of the old six-point
count has absolute value at most H_3. Give each new point a Gaussian
majorant with beta=(t-1)N/(2tR^2).

The one-dimensional integer Gaussian Fourier transform F_beta on F_q is
positive by Poisson summation. Holder and the permutations u -> c_i u for
nonzero c_i show

```
q^(-1) sum_u product_(i=1)^t F_beta(c_i u)
 <= q^(-1) sum_u F_beta(u)^t.
```

The right side counts Gaussian integer tuples with sum zero modulo q.
Their zero-layer lattice has squared Gram--Schmidt lengths
2,3/2,...,t/(t-1), and layer qv has squared distance q^2 v^2/t. Uniform
shifted Gaussian summation therefore bounds the new group by

```
J_t = exp(t beta R^2)
      * [product_(j=1)^(t-1) theta(beta (j+1)/j)
         * theta(beta q^2/t)]^N.
```

Thus the joint old/new lifted count is at most H_3 J_t, uniformly over the
nonzero third-relation coefficients. This retains the old ball count instead
of replacing it with a six-point Gaussian bound. It includes every modular
layer. The uniform bound also applies to nonzero targets in the third relation.

## Labelled witness count

Write A_3=H_3/q^(4m) and K_t=J_t/q^(m(t-1)). A triangular anchor can be
specified by choose(h,6) choices of positions, 15 unordered pairings, and
five affine-compatible sign patterns. Choose the t new positions, the a old
basis positions, and the remaining r-t-3 basis positions. A normalized affine
relation on t+a points has at most q^(t+a-2) coefficient choices.

The rank-r, t,a contribution is bounded by

```
choose(h,6) * 75 * choose(h-6,t) * choose(4,a)
 * choose(h-6-t,r-t-3) * q^(t+a-2)
 * A_3 * K_t * mu^(r-t-3)
 * q^((r-1)(h-r-3)) / (r-t-2).
```

The denominator is the genuine minimum number of basis extensions after
contracting A union D: the contraction has rank r-t-3 and no coloops, hence
at least r-t-2 bases. This is the same justified multiplicity principle as
Part 282. Dropping restrictions on completions and overcounting witnesses
only enlarges the bound.

The formula is a positive polynomial in mu of degree r-t-3. With Part 286's
positive transfer coefficients, all normalized monomials decrease with mu,
so the established mean-floor evaluation remains valid.

## Actual-parameter result

At h=14, summing ranks 5,...,9 and all allowed a, t>=3 gives weighted charge

```
< 1.566e-25.
```

The t=2 contribution at rank nine is below 1.484e-24. Together these cover
all rank-nine triangular configurations by the crossing-circuit existence
argument. These estimates include the known-component mixtures through the
linear coefficient L_14 from Part 286.

Add these families to Part 288's admitted baseline. The resulting known
transfer remains below 5.395e-13. The remaining sufficient target stays

```
sum_(h=14)^24 L_h^* U_h + Pr(max_(15..404) b_i>.280) <= 2.4693e-12.
```

Here U_14 may now be restricted to triangular-anchor configurations of ranks
5,...,8 with no eligible >=3-new-point crossing witness. For such a
configuration the constructed crossing witness must have t=2. The formula
for t=2 still fails to give a useful aggregate bound for those ranks; it is
not inserted into the successful budget. The higher-size residual classes
and the later-history probability remain unchanged and unproved.

Validation: `wall1_triangular_third_relation.py` passes 186 fundamental-circuit
checks, 196 exact modular new-group counts with arbitrary targets, the two
new weighted-charge threshold assertions, and the combined known-budget
assertion. No exceptional-event conditioning is used in this refinement.
