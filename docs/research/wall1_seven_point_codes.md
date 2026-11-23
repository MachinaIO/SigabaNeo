# Seven-point shared circuits and the admitted triangle-free remainder

This refinement admits the triangle-free portions of the five remaining
size-fourteen rank/girth strata. Together with the previous admitted classes,
their transfer is below 5.395e-13. Supports containing eligible triangular
six-point anchors, larger residual classes, and later histories remain open.
The derivation below is a paper argument with exact/interval regressions,
not a Lean proof or a complete draw-14 certificate.

## The dominant seven-position codes

In the triangle-free diagnostic, the largest terms have c=4, t=3, and overlap
a=1 or a=3. Their two-dimensional relation code can contain two independent
balanced norm-four words. Full coordinate support forces their four-element
supports to meet in one position. Every mixed projective combination has
weight six or seven, so these are the only two weight-four directions.

Fix the first circuit C and the prescribed second circuit D. Since C has
weight four, it must be one of those two balanced words. If |D|=4, D is the
other word and the shared position is prescribed by C intersect D. If |D|=6,
the shared position is the sole position in C outside D; D is the unique
mixed direction cancelling that coordinate. There are three projective
balanced sign patterns on each four-support, hence exactly nine codes in
either case. No such code has a weight-five direction (overlap a=2).

This replaces the previous generic count (3 choose(7,4))^2=11025 by nine.
The two cases are bounds for different prescribed witnesses; their counts
must not be merged as if they were disjoint configuration classes.

## Direct seven-point integer count

By signs and permutations, write the relations as

```
x0+x1-x2-x3=0,  x0+x4-x5-x6=0.
```

For the integer ball S of radius R in even dimension N, let t(x) be its
ordered triple-sum count. The seven-point count is sum_(x in S) t(x)^2.
The kernel of a three-variable sum has a basis with Gram matrix
[[2,1],[1,2]] in each coordinate, and covolume 3^(N/2). The squared norm of
any point of its basis-coordinate unit cube is at most 3N/2. The standard
half-cube bound for an arbitrary shifted ellipsoid therefore yields

```
t(x) <= 2 pi^N/(N! 3^(N/2))
        * (3R^2+3N/2-||x||^2/3)^N,  x in S.
```

Indeed any three points in S have total squared norm at most 3R^2, while
their perpendicular component forced by their sum x has squared norm
||x||^2/3. Dropping the three separate ball constraints only enlarges the
count. For the half-cube argument, choose the half with nonpositive inner
product against the displacement from the ellipsoid center; the remaining
quadratic contribution is bounded by the stated cube radius.

Set p=N/2, U=R^2+N/4, A=3R^2+19N/12 and B=A-U/3=8R^2/3+3N/2.
Layer-cake summation with the outer shifted-ball count gives

```
sum_(x in S) (3R^2+3N/2-||x||^2/3)^(2N)
 <= 2 V_N p integral_0^U u^(p-1) (A-u/3)^(2N) du.
```

To see the shift, first write the boundary term at R^2 plus the integral
against the ball-counting function. Replace that function by
2 V_N (s+N/4)^p and extend the shifted lower integration endpoint to zero.
Integration by parts gives the displayed expression.

Substitute u=U(1-v) and expand (B+Uv/3)^(2N). All coefficients are positive.
The term of degree j+1 divided by that of degree j, after beta integration,
is (2N-j) U/(3B(p+j+1)). It is at most

```
rho = 2N U/(3B(p+1)) < 1/2.
```

Thus the sum is bounded by its initial term times 1/(1-rho). Squaring the
triple-count bound and combining factors proves the direct integer upper bound

```
Q7 = 8 pi^(5N/2) / ((N!)^2 p! 3^N)
     * U^p B^(2N) / (1-rho).
```

## All nonzero modular layers

Use a weighted quadratic form with weight a=N/(4R^2) on the common point
and b=3N/(8R^2) on the six other points. The integer kernel has squared
Gram--Schmidt lengths 2b, 3b/2, 2b, 3b/2, a+2b/3. Arbitrary integer values
of x0,x1,x2,x4,x5 determine x3,x6, so this is the full integer kernel.

The two-row matrix maps Z^7 onto Z^2. Its weighted inverse row Gram matrix
has smallest eigenvalue ab/(3a+2b). Therefore a layer with right side qv
has weighted squared distance at least q^2 ab ||v||^2/(3a+2b). Let

```
K = theta(2b)^2 theta(3b/2)^2 theta(a+2b/3),
lambda = q^2 ab/(3a+2b).
```

Uniform shifted Gaussian summation bounds all nonzero layers by

```
Q_alias = exp((a+6b)R^2) K^N (theta(lambda)^(2N)-1).
```

The production calculation uses Q7+Q_alias, or the smaller of the previously
valid bounds. It does not neglect aliases. The relation code expressed by
the four- and six-circuit witness is the same modular code, so the count also
applies to overlap three.

## Result and unchanged scope of the goal

After the exact nine-code count and direct bound, the known transfer including
the newly admitted size-fourteen triangle-free strata is

```
0.539475860157221e-12  (rounded upwards), hence <5.395e-13.
```

For comparison, the earlier triangle-free envelope was about 6.84e-4. This
change concerns an upper envelope, not a measured probability. The default
full-class calculation still includes the five triangular six-point codes.

Let U_14 now contain only supports of girth four and ranks 5,...,9 which
contain an eligible triangular six-point anchor of augmented rank four.
Let U_15,...,U_24 retain the previous residual classes. The coefficients L_h^*
from Part 286 do not change, because admitting size-fourteen terms cannot
affect coefficients of degree at most ten. A sufficient remaining condition is

```
sum_(h=14)^24 L_h^* U_h + Pr(max_(15..404) b_i>.280) <= 2.4693e-12.
```

Together with the known 5.395e-13 and reference/error allowance 9.131e-13,
this would fit below 3.922e-12. The condition itself is still unproved.
There is no full draw-14 exit theorem, later-history theorem, or BKZ proof.

Validation: 117 finite code/support checks over fields 5,7,17, 20 modular
seven-point count checks (also checking real counts and nonzero layers),
the existing cumulant regressions, and the actual-parameter interval budget
assertions. Scripts: `wall1_seven_point_codes.py`,
`wall1_triangle_free_remainder.py`, `wall1_factorial_cumulants.py`, and
`wall1_linear_remainder.py`.
