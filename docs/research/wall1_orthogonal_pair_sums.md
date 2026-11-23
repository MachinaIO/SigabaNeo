# Direct orthogonal six-point count and triangle-free diagnostics

Follow-up: [Part 288](wall1_seven_point_codes.md) improves the dominating
seven-point terms and admits the size-fourteen triangle-free remainder.
The failed numerical diagnostic below records the earlier Part 287 bound.

The nine balanced-sign coefficient pairs in Part 283 comprise five triangular
and four orthogonal cases. This note bounds the orthogonal cases directly by
ball intersections, including all modular aliases. The implementation uses
the smaller of this bound and the previous Gaussian bound. The improvement
does not close any of the five residual size-fourteen rank/girth strata.

## Integer count

Let S be the integer N-ball of radius R, N even, and let r(s) count ordered
pairs in S with sum s. Up to coordinate permutations and sign changes the
orthogonal code has rows

```
(1,1,-1,-1,0,0), (1,-1,0,0,1,-1).
```

The real six-point count is therefore
sum_(x,y in S) r(x+y)r(x-y). Symmetry of S identifies differences with sums.
With A=R^2+N/4, the existing shifted-ball argument gives

```
r(s) <= 2 V_N (A-||s||^2/4)_+^(N/2).
```

Apply the arithmetic-geometric mean inequality to the two positive factors,
then the parallelogram identity. Their product is at most

```
4 V_N^2 (A-(||x||^2+||y||^2)/4)_+^N.
```

Dropping the separate constraints x,y in S enlarges the sum to all of Z^(2N).
The half-cube shifted-ball bound in dimension 2N, followed by layer-cake
integration, gives

```
sum_(z in Z^(2N)) (A-||z||^2/4)_+^N
 <= 2 * 4^N * pi^N * N!/(2N)! * (A+N/8)^(2N).
```

Hence the integer count is at most

```
Q_orth = 8 * 4^N * pi^(2N) * N! / ((N/2)!^2 (2N)!)
         * (R^2+3N/8)^(2N).
```

The domain enlargement and the positive-part convention ensure that the
arithmetic-geometric mean step is used only when both original factors are
nonnegative. It does not introduce a negative count outside the ball.

## Nonzero modular layers

For the displayed integer matrix A_0, A_0 A_0^T=4I_2. It maps Z^6 onto Z^2;
for example the third and fifth columns give a unit determinant minor.
The layer A_0 x=qv has squared perpendicular distance q^2||v||^2/4.
A basis of the integer kernel, in the order used for Gaussian summation, is

```
(0,0,1,-1,0,0), (0,0,0,0,1,1),
(1,0,0,1,0,1), (0,1,0,1,0,-1).
```

Its four squared Gram--Schmidt lengths are all two. It is the full integer
kernel: x1,x2,x3,x5 are arbitrary integers and determine x4,x6 integrally.
Iterated shifted Gaussian summation is bounded by theta(2 beta)^4 in each
coordinate, uniformly over each affine layer. Consequently all nonzero
modular layers contribute at most

```
Q_alias = exp(6 beta R^2) theta(2 beta)^(4N)
          * (theta(beta q^2/4)^(2N)-1),
beta = N/(3R^2).
```

Both terms are retained in the production count. At the current parameters
Q_alias/Q_orth is about 10^8.1185: aliases are not negligible relative to this
new real-layer bound. Treating only the zero layer would be invalid.

## Diagnostic exclusion of triangular anchors

The optional `exclude_triangular_anchors=True` argument of `draw14_bounds`
applies only to supports containing no eligible six-position anchor with
augmented rank four and one of the five triangular balanced-sign codes.
Only their explicitly enumerated contribution is removed. The default
continues to bound all supports. Other positive terms may overcount excluded
codes, which remains safe for the restricted family.

The resulting size-fourteen residual transfer is still about 6.8386e-4.
Combining it with the previously admitted classes also fails the target.
Thus neither exclusion of the triangular anchors nor the improved orthogonal
count alone resolves the remaining estimate. The small relative change after
replacing the orthogonal bound shows that those four codes are not the main
source of this particular triangle-free upper envelope. This statement is
about the envelope, not the actual contribution or probability.

No triangle-free residual family is newly admitted to the successful budget
on the basis of this diagnostic. Part 286's five size-fourteen strata, the
larger residual classes and later selected histories remain open.

## Checks

`wall1_orthogonal_pair_sums.py` passes 20 exact finite real/modular comparisons
and four rational Gram--Schmidt checks. `wall1_short_relation_shapes.py`
retains its 41 shape and 15 prior pair-sum checks. The actual-parameter
triangle-free diagnostic is in `wall1_triangle_free_remainder.py`; its upper
envelope is asserted below 0.000684, not below the desired failure budget.
The general formulas remain paper arguments, not Lean proofs.
