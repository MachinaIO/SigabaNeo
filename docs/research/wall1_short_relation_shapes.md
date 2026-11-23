# Short relation shapes and direct pair-sum counting

This paper refinement bounds the draw-14 full-incidence cumulant transfer through
size thirteen by 2.175e-13. It separates a finite collection of very short
relation codes from the other codes and directly counts the dominant
six-point shape. Components of size 14--24, mixtures involving them, later
selected histories and the remaining BKZ conditions are still open.
This is not a complete draw-14 bound or a Lean proof.

## General short-plane bounds

Use the two-row relation code C of an eligible H-point anchor from Parts 278--282.
It has full coordinate support, minimum Hamming weight c>=3, and coordinate sum
zero. Let alpha=pi^2/(beta q^2), q=3329.

Part 282's argument with cutoff L=14 applies in every anchor dimension H<=24.
Three independent short integer representatives would have an integer minor
divisible by q and volume at least q, contradicting L^3<q. Their coordinate sums
are zero since sqrt(H)L<q. Saturation preserves reduction into C because the
index is at most L^2<q. If the short span has dimension two, its saturated
lattice reduces onto the entire code; hence a lattice basis cannot have a
common zero coordinate.

For a reduced basis, the first squared norm is even and at least four. If no
norm-four word exists, it is at least six and the perpendicular squared height
is at least 9/2. Thus the short sum is bounded by theta(6 alpha)theta((9/2)alpha).
For girth c>=5 the stronger pair is theta(s alpha)theta((3s/4)alpha), where
s=2 ceil(c/2).

If a norm-four word exists, fix such a vector of length two. Now any two other
vectors of length at most L'=40 have three-volume with it at most 2(L')^2<q.
Consequently all words of length at most 40 lie in a real plane. The saturation
index is at most 2L'<q, and coordinate sums still vanish. If there is no second
independent norm-four word, the reduced Gram argument of Part 282 bounds this
plane by theta(4 alpha)theta(5 alpha).

For either cutoff, a convenient tail estimate is

\[
 \sum_{\|v\|>L}e^{-\alpha\|v\|^2}
 \le e^{-\alpha L^2/2}\theta(p\alpha/2)^2,\qquad
                       p=\min(H/2,c).                       \tag{1}
\]

Indeed no projective column direction has multiplicity greater than H-c.
The pair-cover Holder argument from Part 278 gives
S_C(alpha/2)<=theta(p alpha/2)^2. Remaining columns, when H>2c, are bounded by
one. This estimate does not require a wrapping correction: the two independent
linear forms are summed exactly over the finite field before extending each
one-dimensional Gaussian sum to all integers.

To pass to F_beta, multiply the code bound by T_beta^H/q^2 and add
T_beta^H sum_(j=1)^H binomial(H,j) delta^j, using the same positive Fourier
majorant and periodic-tail delta as in Part 261. Thus neither cutoff discards
long codewords or periodic terms.

## Counting codes containing norm-four words

A norm-four word here has four entries in {1,-1}, with two of each sign. There
are exactly

\[
                            K_H=3{H\choose4}
\]

projective such words. For fixed circuit positions C_0,D_0 of sizes c,d=t+a,
the old normalized coefficient-pair count is Q=q^(c+d-4).

Pairs whose code contains at least one norm-four word have the upper count

\[
 N_1=\min\left(Q,\ \mathbf1_{c=4}3q^{d-2}+K_Hq^{c-2}\right).  \tag{2}
\]

The first term covers a short first circuit. Otherwise a short word independent
of that circuit determines the code together with its first circuit row.
For a given code, a prescribed proper circuit support determines at most one
projective relation: it must annihilate a nonzero column outside that support.
Consequently the second row introduces no further coefficient choices in this
count. Using (2) for the class with exactly one short direction is safe even
though it can also overcount codes with several short directions.

If two independent norm-four words exist, they span the code, so K_H^2 is an
upper count independent of q. Full coordinate support forces their supports to
cover all H coordinates; in particular H<=8. The following exclusions and
refinements are used in the verifier.

- H=4: two distinct balanced sign rows give a weight-two combination, impossible.
- H=5: their overlap has size three. Absence of weight-two words forces reduced
  inner product of absolute value one, and the code has exactly one weight-three
  direction. Thus c=4 is impossible, as is c=3,d=3.
- H>=6: a mixed combination of the two short words has weight at least 2H-8.
  Together with their own weight four, this rules out c=3.
- H=7: mixed words have weight six or seven, so a five-circuit is impossible.
- H=8: the two supports are disjoint, and the only minimal relations are those
  two disjoint words. This cannot be the union of the overlapping circuit
  witnesses used here.
- H>8 is impossible by full coordinate support.

In the six-column c=4,a=2 case, every weight-four direction in a code generated
by two norm-four words itself has a norm-four representative. The exclusive
coordinate pairs give two projective column classes; the shared pair either
gives one further class or two singletons. These are all possible weight-four
directions. Hence both prescribed circuit rows are balanced sign rows. There
are only 3*3=9 normalized row pairs. Five have inner product of absolute value
two; four have inner product zero.

For the remaining multiple-short-word cases, the reduced basis has squared
lengths 4,4 and squared perpendicular height 15/4 in dimension five or seven,
and at least 3 in dimension six. These follow directly from support overlap
and integer inner products. The cutoff-40 tail in (1) completes their bound.

Combining the three classes uses a positive sum of Gaussian powers, not the
power of an average Gaussian bound:
N_multiple U_multiple^N + N_1 U_one^N + Q U_none^N.
Overcounting in (2) or using Q for the last class only enlarges the result.
The smaller of this valid count and the older count can be selected.

## The five triangular codes are equal-pair-sum configurations

By permuting coordinates and changing individual column signs, any of the five
inner-product-two sign codes becomes the equations

\[
                  x_1+x_2=x_3+x_4=x_5+x_6\pmod q.           \tag{3}
\]

These operations preserve counts in the centrally symmetric candidate ball.
For an upper bound drop the coordinate clipping and use all integer points
S_R in the N-dimensional radius-R ball. Let r(s) count pairs x,y in S_R with
x+y=s over the integers. The exact zero-layer contribution is sum_s r(s)^3.

For any shifted integer ball of squared radius u>=0,

\[
             \#((z+\mathbb Z^N)\cap B_{\sqrt u})
                                  \le2V_N(u+N/4)^{N/2}.      \tag{4}
\]

To prove (4), take the disjoint unit cubes about the counted points. At least
half of each cube has displacement with nonpositive scalar product against
the vector from the ball center. That half lies in the enlarged ball of squared
radius u+N/4. The argument works for arbitrary centers, including s/2.

The parallelogram identity implies

\[
 r(s)\le2V_N\left(R^2+N/4-\|s\|^2/4\right)_+^{N/2}.
\]

Put A=R^2+N/4, a=N/2, b=3N/2. Layer-cake summation and (4) bound the remaining
sum by
2 V_N 2^N b integral_0^A (A-u)^(b-1)(u+N/16)^a du.
Shift the variable by N/16 and enlarge the interval to start at zero.
Multiplying by (2V_N)^3 gives, for even N,

\[
 \sum_s r(s)^3\le
 16\,2^N\pi^{2N}
 \frac{(3N/2)!}{((N/2)!)^3(2N)!}
                       (R^2+5N/16)^{2N}.                   \tag{5}
\]

This direct intersection count retains a polynomial prefactor lost by the
Gaussian exponential bound.

## Modular layers and the four orthogonal codes

For (3), use rows (1,1,-1,-1,0,0) and (0,0,1,1,-1,-1).
The integer kernel has basis given by the three pair differences and
(1,0,1,0,1,0); its squared Gram--Schmidt lengths are 2,2,2,3/2.
A layer with right side q(u,v) has squared perpendicular distance
q^2(u^2+uv+v^2)/3. Shifted Gaussian summation and
u^2+uv+v^2>=(u^2+v^2)/2 therefore bound all nonzero modular layers by

\[
 e^{6\beta R^2}
 [\theta(2\beta)^3\theta((3/2)\beta)]^N
                    [\theta(\beta q^2/6)^{2N}-1].           \tag{6}
\]

The subtraction removes the zero layer from the sum of layerwise upper bounds;
it does not subtract one upper estimate from another estimate of the true count.
Use beta=N/(3R^2), and add (6) to (5).

For each of the four orthogonal sign codes, the two short rows form a primitive
integer basis of their real plane: an exclusive-coordinate two-by-two minor is
one. Their squared lengths are 4,4 and their inner product is zero. A centered
codeword outside that plane has distance at least q/4, since adjoining it gives
a nonzero three-minor divisible by q. Its Fourier Gaussian count is consequently
bounded by

\[
 T_\beta^6\left[
 \frac{\theta(4\alpha)^2+
 e^{-\alpha q^2/32}\theta(p\alpha/2)^2}{q^2}
                         +\sum_{j=1}^6{6\choose j}\delta^j\right]. \tag{7}
\]

For the nine-code contribution use five copies of (5)+(6) and four copies of
the N-coordinate Gaussian count from (7). The probability q^(-4m), position
counts and Part 282's multiplicity divisors are applied afterwards, exactly
as for the earlier anchor counts. Invalid-rank tuples are only added to an
upper count, not assigned a rank-four probability in the original model.

## Actual draw-14 result and remaining obligation

The resulting cumulant transfers from all circuits/rank-two components and
other components through cutoffs eleven, twelve and thirteen are respectively

\[
                 <2.195\,10^{-45},\qquad
                 <4.247\,10^{-30},\qquad
                 <2.175\,10^{-13}.                          \tag{8}
\]

All are outward interval evaluations at q=3329, N=518, m=400. Known Gaussian
terms retain their old mu degrees; the new direct pair-sum bound is independent
of mu. Thus the lower-mean substitutions remain justified termwise.

Let B contain the admitted activity bounds through size thirteen, together with
the already bounded circuits/rank-two components at every size. Let U contain
the omitted size-14--24 components, and put M=C(B+U)-C(B).
A sufficient remaining history condition is

\[
                 M+\Pr(\max_{15\le i\le404}b_i>0.280)
                                             \le2.7913\,10^{-12}. \tag{9}
\]

Then C(F)<=3.0088e-12, so Part 281's incidence-cap and cumulant-error implications
apply, giving conditionally

\[
                         \Pr(b_{14}>0.280)<1.1306\,10^{-12}+M. \tag{10}
\]

The constants sum to 3.9219e-12. Neither M nor the later-history term is bounded
here. The current size-fourteen envelope is still unusable. Equation (8) alone
must not be reported as a failure-probability bound or as completion of BKZ.

## Verification

Run python3 docs/research/scripts/wall1_short_relation_shapes.py.
It checks 41 full-support short-plane shapes, the exact five/four sign-code
split, and 15 independently enumerated integer pair-sum counts against the
volume and modular-layer bounds. The codeword classification is supported by
the general arguments above, not just these finite cases.

Run python3 docs/research/scripts/wall1_factorial_cumulants.py for the actual
interval bounds, 240 exact transfer identities and 1866 connected/error checks.
Part 282's basis and unique-direction checks remain applicable. No independent
audit or Lean formalization of these new geometric deductions is claimed.
