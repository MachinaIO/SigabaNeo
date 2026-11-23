# Cancelling the leading nine-input contribution

A small change to Part 257's square certificate removes its unsuppressed
nine-input correction. At draw 13, the adjusted reference, independent Bernoulli
error, known small-component corrections, and **all nine-input supports** have
explicit bounds. The remaining draw-13 term has exactly ten distinct inputs in
a connected component of rank >=3 and nullity >=2. This is a paper result with
exact finite and interval checks, not a complete BKZ theorem or a Lean proof.

## The adjusted square

Use the polynomials C_j, K_5 and D_5 from Part 257. Set

\[
 H(x;\mu)=K_5(x;\mu)+C_4(x;\mu)/16,\qquad
 H(0;\mu)=D_5(\mu)+\mu^4/16>0.
\]

The pointwise square certificate remains valid. Under X~Poisson(mu), orthogonality
gives exactly

\[
 \mathbb E H(X;\mu)^2=D_5(\mu)+7\mu^4/32.                 \tag{1}
\]

Indeed the C_4 coefficient of K_5 is 1/24, and E[C_4^2]=24 mu^4.
The cross term contributes mu^4/8 and the new square contributes 3 mu^4/32.
We may use H(0)^2>=mu^10/(5!)^2. This yields a reference bound that is a sum
of negative powers of mu and is valid at the existing lower count.

Expand H(mu+z;mu)^2=sum_(j=0)^10 c_j(mu) z^j. Its two leading coefficients are

\[
             c_{10}=1/14400,\qquad c_9=-45c_{10}.          \tag{2}
\]

They are independent of mu. For example, C_5(mu+z) has leading terms z^5-10z^4,
and C_4(mu+z) has leading term z^4. Hence H has leading coefficients -1/120 and
3/16, proving (2). All other coefficients are explicit rational polynomials in mu
of degree at most 10-j, constructed exactly by the verifier.

The factorial-basis coefficients of H have the same alternating sign as those
of K_5: the added coefficient at degree l is (1/16) binomial(4,l)(-mu)^(4-l).
Their absolute values are polynomials with nonnegative coefficients. Part 257's
independent Bernoulli correction therefore transfers with the same negative-power
argument and the same upper bound on the largest fiber density rho_max.

## Exact cancellation for nine distinct inputs

Write X_y=J_y-rho_y. For a nine-input support T, put
W_T=E product_(y in T) X_y. Only orders nine and ten of the polynomial expansion
can have exactly this support. Their combined contribution is

\[
 9!\,c_{10}\left[-45W_T+5\sum_{y\in T}
                   \mathbb E X_y^2\prod_{z\ne y}X_z\right].
\]

Use the pointwise Bernoulli identity

\[
                   X_y^2=(1-2\rho_y)X_y+\rho_y(1-\rho_y).
\]

The bracket becomes

\[
 -10\left(\sum_{y\in T}\rho_y\right)W_T
       +5\sum_{y\in T}\rho_y(1-\rho_y)W_{T\setminus\{y\}}.     \tag{3}
\]

This is an exact identity for the dependent affine law. No output independence
is used. The independent-model products for the distinct supports of sizes eight
and nine are zero, so (3) is also their actual-minus-independent correction.
The constant multiple of W_T has disappeared; its coefficient now carries a
small density factor.

Let A_j be the sum of |W_T| over ordered j-tuples of distinct inputs. After
summing (3) over supports, the absolute contribution from all nine-input supports
is at most

\[
             c_{10}\bigl(90\rho_{\max}A_9+45\mu A_8\bigr).    \tag{4}
\]

For the second term, fix the ordered eight remaining inputs, sum the omitted
input's density over all possibilities, and bound it by mu. There are nine
positions for that omitted input, giving 5*9=45. Restrictions excluding repeated
inputs can be dropped in this nonnegative sum.

The existing component bound B_j on the sum of absolute tuple corrections in
the full j-th central moment bounds A_j as well. Use Part 256's size-eight
activities for B_8 and its size-nine activities for B_9. Even though the latter
majorant was too large when transferred directly in Part 257, its multiplier
rho_max in (4) is now tiny. Finally c_10/H(0)^2<=mu^(-10), so the normalized
upper bound is

\[
           (90\rho_{\max}B_9+45\mu B_8)/(\rho\mu^{10}).       \tag{5}
\]

All powers of mu after expanding the existing nonnegative activity bounds are
negative, including the additional mu multiplying B_8. Using the lower candidate
count is therefore valid.

## Numerical scope and the final remaining draw-13 class

At draw 13, q=3329, with rho=0.280, outward 80-digit interval arithmetic gives:

- reference term from (1), normalized by rho H(0)^2: <2.390e-12;
- independent Bernoulli correction: <2.597e-293;
- previously controlled components through size eight, plus all circuit/rank-two
  components, transferred using the new exact coefficients: <4.950e-22;
- all nine-input supports via (5): <3.210e-22.

The classes in the last two bounds may overlap; summing nonnegative bounds is
still valid. A ten-input support containing a nine-input component and one coloop
contributes zero: at degree ten each input appears once and the coloop's centered
mean vanishes. Thus no additional nine-component case is hidden at degree ten.

Let Delta_10 be the signed sum of W_T over ordered ten-input supports which are
connected and have rank >=3 and nullity >=2. The whole remaining statement is

\[
 \Pr(b_{13}>0.280)
       \le2.391\cdot10^{-12}
             +\frac{|\Delta_{10}|}{14400\cdot0.280\,H(0;\mu)^2}.   \tag{6}
\]

Delta_10 is not bounded here. Its single-circuit/rank-extension majorant remains
too large; a joint-constraint estimate is still needed. Draws 14--404 and the
selected-projection problem are also unchanged. In particular (6) is not a
numerical bound for the full draw-13 failure probability.

## Verification

Run `python3 docs/research/scripts/wall1_affine_nine_cancellation.py`.
It constructs the centered polynomial over the rationals, verifies (1)--(2), the
pointwise certificate, and (3) on nine distinct inputs in F_3^2 with nonuniform
output fibers, using all 27 affine maps. There are 84 exact checks. The script
then checks all four displayed numerical bounds by outward intervals. The shared
polynomial helpers retain the unmodified certificate as their default; its
original verifier is also rerun. These checks support the paper proof, not a
Lean formalization or a simulation of the selected width-506 process.
