# Alternative certificate route: an exact discrete moment barrier

This investigates avoiding the size 18--24 component problem by changing the
void certificate, rather than classifying more short relation planes. It does
not modify the production envelope or complete a BKZ probability bound.

The parameter used here is the exact rational reference mean
`mu0 = 58.15006220912`, with `rho = 0.280`. This is the conservative rounded
mean floor used in the draw-14 analysis. It is not an assertion that the
actual affine count has precisely this mean, or has the Poisson law.

## A certificate beyond squares

For positive integers a_1,...,a_t whose adjacent pairs are disjoint, define

    P(x) = product_i ((x-a_i)(x-a_i-1)/(a_i(a_i+1))).

Every factor is nonnegative for integer x, including integers between the two
roots (there are none). Consequently P(0)=1 and P(x)>=0 on the nonnegative
integers: `1_{x=0} <= P(x)`. This is a degree 2t certificate; it need not be a
square over the reals. The code expands it exactly in the falling factorial
basis. If `P(x)=sum_h f_h (x)_h`, its Poisson expectation is exactly
`sum_h f_h mu0^h`.

The script uses approximate Jacobi eigenvalues only to choose candidate
integer pairs. All certificate expectations, all comparison decisions, and
all subsequent optimality checks are exact rational arithmetic. A numerical
root computation is therefore not a premise of the proof.

## Exact optimality among all integer-nonnegative polynomials

Let S consist of 0 and the 2t roots of P. For s in S let

    ell_s(x) = product_{u in S, u != s} (x-u)/(s-u),
    w_s = E_{Poisson(mu0)} ell_s(X).

Lagrange interpolation implies for every polynomial Q of degree at most 2t,

    E Q(X) = sum_{s in S} w_s Q(s).

The script computes every w_s as an exact rational and verifies all 2t+1
falling-factorial moment identities, including total mass one. In each row
below every weight is positive. Thus, if Q is nonnegative on the nonnegative
integers and Q(0)>=1, its expectation is at least w_0. The constructed P
achieves equality because it vanishes at all the other nodes. This proves
*global* optimality over that full class of polynomials, not merely over
squares or over the root-pair family.

| Degree | Optimal E[P]/rho | Best square E[P]/rho | Below 3.922e-12? |
| --- | ---: | ---: | --- |
| 16 | 9.239871568658132e-10 | 9.528011011492361e-10 | no |
| 18 | 1.407157201234634e-10 | 1.446006334604108e-10 | no |
| 20 | 2.372267426391858e-11 | 2.437431958870082e-11 | no |
| 22 | 4.365318302163839e-12 | 4.517709260819960e-12 | no |
| 24 | 8.792497949410801e-13 | 9.130971510952572e-13 | yes, reference only |

Displayed decimals are rounded renderings of rational values. The target
comparisons themselves are exact. The degree-22 pair starts are
`27,34,41,48,55,62,69,77,85,95,106`; degree 24 uses
`25,32,39,46,52,59,66,73,81,89,98,110`.

### Odd degrees do not avoid the barrier

The same optimum holds through degree 2t+1. Indeed, let
R(x)=product_(s in S)(x-s)=x*product_i(x-a_i)(x-a_i-1).
This is nonnegative at every nonnegative integer. For any polynomial Q of
degree at most 2t+1, interpolation at S gives Q=I_Q+cR, where I_Q has degree
at most 2t and c is the coefficient of x^(2t+1) in Q. If Q is nonnegative
on all nonnegative integers, c>=0: a negative leading odd coefficient would
make Q negative for all sufficiently large integers; if its degree is smaller,
c=0. Hence

    E Q = sum_s w_s Q(s) + c E R >= w_0.

The even polynomial P still attains w_0. The script verifies E R>0 and the
exact degree-(2t+1) factorial-moment interpolation defect for every row.
Thus **degree23 has the same optimal value as degree22**, and degree25 the
same value as degree24, at this reference mean. No positive quadrature
matching the extra odd moment is being asserted.

In particular, this rules out eliminating size24 by a degree-at-most-23
nonnegative polynomial **within the Poisson-reference, mean-floor strategy**,
even before paying a nonnegative dependence-error charge. It does not rule
out using a sharper actual mean, signed dependence cancellations, rational or
non-polynomial certificates, a different event decomposition, or direct
bounds on the dependent law. It is not a lower bound on the actual failure
probability.

## Transfer weights and the remaining obstruction

For any fixed polynomial P and Poisson reference mean mu, its exact transfer
weight at order j is

    W_j = E Delta^j P(X)
        = sum_{h>=j} f_h h!/(h-j)! mu^(h-j).

The factorial-cumulant identity therefore transfers cumulant corrections
through degree 24 using these W_j. The script prints every exact f_h and W_j
for the degree-24 candidate, and compares `abs(W_j)/rho` with the production
positive difference majorant at the same mu0 and its conservative normalizer
`(12!)^2/(rho*mu0^24)`.

All new W_j for 3<=j<=24 are positive at mu0. Representative ratios are

| j | New absolute weight / production majorant |
| --- | ---: |
| 3 | 0.2193178359 |
| 13 | 0.6141243388 |
| 16 | 0.6256603761 |
| 17 | 0.6309053378 |
| 18 | 0.6340876249 |
| 22 | 0.6498822737 |
| 24 | 0.6571775673 |

For all 17<=j<=24 the ratio is between 0.6309 and 0.6572. Thus applying the
new weights to the *same* nonnegative correction series cannot remove more
than a small constant factor from its high-order contribution. This statement
also covers mixtures with admitted components, since they are positive sums
of these weights. At order 24 the ratio is exactly the last displayed ratio.
The degree-24 reference baseline improves by only about 3.7%.

The Part 384 component snapshot gives the following weighted upper envelopes.
These are upper-bound values, not probabilities or lower bounds on activities.
They are included as a dated diagnostic; the new script does not recompute
the expensive production classification.

| Component size | log10 existing weighted envelope | Orders above entire 2.6629e-12 residual allocation |
| --- | ---: | ---: |
| 18 | 17.33355 | 28.90819 |
| 19 | 51.23412 | 62.80877 |
| 20 | 85.23859 | 96.81323 |
| 21 | 119.06137 | 130.63601 |
| 22 | 153.08356 | 164.65821 |
| 23 | 189.80061 | 201.37525 |
| 24 | 226.84695 | 238.42159 |

A factor around 0.65 does not make these envelopes useful. In particular the
size-24 diagnostic remains around 10^226.665 with the new reference weights.
This is a completed negative test of this alternative, not a reason to
conclude that the desired probability bound is false.

No production improvement is asserted: applying a polynomial chosen at mu0
to all possible actual means needs a separate uniform mean argument. The
new fixed polynomial's expectation cannot simply be evaluated at a lower
mean and called an upper bound. The current calculation is an exact
single-reference comparison and an exact discrete polynomial optimality
certificate. Nothing here supplies the selected-history BKZ bridge.

## Reproduction

    python3 docs/research/scripts/wall1_global_remainder_alternative.py

Observed log: `/tmp/wall1_global_remainder_alternative.log`. All five positive
quadratures and their 105 exact factorial-moment identities pass, as do the
exact target comparisons. The full rational coefficients and difference
weights are present in that log. No Lean formalization or production files
were changed.
