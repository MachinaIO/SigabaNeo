# Input-only completion temperature with a fixed anchor temperature

For H=13, augmented rank r=11, six dependent input positions, input dimension
118, output dimension400 and radius2933, a positive completion temperature
safely improves the zero-temperature q^60 cap by only 0.07777065 decimal
orders. Its globally optimized bound is worse than the existing volume
completion bound by 0.76888104 orders at the same radius. Thus this universal
pivot-Gaussian route supplies no production improvement. At the actual production radius the corresponding figures are 0.07713567
orders saved against q^60 and 0.76563381 orders worse than the existing cap.
Anchor temperature and all output constraints are left unchanged.

## A universal Gaussian bound by pivot injection

Fix any valid spanning anchor A. Its affine input span U has dimension d=10.
Choose d input coordinate functionals that are independent on the direction
space of U. Projection to them is a bijection U -> F_q^d, including affine
translates. Centered coordinate projection cannot increase squared norm, so
for every beta>=0,

    sum_(y in U) exp(-beta ||[y]||^2) <= theta_q(beta)^d,
    theta_q(beta)=sum_(j=-(q-1)/2)^((q-1)/2) exp(-beta j^2).

This is a finite sum: there is no omitted tail. Equality holds for the
coordinate d-plane through zero. For six ordered input-ball completions,
allowing repetitions and already-used inputs only enlarges the count. The
complete Chernoff bound is therefore

    [exp(beta_new R^2) theta_q(beta_new)^10]^6.             (1)

The exponential ball-majorant factor cannot be dropped. The beta_new=0
limit is exactly q^(10*6), the existing dependent-coordinate chart count.
Each affine point has q^10 coefficient choices in a fixed affine basis;
(1) replaces their sum, and does not multiply an additional q^60 onto it.

The pivot projection depends on the anchor, which causes no problem: (1)
is pointwise on every valid fixed anchor and can be multiplied by any
nonnegative anchor incidence weight. Sum those weights afterward, or then
apply their original Gaussian upper bound at the unchanged beta_anchor.
This preserves the existing rank normalization q^(-400*11). It introduces
neither an output probability q^(-400*6) nor output-ball constraints at the
new positions. The exact input/output factorization of the nineteen-point
mixed-fiber model remains as in `wall1_independent_map_energy.md`.

In particular, 518 is not a valid coordinate exponent for new-point weights.
There are only118 input coordinates, and after pivot injection only10 free
input coordinates per completed point remain. The other108 input weights
were dropped by a valid inequality; no additional output coordinates exist
for these completions. Applying a scalar improvement independently518 times
would bound a different event.

## Global one-variable optimization

Let t=q^2 beta_new and

    f(t)=t R^2/q^2 + d log(sum_j exp(-t j^2/q^2)).

Then f'(t)=R^2/q^2-d E_t[j^2/q^2], and
f''(t)=d Var_t(j^2/q^2)>0 for finite t. Thus f is strictly convex.
At zero the derivative has the sign of

    R^2-d(q^2-1)/12.

For q=3329,d=10,R=2933 this is negative, so a strictly positive temperature
really does improve the q^60 limit. At large t the derivative is positive,
and the unique minimizer is certified in the interval

    beta_new in [9.51993054310946e-8, 9.51993054328994e-8].

The script brackets the root by interval signs of f', bounds the minimum
below by a supporting tangent at the left endpoint, and above by the value
at the midpoint. It is a global certificate, not a grid-search assertion.

| completion factor | log10 |
|---|---:|
| q^60, beta_new=0 | 211.33882770940 |
| globally optimized (1) | 211.26105706087 |
| volume cap M_10^6 at exactly R=2933 | 210.49217601926 |

Here M_10=min(q^10,V_10*(R+sqrt(10)/2)^10). The volume cap is justified by
placing disjoint unit cubes around the pivot integer points and enclosing
them in the enlarged ball. The reported production-radius snapshot has a
slightly different value; the table deliberately compares at exactly2933.

The optimized positive-temperature ratio to q^60 is about10^(-.07777),
whereas its ratio to the same-radius volume bound exceeds10^(.76888).
Taking the minimum with the current cap therefore selects the current cap.
The fixed anchor factor multiplies every column of this comparison equally.
Consequently these are completion-envelope comparisons, not a new selected
stratum gain or a failure-probability estimate.

## Actual production radius

The diagnostic also evaluates the exact expression from
`wall1_draw14_frontier.py`, computing the volume locally:

    R_prod^2=1.21*exp(2*(386*log(3329)-log(V506))/506)-2,
    V506=pi^253/253!.

This gives R_prod=2933.43724183307456.... Interval-sign bisection of the
strictly increasing derivative certifies the unique optimum at

    beta_new in [9.48025423259672e-8, 9.48025423260083e-8].

| production-radius completion factor | log10 |
|---|---:|
| q^60 | 211.33882770940 |
| globally optimized Gaussian | 211.26169204006 |
| existing volume cap M_10^6 | 210.49605822720 |

The Gaussian factor is 0.76563381286 orders larger than the existing cap,
so the actual target also receives no improvement. The diagnostic imports
no heavy evaluator and checks both endpoint derivative signs and convex
supporting-tangent/value bounds separately for both radii. The original
exact2933 log is preserved; the extended log is
`/tmp/wall1_mixed_completion_temperature_actual.log`.

## Limitation and verification

The scalar Gaussian pivot inequality is already attained by coordinate
planes. A stronger result must use the distribution of eligible anchor spans,
additional restrictions excluding extremal spans, or geometry retained from
the other input coordinates. Merely optimizing beta_new in this universal
pivot formula cannot provide it. This does not rule out an asymmetric
mixed-fiber estimate that retains that extra anchor geometry.

Run `python3 docs/research/scripts/wall1_mixed_completion_temperature.py`.
Log: `/tmp/wall1_mixed_completion_temperature.log`. The derivative-at-zero
comparison is exact rational arithmetic; finite theta sums, the convex
minimum certificate, and the same-radius comparison use65-digit interval
arithmetic. No production files are edited.
