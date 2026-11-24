# Primal/dual Gaussian polynomial lens majorants

Both lambda_1(M)>r and lambda_1(M*)>=s can enter a valid auxiliary-function
bound. However, the simplest quadratic Gaussian fails its sign test at the
shell-matching width with the current certified dual floors. No improved
production collision bound is obtained.

## Exact inequality

For d=505, b=d/2 and a>0, set

    c(a)=a²s²−ba/pi,
    g_a(x)=(||x||²+c(a)) exp(−pi||x||²/a).

Differentiating the Gaussian transform, with convention exp(−2pi i<w,x>),
gives

    ghat_a(w)=a^(b+2)(s²−||w||²) exp(−pi a||w||²).

Nonzero dual terms are nonpositive. Poisson summation implies

    sum_(v in M, v!=0) g_a(v) <= a^(b+2)s²/D−c(a).

Let ell(t) be the radius-rho lens volume, with r<2rho. If finite C>0
satisfies C g_a(t)>=ell(t) for all t>=r (including ell=0 for t>2rho),
then

    sum_(v in M, v!=0) ell(||v||) <= C [a^(b+2)s²/D−c(a)].

This addresses a continuum lens sum, not the discrete projected-grid error E
in the [lens/shell identity](wall1_lens_shell_identity.md). Since ell(r)>0,
a necessary sign condition is r²+c(a)>0. Equality does not suffice: the
strict lattice minimum gives no uniform positive separation from r.

## Width exclusion

Scale primal lengths by r. The primal threshold becomes 1 and the dual
floor becomes r*s; denote the latter by s in the formulas below. For
s<b/(2pi), the sign condition permits only a<a_minus or a>a_plus, where

    a_plus/minus=(b/pi +/- sqrt((b/pi)²−4s²))/(2s²).

At s=25, these endpoints are approximately .01395667 and .11464052.
The Gaussian radial scale matching ||v||=sqrt(2)rho is
a_match=2pi rho²/b, approximately .02488 when rho≈1. It is excluded.

The [existing corridor screen](wall1_covering_ceiling.md) proves
2pi sqrt(r²−1)R0<157.28 and r>1.1*32.18553 on its tested draws. Therefore
the available normalized certified floor r R0 is below25.04189<25.1.
This is not an upper bound on the actual dual minimum.
For the present lens radius, normalized rho²=1−2/r². At a_match,

    1+c(a_match)=1−2rho²+4pi²rho^4 s²/b² < −.6067.

Thus this width is inadmissible with the supplied floors. Other widths,
higher degrees and stronger dual information remain possible. This is not
an all-width impossibility result or a statement about BKZ failure.

## Repeated-root sextic extension: exact all-parameter exclusion

A natural higher-degree family enforces the dual sign by a square:

    Fhat(w)=(s²−y)(y−eta)² exp(−pi a y), y=||w||²,

where eta is any real number. It is nonpositive for y>=s². Its primal
factor has degree six in coordinates, or degree three in squared radius.
At the same shell-matching width, this whole family also fails, not merely
the parameters in a numerical grid.

Let u=pi||x||²/a, sigma=pi a s² and tau=pi a eta. Up to the positive
factor a^(−b)/(pi a)³ exp(−u), the inverse transform is

    P_sigma,tau(u) = sigma tau² L0(u)
       −(2sigma tau+tau²)L1(u)+2(sigma+2tau)L2(u)−6L3(u),

where Lk are generalized Laguerre polynomials with parameter b−1.
To verify the transform without a sign convention ambiguity, multiply
their generating function by exp(−u). Fourier transformation gives
a^b exp(−z) exp(z T), where z=pi a||w||² and T is the generating variable.
Its kth coefficient is a^b exp(−z)z^k/k!, giving the formula above.

At a=2pi rho²/b, the current parameter range gives sigma<50 and the
threshold for ||x||>=1 is u>=b/(2rho²)<127. Both u=127 and u=185 are
strictly inside the required lens interval, because u<2b=505 is equivalent
to ||x||<2rho. Their equally weighted evaluation at sigma=50 is exactly

    [P_50,tau(127)+P_50,tau(185)]/2
      = −(93/2)tau²+(21075/2)tau−4998431/8
      <= −3449743/124 <0.

The derivative of this average with respect to sigma is

    (tau−193/2)²+1563/2 >0.

Therefore the average remains negative for every sigma<=50 and every
real tau. At least one primal evaluation is negative where the lens volume
is positive. No positive scaling can be a lens majorant. The proof is an
exact rational two-evaluation certificate covering the continuous parameter
eta; it is not a sampled sign test.

The two evaluations extend to all radial Gaussian polynomials through
coordinate degree six, as follows.

## General degree-six exclusion at the matching width

Define a linear functional L on polynomials in z=pi a||w||² by averaging
the inverse-Gaussian polynomial at u=127 and u=185. Its moments are

    (L(1),L(z),L(z²),L(z³))
      = (1,193/2,40375/4,9035931/8).

For every nonzero linear polynomial l, L(l²)>0. Its 2-by-2 moment matrix
has positive first entry and determinant 1563/2. Likewise
L((z−50)l²)>0: its moment matrix has entries

    [[93/2,21075/4],[21075/4,4998431/8]],

with determinant 10349229/8>0. For sigma<=50 the corresponding matrix
for z−sigma is this matrix plus (50−sigma) times the first positive
matrix. It too is positive definite.

Every polynomial p of degree at most three nonnegative on [sigma,infinity)
has a representation

    p(z)=sum_j l_j(z)²+(z−sigma)sum_j m_j(z)²

with linear or constant l_j,m_j. One elementary proof factors the globally
nonnegative polynomial p(sigma+t²) as |A(t)+i B(t)|², with real polynomials
A,B of degree at most three. Real roots have even multiplicity and complex
roots occur in conjugate pairs, so such a factorization exists. Averaging
the squares at t and −t separates their even and odd parts. Even parts
are linear in t²; odd parts are t times linear polynomials in t², giving
the displayed representation after translating back.

Consequently L(p)>0 for every nonzero such p. If a nonzero Fourier
polynomial P of degree at most three is nonpositive on [sigma,infinity),
then L(P)<0. At least one of its two inverse-Gaussian polynomial values
is negative at a radius where the lens is strictly positive. The Gaussian
and scaling factors are positive, so they cannot repair this sign.

Thus no radial Fourier polynomial of degree <=3 in squared radius times
this Gaussian can give the required majorant. This covers all coefficients
and sums of squares, not just the repeated-root ansatz. It requires the
matching width and the available dual floor; it does not exclude other
widths, nonradial auxiliary functions, higher degrees or stronger dual data.
It also does not exclude conditions imposed only on the actual discrete dual
spectrum instead of the whole half-line, or sums of different Gaussian widths.
This is a restriction on a proposed proof method, not on BKZ performance.

## A feasible broader-width candidate and its cost

To check whether the sign obstruction merely requires changing width,
consider the normalized continuum benchmark r=rho=1, not the assertion that
the production radius equals its minimum threshold. Take

    a=57/500, sigma=443/500, tau=3/2,
    z=pi a||w||²/b,
    Fhat(w)=(sigma−z)(z−tau)² exp(−pi a||w||²).

Its inverse is a^(−b)exp(−pi||x||²/a)P(v), v=pi||x||²/(ab), where

    P(v)=v³+(43543/50500)v²+(898692/6375625)v
             −2552541/102010000.

The nonconstant coefficients are positive and P(pi/(ab))>.00193, so
F is positive at every radius >=1. The dual sign holds above
s_star=sqrt(sigma b/(pi a))<24.993104. This is a required dual premise;
it is not asserted on every production history by the existing floors.

Let f(t)=ell(t)/V_505. The axial integral implies

    (log f)'(t) <= −504t/(4−t²),  1<=t<2.

Indeed the logarithmic derivative of the axial integrand is decreasing,
so its tail integral is bounded by its endpoint value divided by the
endpoint logarithmic decay rate. Meanwhile P'>0 and 2pi/a<168.
It follows that (log(f/F))'<0. Thus C=f(1)/F(1) is a valid global
majorant multiplier; beyond radius2, f=0 and F remains positive.

For nu=V_505/D, the resulting upper certificate for the normalized torus
second moment (not its variance) equals

    1/nu + f(1) exp(pi/a)/P(pi/(ab))
             * [a^b sigma tau²/V_505−P(0)/nu].

Here f(1)=2 I_(1/4)(253,253), computed by an exact rational binomial tail.
Since P(0)<0, discarding the positive terms involving 1/nu proves that
the value of this particular certificate exceeds 10^117.07056 for every
nu>0. This is an ineffective upper certificate, not a lower bound on the
true collision ratio. Nor does it bound the finite-grid lens error.

Thus feasible signs do not by themselves give a useful majorant. This
candidate is rigorously validated, but it neither closes the production
variance target nor proves that all other widths and higher degrees fail.

## Actual candidate radius and applicability of the existing dual floor

Normalize lengths by the old minimum threshold r_phys=1.1g. The candidate
radius used in the pair argument becomes eta=sqrt(1-2/r_phys²), rather than
one. Throughout the incoming-draw range g>32.18553, eta>999/1000.
Keep the same F and write

    f_eta(t)=ell_eta(t)/(V_505 eta^505),
    f_eta(1)=2 I_x(253,253),  x=1/2-1/(4eta).

The axial argument now gives

    (log f_eta)'(t)<=-504t/(4eta²-t²)<=-168t,  1<=t<2eta.

Consequently C=f_eta(1)/F(1) is still a global majorant multiplier for
every eta in [999/1000,1]. For nu=V_505 eta^505/D, the normalized torus
second-moment upper certificate becomes

    1/nu + f_eta(1) exp(pi/a)/P(pi/(ab))
             * [a^b sigma tau²/(V_505 eta^505)-P(0)/nu].

Since x>=499/1998 and eta^-505>=1, an exact rational binomial tail at
499/1998 gives a uniform lower bound on the value of this certificate.
Its base-ten logarithm exceeds 116.99675. Thus moving to the actual
candidate radius does not make this particular certificate useful. This
remains a statement about an upper certificate, not an actual moment lower
bound; the finite-grid lens discrepancy is still uncontrolled.

There is also a separate applicability restriction. Use exactly the residual
determinant corridors and dual floor R_0 from
[the covering analysis](wall1_covering_ceiling.md), with incoming draws
11 through 405. The required normalized dual minimum is s_star. The
existing floor supplies it only if

    g >= s_star/(1.1 R_0(i-1)).

Checking this threshold against the upper end of each corridor with outward
interval arithmetic excludes 389 of the 395 corridors. Only draws 34
through 39 have a nonempty possible interval below that upper endpoint.
The largest upper-end product is at draw 37 and lies between
25.00362578421274 and 25.00362578421275; s_star lies between
24.99310364312220 and 24.99310364312221. For example, at draw 37 the
threshold for g lies between 2212.70516202864 and 2212.70516202865,
while the corridor ceiling lies between 2213.63671483773 and
2213.63671483774.

These exclusions mean that this available floor cannot establish the
candidate's premise there. They do not show that the actual dual minimum
is too small. The six remaining intervals are not a proof of reachable
selected histories, and the applicability calculation retains the original
exceptional-event qualification of R_0. Neither this comparison nor the
continuum majorant proves a selected-history collision estimate.

## Reproduction details

`python3 docs/research/scripts/wall1_primal_dual_auxiliary.py` checks the
root intervals, scaling and negative margin with outward interval arithmetic.
It also verifies the sextic certificate with exact rational arithmetic,
including the all-real-parameter maximum, monotonicity in sigma, and both
positive-definite moment matrices for the general degree-six extension.
The broader-width example additionally checks its inverse-transform
coefficients exactly and bounds the dual threshold, boundary positivity,
derivative comparison and certificate cost with interval arithmetic.
It also checks the radius-uniform rational-tail bound and all 395 corridor
dual-floor comparisons; the six potentially applicable draw indices and
their g thresholds are printed explicitly.
Independent review checked the Fourier transform, Poisson direction, strict
endpoint requirement, and the broader-width global majorant and its cost.
The radius extension and its normalization were independently reviewed too.
A floating-point parameter scan found poor candidates,
but is not used as a rigorous all-width exclusion. The actual selected-history
radial and discrete-lens estimates remain unproved.
