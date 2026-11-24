# Gaussian periodization of frozen fibers

This deterministic lemma replaces a hard fundamental strip by a broad
Gaussian along the frozen lattice. It avoids a fixed multiplicative loss
per frozen dimension. It does not bound selected-history probabilities.

## Uniform bounds

Let Gamma be a full lattice of rank r in the Euclidean space F, with a
measurable fundamental cell D contained in the radius-rho ball. A half-open
Gram--Schmidt box gives rho^2 = sum_j s_j^2/4 and volume det(Gamma).
For a>0 define

    Theta(a,x) = sum_(gamma in Gamma) exp(-a ||x+gamma||^2),
    C(a) = (pi/a)^(r/2) / det(Gamma).

For every epsilon>0 and x in F,

    C(a) (1+epsilon)^(-r/2) exp(-a(1+1/epsilon)rho^2)
      <= Theta(a,x)
      <= C(a) (1+epsilon)^(r/2) exp(a rho^2/epsilon).       (1)

Proof: write y=gamma+d with d in D. Young's inequality gives

    ||x+gamma||^2 <= (1+epsilon)||x+y||^2
                       +(1+1/epsilon)rho^2.

Exponentiate, integrate over gamma+D, and sum the cells. The left
integral is det(Gamma)*Theta; the right integral is the full Gaussian
integral times the displayed exponential. This proves the lower bound.
For the upper bound, use instead

    ||x+y||^2 <= (1+epsilon)||x+gamma||^2
                       +(1+1/epsilon)rho^2,

and rearrange before exponentiating. The resulting integrand has parameter
a/(1+epsilon) and prefactor exp(a rho^2/epsilon). All sums and integrals
are nonnegative, so their interchange is justified by Tonelli.

For r>=1, 0<eta<=1 and beta>0, choose

    epsilon = eta/(2(r+1)),
    0<a<=min(beta, eta*epsilon/(4rho^2)).

Then log(1+epsilon)<=epsilon proves

    exp(-eta) <= Theta(a,x)/C(a) <= exp(eta).              (2)

Indeed the upper log error is at most eta/4+eta/4; the lower
log error is at most eta/4+eta*(1+epsilon)/4 < eta.
The rank-zero case has Theta=C=1 and needs no parameter choice.

## Exact fiber normalization

Let L be a full lattice in ambient Euclidean space and F a rational
subspace for L. Put Gamma=L intersect F and let P project onto F-perp.
The fibers in any translate t+L over its projected points are precisely
z+Gamma. For a bounded projected test region E, let N be its finite
number of projected points, and put

    W = sum_(z in t+L) 1_E(Pz) exp(-a ||(I-P)z||^2).

Every fiber contributes Theta(a,(I-P)z). In particular, (1) implies
L_epsilon*N<=W<=U_epsilon*N and W=0 iff N=0. More strongly,

    N = sum_(z in t+L) 1_E(Pz)
          exp(-a ||(I-P)z||^2)/Theta(a,(I-P)z).            (3)

The denominator is constant on each fiber by Gamma-periodicity, so each
fiber sums exactly to one. Using a proper sublattice of L intersect F
would require accounting for the extra fibers and is not justified here.

With T=W/C(a), (2) gives exp(-eta)N<=T<=exp(eta)N.
For any law of translates, and also for random frozen configurations when
this comparison is uniform and C(a) is normalized separately in each
configuration, the same pointwise comparison gives

    Pr(N>0) >= (E T)^2 / E(T^2)
              >= exp(-4eta) (E N)^2 / E(N^2),             (4)

provided the second moments are finite and the nonzero denominators exist.
If EN=0 the coverage is zero and one uses that trivial case separately.
The first inequality is Cauchy--Schwarz on {T>0}={N>0}.
Equation (4) compares certificates; it does not compute either moment.

## Compatibility and unresolved step

Combining the parallel Gaussian with a transverse Gaussian of precision
beta gives the positive-definite matrix

    Q = beta P + a(I-P),    Q_ii <= beta  (a<=beta).

Thus making a small does not worsen the scalar precision-diagonal bound
in [correlated packing](wall1_correlated_packing.md), when these are the
actual unrestricted integer coordinates. The factor a^(-r/2) in C(a)
must be canceled explicitly in any counting argument; it cannot simply
be discarded. Coordinate parametrizations, congruence restrictions and
selection conditioning still need their own treatment.

In particular, W and T are generally noninteger. Substituting them for
integer counts in the existing factorial-cumulant or Bonferroni proof is
invalid without a new argument. Formula (3) retains an integer count but
introduces a varying theta denominator. Bounding a count above alone
does not bound its void probability above. Production weighted first and
second moments, or an appropriate higher-order witness, remain unproved.
No accumulated BKZ transport bound follows from (1)--(4) alone.

## Factorial moments require distinct projected fibers

There is nevertheless a way to retain factorial moments without treating
T as an integer. Let the projected candidates be p_1,...,p_N and write
w_i=Theta(a,x_i)/C(a) for their normalized fiber masses. Define D_0=1 and

    D_k = sum_(i_1,...,i_k pairwise distinct) product_j w_(i_j).

Then, pointwise for every frozen configuration and translate,

    exp(-k eta)(N)_k <= D_k <= exp(k eta)(N)_k.            (5)

In particular D_k=0 when N<k. Its exact raw-lift expression is the
nonnegative sum over k lifts z_j with Pz_j in E and pairwise distinct
Pz_j, of exp(-a sum_j ||(I-P)z_j||^2)/C(a)^k. Tonelli and the fiber
partition prove this identity; no independence of the lifts or history
is required. The restriction is on projected points, not merely on raw
lifts. Many distinct raw lifts represent the same point.

For a finite-degree polynomial f(n)=sum_(k=0)^d f_k (n)_k, set
B=sum_k f_k D_k. Then

    |B-f(N)| <= sum_k |f_k|(exp(k eta)-1)(N)_k.           (6)

For any nonnegative random weight H, (5)--(6) may be multiplied by H
and averaged under the actual joint law, provided the moments are finite.
This includes indicators of selection and saturation, and nonnegative
competitor-count weights. A direct signed upper bound is

    E[H f(N)] <= sum_(f_k>=0) f_k exp(k eta) E[H D_k]
                 + sum_(f_k<0) f_k exp(-k eta) E[H D_k]. (7)

Reversing the two exponential factors gives a lower bound. These follow
term by term from (5); neither f nor B needs to be nonnegative for this
algebraic comparison. Using such a polynomial as a probability witness
still requires the original pointwise witness inequality.

Thus the approximation error can tend to zero for each finite moment
problem without losing the selected weight H. This is not a uniform
production estimate unless the relevant weighted moments and geometry
are controlled. Small eta alone cannot bound (6) when the absolute
coefficient-weighted moments are unknown or enormous.

For fixed flags, the raw-lift distinctness restrictions are deterministic
geometry, while graph membership still uses the joint constraint-rank
formula. Enlarging this domain to all tuples is legitimate for an upper
bound on a positive moment. It is not legitimate to replace a negative
term in (7) by that enlarged upper bound: a lower moment bound is needed
there. Nor can the correlated-Gaussian packing theorem be applied to the
distinct-fiber restricted law without proving its conditional atoms.
This identifies the remaining cancellation obstacle even after removing
the fixed strip loss.

## An integer auxiliary count with a uniform void error

One can also recover an actual integer count by thinning, without asserting
that the original candidates are independent. Conditional on the complete
original configuration, introduce independent auxiliary Bernoulli variables
with retention probabilities p_i=exp(-eta)w_i, and let Z be their sum.
Here exp(-2eta)<=p_i<=1 and Z<=N. Conditional factorial moments satisfy

    E[(Z)_k | configuration] = exp(-k eta) D_k.            (8)

For N=0 the auxiliary count is zero. For N>0 its zero probability is
product_i(1-p_i), at most (1-exp(-2eta))^N and hence at most
1-exp(-2eta). Thus for any nonnegative original-history weight H,

    0 <= E[H 1_(Z=0)] - E[H 1_(N=0)]
       <= (1-exp(-2eta)) E[H 1_(N>0)].                   (9)

This error does not grow with the number of candidates. The independence
used here is only newly introduced auxiliary randomness conditional on
the full original state. It does not assert independent lattice hits.

If f(n)=sum f_k(n)_k is any polynomial satisfying
f(n)>=1_(n=0) for every nonnegative integer n, then (8) gives the exact
valid upper witness

    E[H 1_(N=0)] <= sum_k f_k exp(-k eta) E[H D_k].      (10)

For a finite uniform state space these identities have finite moments;
more generally the displayed polynomial moments must be integrable.
This provides an integer-valued route for using existing void polynomials.
Unlike naively evaluating f(T), its validity follows from a genuine integer
random variable and the original pointwise polynomial inequality.
Nevertheless, numerically bounding the signed expression in (10) still
requires lower bounds for its negative terms. Neither thinning nor the
uniform error (9) supplies those missing selected-history moment bounds.

## Precision audit: why low moments do not close the signed bound

The exact rational diagnostic `scripts/wall1_factorial_precision_audit.py`
uses the fixed reference mean mu=58.15006220912 and the existing degree-24
square witness K_12(n;mu)^2/D^2, where D=sum_(j=0)^12 mu^j/j!.
This is a diagnostic at the draw-14 scale, not an assertion that any
production selected mean equals that rational.

At Poisson factorial moments mu^k, the normalized positive and negative
contributions are each about 3495143.524217, while their signed difference
is 1/D, about 2.5566720231e-13. The sum S of absolute nonconstant
contributions is between 6990286 and 6990287. Moment zero is known exactly
and must be excluded from S.

If each higher factorial moment is enclosed independently within relative
error epsilon of mu^k, the resulting interval-box upper bound is exactly
1/D+epsilon*S. Keeping this particular bound below .280*3.922e-12 requires

    epsilon <= (.280*3.922e-12 - 1/D)/S,
    1.2052e-19 < the right-hand side < 1.2053e-19.

The endpoint is exact for the independent interval box, whose extrema
need not be realizable by a common count law. Thus this is a limitation
of coefficientwise absolute error propagation, not a necessary precision
for every proof or every actual distribution. Joint cancellation, including
the existing cumulant method, can be substantially stronger.
If additional moments are known exactly, their terms must also be removed
from S for the sharp interval-box threshold.
Periodization can make eta arbitrarily small; this audit does not prove an obstruction
to choosing a small eta, only to using coarse moment enclosures afterward.

There is also a genuine obstruction to relying on only two moments. The
integer law supported on 0,59,60 with probabilities

    p59 = mu*(59-mu)/59,
    p60 = mu*(mu-58)/60,
    p0  = 1-p59-p60

has E N=mu and E(N)_2=mu^2 exactly, but p0 is about .01687073284.
The script checks positivity, normalization, both moment identities and
rational enclosures. Consequently matching those two Poisson moments
alone cannot imply a tiny void probability. This is an abstract integer
count law, not a reachable BKZ configuration or a counterexample to the
production claim. It rules out a proposed low-moment shortcut under only
those hypotheses; higher joint information remains necessary.
