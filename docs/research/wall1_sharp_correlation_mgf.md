# Sharpening the correlation MGF with the same two moments

This applies the existing sharp two-moment quadratic-majorant method from
[the overlap-energy analysis](wall1_overlap_energy_drift.md) to the exponential
in [the correlation compensator bound](wall1_correlation_mgf.md). It reduces
that route's proved exponential remainder. It does not bound the remaining
selected-history radius-exit event or complete the BKZ theorem.

## Enlarge a fractional indicator to fix its mean

Let H be a finite group of exponent q, and A its old miss set of density
p<=rho<1. Define

    t=(rho-p)/(1-p), f=1_A+t*(1-1_A),
    C_f(u)=E_v f(v)f(v+u).

Then 0<=f<=1, E f=rho, and C_f>=C_A pointwise. Cauchy--Schwarz and
f²<=f give 0<=C_f<=rho, while E_u C_f=rho². The Fourier-coefficient proof
in the correlation note applies unchanged to [0,1]-valued functions: its
fiber averages still lie in [0,1]. Put

    m=sin(pi*rho)/(q*sin(pi/q)), mu=rho²,
    v=m²*rho*(1-rho).

Finite Parseval and E f²<=rho imply

    Var(C_f)=sum_(chi!=1) |fhat(chi)|^4
             <=m²*(E f²-rho²)<=v.

The fractional filling avoids an unproved monotonicity claim in the original
density p. It preserves the actual group and common fresh mark. For the
trivial group the nonconstant Fourier sum is zero and the same inequality
continues to hold.

## Sharp exponential majorant from mean, variance and range

For a general rho, first replace v by min(v,mu*(rho-mu)), using the
support-implied variance bound. This cap is inactive at rho=.280. Set

    a=mu-v/(rho-mu), omega=v/(v+(rho-mu)²),
    B_sharp(rho,lambda)=omega*exp(lambda*rho)
                         +(1-omega)*exp(lambda*a).

For every lambda>0, the quadratic tangent to exp(lambda*x) at a and
interpolating it at rho majorizes it on [0,rho]. Explicitly, its quadratic
coefficient is

    K=[exp(lambda*rho)-exp(lambda*a)
                      -lambda*exp(lambda*a)*(rho-a)]/(rho-a)² >0.

Taylor's integral remainder divided by (x-a)² is
lambda² integral_0^1 (1-s) exp(lambda*(a+s*(x-a))) ds. This increases
with x, so its maximum for x<=rho is K, including when x<a.
The expectation of the quadratic at a fixed mean mu increases with the
variance because K>0. The two-point law on {a,rho} with mass omega at rho
has mean mu and variance v, and attains the quadratic majorant exactly.
Consequently, for X<=C_A pointwise with X>=0,

    E exp(lambda*X) <= E exp(lambda*C_f) <= B_sharp(rho,lambda).

The two-point expression is optimal using only this mean, variance bound
and interval. This does not claim its extremizer is a lattice correlation,
or that the Fourier variance bound is sharp for the selected miss sets.
The case v=0 reduces to the deterministic-mean exponential.

## Production-dimension compensator remainder

Keep precisely the events and filtration of the correlation note:
p_i is the conditional long-winner probability, b_i is the smaller-radius
old void fraction, and E_rho={some b_i>rho, i=7,...,404}. The old argument
bounds the stopped p_(i+1) pointwise by the current C_A(U_i), with U_i fresh
uniform conditional on the complete incoming history. Replace only its
conditional MGF majorant by B_sharp. The same 398-step iteration gives

    Pr(sum_(i=1)^405 p_i>48.6)
      <=Pr(E_rho)+exp(-48.6*lambda)*B_sharp(rho,lambda)^398.

At q=3329, rho=.280 and the fixed choice lambda=3.020, outward interval
arithmetic proves

    1.0466e-12 < exp(-48.6*lambda)*B_sharp^398 < 1.047e-12.

The old rounded remainder was 1.174e-12. Hence the sufficient allowance
for Pr(E_.280) in the same 7.6e-12 compensator budget increases from
6.426e-12 to 6.553e-12. This is a sharper sufficient condition with the same
unproved exit event. No global optimality over lambda is claimed.

## Reconcile the draw-14 allocation

The [two-constraint initial bound](wall1_affine_two_constraints.md) uses the
same b_i and rho=.280, with charges 7.150e-14 for draws7..12 and 2.432e-12
for draw13. Its previous accounting was

    7.150e-14+2.432e-12+3.922e-12+1.174e-12
      =7.5995e-12<7.6e-12.

Replacing only the last term permits the following allocation:

    7.150e-14+2.432e-12+4.049e-12+1.047e-12
      =7.5995e-12<7.6e-12.

Thus Pr(max_(14<=i<=404) b_i>.280)<=4.049e-12 is a new sufficient
later-history target under those same previously established initial inputs.
The earlier numerical initial certificates are retained, not rerun here.
The strict exit in the MGF route is covered conservatively by the >= exit
used in [the capped-potential bridge](wall1_capped_history_potential.md).
No new observable or radius is introduced.

For the matching draw14 seed D=1.9704509e-12, the updated sufficient sum of
normalized additive charges is

    4.049e-12-D = 2.0785491e-12.

Draw14 is already included in the seed and is not charged a second time.
Alternatively, the existing multiplicative stopped argument for390transitions
fits the new budget whenever each required conditional multiplier is at most
1.00184, since exact rational arithmetic gives

    D*(1.00184)^390 <4.035794e-12<4.049e-12.

The choice 1.00185 does not fit this budget. Neither multiplier is proved
for production histories. Additional bad gates must still be charged within
the same allocation. These are relaxed sufficient conditions, not a proof of
the exit bound, a paid drift charge, or an improved full BKZ failure guarantee.

## Reproduction

Run `python3 docs/research/scripts/wall1_sharp_correlation_mgf.py`.
It verifies the support/variance regime, the strict numerical improvement
at the chosen lambda, and the rounded remainder with 70-digit outward
interval arithmetic. The majorant and fractional-filling arguments above
are paper proofs. No Lean declaration or production cost claim is changed.

Independent review confirmed the fractional filling, Fourier variance bound
and quadratic-majorant argument, including the support-implied variance cap.

## Alternative threshold, retaining the physical radii

A separate sufficient route uses rho=.276 instead of .280. This changes the
threshold on the void fraction, not its physical test radius. The initial
certificates can be rescaled because their proofs bound the raw expected
void: equation(3) of the affine-void note is valid for every rho>0, and the
draw13 two-constraint remainder carries the same final inverse-threshold
Markov normalization. The draw14 seed explicitly bounds E[P14]/.280.
Consequently all three normalized initial bounds acquire factor
.280/.276=70/69. A tail-only certificate at .280 would not justify this step.

At q3329,rho=.276,lambda3.238, the same sharp-MGF proof and an outward
interval computation give a compensator remainder below2.982e-14.
The exact allocation

    (7.150e-14+2.432e-12)*(70/69)+5.030e-12+2.982e-14
      =8739543/1150000000000000000 <7.6e-12

therefore permits5.030e-12 for the stricter exit on draws14..404. Its
rescaled first-moment seed is

    D_.276=1.9704509e-12*(70/69)
           =137931563/69000000000000000000.

The sufficient remaining additive normalized charge exceeds3.03099e-12.
For the linear capped potential min(1,P/.276), a conditional multiplier
1.00236 on each of390transitions would suffice, since

    D_.276*(1.00236)^390 <5.012661e-12<5.030e-12.

The multiplier1.00237 does not fit this chosen allocation. These comparisons
are exact rational inequalities. They neither optimize over all thresholds
nor establish a multiplier for the actual selected histories.

This alternative is not an unconditional improvement over the .280 route:
the event b_i>.276 is larger, the potential changes, and the relevant
pre-exit histories must satisfy the new drift premise. A bound proved only
for the .280 event or potential cannot be transferred automatically. Prior
termination and bad-gate costs must still be accounted for, and draw14 is
paid by its rescaled seed exactly once. The original radius definitions and
all selected-history conditioning requirements remain unchanged.

## Retain the proved early first moments inside the MGF

A stronger refinement keeps rho=.280 and the same exit event, but avoids
using the uniform worst-case MGF at the first eight tested indices. Let

    X_i=p_(i+1)*1{b_j<=rho for every j=7,...,i}, i=7,...,404.

These are precisely the original stopped variables. Conditional on F_i,
the correlation domination gives E[X_i|F_i]<=1_live*b_i²<=rho*b_i.
The initial raw-void certificates, including the matching draw14 seed,
therefore supply

    sum_(i=7)^14 E b_i <= T,
    T=.280*(7.150e-14+2.432e-12+1.9704509e-12)
      =313176563/250000000000000000000.

This uses the first-moment provenance of those certificates, not a conversion
from upper-tail probabilities alone. The physical radii and observables are
unchanged. For Y=sum_(i=7)^14 X_i, we have 0<=Y<=8rho and E Y<=rho*T.
The convex chord for exp on this interval gives

    E exp(lambda*Y) <= 1+(exp(8lambda*rho)-1)*T/8 = A_early.

No independence among the initial eight variables is needed. The early block
is measurable by F_15. Apply the uniform conditional sharp-MGF bound to
indices15,...,404 by iterated conditioning backwards from the last step.
There are390 such indices, and hence

    E exp(lambda*sum_(i=7)^404 X_i)
      <= A_early * B_sharp(rho,lambda)^390.

Consequently the same compensator event satisfies

    Pr(sum_(i=1)^405 p_i>48.6)
      <=Pr(E_rho)+exp(-48.6lambda)*A_early*B_sharp^390.

At lambda=3.1724 the interval checker proves that the last term is less than
8.850e-14. The early factor is below1.000000000191. Both facts are certified
with outward rounding; lambda is a fixed choice, not a claimed global optimum.
This strictly improves the same-rho remainder above without tightening the
exit threshold or assuming independent selected histories.

Keeping the previous early-exit charges gives the exact allocation

    7.150e-14+2.432e-12+5.0075e-12+8.850e-14
      =7.5995e-12<7.6e-12.

Thus the matching draws14..404 sufficient exit allowance is now5.0075e-12,
and its sufficient normalized additive drift allowance after the seed is
3.0370491e-12. Alternatively, the conditional multiplier1.00239 fits:

    D*(1.00239)^390 <4.999063e-12<5.0075e-12,
    D=1.9704509e-12.

The choice1.00240 fails this chosen allocation. Using the first-moment seed
in the MGF proof and in the later stopped bound is legitimate: these are
two bounds in the event decomposition, not two independent random samples.
No extra draw14 union term is added. The actual later-history exit and drift
premises remain unproved, so the full BKZ failure guarantee is unchanged.

Independent review confirmed the early-block filtration, first-moment
provenance and absence of a survival-conditioning step, and independently
reproduced the remainder with outward interval arithmetic.
