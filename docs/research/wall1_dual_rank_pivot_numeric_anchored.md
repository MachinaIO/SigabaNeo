# Anchored rank-pivot evaluation with all Gaussian frequency tails

Retaining the anchor kernel on nonpivot coordinate rows changes the reference
substantially. The tested gamma=1.25e-6 gives a complete completion multiplier
below10^101.449506 relative to the **same relaxed anchor input kernel**. This
is109.04655 orders below the current M10^6 factor, conditional on matching that
anchor reference to the production envelope. This note does not assert that
this final reference comparison has been established.

The prior free-basis diagnostic and log are preserved independently in
`wall1_dual_rank_pivot_numeric.py/.md`. This calculation uses the anchored
inequality independently audited by the parent and small_configuration.

## Uniform anchor control from its zero dual frequency

For the periodic Gaussian f(x)=sum_z exp(-pi^2(z+x/q)^2/alpha), define

    psi_A(x)=sum_(b in Z^2) exp(-tau_A ||b||^2)
                    product_(j=1)^11 f(x_j+(A b)_j),
    tau_A=pi^2/(q^2 alpha), h=f(0), Q=sum_(x in F_q) f(x).

Its Fourier coefficients are nonnegative: those of f are nonnegative by
Poisson summation, and summing exp(-tau_A||b||^2) against any character gives
a product of positive periodized Gaussian sums. Absolute convergence justifies
interchanging these sums. Thus psi_A(x)<=psi_A(0). All affine offsets are
allowed. Let J_A be the maximum sum of psi_A over a coordinate-sum hyperplane.
Summing d=10 freely chosen coordinates and bounding the last f factor by h
proves

    J_A <= theta(tau_A)^2 * h * Q^10.

Crucially, just b=0 gives psi_A(0)>=h^11, uniformly in A. Therefore

    eta_A=J_A/(q^10 psi_A(0))
      <= min(1, theta(tau_A)^2*(Q/(q h))^10) =: eta_bar.    (1)

No coefficient-norm bound or unwrapped Gram estimate is needed for (1).
At the requested parameters log10 eta_bar=-23.50229868015....

Applying the coefficient pivot argument to psi_A, each of the t independent
frequency columns contributes J_A, whereas every nonpivot column retains
psi_A(0). Relative to the complete relaxed anchor input kernel, this gives

    sum_V Krel([A,V])^118 / Krel(A)^118
      <= q^60 * theta(q^2 gamma)^(6*118)
                      * E[eta_bar^rank(B mod q)].          (2)

The input ball majorant adds exp(6 gamma R^2). Equation (2) sums all anchor
dual frequencies before the pivot bound; it does not independently average
the118 coordinate rows after summing coefficients V. The rank matrix B has
6 by118 entries distributed by the normalized diagonal dual Gaussian with
tau=pi^2/(q^2 gamma).

## Complete numerical evaluation

Use the same actual radius and alpha as the free-basis diagnostic:

    R=2933.43724183307456...,
    alpha=11*518/(26R^2)=2.54680382988048e-5.

For the maximum residue atom M=theta(q^2 tau)/theta(tau), set

    P_t=min(1,GaussianBinomial(6,t;q)*M^(118*(6-t))),
    E_upper=eta_bar^6+(1-eta_bar)*sum_(t=0)^5 eta_bar^t P_t.

The verified upper completion factor is

    F_anchor=q^60 exp(6 gamma R^2)
                    theta(q^2 gamma)^708 E_upper.          (3)

Every t=0,...,5 rank tail is retained; the calculation does not assume
full-rank dominance. All theta values include certified infinite tails,
using Poisson transformation for small arguments and a geometric tail
beyond |j|=20 for arguments at least pi. The grid is
1,1.25,1.5,1.75,2,2.25,2.5,3,4,5,6.85 times10^-6. Its best tested value is

    gamma=1.25e-6,
    log10 F_anchor=101.44950507205330... .

This is a tested admissible parameter, not a globally optimized temperature.
The same-radius cap has log10 M10^6=210.49605822720031, so the difference is
109.04655315514701 orders. If the production anchor-envelope term and this
relaxed-anchor expression differ by a multiplier C_ref, improvement requires
log10 C_ref<109.04655315515. For a conditional leading reference39.9478 and
target-12, the sufficient budget is log10 C_ref<57.09875315515. Neither
C_ref nor that rounded production reference is certified by this diagnostic.
All unchanged anchor prefactors, output kernels and chart multiplicities
must match in establishing C_ref.

## Cross-check using a weaker determinant certificate

The script also evaluates the separately valid but weaker bound

    eta <= Dcap*theta(alpha q^2)^2*h*(Q/q)^10,
    Dcap=1+11*1664^2=30457857.

For centered11-by2 coefficient lifts, det(I+AA^T)=det(I+A^T A).
The trace bound and two-dimensional arithmetic-geometric mean give
sqrt(det(I+A^T A))<=1+||A||_F^2/2<=Dcap. Together with the zero-alias
integer-theta lower bound by the continuous integral, this gives the stated
certificate after Poisson simplification. It yields log10 eta<=-17.97207255
and best tested log10 F_anchor=129.21992935 at gamma1e-6. This cross-check
is not used instead of the stronger bound (1).

## Scope and reproduction

Run `python3 docs/research/scripts/wall1_dual_rank_pivot_numeric_anchored.py`.
Log: `/tmp/wall1_dual_rank_pivot_numeric_anchored.log`. Numerical bounds use
75-digit intervals and exact Gaussian binomial coefficients. This note and
script are separate from the original free-basis baseline. No production
files are changed. The anchored reference comparison, eligible-chart coverage,
and any production integration remain the parent's separate obligations.

## Reusable helper

`scripts/wall1_anchored_dual_completion.py` provides
`completion_bound(s,r,h)` and `completion_details(s,r,h)`, the latter also
returning the chosen grid temperature. It uses k=h-r-2 and
alpha=r*518/(2*(r+2)*R^2), with118 input rows and two extra-anchor columns.
It requires q3329,N518 and the existing mpmath interval context; it does not
change its precision. Theta values, rank tails, and final caps are cached
with precision and exact interval endpoints in the keys. k=0 returns one.
The standalone check covers154 pairs with15<=h<=24 and
3<=r<=min(21,h-2), and independently reproduces the r11,h19 diagnostic.
Log: `/tmp/wall1_anchored_dual_completion.log`.

Only full H=r+2 anchors with no remaining free-basis points are in scope.
The helper supplies the isotropic theta candidate; direct/anisotropic
selected anchor envelopes cannot simply be multiplied by this cap without
a matching proof. A separate common-temperature theta anchor candidate is
needed when the existing selected bound mixes these constructions.
