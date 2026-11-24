# Uniform anchored dual completion multiplier

For a full two-relation anchor with H=r+2 positions, use a common positive
Gaussian weight alpha on every position. There are n input coordinates and
m output coordinates. A basis chart has r columns forming the identity and
two extra columns A; their coefficients sum to one modulo the prime q.
Let K_A be the integer code-lattice theta sum

    K_A=sum_(x in Z^r,z in Z^2)
             exp(-alpha*(||x||^2+||xA-qz||^2)).

This is the relaxed Gaussian anchor kernel, not the joint-ball probability.
For k ordered dependent input completions, the common-weight anchor sum can
be bounded by K_A^n times the following multiplier, uniformly in A. The
output factor K_A^m, q^(-mr), anchor Chernoff factor and chart multiplicities
remain separate and unchanged.

Put d=r-1 and, for the chosen gamma>0,

    h0=theta(pi^2/alpha), Q=theta(pi^2/(q^2 alpha)),
    eta=min(1,Q^2*(Q/(q*h0))^d), tau=pi^2/(q^2 gamma),
    M=theta(q^2*tau)/theta(tau),
    P_t=min(1,GaussianBinomial(k,t;q)*M^(n*(k-t))),
    E=eta^k+(1-eta)*sum_(t=0)^(k-1) eta^t P_t.

Then a valid completion multiplier is

    F(r,k;gamma)=q^(dk)*exp(k gamma R^2)
                    *theta(q^2 gamma)^(nk)*E.             (1)

For k=0 use F=1. Each gamma gives a bound independently, so minimizing a
finite grid of certified upper endpoints is valid and needs no assertion
of global optimality.

## Why the same anchor kernel is retained

In the joint dual expansion, sum the two anchor frequencies first. On
F_q^r define

    f(x)=sum_z exp(-pi^2*(z+x/q)^2/alpha),
    psi_A(x)=sum_(b in Z^2) exp(-tau_A*||b||^2)
                              product_j f(x_j+(Ab)_j),
    tau_A=pi^2/(q^2 alpha).

The Fourier coefficients of f and the Fourier transform of the pushed
integer Gaussian on b are nonnegative, by Gaussian periodization. Hence
psi_A(x)<=psi_A(0). For J_A the largest sum of psi_A on a coordinate-sum
hyperplane, summing d free coordinates and bounding the last f by h0 gives
J_A<=Q^2*h0*Q^d. The term b=0 gives psi_A(0)>=h0^r, and therefore
J_A/(q^d psi_A(0))<=eta. These statements hold for every basis coefficient
chart A, including large centered coefficients and all modular aliases.

For a fixed k-by-n completion-frequency matrix B of rank t, the affine
coefficient pivot lemma retains psi_A(0) on every nonpivot row and gives
an average at most psi_A(0)^n eta^t. Restoring the joint dual prefactors
changes the input factor from K_A^n by exactly

    q^(dk)*(sqrt(pi)*theta(tau)/(q*sqrt(gamma)))^(nk)
                     *E_B eta^(rank(B mod q)).

Poisson summation identifies the parenthesized quantity with
 theta(q^2 gamma). The normalized bare frequency law has independent
integer entries proportional to exp(-tau b^2). Systematic pivots in each
finite-field subspace give Pr[rank B<=t]<=P_t. The exact rank-tail identity
then bounds its eta moment by E. This proves (1), with every rank and
frequency included. The auxiliary product law here does not assume an
independent actual anchor distribution.

The underlying count starts with distinct centered residue inputs. Dropping
pinning/distinctness, then replacing each completion ball indicator by its
positive Gaussian majorant and summing all integer aliases, enlarges the
sum. The coefficient count q^(dk) is already included in (1); it is not
an extra factor to be added by the caller.

## Required production interface

`wall1_anchored_dual_completion.py` evaluates (1) for n=118, q=3329,
alpha=r*518/(2(r+2)*R^2) and k=h-r-2, without changing caller precision.
The exact interval radius is part of its cache key. It validates154 cases
and reproduces the independently calculated r11/h19 cap.

This multiplier can replace the uniform completion cap **only in a
candidate that bounds the same common-alpha Gaussian anchor theta**.
The current production `anchors` dictionary also contains direct ball
counts and anisotropic Gaussian refinements. Multiplying those selected
minima by (1) is not justified by this proof. A safe implementation keeps
a separate common-alpha theta candidate and minimizes its completed bound
against the existing completed bound. The full-anchor condition also
requires zero remaining free basis points; terms with free basis points
are not covered by this interface.

See `wall1_dual_rank_pivot_bound.md`, `wall1_dual_frequency_rank.md`, and
`wall1_dual_rank_pivot_numeric_anchored.md` for independent audit and
finite/interval checks. Production applicability must be verified before
claiming a reduced global residual or a new BKZ guarantee.

## Integrated full-anchor checkpoint

Production now stores a separate `theta_anchors` candidate at the initial
common-weight theta bound. The independently audited c4/H13 path additionally
retains its last common-weight one/none split before the direct-ball minimum.
For terms with r=c+t-2, the completed candidate using (1) is minimized against
the old completed bound. Anisotropic and direct-ball minima are never
multiplied by (1). Terms with free basis points are unchanged at this checkpoint.

`/tmp/wall1_anchored_dual_cumulants.log` exits successfully, including2106 exact
checks. Through17 is below6.143e-13; through24 is about4.2321e208, still an
ineffective upper envelope, not a failure probability. The rerun
`/tmp/wall1_anchored_dual_frontier.log` passes the selected-cover and remainder
reconstruction comparisons after adding both new dictionaries to the capture
state. The remaining leading terms now have free basis points. Extending the
common Gaussian reference to those points requires a separate audited bound.
