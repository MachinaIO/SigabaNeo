# An exact fixed-chart mixed-kernel temperature check

This finite example checks the asymmetric kernel from
`wall1_independent_map_energy.md` before using it for the high-dimensional
completion problem. It also gives a rigorous boundary-derivative test for
whether a new-input Gaussian temperature can improve a fixed anchor bound.
It supplies no production improvement or selected-history estimate.

## Exact model and majorant

Use q=5, two input coordinates, one output coordinate, radius squared4,
and an ordered anchor with affine parameters 0,1,2 on a line. Its input
basis is (a,b) with b nonzero. New ordered parameters are chosen without
repetition from {3,4}; use k=1 or2. Output restrictions have q^2 equally
likely values, hence normalization q^(-2). The script exhausts these
full-rank input anchors and all output restrictions. The exact mixed count
is208/25 for either k. The additional inputs have no output-ball condition.

For anchor temperature beta>=0 and new-input temperature gamma>=0, let
S_A(beta) be the scalar Gaussian sum over (a,b) in F5 squared with weights
at parameters0,1,2, and S_t(beta,gamma) the sum also weighting the new
parameters in an ordered chart t. Relaxing input full rank gives

    G(beta,gamma)=exp(12 beta+4k gamma)/25
                     * S_A(beta) * sum_t S_t(beta,gamma)^2.

This is an upper bound, since each valid mixed tuple satisfies all the
ball constraints being majorized. The chart sum is outside the square:
the same completion coefficients are used by both input coordinates.
At gamma=0, every S_t=S_A and the expression is exactly the anchor-only
Gaussian majorant times the number of allowed coefficient charts.
The script checks this equality, all120 tested upper bounds, and the exact
mixed count with rational arithmetic, using rational exp(-beta) and
exp(-gamma). There is no Gaussian approximation or floating-point certificate.

## Boundary derivative and convexity

For a fixed beta, G(beta,gamma) is a finite positive sum of terms
c*exp(gamma*(k R^2-E_new)), where E_new is the total new-input energy.
Consequently log G is convex and

    d/dgamma log G(beta,0)=k R^2-E_beta[E_new].

Here E_beta is the probability distribution proportional to the actual
Gaussian summands, including their coefficient charts and all input
coordinates. If this derivative is nonnegative, gamma=0 is a global
minimum over gamma>=0 for that fixed beta. If negative, sufficiently small
positive gamma strictly improves that fixed-beta expression. This criterion
does not optimize beta or remove any modular alias terms.

In this fixture the derivative is positive at exp(-beta)=3/4 and negative
at exp(-beta)=9/10, for both k. Thus its sign is not a universal property
of input-only completions. In particular one cannot replace the new-input
energy distribution by independent uniform residues without proof.
The best pair in the specified finite grid remains exp(-beta)=3/4,
gamma=0, so this grid does not improve the best anchor-only cap. This is
not a claim of global optimality over beta. The exact small example cannot
be extrapolated to q3329, input dimension118, or the selected residuals.

Run `python3 docs/research/scripts/wall1_mixed_kernel_fixture.py`.
The printed decimal derivatives are diagnostic; their signs and all
probability/majorant comparisons can be tested as exact rational numbers.
