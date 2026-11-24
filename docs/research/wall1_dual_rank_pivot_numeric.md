# Numerical rank-pivot bound relative to a free affine basis

This evaluates Eq. (3) of `wall1_dual_rank_pivot_bound.md` with all theta
and rank-tail contributions retained. A tested gamma=1.25e-6 gives a complete
upper multiplier below10^91.686104 relative to the **free affine-basis input
kernel** theta(alpha)^(11*118). This is not the original anchor-input kernel.
The missing comparison with that anchor prevents a production-gain claim.

## Parameters and reference

Use q=3329, r=11, d=10, n=118, k=6, two extra-anchor columns, isotropic
basis weight D=alpha I and both anchor-column weights lambda=alpha. The
actual production radius and fixed anchor temperature are

    R^2=1.21 exp(2(386 log q-log V506)/506)-2,
    V506=pi^253/253!,
    alpha=11*518/(26R^2)=2.54680382988048e-5.

The calculation includes exp(k gamma R^2), the completion-ball majorant,
and the exact q^60 coefficient count. It excludes all anchor-ball majorant
prefactors, output kernels, and output-map normalization. Those omitted
factors must be common to any later comparison; no extra output constraints
are imposed on the six new points.

Write theta(t)=sum_(j in Z) exp(-t j^2), h=theta(pi^2/alpha),
Q=theta(pi^2/(q^2 alpha)), and zeta=(Q/(q h))^10. Numerically
log10 zeta=-25.45577189205.... For each gamma, let

    tau=pi^2/(q^2 gamma),
    M=theta(q^2 tau)/theta(tau),
    P_t=min(1, GaussianBinomial(6,t;q)*M^(118*(6-t))),
    E_upper=zeta^6+(1-zeta)*sum_(t=0)^5 zeta^t P_t.

The maximum residue atom is M; a pivot bound on the mass of each t-space
and a union over such spaces prove the rank-tail bounds P_t. The exact
rank-tail identity then gives E[zeta^rank]<=E_upper. The law used here is
the normalized diagonal Gaussian frequency law, not uniform residues.

Dividing Eq. (3) by theta(alpha)^(r*n), and using the exact Poisson identity
for each scalar theta, simplifies the tested upper multiplier to

    F_free(gamma)=q^60 exp(6 gamma R^2)
           *theta(q^2 alpha)^(2*118)
           *theta(q^2 gamma)^(6*118) * E_upper.             (1)

Indeed theta(alpha)=sqrt(pi/alpha)*h and
sqrt(pi)/(q sqrt(gamma))*theta(tau)=theta(q^2 gamma).
This cancellation is relative to the free basis, not relative to the
anchor kernel containing its two extra-point constraints. The rank-pivot
step bound those anchor offsets uniformly, losing their geometry.

## Certified grid results

All entries below are log10 of the explicit upper formula (1), enclosed
with75-digit interval arithmetic:

| gamma | log10 F_free |
|---:|---:|
| .5e-6 | 142.732297 |
| .75e-6 | 108.776103 |
| 1e-6 | 95.521370 |
| 1.25e-6 | 91.686104 |
| 1.5e-6 | 92.767522 |
| 1.75e-6 | 97.844153 |
| 2e-6 | 103.449726 |
| 3e-6 | 125.872491 |
| 6.85e-6 | 212.200136 |

The full grid also includes2.25e-6,2.5e-6,4e-6,5e-6. The best tested value
is1.25e-6; no claim of a global optimum is made. At this temperature
log10 E_upper=-147.68177246. Its leading weighted tail terms are t=5 at
-147.68613486 and t=4 at-149.68239639; the full-rank baseline is-152.73463135.
Thus low-rank frequency tails are retained and materially affect the bound.

## Missing anchor-input penalty

The same-radius existing completion cap has log10 M10^6=210.49605822720.
For a fixed eligible anchor chart, let J_A be its desired input anchor
kernel raised to118, using the same anchor temperatures and reference domain.
Define the reference penalty

    C_input=theta(alpha)^(11*118)/J_A.

If output kernels and anchor prefactors match, the new input estimate
relative to this anchor is C_input*F_free. Thus sufficient comparison budgets
at the tested gamma are

    log10 C_input <118.80995434756              (beat M10^6),
    log10 C_input <66.86215434756               (39.9478 to -12).

The second line is conditional on the rounded leading-envelope reference
39.9478 and a consistent anchor factorization; a certified replacement for
that reference must be substituted in an actual proof. Neither inequality
for C_input is established here. If J_A denotes a different selected anchor
envelope rather than the same-temperature theta input expression, any
additional discrepancy must be included explicitly.

When summing multiple anchor charts, the analogous penalty is a ratio of
weighted anchor sums (with the same nonnegative output/chart weights), not
an unweighted average of per-chart penalties. The uniform-in-anchor Eq. (3)
permits such summation, but does not evaluate the denominator. Consequently
the numerical savings against M10^6 cannot be called production savings.

## Infinite sums and validation

For t>=pi, the script sums theta through |j|=20 and encloses the remaining
positive terms by

    2 exp(-441t)/(1-exp(-43t)).

For t<pi it first uses theta(t)=sqrt(pi/t)*theta(pi^2/t). This keeps all
sums and tails stable even for the very large arguments in h and the residue
numerator. Gaussian binomial coefficients are exact integers imported from
the rank-tail verifier. Every rank-tail bound is capped at one.

Run `python3 docs/research/scripts/wall1_dual_rank_pivot_numeric.py`.
Log: `/tmp/wall1_dual_rank_pivot_numeric.log`. The evaluation imports no heavy
production evaluator and changes no production file.
