# Variance-based cube enlargement for the shared-point count

Replace the uniform half-cube loss in Part 288 by a one-sided second-moment
bound. For a uniform vector e in [-1/2,1/2]^d, E[e]=0 and Cov(e)=I/12.
For a fixed displacement z and positive quadratic form G, the cross term
X=2 z^T G e has mean zero and variance z^T G^2 z/3.

For any centered random variable with variance at most sigma^2, and u>0,

    Pr(X<=u) >= u^2/(sigma^2+u^2).

Indeed Markov's inequality on (X+s)^2 over X>u, with s=sigma^2/u, gives
the complementary bound sigma^2/(sigma^2+u^2). Thus, if e^T G e<=C on
the whole cube and z^T G z<=T, at least that fraction of the cube lies
in the enlarged ellipsoid of squared radius T+C+u. Disjoint cubes around
lattice points give the count bound

    (1+sigma^2/u^2) * volume(ellipsoid(T+C+u)).

This argument is valid for arbitrary shifts of the ellipsoid center.

For the three-variable-sum kernel, G is a block sum of [[2,1],[1,2]],
whose largest eigenvalue is three. The cube quadratic maximum is 3N/2,
and the cross-term variance is at most T<=3R^2. Choosing u=kR therefore
replaces the old factor two by 1+3/k^2, and adds kR to the squared radius.
For the outer unit lattice, at every radius squared s<=R^2 the variance
is at most R^2/3 and cube maximum N/4. Choose u=lR, giving factor
1+1/(3l^2) and squared-radius shift N/4+lR.

Put p=N/2 and

    U=R^2+N/4+lR,
    B=8R^2/3+3N/2+kR,
    rho=2N*U/(3B(p+1)).

The same positive layer-cake expansion as Part 288 gives, when rho<1,

    Q7 <= (1+3/k^2)^2 (1+1/(3l^2))
          * pi^(5N/2)/((N!)^2 p! 3^N)
          * U^p B^(2N)/(1-rho).

The outer shift cancels from the boundary B after changing integration
variables, just as in the old proof. Every term in the expanded integral
is nonnegative; the geometric-ratio bound is retained. The implementation
takes the minimum of the old half-cube bound and the 28 choices
k=2,...,8 and l=1,...,4. Nonzero modular layers retain their existing
weighted Gaussian bound unchanged.

The exact low-dimensional real and modular shared-point checks pass,
as do full cumulant regressions. The size-fifteen full residual weighted
log10 improves from -11.30167 to -11.47301 (about 3.37e-12). This still
exceeds even the updated residual budget below, before the unresolved
larger sizes and selected histories. No complete BKZ or Lean proof is claimed.

The full admitted contribution through fourteen also decreases to less
than 3.419e-13. Retaining the reference/error allowance 9.131e-13 leaves
the following sufficient open target with the previous rounding slack:

    sum_(h=15)^24 L_h^* U_h + Pr(max_(15..404) b_i>.280) <= 2.6669e-12.

Indeed (0.9131+0.3419+2.6669)e-12=3.9219e-12<3.922e-12. This updates
the earlier 2.4692e-12 residual allocation; it does not prove the target.
