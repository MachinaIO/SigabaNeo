# Joint completion via disjoint frequency bases

This is a paper lemma for the auxiliary dual-frequency sum. It does not
assume that the actual BKZ selected history is independent.

Let V be uniform among r-by-k matrices over Fq whose columns sum to one.
Let B have k rows, rank t, and L disjoint sets of t columns, each a basis
of its column space. Let f:Fq^r->[0,1] and arbitrary fixed offsets o_i.
Define

    eta_L = max_c q^{-(r-1)} sum_{sum(x)=c} f(x)^L.

Then E_V product_i f(V b_i + o_i) <= eta_L^t <= eta_1^t.
For each selected basis, the linear map V to its t images has constant
fibers and is onto the product of the t hyperplanes with sums 1^T b_i.
Translations by the offsets only change those sums. Drop unused factors
using f<=1. Apply Holder with exponent L to the L basis products. Each
L-th moment factors into t uniform hyperplane averages, each at most
eta_L. Multiplying the resulting L factors gives eta_L^t. Pointwise
f^L<=f proves the second inequality. For t=0 the bound1 is immediate.

For the anchored Gaussian lemma, f=psi_A/psi_A(0) is admissible by Fourier
positivity. The proof retains correlations between several sets of
frequency columns rather than discarding all but one basis.

Numerical use still requires certified bounds on eta_L and on the number
of disjoint bases under the auxiliary Gaussian frequency law. Rank alone
does not guarantee L>1: a single basis followed by zero columns is a
counterexample. Replacing eta_L by eta_1 discards the potential gain.
No improved production bound from this lemma is claimed yet.

The companion exact-rational script checks affine offsets, nontrivial
basis changes, and discarded zero columns over F3 and F5. These finite
checks support the implementation of the inequality; the argument above,
not finite enumeration, supplies its general scope.

## Part 428: certified packing failure via sequential exposure

Assume now B has k rows and n columns with independent entries over Fq,
each having maximum atom at most M<1, and n>=Lk. Read columns sequentially,
accept a column when it is outside the current span, and reset the span
when k accepted columns complete a basis. Stop after L bases. Before that
stop the current span is proper. For any proper subspace, choose a nonzero
linear equation containing it and condition on all but one coordinate with
a nonzero coefficient. The remaining coordinate has atom at most M.
Consequently every fresh column is accepted with conditional probability
at least1-M, even though the current span depends on previous columns.

Couple these acceptances to independent Bernoulli(1-M) variables using
fresh uniforms. After the stopping time extend the acceptance sequence
with ones. The algorithm's count dominates their sum. If no L disjoint
bases exist, this algorithm cannot accept Lk columns, so

    p_bad <= sum_(j=0)^(Lk-1) binom(n,j) (1-M)^j M^(n-j).

This argument requires fresh independent columns. It is applied only to
the auxiliary Gaussian frequency law, not selected BKZ vectors. It avoids
union bounds over possible adaptive spans.

For comparison an independent elementary bound follows by deleting at
most(L-1)k accepted columns until the remainder has rank<k, padding the
deleted set to s=(L-1)k, and union bounding all such sets and hyperplanes:

    p_bad <= min(1, binom(n,s) (q^k-1)/(q-1) M^(n-s)).

This alternative is valid but usually much weaker here.

For the discrete Gaussian frequency law, tau=pi^2/(q^2 gamma) and
M=theta(q^2 tau)/theta(tau). The interval diagnostic at q3329,n118,k14,
L2,gamma1.25e-6 gives p_bad<5.40e-11. This bounds packing failure only;
it is not a BKZ failure probability or an improvement of the production
completion envelope.

Let eta_L<=eta_1<=1 be certified moment bounds and let P_t bound
Pr(rank(B)<=t). Combining packing with the existing rank-tail identity gives

    moment <= eta_L^k + (eta_1^k-eta_L^k) p_bad
                     + (1-eta_1) sum_(t=0)^(k-1) eta_1^t P_t.

Indeed, the fixed-B bound is eta_1^rank minus
(eta_1^k-eta_L^k) on the packing-good event, which implies full rank.
Rank-deficient events are included and are never silently discarded.
Quantitative eta_L bounds remain the missing step before production use.

The script `wall1_disjoint_basis_tail.py` exhaustively checks2688 binary
matrix/distribution cases with exact rational weights, including the
adaptive-deletion witness and both failure bounds. Its interval grid log
is `/tmp/wall1_disjoint_basis_tail.log`. No full production run is needed
for this standalone lemma; the production evaluator is unchanged.

Independent read-only audit approved the sequential coupling and its scope.
A further paper-level refinement retains codimension c: a fixed codimension-c
subspace has mass at most M^c by pivot-coordinate conditioning. The waiting
time to the next accepted column is therefore conditionally dominated by a
geometric waiting time with failure probability M^c. Iterating its moment
generating bound over L complete bases yields, for1<z<1/M,

    p_bad <= z^{-(n-Lk+1)}
             * product_(c=1)^k ((1-M^c)/(1-z*M^c))^L.

Here n-Lk+1 is the minimum number of rejected columns causing completion
after n columns. This refined expression has not yet been numerically
integrated or used for any claimed production improvement.

## Free-coordinate moment bound and production candidate

For A_ext=[A0;0], the normalized kernel factorizes exactly as
f(x)=f0(x_old) product_i g(x_free,i), where

    g(x)=phi_beta(x)/theta(pi^2/beta),
    phi_beta(x)=sum_z exp(-a(z+x/q)^2),  a=pi^2/beta.

Fourier positivity gives0<=f0,g<=1. Summing the old coordinates first on
any prescribed hyperplane and using f0^L<=f0 shows

    eta_L <= eta_old,1 * rho_free,L^f,
    rho_free,L = q^-1 sum_(x mod q) g(x)^L,
    eta_old,1 <= min(1,Q_old^2 rho_old^(r0-1)).

For centered |x/q|<=1/2, all nonzero aliases sum to at most

    delta = 2 exp(-a/4)/(1-exp(-2a)).

Expand (exp(-a(x/q)^2)+delta)^L. The constant term averages to delta^L;
for each j>=1 extend the centered residue sum to all integers. Dropping
the normalizer theta(a)^L>=1 yields the explicit bound

    rho_free,L <= delta^L
       + sum_(j=1)^L binom(L,j) delta^(L-j) theta(j*a/q^2)/q.

The implementation also retains the bound1 and minimizes eta_L against
eta_1. All aliases and rank tails remain. For L in{2,3,4,5,6,8} with Lk<=118,
it evaluates the binomial and codimension-geometric packing bounds, then
adds the completed candidate

    eta_L^k + eta_1^k p_bad
            + (1-eta_1) sum_(t=0)^(k-1) eta_1^t P_t.

This drops a negative term from the preceding exact expression, so is an
upper bound. It is minimized against the previous rank-only candidate.
The free basis Gaussian and original anchor prefactors remain outside the
completion multiplier. For no free extensions, the old path is unchanged.

Independent mathematical and implementation audits approved these steps.
The finite suite includes48 Holder checks,72 free-factor hyperplane checks,
and2688 matrix/distribution cases, now also checking the geometric
waiting-time bound with exact rational dynamic programming. Full production
results are recorded separately after the current runs complete.

## Part 429: full production outcome and next obstruction

Both production runs exited0: `/tmp/wall1_holder_free_cumulants.log` and
`/tmp/wall1_holder_free_frontier.log`. All2106 exact cumulant checks and18
frontier interval comparisons pass. Through17 remains below1.526e-14 and
through24 below4.557e133. The added candidate changes the upper endpoints,
but has no substantial effect on the size24 residual or its rank8/girth4
six-point leader. The full transfer target remains unproved.

The standalone diagnostic `wall1_holder_rank_bottleneck.py` evaluates
r8,h24,H6, four free extensions at beta_free=518/(2R^2). The selected
gamma is1.5e-6. In the rank-moment decomposition, the full-rank term has
log10 approximately-224.9431, whereas the largest rank-tail contribution
(t11) has log10 approximately-188.5762; t10 andt12 follow. These are
components of an upper bound, not measured rank probabilities. The
current full-rank packing/Holder improvement cannot remove the unchanged
rank-tail contribution. Sharper auxiliary rank tails, or a moment bound
that also exploits multiple bases within deficient-rank strata, is the
next necessary direction. No selected-history law or complete BKZ proof
follows from this checkpoint.

## Part 432: extended full-coordinate Holder search

For the518-coordinate candidate, the finite Holder grid now also includes
10,12,14,16,20,24,32, always requiring Lk<=518. Additional gamma candidates
.55,.6,.65,.7,.8,.9 times1e-6 retain the entire previous grid. The118 branch
is unchanged. These choices are independent upper bounds under the same
proved lemmas; no global parameter optimality is claimed. The cache includes
the actual order tuple and gamma tuple.

The higher-order finite factor tests now pass144 cases, in addition to48
Holder checks. Both full runs exit0 with2106 cumulant checks and18 frontier
comparisons: `/tmp/wall1_holder_extended_cumulants.log` and
`/tmp/wall1_holder_extended_frontier.log`. Through17 is below3.219e-17;
through24 is below1.913e31, still ineffective. The size24 leader is now
rank8/girth3, H9 t6/overlap2, with only one free extension. Its theta snapshot
needs a separate branch audit. The two-four normalizer research concerns
a different residual family and is not included in this numerical bound.
