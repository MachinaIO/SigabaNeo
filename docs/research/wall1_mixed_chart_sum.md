# Shared completion coefficients and a matrix-dependent bound

For the nineteen-point mixed-fiber problem, the six completion coefficient
vectors are shared by every input coordinate. Their sum cannot generally
be averaged before raising a scalar coordinate kernel to the input
dimension. This note gives the exact chart count, a concrete failure of
that factorization, and a usable conditional bound when the fixed anchor
matrix has repeated coordinate functions. Production is unchanged.

## Exact coefficients after the full anchor is fixed

Choose r affine-independent inputs x0,...,x_(r-1) from the H-point anchor,
and let X be their n-by-r coordinate matrix. Every input in their span
has a unique coefficient vector

    c in A_r={c in F_q^r : sum c_i=1},   y=Xc.

There are q^(r-1) such vectors. Let P contain the H distinct coefficient
vectors of the already used anchor, including the chosen basis columns.
For k ordered new distinct inputs, the exact unrestricted chart count is

    (q^(r-1)-H)_k.                                         (1)

Writing d=r-1 and c=(1-sum u_j,u_1,...,u_d), every coordinate of Xc is
an affine function L_i(u). The actual input-ball count is

    C_X=sum_(u in F_q^d) 1{sum_i [L_i(u)]^2<=R^2}.

Provided all anchor points lie in that ball, the exact pinned completion
count is (C_X-H)_k. This identity keeps the full coordinate matrix X and
does not replace its span by an independent random plane.

For H=13,r=11,k=6 the unpinned count is q^60, whose log10 at q=3329 is
211.33882770940004. Pinning and distinctness multiply it by a factor at
least 1-93/q^10; the possible deletion is below 5.564e-34. The coefficient
normalization itself therefore supplies no substantial gain.

## Summation before coordinate powers

For fixed anchor coefficient matrix P and ordered completion matrix C,
define the scalar coordinate partition function

    Z_(P,C)(beta,gamma)=sum_(v in F_q^r)
      exp(-beta*sum_(a=1)^H [v.P_a]^2
          -gamma*sum_(j=1)^k [v.C_j]^2),
    Z_P(beta)=sum_(v in F_q^r)
      exp(-beta*sum_(a=1)^H [v.P_a]^2).

After the Gaussian majorants and relaxation of the full-rank input
condition, the mixed-fiber chart sum has the upper bound

    exp((H*beta+k*gamma)R^2)/q^(mr)
         *Z_P(beta)^m * sum_(C eligible) Z_(P,C)(beta,gamma)^n. (2)

Output coordinates occur only at the anchor; there are m output-coordinate
factors. The n input-coordinate factors use the **same** C, hence the sum
is outside the nth power. The q^(-mr) normalization belongs to the fixed
rank-r anchor law before the nonnegative relaxation. Anchor chart counts
and witness multiplicities remain outside (2) with their actual weights.

Let Q be the number of eligible completion charts. Jensen gives

    (sum_C Z_C / Q)^n <= sum_C Z_C^n / Q,                    (3)

which is the wrong direction for replacing the right side by the power
of the average. The unnormalized relaxation
sum_C Z_C^n <= (sum_C Z_C)^n is valid for integer n>=1 but allows an
independent C in every coordinate and adds cross terms. It does not save
the coefficient factor; the naive normalized replacement can be smaller
than the required quantity by up to Q^(n-1).

An equivalent fixed-X identity is

    sum_c exp(-gamma*sum_i [L_i(c)]^2)
       =sum_c product_i exp(-gamma*[L_i(c)]^2).

The same c occurs in every factor. Holder can bound this by
product_i (sum_c exp(-n*gamma*[L_i(c)]^2))^(1/n), but that uses higher
moments, not products of first moments. With distinct pinned k-tuples the
exact Gaussian sum is k! times the elementary symmetric polynomial of
order k in the nonanchor chart weights. Dropping distinctness gives the
power of their sum, which is an upper bound; it does not justify splitting
that sum across coordinate rows.

## Exact obstruction to normalized factorization

Take q=5, one affine parameter u, and two identical coordinate functions
L1(u)=L2(u)=u. Set gamma=log2 and f(u)=2^(-[u]^2). Then

    sum_u f(u)^2 = 193/128,
    (sum_u f(u))^2/q = 289/320.

The supposed normalized independent-coordinate upper bound is strictly
smaller than the true shared-coefficient sum. This is an actual affine
coordinate matrix of full affine rank one, not an arbitrary density tilt.
It establishes the obstruction without invoking selected-history laws.

## A valid bound using the fixed matrix's coordinate structure

There is nevertheless a deterministic improvement when the rows provide
additional energy. Choose d affine coordinate functions L_(i1),...,L_(id)
whose linear parts are independent. For each j, let lambda_j be the number
of rows equal to L_(ij) or -L_(ij) as affine functions over F_q. These
groups are disjoint because the selected linear parts are independent.
Let E0 be the summed squared centered values of all constant rows. Since
centering preserves the squared norm under negation,

    sum_i [L_i(u)]^2 >= E0 + sum_j lambda_j*[L_(ij)(u)]^2.

The selected affine functions define a bijection F_q^d -> F_q^d. Thus

    C_X <= #{z in F_q^d : sum_j lambda_j*[z_j]^2<=R^2-E0}
        <= inf_(gamma>0) exp(gamma*(R^2-E0))
                        *product_j theta_q(gamma*lambda_j), (4)

where theta_q(s)=sum_(a in F_q)exp(-s*[a]^2). If R^2<E0 the count is zero.
The finite weighted count can also be evaluated by a dynamic program over
the integer energies. An integer upper cap L_X from (4) yields the valid
pinned bound (L_X-H)_k on each fixed valid anchor. No independence of X
and its selecting incidence weights is required for this pointwise bound.

For example take q=5 and X mapping (u,v) to (u,u,u,v,v,v). At R^2=6,
the connected four-point anchor (0,0),(1,0),(0,1),(1,1) and its embedded
images are valid. The exact weighted count in (4) is C_X=9, compared to
the arbitrary affine cap q^2=25. The Gaussian value at gamma=log2/3 is
289/16<25, already a strict improvement; the exact pinned count for two
new inputs is (9-4)_2=20. This is an actionable matrix-dependent bound,
not a forecast for the current H13 anchor law.

For a coordinate plane, every lambda_j is one and E0=0, so (4) reduces
to the centered d-ball count. It cannot beat the established uniform-cap
obstruction. To apply the improvement on average in the production
nineteen-point problem, one must retain these row statistics under the
actual anchor incidence weights, or prove a stronger bound for the
coupled sum in (2). Fixing P alone does not control the row structure of X.
No numerical improvement for that actual weighted sum is established here.

## Verification

`wall1_mixed_chart_sum.py` checks the exact factorization counterexample,
the Jensen directions for powers1,2,3,6, six distinct-coefficient counts,
the repeated-coordinate full-rank fixture and its Gaussian bound, and the
q3329 coefficient-count deficit. All mathematical comparisons use rational
arithmetic; displayed logarithms are diagnostics only. No production code
or existing proof note is edited.
