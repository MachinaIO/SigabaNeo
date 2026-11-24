# Mixed Gram kernels for weighted affine completion

This gives an exact modular kernel and a Schur-complement expansion for averaging
completion counts with anchor Gaussian weights. It keeps the input lattice and
modular aliases. It does not replace the weighted anchor span by a random plane,
and it does not prove that the resulting alias sums are small.

## Basis, affine coefficients, and the exact finite kernel

Let q be an odd prime, r the augmented anchor rank, and X an n by r matrix of centered
integer input coordinates of an affine basis. In the intended branch n=118 and
r=11; the augmented matrix [1;X] must have rank r over F_q. Extra anchor points
have coefficient columns A, with 1^T A=1^T over F_q. Completion coefficients
V satisfy the same affine condition. Choose integer lifts of their residues,
and let W=[A,V]. These lifts need not sum to one over the integers: the actual
condition is modulo q. Every completed input is [Xv]_q, with componentwise
centered residues. Changing the lifts does not change any exact modular count.

For a positive diagonal r by r matrix D and positive diagonal s by s matrix
Lambda, where s is the number of columns of W, define

    K_q(W;D,Lambda)
      = sum_(x in centered F_q^r)
          exp(−x D x^T − [xW]_q Lambda [xW]_q^T).            (1)

Here x is a row vector. Gaussian weights for the basis columns enter D, and
weights for the extra anchor and completion columns enter Lambda. For fixed
coefficients, summing over all n coordinate rows gives exactly K_q^n.
Requiring full augmented rank, distinct points, connectedness, and bounded
input norms restricts this nonnegative sum and hence gives an upper bound by
K_q^n; it is not an equality after those eligibility restrictions are imposed.

For a fixed basis X, the affine completion count is

    C_R(X)=sum_(v in F_q^r, 1^T v=1)
                   1{ ||[Xv]_q||²<=R² }.                  (2)

Its kth ordinary power sums ordered k-tuples of coefficients with repetitions.
Inserting exp(tau R²−tau ||[Xv]_q||²), tau>0, for each indicator yields

    sum_(eligible X) w_A(X) C_R(X)^k
      <= exp(k tau R²) sum_(affine V with k columns)
            K_q([A,V]; D, diag(Lambda_A,tau I_k))^n.        (3)

Here w_A(X)=exp(−sum_rows [xDx^T+[xA]_q Lambda_A [xA]_q^T]).
The left sum uses centered residue inputs, and (3) is valid for every R
under that convention, including the production radius greater than q/2.
A separately defined count of raw integer representatives may have several
representatives per residue; such a count needs its multiplicity weights.
Those multiplicities are not part of the residue occupancy (2).
Additional anchor ball majorant prefactors can be multiplied into (3).
Inequality (3) is a mixed coefficient/kernel sum, not a uniform completion cap.

There is also an exact output normalization relevant to full incidence.
Given an eligible affine basis and a uniform affine map into F_q^m, its r basis
outputs are independent uniform vectors. Gaussian output weights of the same
coefficient chart therefore contribute

    q^(−mr) K_q(A; D_out,Lambda_out)^m.                     (4)

If completions are counted only as input occupancy, they are absent from (4).
If they also require output incidence, include V with their output weights in
(4). For fixed coefficient charts the factor in (4) is independent of X.
After eligibility is dropped in the input sum, it can still multiply the
upper bound: (4) was used only on eligible bases. Ball-incidence Chernoff
prefactors are necessary and are not included in the normalized kernel itself.

## Exact modular aliases and a positive relaxation

For each centered basis row x, there is a unique integer vector z with
xW−qz centered. Thus (1) is exactly

    sum_(x in centered F_q^r) sum_(z in Z^s)
      1{xW−qz centered}
      exp(−xDx^T−(xW−qz)Lambda(xW−qz)^T).                  (5)

Dropping both centered restrictions gives the positive upper bound

    K_q <= K_tilde
      := sum_(x in Z^r,z in Z^s)
            exp(−xDx^T−(xW−qz)Lambda(xW−qz)^T).            (6)

All sums converge, since the joint quadratic form is positive definite.
This relaxation is also invariant under changing W to W+qT for integer T,
by reindexing z as z+xT. Its decomposition into z=0 and z!=0 is not invariant.
In particular a large chosen integer lift is not by itself evidence that a
modular completion is rare.

## Schur complement: determinant term, discreteness, and aliases

Put

    G=D+W Lambda W^T,
    S=Lambda−Lambda W^T G^(−1) W Lambda
     =(Lambda^(−1)+W^T D^(−1)W)^(−1),
    h_z=q z Lambda W^T G^(−1).

Both G and S are positive definite. Completing the square proves exactly

    xDx^T+(xW−qz)Lambda(xW−qz)^T
       =(x−h_z)G(x−h_z)^T+q² z S z^T.                    (7)

Define theta_G(h)=sum_(x in Z^r) exp(−(x−h)G(x−h)^T). Then

    K_tilde = sum_z exp(−q² z S z^T) theta_G(h_z).          (8)

The continuous unwrapped Gaussian integral is exactly

    integral_(R^r) exp(−xGx^T) dx = pi^(r/2)/sqrt(det G).   (9)

For n independent coordinate rows its power is
pi^(nr/2) det(G)^(−n/2). Equation (9) is not an equality for the integer sum.
Fourier expansion of the periodized Gaussian gives

    theta_G(h)=pi^(r/2)/sqrt(det G)
      * sum_(ell in Z^r) exp(−pi² ell G^(−1)ell^T)
                            exp(2pi i ell h^T).           (10)

Indeed its ell-th Fourier coefficient is the Gaussian Fourier integral
pi^(r/2)/sqrt(det G) times exp(−pi² ell G^(−1)ell^T);
absolute convergence justifies periodization and Fourier summation. Taking
absolute values termwise gives theta_G(h)<=theta_G(0), hence the useful bound

    K_q <= theta_G(0) theta_(q² S)(0).                     (11)

The z=0 term in (8) is the unwrapped integer Gram kernel theta_G(0).
The exact nonnegative alias correction to that term is

    E_alias = sum_(z != 0) exp(−q² z S z^T) theta_G(h_z)
             <= theta_G(0) [theta_(q² S)(0)−1].            (12)

It is the correction for the relaxed kernel (6), not a claim that the original
finite kernel equals its unwrapped term plus this correction: (5) retains
centered restrictions. In particular K_q>=theta_G(0) is not asserted.

Equations (10) and (12) distinguish the two obligations lost by a pure Gram
integral argument: the dual theta correction for integer x and the alias theta
correction for modular xW. For n=118 even moderate row-wise losses are raised
to the 118th power. If theta_(q²S)(0)<=1+epsilon, the alias bound costs at most
(1+epsilon)^118 in that input factor. Formula (11) keeps the full matrices;
replacing S by a scalar eigenvalue floor is optional and may be very lossy.

## A coefficient-invariant prefactor in the joint dual expansion

The block quadratic matrix in (6) is

    Q=[[D+W Lambda W^T, -q W Lambda],
       [-q Lambda W^T, q^2 Lambda]].

The linear change (x,z)->(x,xW-qz) has absolute determinant q^s,
so det Q=q^(2s) det D det Lambda. Equivalently,
det G det S=det D det Lambda. Applying the same periodized-Gaussian
identity to Q yields the exact relaxed-kernel expression

    K_tilde = pi^((r+s)/2)/(q^s sqrt(det D det Lambda))
      * sum_(a in Z^r,b in Z^s)
          exp(-pi^2 [ (a+Wb/q)^T D^(-1)(a+Wb/q)
                       + b^T Lambda^(-1)b/q^2 ]).         (13)

Here a,b are columns. To check the inverse form, solve the transpose of
(x,z)->(x,xW-qz) on a dual frequency (a,b). Its transformed frequencies
are a+Wb/q and -b/q. This proves the displayed inverse quadratic form.
The zero dual frequency gives a prefactor independent of W; all coefficient
dependence is in the remaining nonnegative dual terms. Under W->W+qT,
replacing a by a+Tb reindexes this sum, so modular invariance is explicit.

This does not upper-bound the sum by its zero mode: the zero mode is a
lower bound on the relaxed kernel. It exposes why a large unwrapped Gram
determinant cannot alone certify a small modular kernel. An application
could instead bound or average the nonzero dual terms over the same
coefficient matrices shared by all input rows. Formula (13) supplies no
independence between those rows after the coefficient sum.

## Arithmetic obstruction and what the bridge still needs

Already q=5, r=2, x=(2,−2), and the affine coefficient v=(2,−1) give
xv=6 but [xv]_q=1. Their squared costs are 36 and 1. This is a concrete
integer alias, not a different random-plane model. Large coefficient lifts
can make det G large while simultaneously making S small; the missing aliases
then compensate the apparent unwrapped suppression. W and W+qT represent the
same modular geometry, so estimates based solely on their chosen Gram
determinants cannot be invariant or sufficient without the correction.

The formulation offers a concrete bridge: sum the mixed kernel (11), or the
sharper exact finite kernel (1), over allowed affine coefficient tuples, while
retaining anchor-specific weights and rank eligibility as necessary. An
application must bound that coefficient sum, including the aliases, and show
that its normalized value beats the current completion envelope. For a
normalized weighted expectation, a lower bound for the actual anchor weight
normalizer is additionally necessary; an upper bound cannot be put in its
denominator. No favorable coefficient distribution, actual numerical gain,
or selected-history estimate has been proved here.

Run `python3 docs/research/scripts/wall1_mixed_gram_kernel.py`. Its 1337 exact
rational checks verify (7), the Woodbury identity for S, centered alias
indexing, and the explicit 36-versus-1 example for several affine charts.
A further432 exact checks verify the inverse quadratic form in (13).
The checker does not approximate an infinite theta sum or certify a numerical bound.
