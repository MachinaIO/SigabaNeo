# A weighted pivot bound for shared dual coefficients

The rank identity in `wall1_dual_coefficient_rank.md` alone preserves the
full coefficient count. Keeping the periodic Gaussian weights gives the
following upper bound, without treating coordinates as independent after
coefficient averaging. It still requires summing the dual-frequency weights.

## Fixed dual matrix and arbitrary offset

Let q be prime, d=r-1, and V range over all r-by-k matrices over F_q with
each column summing to one. Let B be a fixed k-by-n matrix of rank t and
O any fixed r-by-n matrix. Let f:F_q->[0,infinity) have maximum h>0 and
sum Q. Then

    sum_V product_(j=1..r,i=1..n) f((VB+O)_(j,i))
      <= q^(d(k-t)) (h Q^d)^t h^(r(n-t)),                  (1)

or, dividing by the exact number q^(dk) of V,

    E_V product f((VB+O)_(j,i))
      <= h^(rn) (Q/(qh))^(dt).                            (2)

Choose t independent columns of B. The first d rows of V are free; their
images on these columns range independently over F_q^t, each with fiber
q^(k-t). The last row of V is fixed by the column-sum condition. Thus each
selected column of VB+O ranges over an affine hyperplane of prescribed
coordinate sum. Summing its product of f gives at most h Q^d: freely sum
the first d coordinates and bound the last factor by h. All unselected
columns contribute at most h^r each. This proves (1). No condition on the
column sums of O is needed. The pivot columns can depend on B; no union
or binomial multiplicity is introduced, since the same bound holds for
any valid choice. Degenerate cases t=0 and r=1 are included.

For the isotropic basis weight D=alpha I_r, alpha>0, in the joint dual
kernel, use the periodic function

    f(x)=sum_(z in Z) exp(-pi^2 (z+x/q)^2/alpha).

The shifted-Gaussian maximum gives h=theta(pi^2/alpha), where
theta(u)=sum_(z in Z)exp(-u z^2). Reindexing qz+x gives
Q=theta(pi^2/(alpha q^2)). Thus (2) is an explicit Gaussian coefficient
average. In particular Q<=qh, and the rank-dependent factor is at most one.
This bound is uniform in the anchor offset O=A B_anchor, so that offset
need not be independent of any selected anchor.

## A bound for the full relaxed input kernel

Fix an extra-anchor coefficient matrix A with s_A columns. Its weights
are positive diagonal entries lambda_j; completion weights are gamma>0.
Put s=s_A+k and retain the relaxed kernel K_tilde from
`wall1_mixed_gram_kernel.md`. Its joint dual prefactor is

    C=pi^((r+s)/2)/(q^s sqrt(alpha^r * product_j lambda_j * gamma^k)).

Define tau_j=pi^2/(q^2 lambda_j), tau=pi^2/(q^2 gamma), and
zeta=(Q/(qh))^d. Let B have k*n independent integer entries with probabilities
exp(-tau b^2)/theta(tau), and take its rank modulo q. Nonnegative summation
of (1), including every anchor dual frequency, gives

    sum_V K_tilde([A,V])^n
      <= q^(dk) C^n h^(rn)
           * product_j theta(tau_j)^n * theta(tau)^(kn)
           * E[zeta^(rank(B mod q))].                     (3)

The distributions in this expression normalize the Gaussian frequency sums;
they are not assertions that actual selected anchors or lattice vectors
are independent. Their independence is simply the factorization of the
bare diagonal frequency weight. The anchor offset was bounded uniformly
before those sums were normalized. That step may lose important anchor
geometry, so (3) is not promised to improve the current estimate.

Equation (3) is for a fixed A and isotropic D. The actual mixed-fiber bound
must also retain the output-anchor kernel q^(-mr)K_output(A)^m, the ball
Chernoff prefactors, and any sums or multiplicities of anchor coefficient
charts. Distinct/pinned completion restrictions can be dropped only as a
nonnegative enlargement of their unnormalized sum. No extra q^(dk) factor
is to be multiplied into (3).

For 0<zeta<=1 and rank R in {0,...,k}, the exact tail identity is

    E zeta^R = zeta^k
        + sum_(t=0)^(k-1) (zeta^t-zeta^(t+1)) Pr[R<=t].    (4)

Thus rigorous upper bounds for low-rank Gaussian matrices can be inserted
without replacing the frequency law by uniform residues. The relevant
frequency temperature is tau=pi^2/(q^2 gamma), not gamma itself. In particular
small primal gamma does not imply a nearly uniform dual residue distribution.

## Scope and verification

The fixed-matrix argument received an independent mathematical audit. The
companion script checks (1) and (2) exactly for all2-by-2 dual matrices over
F3 and F5 at two offsets, using a rational periodic weight, and checks (4)
for eighty finite distributions. The proof covers the actual periodic
Gaussian; the finite rational examples test the algebra and count factors.

No infinite theta sum is numerically truncated by this script. Equation (3)
has not been evaluated as a production improvement. Bounding the complete
expression, including the anchor comparison and any lost offset geometry,
remains necessary for the BKZ proof.
