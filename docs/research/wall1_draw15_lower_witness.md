# A signed lower witness for the actual draw15 raw count

The existing [reference barrier](wall1_affine_reference_barrier.md) rules out
an independent-reference upper certificate at draw15. The following witness
also applies to the actual raw count. The subsequent [complete incidence
transfer](wall1_draw15_incidence_transfer.md) now bounds its factorial-moment
discrepancy and proves an averaged raw-void lower bound. Neither note
bounds selected projected void or BKZ failure from below.

Let Z be the nonnegative integer raw fiber-hit count at the fixed draw15
radius of the reference note, and let mu=E Z. The established candidate-count
upper bound gives0<=mu<9.287185 under the original matrix law. This does not
condition on the selected state. Define a polynomial Q of degree10 with
Q(0)=1 as follows. Write (z)_i for the falling factorial, and, for a Poisson
variable X of mean10, set

    M_ij=E[(X)_i(X)_j]
        =sum_(k=0)^min(i,j) binom(i,k)binom(j,k)k!10^(i+j-k),
    H_ij=M_(i+1,j)+(i-1)M_ij,
    (c_1,...,c_10)^T=-(H_ij)_(i,j=1)^10^(-1)(H_0j)_(j=1)^10,
    Q(z)=1+sum_(i=1)^10 c_i (z)_i,
    g(z)=(1-z)Q(z)^2.

The script constructs these rational coefficients by exact elimination.
The matrix is invertible: for a nonzero polynomial R with R(0)=0,
E[(X-1)R(X)^2]>0, since the summands at integers X>=2 are nonnegative
and infinitely many have positive Poisson mass. This construction chooses
one fixed polynomial; it does not set the actual mean equal to10.

For every nonnegative integer z, g(z)<=1{z=0}. At zero there is equality;
at positive integers1-z<=0. Expand g(z)=sum_(j=0)^21 a_j(z)_j and define
F(u)=sum_j a_j u^j=E_Poisson(u) g. Exact Bernstein coefficients on40 equal
subintervals certify

    F(u)>0.0000647  for all0<=u<=9.287185.

Thus the argument does not rely on monotonicity in an unknown mean.
Bernstein basis functions are nonnegative and sum to one on each interval,
so the smallest exact coefficient is a lower bound for that interval.

## Actual-law transfer and the missing estimate

For the actual factorial moments f_j=E[(Z)_j], put

    Delta=sum_(j=2)^21 |a_j| |f_j-mu^j|.

The zeroth and first discrepancies vanish identically. By linearity and
the triangle inequality,

    Pr(Z=0)>=E g(Z)>=F(mu)-Delta>0.0000647-Delta.

In particular Delta<0.00006 would prove an actual raw-void lower bound
greater than0.0000047. Conversely, an actual raw void at most10^(-12)
would require Delta>0.000064699999. The subsequent complete incidence transfer certifies Delta<1e-25. The result concerns the fixed raw candidate family only:
projected witnesses can have long raw lifts and can still cover missed marks.

The existing draw14 moment pipeline cannot be reused unchanged. Its raw
dimension518, input count118, radius exponent386, mean-floor assertions and
squared-kernel weights are specialized to draw14. Draw15 uses519,119,385
and the signed witness above. Its exact finite-difference weights, if using
the factorial-cumulant expansion, are

    E_Poisson(mu)[Delta_forward^k g(X)]
      =sum_(j=k)^21 a_j*j!/(j-k)!*mu^(j-k).

These replace the squared-kernel-specific `difference_weights` routine.
Neither the existing draw14 total error nor an unsigned reference lower
bound certifies the needed draw15 discrepancy. The subsequent complete
incidence transfer separately instantiates this new geometry and supplies it.
The[odd-dimensional kernel extension](wall1_odd_relation_counts.md) now
removes the even-dimension restriction from three direct count helpers.
It is used by the new geometry-specific incidence entry point.

## Fixed-mean alternative for a cumulant transfer

Independently append Y with Poisson mean10-mu, which is nonnegative.
Then Pr(Z=0)>=Pr(Z+Y=0), and the factorial cumulants of Z+Y are10
at order1 and those of Z at every higher order. Define

    e_k=[t^k] exp(sum_(j=2)^21 kappa_j t^j/j!),
    w_k=sum_(j=k)^21 a_j*j!/(j-k)!*10^(j-k).

The polynomial transfer identity gives exactly
E g(Z+Y)=F(10)+sum_(k=2)^21 w_k e_k, with F(10)>0.0000247527
by rational comparison. If actual-law bounds |kappa_j|<=C_j were proved,
the nonnegative series with C_j in place of kappa_j would bound |e_k|.
Thus the sum of |w_k| times those coefficients would be a sufficient error
charge. This fixes the weights without knowing mu, at the cost of the
smaller baseline. It does not supply the missing C_j. The checker verifies
the padding and generic cumulant identity exactly on the same four laws.

Run `python3 docs/research/scripts/wall1_draw15_lower_witness.py`.
The checker constructs the coefficients, certifies the entire mean interval
using rational Bernstein bounds, and checks the factorial-moment identity
on four finite laws. These computations verify the lower witness and its
transfer formula, not the production discrepancy.
