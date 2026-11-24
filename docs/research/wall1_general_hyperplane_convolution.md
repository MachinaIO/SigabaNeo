# General affine Gaussian hyperplane convolution

Let the r basis weights be D_i>0 and the two anchor weights be alpha>0.
Every column of A_ext has coordinate sum1 moduloq. Put

    tau_i=pi^2/(q^2 D_i), f_i(x)=sum_z exp(-tau_i(x+qz)^2),
    tau_old=pi^2/(q^2 alpha).

Summing psi_A over the hyperplane sum(x)=c gives exactly the convolution
of the r basis functions and two additional f_old functions, evaluated
at c. Summing anchor frequencies by residues supplies these last two
factors; symmetry absorbs the sign. This uses only affine column sums,
not small coefficients or independence of actual anchors.

All finite Fourier coefficients of these periodized Gaussians are positive.
Consequently the convolution has maximum at0. Set a=q^2 alpha,b=q^2 beta_free,
m=r0+2, and f=r-r0. Poisson summation gives

    J(0)=(q sqrt(alpha/pi))^m (q sqrt(beta_free/pi))^f
         * [q^-1 sum_(ell modq) phi_a(ell/q)^m phi_b(ell/q)^f],
    phi_a(u)=sum_z exp(-a(z+u)^2).

For centered u in[-1/2,1/2], phi_a(u)<=exp(-a u^2)+delta_a,
where delta_a=2exp(-a/4)/(1-exp(-2a)); similarly for b. Expand both powers.
The raw Fourier average is bounded by

    sum_(j=0)^m sum_(l=0)^f binom(m,j)binom(f,l)
      delta_a^(m-j)delta_b^(f-l) T(j,l),
    T(0,0)=1, T(j,l)=theta((ja+lb)/q^2)/q otherwise.

The zero term averages over q residues and is exactly1. No second1/q
factor belongs outside this expression. This is an unnormalized average:
it is not divided by h and is not clipped at1.

Divide Jupper by q^(r-1) and the established lower bound on psi_A(0),
h_old^r0 h_free^f times any separately certified chart boost. Minimize the
result against1 and the previous hyperplane bounds. For the old-anchor
eta used in the free-coordinate Holder argument, apply the same calculation
with f=0 and rank r0. Both candidates preserve all aliases and tails.

The mathematical derivation and implementation received independent audits.
Four exact mixed-weight convolution fixtures and twelve interval Gaussian
envelope checks pass. All old bounds remain available. Production results
are recorded below. No selected-history theorem is claimed here.

## Part 436 validation checkpoint

Both full runs exit0: `/tmp/wall1_convolution_eta_cumulants.log` and
`/tmp/wall1_convolution_eta_frontier.log`. All2106 exact cumulant checks and
18 frontier interval reconstructions pass. Through17 remains below3.219e-17;
through24 is below2.981e10 and still ineffective against the3.01e-12 target.
These are upper envelopes, not actual failure probabilities.

The size24 leader remains rank9/girth4, with the H7 shared-four family
still the next targeted normalizer improvement. The candidate in
`wall1_shared_four_normalizer.md` has a proof audit and18 exact chart checks,
but is not included in these results. Selected histories and full BKZ
remain unproved; no Lean formalization is claimed here.
