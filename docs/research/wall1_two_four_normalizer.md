# Canonical two-four charts and a stronger anchor normalizer

This lemma applies only to the nine balanced two-four codes on six positions.
It is not a replacement for a bound on all one-four/no-four configurations.
Fix supports C=0123 and D=0145. Choose basis positions(0,1,2,4) and omitted
positions(3,5). Their two-by-two relation minor is diagonal with entries
+/-1, hence is unimodular for every balanced-sign pair. Solving for the
omitted coordinates gives an affine integer4-by-2 matrix A. Each column
has squared norm3 and sum1. The cross inner product is +/-2 for five
triangular codes and0 for four orthogonal codes. Thus

    det(I2+A^T A)=12 (triangle), or16 (orthogonal).

The script `wall1_two_four_normalizer.py` verifies all nine charts exactly.
No summation over arbitrary basis choices is needed: this chart is fixed
by the prescribed supports. Independent extensions still append zero rows
to A, so their normalized dual factors separate as before.

At common anchor weight alpha, define the integer zero-layer theta
K0=sum_x exp(-alpha x^T(I4+AA^T)x). Poisson summation on this rank4 lattice
implies K0 >= (pi/alpha)^2/sqrt(D). The modular anchor kernel includes
this zero layer, while its full dual identity is
K=(pi/alpha)^3/q^2 * psi_A(0). Therefore

    psi_A(0) >= max(h^4, q^2 alpha/(pi sqrt(D))),
    h=theta(pi^2/alpha).

This improves a denominator bound, without claiming that a lower bound
on the kernel is an upper bound on a ball probability. Only a numerator
upper bound divided by this certified denominator lower bound may be used.

For tau=pi^2/(q^2 alpha), put f(x)=sum_z exp(-tau(x+qz)^2).
Because both columns of A sum to1, summing psi_A on a coordinate-sum
hyperplane gives exactly J_A(c)=f^{*6}(c), convolution on Fq. This identity
is independent of the particular A. Fourier positivity gives J_A(c)<=J_A(0),
and the finite Fourier formula is

    J_A(0)=(pi/tau)^3/q
       *sum_(ell modq) [sum_z exp(-(pi^2/tau)(z+ell/q)^2)]^6.

The existing centered-alias binomial expansion can upper-bound this finite
sum with all tails retained. Dividing by q^3 and the lower bound on psi_A(0)
gives an anchor-specific hyperplane eta bound. Free-coordinate moments can
then be joined as in the earlier Holder lemma.

Integration requires: the five/four coefficient families must be
separated from the one-four/no-four theta remainder, and each family must
receive its own complete completion multiplier before summing. Applying
this better normalizer to the entire theta_anchors minimum would be invalid.
This note records a paper lemma and exact chart checks, not a production
improvement or proof of the selected-history law.

## Audited integration design

An additional read-only review approved a split completed candidate. Store
three separate common-theta masses, each with the original anchor prefactor:

    A_triangle = n_triangle * bad_bound^N / coefficient_count,
    A_square = n_square * min(bad_bound^N, square_gaussian^N) / coefficient_count,
    A_rest = four_six_theta_power + none_power.

Use the D12 and D16 normalizers only on the first two masses; use the generic
completion on A_rest. Sum the completed masses before minimizing against old
complete candidates. The square Gaussian must be captured before its direct
ball replacement. Exclusions remove the corresponding5/4 code counts exactly;
the D24 exclusion belongs to the remainder's coefficient classification.

With boost=max(1,q^2 alpha/(pi sqrt(D) h^4)), divide each raw eta numerator
bound by boost before taking min with1. In particular use
min(1,raw_old_eta/boost), not min(1,raw_old_eta)/boost: the latter does not
follow from the two separate bounds. Preserve the determinant flag in the
cache and118-coordinate fallback, and restrict it to an explicitly certified
H6 two-four family. The old selected anchor and other families are untouched.

The exact test now also verifies four hyperplane/convolution identities over
F3 andF5 with two canonical charts and symmetric rational weights. The
nine chart checks and these identities pass. The split candidate is implemented and validated below.

## Implemented split candidate

The helper accepts an explicit anchor_gram_det flag restricted to H6 and
D12/D16. The boost divides both raw hyperplane eta candidates and the raw
old-anchor eta before clipping at1. The flag is present in the cache and
is propagated to the retained118-coordinate candidate. Default behavior
remains the generic bound.

Production retains separate triangle, square and remainder theta masses
for c4,t2,overlap2. Each uses the common anchor prefactor. Both same-weight
and separately weighted free-basis candidates are completed family by
family and summed. The previous candidates remain available; witness
multiplicity and the final factor1/2 are applied as before. The frontier
captures the new masses and cap dictionaries and reconstructs this extra
candidate before its interval comparison.

Only the denominator improvement is integrated at this checkpoint. The
exact six-fold hyperplane convolution formula remains unused, so it must
not be counted as part of a claimed numerical improvement.

## Part 434 validation checkpoint

Independent implementation review approved the classification, exclusions,
normalization, cache keys and118 fallback. Nine exact chart checks, four
exact hyperplane/convolution identities and six determinant-specific scalar
completion/cache cases pass. The full runs both exit0:
`/tmp/wall1_two_four_normalized_cumulants.log` and
`/tmp/wall1_two_four_normalized_frontier.log`. All2106 exact cumulant checks
and18 independently reconstructed frontier interval comparisons pass.

Through17 is below3.219e-17; through24 is below5.931e25 and remains an
ineffective envelope against the3.01e-12 target. It is not a failure
probability. The size24 leader is now rank8/girth4, H8 t4/overlap3 with
2 free extensions. The neighboring rank7/girth4 and rank9/girth4 strata
are also substantial. This supersedes the Part433 six-point leader.

A read-only audit of the next H8/H9 families identifies a safe isotropic
one-four counterpart: save one_power before weighted short-pair minima,
reconstruct the filtered determinant sum with fixed_four_plane(D/4),
retain the higher-norm remainder, and snapshot before direct_one. These
are next-step candidates, not part of the Part434 numerical checkpoint.
The full transfer target, actual selected histories and full BKZ remain open.
