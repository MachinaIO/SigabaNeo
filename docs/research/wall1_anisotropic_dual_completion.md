# Different Gaussian weights for independent basis extensions

The original anchor keeps its common temperature alpha, while f additional
independent basis points receive a separate positive temperature beta_free.
This is an explicit anisotropic extension of the anchored multiplier, not
permission to reuse arbitrary anisotropic selected-anchor estimates.

Let H0=r0+2 be the original two-relation anchor, and r=r0+f the extended
augmented rank. In an extended basis the two extra anchor columns are
A_ext=[A0;0]. Set

    D=diag(alpha I_r0, beta_free I_f), Lambda_A=alpha I_2.

The integer code theta factors for both input and output coordinates:

    K_ext=K_anchor(alpha)*theta(beta_free)^f.

The Chernoff factor is exp((H0*alpha+f*beta_free)R^2) and the output
normalization is q^(-400r). Consequently each added independent point
costs exp(beta_free R^2)*theta(beta_free)^518/q^400. Dependent completions
still impose input occupancy only, so their frequency rank law uses118
coordinates. The original anchor probability and its coefficient-chart
counts are not altered.

## The anisotropic hyperplane estimate

For each basis weight D_i>0, define

    phi_i(x)=sum_z exp(-pi^2*(z+x/q)^2/D_i),
    h_i=phi_i(0), Q_i=sum_(x in F_q)phi_i(x), rho_i=Q_i/(q h_i).

Sum the two anchor dual frequencies first, with tau_A=pi^2/(q^2 alpha):

    psi_A(x)=sum_(b in Z^2) exp(-tau_A||b||^2)
                              product_i phi_i(x_i+(A_ext b)_i).

As before, Gaussian Fourier positivity gives psi_A(x)<=psi_A(0), and
b=0 gives psi_A(0)>=product_i h_i. In a coordinate-sum hyperplane, freely
sum all coordinates except any selected j and bound its remaining factor
by h_j. Therefore the normalized hyperplane maximum is at most

    eta_bar=min(1, min_j theta(tau_A)^2*product_(i!=j)rho_i). (1)

For the two weight groups this becomes the minimum of

    1,
    theta(tau_A)^2*rho_old^(r0-1)*rho_free^f,
    theta(tau_A)^2*rho_old^r0*rho_free^(f-1)  [only if f>0].

The frequency pivot argument applies unchanged to this eta_bar. The basis
and extra-anchor determinants cancel from the ratio of the completed and
anchor Gaussian prefactors. Thus the completion multiplier remains

    q^((r-1)k)*exp(k gamma R^2)*theta(q^2 gamma)^(118k)
                  *upper_bound E[eta_bar^rank(B mod q)],

where k=h-r-2 and B has independent bare integer Gaussian entries with
exponent pi^2/(q^2 gamma). Every low-rank tail is retained. This auxiliary
product law is not an independence assumption about selected anchors.

The witness multiplicity f+1 and final double-four symmetry correction
are exactly those proved for the same-temperature extension. Each witness
still has a nonnegative Gaussian majorant, irrespective of its weight.

## Candidate choice and implementation

Production keeps three separately valid completed bounds: the old bound,
the same-temperature anchored candidate, and this new candidate with
beta_free=518/(2R^2). This is the continuous-Gaussian optimum for a single
point, adopted as an admissible choice; no exact finite-theta optimality
is claimed. The original alpha=(H0-2)*518/(2H0 R^2) remains unchanged.

Only the separately stored common-alpha theta anchor envelope is used by
the two new candidates. The existing selected direct-ball and differently
weighted anchor bounds remain solely in the old candidate. The helper
cache distinguishes both temperatures, H0, total r, k, radius and precision.
When f=0 the irrelevant free weight is discarded and the previous cap is
reused. The frontier captures and reconstructs every completed candidate.

The derivation and implementation received independent read-only reviews.
`wall1_anisotropic_dual_completion_check.py` verifies81 exact shared-coefficient
sums over F3 with unequal positive Fourier weights and a nontrivial anchor
convolution. It checks the hyperplane maximum, both drop-coordinate bounds,
and the actual coefficient average against the pivot upper bounds. Small
API checks also covered equal weights, no free points, and k=0. These are
finite checks of the identities; the general Gaussian proof is above.

No new selected-history result or Lean theorem follows from the extension.

## Integrated validation checkpoint

`/tmp/wall1_anisotropic_dual_cumulants.log` passes240 exact Poisson/cumulant
checks and1866 connected-support checks. Through17 is below2.666e-13.
Through24 is about1.96044e153; this is still an ineffective upper envelope,
not an actual failure probability.

`/tmp/wall1_anisotropic_dual_frontier.log` passes all18 selected-cover and
remainder reconstructions. The size24 leader is rank9/girth3 with crossing
t3/overlap2 (six-point anchor) and5 free basis points. Its selected cover
is the unrestricted two-relation candidate. These results do not close
the residual transfer or the adaptive selected-history law.
