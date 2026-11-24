# Anchored dual completion with additional independent basis points

The anchored dual multiplier extends to the free basis points in the
production two-relation cover, provided they are Gaussian-majorized at the
**original anchor temperature**. This does not permit multiplication of a
selected direct-ball or anisotropic anchor minimum by that multiplier.

Let H0=c+t, r0=H0-2, total augmented rank r, and f=r-r0>=0. Choose f
additional independent input points to extend the original anchor basis.
In that extended basis the two extra anchor coefficient columns are
A_ext=[A0;0], with f zero rows. All columns remain affine. At the same
positive beta on every position, the integer theta kernel factors exactly:

    K_ext(beta)=K_anchor(beta)*theta(beta)^f.

Thus the anchor and free-point Gaussian incidence expression is

    exp((H0+f)*beta*R^2)*K_ext(beta)^518/q^(400*(r0+f))
      = [exp(H0*beta*R^2)*K_anchor(beta)^518/q^(400*r0)]
          * mu_G(beta)^f,
    mu_G(beta)=exp(beta*R^2)*theta(beta)^518/q^400.          (1)

After conditioning on a valid extended basis, its output values are
independent uniform values of the affine map. Relaxing eligibility in the
nonnegative Gaussian input sum is valid only after this normalization is
fixed. Formula (1) accounts for both the118 input and400 output coordinates
of each new independent point. These independent points differ from the
remaining dependent completions, which impose input occupancy only.

There are k=h-r-2 dependent positions after the extension. The anchored
dual cap is evaluated at total r and k, but with

    beta=(H0-2)*518/(2*H0*R^2),

not the temperature recomputed from r+2. All extra positions have the same
beta, so the established isotropic anchored lemma applies without a new
anisotropic estimate. The two nonbasis columns and their Gaussian weights
are unchanged. The cache must retain this beta as well as total r and k.

## Multiplicity and the completed candidate

The original division by f+1 remains valid. Contracting the anchor in the
connected configuration leaves a coloop-free matroid of rank f. It has
at least f+1 bases: for f>0, fix a basis and, for each of its f elements,
use absence of a coloop to exchange that element, producing f distinct
additional bases. For f=0 the empty basis suffices. Loops do not affect
this argument. Contraction cannot introduce a coloop, as is also seen by
duality with deletion, which cannot introduce a loop.

Every actual configuration is therefore represented by at least f+1
extension-basis witnesses. The Gaussian majorant for each witness bounds
the actual indicator, even if its value depends on the chosen basis.
Summing those majorants and dividing by f+1 is still an upper bound.
No independence or uniform distribution of the selecting witnesses is used.
The existing circuit-position counts and coefficient-chart counts remain
unchanged. The special double-four symmetry factor is applied afterward.

For a common-beta theta anchor envelope A_theta, the new candidate is

    choices*q^(c+t+a-4)*A_theta*mu_G(beta)^f
            *dual_cap(r,h;beta)/(f+1).                    (2)

It is minimized against the **old completed bound**, not inserted into the
old selected anchor envelope. At f=0, (2) recovers the earlier full-anchor
candidate exactly. Terms using direct-ball or anisotropic anchor estimates
remain available through the old completed candidate.

## Implementation and verification scope

`wall1_anchored_dual_completion.py` accepts `anchor_size=H0`, computes beta
from H0, and includes its exact interval in the cap cache key. The production
caller separately computes mu_G; the helper does not include it or any
anchor/output normalizer. The frontier records and reconstructs both
`extended_dual_completions` and `gaussian_free` along with `theta_anchors`.

The mathematical extension received an independent read-only review before
implementation. Both full evaluations completed successfully with these additional
candidates. This note does not assert that they close
sizes18–24 or the selected-history bound.

## Integrated numerical checkpoint

The cumulant run `/tmp/wall1_extended_dual_cumulants.log` passes240 exact
Poisson/cumulant and1866 connected-support checks. Its interval upper endpoint
through17 is below2.752e-13. Through24 is about2.5742e194, still an ineffective
upper envelope rather than an actual failure probability.

`/tmp/wall1_extended_dual_frontier.log` passes all18 selected-cover/remainder
reconstructions. The size24 leader is rank12/girth3, with crossing t2,
overlap2 and9 free basis points. This identifies a cost left by using the
small original anchor's temperature on all free points. A different free-point
temperature requires an explicitly anisotropic version of the anchored lemma;
it is not justified merely by changing the existing scalar parameter.

No selected-history law or new Lean proof has been established at this
checkpoint. The full BKZ objective remains open.
