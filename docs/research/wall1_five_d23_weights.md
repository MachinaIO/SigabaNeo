# Five-position determinant-23 weighted kernel

For the prescribed H=5, first-circuit support {0,1,2} and second support
{0,1,3,4}, the one-four split remaining after removal of determinant 20 is

    (6 K_23^N + 6 K_24^N + 12 K_31^N + 15q K_36^N)/q^3.

Here K_D is the complete fixed-four Gaussian kernel with second squared
Gram--Schmidt length D/4, and K_36 denotes the remaining height-nine term.
At the current draw-14 parameters the determinant-23 term dominates. The
other three terms divided by it have log10 values -4.78720207475,
-33.2741391761, and -46.4745842674 respectively. These are upper-envelope
comparisons, not measured probabilities.

## Geometry and applicability

Write a for the balanced norm-four integer row and b for a balanced norm-six
row in a determinant-23 plane. They have dot product +/-1. On five positions,
b must have shape (2,-1,-1) up to sign and permutation. Full support forces
its support to intersect the four-support of a in exactly two positions. The
shared coefficients of b have magnitudes 2 and 1, with opposite signs after
multiplication by the corresponding entries of a. The remaining coordinate
of b has magnitude 1. Thus there are two shared positions, two a-only
positions, and one b-only position.

Choose weights

    w_i = 3/20 on the two shared positions,
          47/30 on the three exclusive positions.

They are strictly positive and sum to five. For the inverse-weight inner
product `<u,v>_w = sum_i u_i v_i/w_i`, direct rational calculation gives

    <a,a>_w = 2060/141,
    <b,b>_w - <a,b>_w^2/<a,a>_w = 149730/4841,
    product_i w_i = 103823/1200000,
    product_i w_i * det Gram_w(a,b) = 234577/6000 > 23.

An a-only and b-only column give a minor +/-1, so a,b generate the saturated
integer lattice in their rational plane. This justifies using their exact
weighted Gram--Schmidt lengths. No weighted Gauss-reduction assumption is
required for the successive one-dimensional theta upper bounds.

All 60 balanced full-support norm-four/norm-six D23 pairs satisfy these
identities. Exhaustive normalization at q=7,17,3329 gives the same six
prescribed coefficient charts, and the check excludes a second norm-four
line. The weights are assigned from the actual rows, so no coordinate sign
change that might destroy affine balance is used to transport counts.

A norm-eight partner with determinant 23 has dot product +/-3 with a.
Subtracting the corresponding sign of a produces a balanced norm-six partner
of the same integer plane. The union of supports remains all five positions:
on the one position outside a the new partner is unchanged. Hence such a
norm-eight presentation is also covered. The script checks its normalized
chart belongs to the same six-chart family.

## Complete kernel, including tails

Use the existing H=5 beta, a=pi^2/beta, alpha=a/q^2, and cutoff L=40. Put

    s = 30/47,
    d = 2 exp(-s*a/4)/(1-exp(-2*s*a)),
    T = exp(-800*s*alpha) theta((5/2)*s*alpha/2)^2,
    E = sum_{j=1}^5 binomial(5,j) d^j.

A valid weighted complete kernel is

    K_w = (pi/beta)^(5/2) sqrt(1200000/103823)
          * ((theta((2060/141)*alpha)
              * theta((149730/4841)*alpha) + T)/q^2 + E).

The weight sum preserves the original Markov factor exp(5 beta R^2).
The existing short-plane lifting uses the *unweighted* cutoff and is
unchanged. Since the maximum weight is 47/30, the inverse-weight quadratic
form dominates (30/47) times the unweighted form. This gives the displayed
scaled tail and periodic correction; neither may be dropped. Multiplication
by the inverse square root of the weight product is necessary as well.

Production can replace K_23 by min(K_23,K_w), retaining its coefficient six,
and leave the remaining determinant terms untouched. This excludes no family
and therefore needs no separate anchor addback.

## Complete-kernel verification

The standalone script retains every tail and periodic term and uses the
existing 80-digit interval parameter calculation. It verifies

    log10((K_w/K_23)^518) = -58.97925877067...,
    log10(new complete one-four split / old split) = -4.78720916365....

The determinant-24 term becomes the largest retained term, explaining why
the complete split improves much less than the determinant-23 kernel alone.
These assertions concern the one-four split; improvements to the complete
size/rank envelope require the parent integration and its full regression.

A near-boundary determinant optimization is misleading here. The initially
considered weights 1/100 on shared positions and 83/50 elsewhere improve
the weighted determinant product but worsen the complete kernel to a power
by roughly 283 decimal orders. The inverse weight prefactor and the discrete
theta values must be evaluated, not replaced by their continuous determinant
approximation. The chosen rational weights passed that complete check.

Reproduce with

    python3 docs/research/scripts/wall1_five_d23_weights.py

Observed output: `/tmp/wall1_five_d23_weights.log`. Exact rational checks and
interval kernel assertions pass. This note does not prove the remaining
sizes 17--24, selected BKZ histories, or a Lean formalization.

## Integrated verification

The production envelope now uses min(K_23,K_w). Combined with the exact H6
two-six classification, the complete size17 weighted residual has log10
-9.422463228182312 (about3.7804e-10). All2106 cumulant regression checks
pass. Logs are `/tmp/wall1_h5_d23_weighted_cumulants.log` and
`/tmp/wall1_h5_d23_weighted_components.log`. The through16 certified cap
is unchanged, and the through24 envelope remains ineffective at about7.03e226.
The leading remaining strata are rank8/girth4, rank6/girth4 and rank9/girth6.
