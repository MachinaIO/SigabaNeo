# Size 19, rank 10, girth 6: the actual H10 bottleneck

The selected H10 kernels at t=4 and overlaps 2 and 4 are controlled by the
weighted determinant-32 two-six family. Refining the one-six/eight or no-six
branches cannot materially improve this selected bound. Conditional on the
existing D27 exclusion, their ratios to the selected local kernel are:

| overlap | log10 one-six / selected | log10 no-six / selected |
| --- | ---: | ---: |
| 2 | -16.89096980664 | -25.83278415593 |
| 4 | -16.89096980664 | -18.78815656562 |

These are comparisons of full upper envelopes, not event frequencies.
The parent has not integrated any change from this note.

## A small complete improvement to the controlling kernel

The two unit-six rows a,b have two shared positions with agreeing signs,
so their ordinary Gram determinant is 32. Give the two shared coordinates
weight w and each of the eight exclusive coordinates weight
z=(10-2w)/8. The sum of coordinate weights remains ten, so the existing
weighted Gaussian Markov normalization is unchanged. In the inverse-weight
metric their squared GS lengths are

    g1 = 2/w + 4/z,
    g2 = (16/(w*z) + 16/z^2)/g1.

Their unit minor gives saturation independently of the weights. The
weighted determinant including the Jacobian is

    F(w) = w^2*z^8*g1*g2 = 16*w*z^6*(z+w).

For positive w,z, the derivative of log F has the sign of
z^2+w*z/4-3*w^2/2. Its sole positive stationary weight is
w*=10/(1+sqrt(97)); F increases before and decreases after that point.
This optimizes the continuous determinant proxy, not automatically the
full discrete theta kernel. Use the rational candidate w=921/1000 and
z=4079/4000, compared to the existing w=11/12 and z=49/48. Rational
arithmetic verifies F(921/1000)>F(11/12)>32. Full interval comparison,
including all tails, separately verifies that the candidate improves the
actual kernel.

Write beta=8N/(20R^2), a0=pi^2/beta, alpha=a0/q^2. For these weights,
z is the largest coordinate weight. The same existing cutoff-36 argument
therefore uses

    scaled_alpha=alpha/z, scaled_a=a0/z,
    delta=2*exp(-scaled_a/4)/(1-exp(-2*scaled_a)),
    E=sum_(j=1)^10 binomial(10,j)*delta^j,
    T=exp(-648*scaled_alpha)*theta(5*scaled_alpha/2)^2.

The full weighted kernel is

    K(w)=(pi/beta)^5/(w*z^4) *
       ((theta(g1*alpha)*theta(g2*alpha)+T)/q^2+E).

All long-vector and periodic errors remain included. This is the existing
valid weighted D32 bound with another positive weight vector of the same
total weight; no new exclusion or omitted complement is involved. Minimize
K(921/1000) with the previous weighted/unweighted D32 kernels. The other
Gram-36, one-six, and no-six terms remain unchanged.

## Actual selected comparison and limits

`wall1_six_ten_frontier_refinement.py` uses the AST return-capture helper,
without global tracing, to obtain the actual local anchors and completion
bounds from `draw14_bounds(exclude_nine_twenty_seven=True)`. It reconstructs
the old two-six terms to relative tolerance 1e-60, including the 52 D32
charts at each overlap and the additional 48 D36 charts at overlap two.
It also verifies that the recorded local selected kernels equal the
normalized anchors actually used by the residual sum.

The log10 improvement in the D32 N-power is -0.00240941586249. The full
selected local improvement is -0.00240941586249 at both overlaps to the
shown precision. Recomputing the complete rank-10, girth-6 size-19 residual
with the unchanged one-circuit competitor gives

    log10(new residual / old residual) = -0.00240941205091.

This is only about a 0.55 percent reduction. It is not a route to closing
the remaining orders-of-magnitude gap. Sharper counts in the branches that
are already 16 or more decimal orders below the controlling term would
have even less effect. A substantial improvement requires a different
bound on the D32 family itself, or a higher-rank crossing cover with its
complete residual and addbacks; the rank-nine-only D32 anchor cover cannot
simply be reused at rank ten.

Reproduce with
`python3 docs/research/scripts/wall1_six_ten_frontier_refinement.py`.
The interval log is `/tmp/wall1_six_ten_frontier_refinement.log`.
No production files, selected-history estimates, or cost claims change.
