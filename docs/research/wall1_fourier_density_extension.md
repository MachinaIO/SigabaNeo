# Extend the existing Fourier count and return to a variance target

Parts 215 and 217 already prove a stronger candidate-density estimate than
the elementary rounding estimate of Part 475, on their original radius and
draw range. The following extension covers the smaller radius used in
Parts 472–476 and all scalar floors through freeze 406. It is a deterministic
count improvement, not a proof of selected-history concentration or BKZ.

## Count extension

Write b=505/2, D=h det(K)=V_506 g^506, and R²=1.21g²−2.
The existing determinant floors and D≤q^400 give
31.9457118986<g≤3337.6399803623. Put beta=(b+2)/R².
The open cell |beta||y||²−b|<2 is contained in B_R and excludes zero.
The largest beta is below the Part 215 reference beta. Its complex-Gaussian
Fourier error bound increases with beta, so the same minorant supplies
normalized tilted mass greater than .01060. The accompanying checker also
re-evaluates all three frequency bands and the continuum gamma-density bounds.

Undoing the tilt proves, for the number A of points in this cell,

    A/h > .01060 exp(b−2) [pi(1.21g²−2)/(b+2)]^b / (V_506 g^506).

The logarithmic derivative with respect to log(g) is
−1+1010/(1.21g²−2)<0 throughout the interval. Evaluation at its upper endpoint
therefore gives the uniform lower bound

    A/h > 16786646102249696.79 > 10^16.

This is an extension of the [existing Fourier minorant](wall1_fresh_mark_extension.md)
and [uniform mean argument](wall1_long_winner_ceiling.md), not a new discovery
that these candidate families have large mean. Parts 474–475 provide a separate
elementary counting method; their weaker density should not be treated as the
best available bound.

## Exact mean and the remaining variance obligation

For h>1, choose L=mu(h−1) distinct cell points by a deterministic geometric
ordering, where mu=10^16. The count above guarantees enough points. Use an
ordering fixed by the projection geometry and h, before the fresh mark is read;
no selection by their unknown quotient labels is required.

On the entry-measurable gate G={h>1, lambda_1(M)>1.1g}, all these nonzero
points have nonzero labels. With U uniform in H conditional on the full entry
history, let Z count points whose label equals U. Then

    E[Z | entry history, U!=0] = L/(h−1) = mu.

This does not require independent labels. A next winner longer than 1.1g
requires G, U!=0, and Z=0: any counted point gives a height-one vector with
squared norm at most R²+1=1.21g²−1. The h=1 case has a unit-height witness;
the scalar floors ensure 1.1g>1.

For an actual reached entry i, define the unnormalized moment

    T_i = E[1_G 1_{U!=0} (Z−mu)²].

The sufficient, **unproved** aggregate obligation is

    sum_i T_i <= 405*40*mu.

It implies that the probability of any long winner among those 405 transitions
is at most 405*40/mu=1.62e-12. A stronger per-entry conditional variance bound
of 40mu would suffice, but is not necessary. The aggregate formulation allows
rare bad histories and does not divide by a rare gate probability.

Equivalently, since the gated first moment is exact, with
a_i=P(G and U!=0) and
C2_i=E[1_G 1_{U!=0} ((Z)_2−2mu Z+mu²)], one has
T_i=a_i mu+C2_i. Thus C2_i≤39 a_i mu is one sufficient per-entry bound.
Neither this collision bound nor the aggregate bound is established here.

The [existing long-winner count implication](wall1_long_winner_routes.md)
connects a small-g crossing on draws 396–406 to at least 100 long winners
among the first 405 transitions. Hence the much stronger event bound above
would also bound that crossing. It does **not** control the smaller-radius
capped-void potential, and its numerical comparison with the 1.9515491e-12
residual budget does not justify exchanging the two events in a proof.
Other BKZ obligations remain unchanged.

The [full-family variance analysis](wall1_full_family_variance.md) improves
this sufficient reduction: the crossing needs 100 long winners, so charging
their expected number permits a 100-times larger aggregate moment budget.
It also shows why uniform thinning cannot improve relative variance on average.

## Verification

`python3 docs/research/scripts/wall1_fourier_density_extension.py` passes with
80-digit outward-rounded interval arithmetic. An independent mathematical
review checked the radius change, monotonicity, zero exclusion, exact conditional
mean, and union bound. No selected-history variance estimate or Lean theorem
is claimed by this check.
