# Weighted H7 determinant-28 remainder kernel

This improvement concerns the remaining term of the D28-ten cover selected
for size 17, rank 8, girth 4 in Part 393. The diagnostic uses precisely that
cover's exclusions; it does not add the unselected D31-eleven exclusion.

The largest raw remaining term is `(r,c,t,overlap)=(8,4,3,2)`, with relative
log10 -0.12982224378 in the selected residual. The next is `(8,4,2,2)`, with
relative log10 -0.58786517902. The first term is controlled by its one-four
part; its no-four part is smaller by 22.6648 decimal orders. Thus refining
its two-six/no-six subparts would not materially change the selected bound.
The new diagnostic `wall1_rank_eight_remaining_diagnostic.py` records these
values without editing the production source.

## Geometry

Let a be a balanced norm-four row on C={0,1,2,3}, and b an independent
balanced norm-eight row in a full-support plane on seven positions, with
Gram determinant 28. Then |<a,b>|=2. A balanced norm-eight row on seven
positions compatible with girth four and all three new positions must have
support five, with shape (2,1,-1,-1,-1) up to sign and permutation. A unit
eight-row cannot fit, and the support-two shape (2,-2) is incompatible.

Exactly two entries of b are old and three are new. The magnitude-two entry
must be new: otherwise the two old entries would have magnitudes 2 and 1,
and their inner product with a would be odd, contrary to |<a,b>|=2.
The two old unit entries therefore align with a with the same sign.

The unique norm-four line cannot instead be a crossing line containing all
three new positions. Such a line and a norm-eight support-five crossing line
would share at least three positions, so their union would have at most six
positions. A norm-eight line supported only on C cannot have the required
support five. This also justifies retaining a as the prescribed C row in
this determinant stratum.

Assign weights

    1       on each of the four old coordinates,
    1/5     on the new coordinate where |b_i|=2,
    7/5     on the other two new coordinates.

All weights are positive and their sum is seven. In the inverse-weight
metric the exact squared GS lengths are

    g1 = 4,
    g2 = (2+20+10/7) - (+/-2)^2/4 = 157/7.

Furthermore,

    product_i w_i = 49/125,
    product_i w_i * det Gram_w(a,b) = 4396/125 > 28.

An old coordinate where a is nonzero but b is zero, together with a new
unit coordinate of b, gives a 2x2 minor +/-1. Hence these rows form a
saturated basis of the plane's integer lattice. Successive shifted-theta
upper bounds use their exact weighted GS lengths; weighted Gauss reduction
is unnecessary.

The script checks all 108 such balanced full-support row pairs. Their
normalized prescribed coefficient charts at q=7,17,3329 number 18 for
second-support overlap two, and zero for overlaps one and three. The
applicable coefficient 18 is exactly the existing D28 coefficient. The
weight assignment is intrinsic to the actual rows and does not transport
affine balance through coordinate sign changes.

## Complete kernel

Keep the existing beta=5N/(14R^2), a0=pi^2/beta, alpha=a0/q^2, and unweighted
cutoff 40. Set

    s = 5/7,
    delta = 2 exp(-s*a0/4)/(1-exp(-2*s*a0)),
    tail = exp(-800*s*alpha) theta((7/2)*s*alpha/2)^2,
    periodic = sum_{j=1}^7 binomial(7,j) delta^j.

The complete weighted Gaussian kernel is

    K_w = sqrt(125/49) (pi/beta)^(7/2)
          * ((theta(4 alpha) theta((157/7) alpha) + tail)/q^2
             + periodic).

The maximum weight is 7/5, so the inverse-weight quadratic form dominates
(5/7) times the unweighted form. This proves the scaled tail and periodic
bounds. The short-plane lifting cutoff itself stays unweighted and unchanged.
Since the weights sum to seven, the ball Markov factor is unchanged as well.

In the c=4, union=7 `seven_split`, replace only the D28 kernel by
`min(old_D28_kernel,K_w)`. Its count is still 18 and all other terms remain.
There is no excluded family requiring a separate addback.

## Numerical verification and actual scope

With the existing interval geometry calculation and every correction term
retained, the script verifies

    log10((K_w/K_old)^518) = -25.62736041756...,
    log10(new one-four split / old split) = -11.70381122629....

After the D23 family is excluded as already required by the selected cover,
the other one-four terms relative to D28 have log10 values -11.70402109053
(D31), -15.01991426717 (D32), and -18.47508525261 (the height-nine remainder).
D31 therefore becomes the local limiting term. The no-four contribution is
retained separately and remains smaller at this stage.

This is not an eleven-order improvement of the full remaining rank-8 bound:
the unchanged `(8,4,2,2)` term was already about 25.8% of that bound. Removing
the leading term alone improves the full remaining sum by only about 0.588
orders. Parent integration must report the recomputed selected cover rather
than infer the global improvement from a single kernel.

Reproduce:

    python3 docs/research/scripts/wall1_seven_d28_weights.py
    python3 docs/research/scripts/wall1_rank_eight_remaining_diagnostic.py

Logs: `/tmp/wall1_seven_d28_weights.log` and
`/tmp/wall1_rank_eight_remaining_diagnostic.log`. Exact rational row checks,
finite-field chart checks, and complete interval-kernel checks pass. This
worker changed only new research files, not the production main module.
