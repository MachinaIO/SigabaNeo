# Capped refinement of the existing two-height convolution bound

The uncapped convolution lemma below is already proved in
[the two-layer power drift note](wall1_two_layer_power_drift.md). It is
restated to derive the capped refinement(2), rather than claimed as a new
power-moment result. It retains the incoming modular geometry and uses no
linear section. It reduces a sufficient drift bound to two radial void
fractions. Those fractions still need control under actual selected histories.

Use the marked transition and nearest representatives of
wall1_winner_coupled_replicas.md. Fix the complete incoming history, and let
U be its fresh uniform mark in H=K/M. Suppose a deterministic B>=1 bounds
every branch's outgoing radius below: b_u>=B. Define

    A0={v:d(v)>B}, A1={v:d(v)>sqrt(B^2-1)},
    p0=|A0|/|H|, p1=|A1|/|H|, so p0<=p1.

The unprojected witnesses at heights0 and1 show, using projection
contractivity pointwise even for a winner depending on U,

    P'_u <= h(u)=|A0 intersect (A1-u)|/|H| <= p0.

Uniform translation, with no shape assumption on either set, gives exactly

    E_U h(U)=p0*p1.

Consequently for every integer k>=1,

    E_U (P'_U)^k <= E h(U)^k <= p0^k*p1.                 (1)

All replicas share the same U. The first moment identity does not claim
independence of those replicas: the deterministic bound h<=p0 is what
controls their higher moments.

For delta>0 and Phi(x)=min(1,(x/delta)^k), the sharper capped consequence is

    E Phi(P'_U) <= (p0*p1/delta)*min(1,p0/delta)^(k-1).   (2)

For p0=0 the result is zero. Otherwise Phi(x)/x increases up to delta
and decreases thereafter. Its maximum on0<x<=p0 is
delta^(-1)*min(1,p0/delta)^(k-1), proving(2). For k=1 the zero power is1.

## A sufficient radial condition for no positive charge

Let P be the current void at its actual incoming radius and assume P<delta.
For k=24, if p0<=delta and

    p0^24*p1 <= P^24,                                   (3)

then the conditional expected capped potential does not increase. Otherwise
the positive excess of the right side of(2) over Phi(P) is a valid charge.
This is a concrete sufficient condition, not a proven property of histories.
The small gap between the two test radii does not bound p0 or p1 relative
to P: the larger shrinkage from the incoming radius to B still matters,
and finite marked distances can have atoms.

More generally, any rigorously known upper bounds a0>=p0,a1>=p1 in[0,1]
can replace p0,p1 on the right side of(2), by monotonicity. A conservative
winner cap C gives B^2=(1.1g)^2 C^(-2/506)-1 when this is at least1.
No conditioning on gate survival or future success is permitted. If only
some fresh marks satisfy the radius floor, their complement needs its own
charge; the uniform translation identity cannot be renormalized for free.

This lemma avoids the linear-section mean-energy obstruction, but it does
not establish the remaining1.9515491e-12 stopped-charge budget. The next
geometric obligation is to bound these nearest-distance tails, or to retain
actual directional projection gains when this sufficient condition fails.

The exact finite checker exhausts nested subsets of cyclic groups of orders
1 through6, including empty/full sets and threshold crossings. It verifies
the convolution identity, shared-U moments, and capped bound at k=1,2,24.
These checks support the algebra, not a selected-history probability claim.
