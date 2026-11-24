# Horizontal transport with the selection weight retained

The elementary two-height convolution can be applied after projecting a fixed
old shortest line, while retaining the event that the algorithm actually
selects that line. This supplies a sufficient bound for the horizontal part
of a transition. It does not estimate the remaining history average at
width506 or the nonhorizontal part of the transition.

## Fixed old line and actual selection

Fix a prime q and the full incoming state M subset K, qK subset M, and H=K/M. Let w be
a primitive shortest vector of M of length s, and let pi project off w.
Write Mbar=pi M, Kbar=pi K and Hbar=Kbar/Mbar. All projected lattices here
are full in w-perp. The homomorphism f:H onto Hbar has equal fibers.

For a fresh uniform mark U in H, form W_U=(M,0)+Z(k_U,1). Let E be the event
that the actual selected winner spans (w,0). For a fixed deterministic
old-coordinate tie rule selecting w among old shortest lines, this is the
entire horizontal-winner event. For another tie rule it may be only one
horizontal line; do not count other lines without treating their events.

On E the projected graph is exactly

    Wbar_U=(Mbar,0)+Z(pi k_U,1).

The outgoing marked group can be identified with Hbar: projection from the
old H has precisely the kernel of f, and graph height separates the old
marks. Its distances depend only on u=f(U). The actual moving radius on
this event is fixed by the incoming state and s; denote it by b. Assume
b>=1 for the two-height formula below.

Let dbar(v) be the distance of mark v from Mbar. Put

    A0={v:dbar(v)^2>b^2},
    A1={v:dbar(v)^2>b^2-1},
    p0=|A0|/|Hbar|,  p1=|A1|/|Hbar|,
    C(u)=|A0 intersect (A1-u)|/|Hbar|.

Height0 and height1 representatives give P'(u)<=C(u)<=p0 on E. Uniformity
of u and the bijection (u,v) -> (v,v+u) imply exactly E_u C(u)=p0*p1.
This is the existing [two-height identity](wall1_two_height_convolution.md),
now applied to the projected old lattice, not to the unprojected state.

Define rho(u)=Pr(E | f(U)=u), including any tie coins in the conditional
experiment. For Phi(x)=min(1,x/delta), delta>0,

    E[1_E Phi(P')] <= E_u[rho(u) Phi(C(u))]
      <= min(Pr(E), p0*p1/delta, Pr(E)*min(1,p0/delta)).       (1)

The first right-hand term is redundant, but makes the probability scale
explicit. The weighted expression retains clipping and selection. Replacing
rho by Pr(E) inside it requires an independence argument that is not supplied.
In particular conditioning on E does not preserve uniformity of u in general.

## A support restriction that uses shortest selection

If, for any positive integer j,

    dbar(j u)^2+j^2 < 3*s^2/4,                              (2)

then rho(u)=0. To prove this, take a nearest projected representative of
j u. For each U above u it lifts to a vector in j k_U+M. Subtract an
integer multiple of w to put its parallel component in [-s/2,s/2]. At
height j this gives a vector of W_U of squared norm at most
dbar(j u)^2+j^2+s^2/4<s^2. It strictly beats every old shortest vector,
regardless of ties. A nearest projected representative exists because
Mbar is a lattice. This argument does not assume that the kernel has order q.

Let T consist of u for which (2) fails for every positive integer j. Only
j with j^2<3*s^2/4 need checking. Symmetry of distances makes negative
heights redundant. The selected expectation in (1) is therefore at most

    E_u[1_T(u) Phi(C(u))].                                 (3)

Equivalently, the support restriction subtracts exactly
E_u[1_(T complement)(u) Phi(C(u))] from the unrestricted capped convolution.
This subtractand is nonnegative; its size in actual histories remains open.
Strict inequality in (2) is deliberate: the boundary can depend on ties.

For 0<=b<1, use only height0, P'<=p0, rather than defining A1 at a negative
squared radius. With the current radius law R^2=(1.1g)^2-1 and
b^2=(R^2+1)*s^(-2/506)-1, every branch with s<=1 has b>=R. Projection of
each incoming hit then proves P'<=P directly. Possible positive drift is
restricted to s>1, though that still includes the relevant production range.

## Fractional selection bound when one mark direction is lost

If ker(f) has order q, primitive w satisfies w/q in K. For a fixed projected
mark u, its q incoming aliases can be represented by k_U+a*w/q, a in F_q.
Fix a positive height j coprime to q and one nearest projected representative
of j*u. A lift x0 for one alias gives lifts x0+j*a*w/q for all aliases.
Modulo addition of w their parallel phases form an equally spaced grid of
spacing s/q on a circle of length s. Put e_j=dbar(j*u)^2+j^2.

For each integer k with 1<=k<=q, the strict comparison

    e_j < s^2*(1-k^2/(4*q^2))                             (4)

implies that at least k aliases have a strictly shorter nonhorizontal
competitor. Indeed their allowed parallel interval is open, has length
2*sqrt(s^2-e_j)>k*s/q, and contains at least k grid phases. This also handles
k=q, when that length is greater than the whole circle. Consequently,

    rho(u)<=1-m(u)/q,

where m(u) is the largest k certified by (4) for any such j, or zero if no
comparison succeeds. Only j^2<s^2 can contribute, so this test is finite.
Taking a maximum over witnesses avoids any independence assumption about
their overlapping winning intervals. In particular (1) is bounded above by

    E_u[(1-m(u)/q)*Phi(C(u))].                            (5)

The k=q case recovers the binary support exclusion (2) for heights coprime
to q. In the current restart s<=q, so every potentially contributing height
in (2) is between1 and q-1 and is coprime to prime q. Thus (5) is no larger
than (3) in that setting. For general s>q the binary exclusion from a
multiple-of-q height must be retained separately. Strictness in (4) prevents
an endpoint tie from being credited as a guaranteed win. No production
distribution of m(u) or its correlation with C(u) is established.

## Remaining estimate and verification scope

Equations (1)--(3) are conditional on the full incoming history. To use them
in [linear capped transport](wall1_linear_capped_transport.md), one must
bound their contribution together with the nonhorizontal branches by the
required multiplier or additive budget. Neither a bound on p0,p1 nor a
quantitative weighted convolution estimate for the selected ensemble is
proved here. This is not a completed BKZ proof or a Lean formalization.

The [complete-branch connection](wall1_phase_winner_tails.md) explains why an
upper bound on rho alone cannot be subtracted from an unconditional
convolution bound. It extends the phase test to shorter-winner thresholds,
which can constrain all branches together in the existing winner-bin program.

The exact checker `scripts/wall1_horizontal_selected_convolution.py` uses
rational two-dimensional old lattices, actual graph shortest-vector selection,
all fresh marks, and complete finite enumeration bounds. Its radii are toy
test values. These checks test the formulas, not their production premise.

The completed check covers17 lattice configurations,929 actual winner
branches and40 radius settings. Of these,227 branches select the horizontal
line. The rectangular family includes116 selected branch/radius pairs with
positive actual outgoing void, so the checks are not restricted to zero-void
branches. Selection weighting strictly improves the coarse bound in6 radius
settings; the binary support restriction improves the unrestricted capped
convolution in14. The fractional phase bound is verified throughout but
gives no further strict improvement in this grid.

For an explicit comparison take q7, K=diag(1/4,1) Z^2, M=7K, b^2=4 and
delta=7/25. The selected contribution is bounded by50/343 using rho,
versus4/7 for the coarse minimum in (1); the unrestricted capped convolution
is197/343. The actual selected contribution is zero in this example.
For K=diag(1/4,2) Z^2 at the same q and b, the actual selected contribution
is4/7 and the weighted bound6/7, while the unrestricted capped convolution
is1. These are explicitly toy-radius examples, not restart certificates.

The support and fractional-phase proofs received independent mathematical
review; the parent reran the complete rational checker successfully.
