# Connecting parallel phases to the complete winner distribution

The horizontal selection bound alone does not improve the complete transition
bound by subtraction. Its valid extension is a lower bound on the fraction
of marks producing a shorter winner, hence an upper tail constraint for the
existing winner-bin optimization. The projected distance profiles under
actual histories remain unestimated.

## Avoid double use of the horizontal contribution

Fix a full incoming state and its designated old shortest vector w, length s.
Every graph winner has length S_U<=s. Let B=b(s)>=1 be the resulting common
outgoing-radius floor. Let h(U) be the unprojected two-height witness at B,
and let C(f(U)) be its projected-old counterpart from
[selected horizontal convolution](wall1_horizontal_selected_convolution.md).
Projection contracts each marked distance. Pulling the projected test marks
back through the equal-fiber quotient therefore gives, pointwise,

    C(f(U))<=h(U).

Set F(U)=Phi(h(U)), G(f(U))=Phi(C(f(U))) for the increasing capped potential.
Let E mean that the actual winner spans the designated line (w,0), with
the same tie-rule qualification as in the linked horizontal note.
On every branch Phi(P'_U)<=F(U); on E it also
satisfies Phi(P'_U)<=G(f(U)). Consequently

    E Phi(P'_U) <= E F - E[1_E*(F-G)].                    (1)

The subtracted term is nonnegative. However an upper bound on
rho(u)=Pr(E | f(U)=u) gives no lower bound on that term. F can vary among
the aliases and correlate with E, even though G is constant on each fiber.
In general the conditional saving is

    rho(u)*(E[F | f(U)=u,E]-G(u)),

with zero contribution when rho(u)=0. Replacing the conditional F by its
unselected fiber average is unjustified. Adding an unconditional bound on
E F to a separate horizontal bound is conservative but spends the horizontal
branches twice; it does not establish an improvement to (1).

## A threshold version of the phase bound

Assume prime q and that projecting w kills one mark direction, so the kernel
of f:H->Hbar has order q and w/q belongs to K. Fix a threshold 0<c<=s.
For u in Hbar and a positive integer j coprime to q put

    e_j(u)=dbar(j*u)^2+j^2.

For each integer 1<=k<=q, the strict inequality

    e_j(u) < c^2 - k^2*s^2/(4*q^2)                      (2)

certifies at least k of the q aliases with S_U<c. Indeed choose one nearest
projected representative of j*u. Across the aliases, its parallel phases
form a shifted grid of spacing s/q modulo s. A lift at height j has length
below c whenever its centered parallel phase belongs to the open interval
of length2*sqrt(c^2-e_j). By (2) that length exceeds k*s/q, so at least k
grid phases give strictly shorter competitors. This uses shortestness only
to infer that the actual winner is no longer than a competitor.

Let m_c(u) be the maximum k certified by any such j, or zero if none exists.
Only j^2<c^2 need testing. Taking a maximum avoids assuming independent
winning events for different heights. Equal fibers and fresh-mark uniformity
give the conditional and unconditional tail bounds

    Pr(S_U>=c | f(U)=u) <= 1-m_c(u)/q,
    Pr(S_U>=c) <= T_phase(c):=1-E_u[m_c(u)/q].            (3)

All comparisons in (2) are strict. Thus (3) retains winners exactly at c
and requires no unproved tie claim. The function m_c(u) is nondecreasing
in c, so its certified upper tail is nonincreasing. At c=s this recovers
the previous upper bound on horizontal selection, possibly also retaining
nonhorizontal winners tied at s. No claim that these events coincide is used.

## Use with the full transition certificate

The existing height-one competitor gives another valid bound,

    Pr(S_U>=c) <= Pr(d(U)^2+1>=c^2)=T_one(c).

Take the minimum of T_phase and T_one; do not multiply them. For ordered
winner cutoffs c_l the strict tail used by
[winner-bin convolution](wall1_winner_bin_convolution.md) is bounded by
this same minimum, because {S_U>c_l} is a subset of {S_U>=c_l}. Its linear
program can therefore use

    sum_(j>l) alpha_j <= min(T_phase(c_l),T_one(c_l)).     (4)

The common convolution budgets across bins must still be imposed. No
individual-bin estimate follows by subtracting two upper-tail bounds.
These constraints include both horizontal and nonhorizontal winners and
do not condition the fresh mark on a winning event.

Equation (4) is useful only if the phase profiles can be bounded at the
actual incoming state, or averaged with valid stopped-history bookkeeping.
They are not known from the determinant or quotient rank alone. No
width506 multiplier, later-history probability bound, or full BKZ proof
is obtained here.

## Verification

### What is lost by reducing the phase bound to a radial marginal

Let m_j(u) be the maximum certified k for one fixed admissible height j.
The conditions are nested in k, so

    E m_j = sum_(k=1)^q Pr(dbar(V)^2<c^2-j^2-k^2*s^2/(4*q^2)).

Here V is uniform on Hbar: multiplication by j is bijective when j is
coprime to q. Each threshold is largest at j=1. For c>1,
max_j E m_j=E m_1; for c<=1 all terms vanish. A nonpositive threshold has
probability zero, and strict comparisons continue to exclude boundary atoms.
Therefore replacing E max_j m_j by max_j E m_j gives the weaker tail

    T_projected1 = 1-(1/q)*sum_(k=1)^q
        Pr(dbar(V)^2<c^2-1-k^2*s^2/(4*q^2)).

Projection and equal-fiber averaging allow a further relaxation using only
the old distance d on H:

    T_rawphase = 1-(1/q)*sum_(k=1)^q
        Pr(d(U)^2<c^2-1-k^2*s^2/(4*q^2)).

The comparisons are

    T_phase<=T_projected1<=T_rawphase,  T_one<=T_rawphase.   (5)

The second inequality on the right follows because every probability in
the average is at most Pr(d(U)^2<c^2-1). Thus this explicit radial relaxation
cannot improve the existing height-one tail, even if the entire old radial
profile is supplied exactly. This is not an impossibility theorem for every
method using radial information. In particular it does not discard possible
use of the shared scalar-orbit structure or other geometric constraints.

There is an exact expression for the missing shared-mark information. For
0<c<=s,

    1_{S_U>=c} = product_(1<=j<c) 1_{d(j*U)^2+j^2>=c^2}. (6)

At height zero all nonzero vectors have length at least s>=c. At a nonzero
height j, the minimum squared length is d(j*U)^2+j^2. Only |j|<c can beat
the threshold; symmetry makes positive heights sufficient. This proves (6),
including ties and the empty product when c<=1. It is the threshold form of
the existing [projective-line competitor count](wall1_subspace_void.md),
not an independence formula. All factors concern the same U. The phase
certificate bounds this event without retaining the full incoming orbit.

The finite radial audit verifies152 fixed-height identities. In this grid,
T_phase<T_projected1 in15 cases, T_projected1<T_one in none, and
T_rawphase>T_one in71. It also checks (6) against actual graph winners for
every tested branch and cutoff. Hence the observed improvements in this
grid require retaining the multiple-height maximum; the scalar radial
relaxation loses them. These counts do not establish which mechanism
dominates production histories.

The [scalar-orbit expansion bound](wall1_scalar_orbit_expansion.md) supplies
one way to retain several heights without independence: it bounds their
union using certified multiplicative-group spectra and the second moment
of short-mark density across projective lines. The required selected-history
line concentration is not supplied by the radial audit or the draw14 seed.

### Finite checks and review

Run `python3 docs/research/scripts/wall1_phase_winner_tails.py`. The finite
checks use rational planar lattices, actual shortest selection, complete
search bounds and exact rational threshold comparisons. They verify (3)
and its comparison with the height-one bound; they do not assert that the
fixtures describe the production history law. The general phase argument
and the complete-branch accounting received independent mathematical review.

The completed checker passes17 configurations,929 actual winner branches,
110 cutoff cases and776 conditional fiber checks. The phase bound is
strictly smaller than the height-one bound in15 cases, while the height-one
bound is smaller in24 cases. For q7, K=diag(1/2,1) Z^2 and c^2=49/8,
the actual tail, phase bound and height-one bound are8/49,12/49 and18/49.
For q11 with the same basis and c^2=121/8 they are8/121,8/121 and48/121.
An independent reviewer reran the checker and verified the search bounds
and the distinction between the inclusive tail in (3) and the strict
winner-bin tail in (4). These are finite examples, not production estimates.
