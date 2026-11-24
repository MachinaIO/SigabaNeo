# Projection gain/loss accounting for the capped history potential

This reduces the remaining geometric drift estimate to losses minus gains of
covered marks, using the actual winner and its radius. It proves an exact
identity and a safe increment envelope. It does not prove that the resulting
conditional charge fits the remaining history budget.

## Common mark space and exact gain/loss identity

Fix the full incoming state as in
[winner-coupled replicas](wall1_winner_coupled_replicas.md). Its finite mark group
is H, of order h. Let d(v) be the incoming marked distance and R its current
test radius. Define the incoming hit set

    A={v in H:d(v)<=R},   P=1−|A|/h.

For each fresh mark u, use the actual selected vector w_u, its orthogonal
projection Q_u, actual outgoing radius b_u, and a fixed finite height set J.
With the representatives and lifts z_j(u,v) from that note, define the outgoing
witness hit set

    B_u={v in H:exists j in J, ||Q_u z_j(u,v)||<=b_u}.

Any v in B_u is truly covered in the outgoing marked lattice. In the common
incoming mark space put

    ell_u=|A minus B_u|/h,    g_u=|B_u minus A|/h,
    H_u=1−|B_u|/h.

The disjoint decompositions of A and B_u give exactly

    H_u=P+ell_u−g_u.                                      (1)

The letters ell and g denote normalized mark fractions, not representative
counts. Loss and gain occur in the same branch u, and may depend arbitrarily
on its actual winner. No independence assumption enters (1).

The true outgoing quotient H'_u is the surjective image of H under
v -> Q_u(k_v,0) modulo Q_u W_u. Every fiber of this homomorphism has the same
size. Thus the true outgoing void P'_u equals its pulled-back miss fraction
on H, and the witness inclusion proves

    P'_u <= H_u.                                         (2)

The finite witness set B_u need not itself be a union of quotient fibers:
particular chosen representatives may witness one preimage but not another.
That causes no error in (2), since B_u is contained in the full pulled-back
true hit set. Do not divide |B_u| by the kernel size or treat B_u as a quotient
subset unless fiber saturation has separately been established.

### Crediting all labels with the same projected image

There is a deterministic improvement available before computing losses and
gains. Put N_u=ker(f_u), B_u^sat=B_u+N_u, and

    H_u^sat=1−|B_u^sat|/h,  a_u=|B_u^sat minus B_u|/h.

Every label in B_u^sat has the same outgoing coset as an existing hit, so

    P'_u <= H_u^sat=H_u−a_u <= H_u.

Equivalently, H_u^sat=1−|f_u(B_u)|/|H'_u|. Count distinct images first;
dividing the unsaturated witness count by |N_u| is not valid. The gain/loss
identity and all increasing-potential bounds apply with B_u^sat in place
of B_u. In particular the exact linear-cap numerator becomes

    E(ell_u−g_u−a_u) − E(H_u−a_u−delta)_+.

The correction is nonnegative and needs no independence assumption, but
there is no production lower bound on its size. The planar checker in
`scripts/wall1_winner_coupled_replicas.py` verifies the inclusions on all270
branches; all these planar witnesses are already saturated, so none improves.
An independently audited [two-dimensional retained fixture](wall1_fiber_saturation_fixture.md)
does improve strictly: at q5 an actual horizontal shortest winner and J={0}
give24 of25 witness hits, while saturation covers all25 marks. Its exact
rational checker exhausts all nearest representatives using a proved
coordinate bound. The fixture has ties and an arbitrary toy radius; it
establishes strictness of the deterministic correction, not a production gain.

For prime q the kernel has order either1 or q. Indeed set Lambda=K×Z and
write the primitive winner in W_u as w=t*w0 with w0 primitive in Lambda.
The kernel is (Lambda intersect Rw)/(W_u intersect Rw), of order t. It is
a subgroup of Lambda/W_u, which has exponent q, hence t is1 or q. If t=q
and the winner has nonzero vertical height, that height has magnitude at
least q. Since (0,q) belongs to W_u, shortestness gives ||w||<=q and forces
w=(0,+/-q). Thus every rank drop with ||w||<q is horizontal. This explains
the existing coprime-height results in [inverse branches](wall1_inverse_branch.md)
and the height-q endpoint in [subspace voids](wall1_subspace_void.md); it
does not bound the probability of horizontal winners. The content/kernel
identity is also checked on all270 planar branches.

Consequently a_u=0 for every nonhorizontal shortest winner of length
strictly below q. The correction cannot improve a transport proof restricted
entirely to those branches; its possible benefit is in the horizontal
branches (or the length-q endpoint). It does not replace the outstanding
geometric estimate on the rank-preserving branches.

## A loss-minus-gain increment envelope

For delta>0 and real k>=1, let Phi(P)=min(1,(P/delta)^k), for 0<=P<=1.
Work before exit, so P<delta, and define

    D_u=max(0,ell_u−g_u),
    C_u=min(1−Phi(P),
            (k/delta) D_u * min(1,(P+D_u)/delta)^(k−1)).   (3)

For k=1 the last power is interpreted as1, including at zero. Then

    [Phi(H_u)−Phi(P)]_+ <= C_u,
    Phi(P'_u)−Phi(P) <= C_u.                              (4)

Proof. If ell_u<=g_u, (1) gives H_u<=P and both positive increments vanish.
Otherwise H_u=P+D_u. On [P,P+D_u], the capped function is absolutely
continuous. Its derivative away from the cap is
(k/delta)(x/delta)^(k−1) below delta and zero above delta. This derivative is
bounded almost everywhere by
(k/delta) min(1,(P+D_u)/delta)^(k−1).
Integration bounds the increment by the second term in (3). The cap also
bounds it by1−Phi(P). Taking their minimum proves the first inequality;
monotonicity and (2) give the second. The derivative argument remains valid
when the interval crosses delta, without differentiability at the cap.

In fact the exact positive witness increment is
Phi(P+D_u)−Phi(P). Formula (3) provides a simpler envelope that still retains
the cancellation of losses and gains in each branch. Replacing D_u by ell_u
is valid but can lose all such cancellation.

For k=24, delta=0.280, an immediately sufficient conditional charge is

    c(S)=E_U[C_u | complete incoming history S].          (5)

Uniformity of the next unused mark permits the explicit average h^(-1)sum_u.
The inequality itself also holds under any correctly specified conditional
law of U; one cannot substitute the uniform average for an already exposed
column without proving that law.

## Signed cancellation across branches

A potentially sharper charge is

    c_signed(S)=max(0,
        E_U[Phi(P+ell_u−g_u) | S]−Phi(P)).                 (6)

By (1)--(2), (6) bounds the conditional expected increase of the actual
potential. Moreover

    c_signed(S)
      <= E_U[[Phi(P+ell_u−g_u)−Phi(P)]_+ | S]
      <= E_U[C_u | S].                                   (7)

The first inequality is generally strict: branches with a net gain can
compensate branches with a net loss after applying the nonlinear potential.
One must average the signed potential increments, not replace them by
Phi(P+E[ell−g])−Phi(P). For k>1 and0<delta<1 the capped function on[0,1]
is neither convex nor concave, and E[ell−g]<=0 alone does not imply
nonpositive potential drift. The k=1 case is different and is treated below.

For a precise scalar separation, set P=delta/2, k=24. Let the witness void be
delta with probability2^(−24), and zero otherwise. Then its expected capped
potential equals Phi(P), so (6) is zero, whereas the expected positive
increment is strictly positive. This rational toy compares the bounds; it
is not asserted to be a reachable BKZ transition.

## What this would close, and what it does not yet prove

The [capped-potential bridge](wall1_capped_history_potential.md) initializes
the matching actual draw14 observable with

    E Phi(P_14)<=D_14,    D_14=1.9704509e−12.

Let tau be the first index with P_i>=0.280. Applying (5) or (6) before exit
and stopping at tau gives

    Pr[exists i in {14,...,T}:P_i>=0.280]
      <= D_14 + sum_(i=14)^(T−1) E[1_(tau>i)c(S_i)].       (8)

Draw14 is already included in D_14 and is not paid again. The remaining
normalized charge allocation is1.9515491e−12, or the conservative rounded
1.951e−12, for the stated3.922e−12 total allocation. Prior alive indicators
and corridor exit charges must be handled exactly as in the capped-potential
note; no conditioning on future survival is allowed.

The substantive missing theorem is a sufficiently small stopped average of
(5) or (6) for reachable selected states. Equations (1)--(7) expose a concrete
geometric statistic: actual projected losses offset by newly covered marks.
They do not bound that statistic. In particular, a bound on radial-shell
mass alone bounds ell_u but omits the gain g_u, while the earlier conservative
cap counterexample does not settle their difference for the actual winner.
No new numerical history probability or completed BKZ proof is claimed.

## Exact checker

Run `python3 docs/research/scripts/wall1_projection_gain_loss.py`.
It exhausts pairs of hit subsets in groups of sizes1 through7 and checks
(1), (3)--(4) at k=1,2,24 with rational thresholds, including crossing the
cap. All39762 increment checks pass. It also checks a true-hit superset,
the signed-cancellation fixture, and equal fibers in a nontrivial quotient.
These checks validate the identities and inequalities, not the outstanding
small-charge premise in (8).

## Exact signed accounting for the linear capped potential

The first-moment seed permits k=1, as established in
[linear capped transport](wall1_linear_capped_transport.md). In this case
Phi_1(x)=min(1,x/delta) is concave. The general warning above about a
nonconcave cap must not be applied to this case.

Before exit, P<delta, and H_u=P+ell_u-g_u lies in[0,1]. The identity
Phi_1(x)=(x-(x-delta)_+)/delta gives exactly

    E Phi_1(H_U)-Phi_1(P)
      = [E(ell_U-g_U)-E(H_U-delta)_+]/delta.              (9)

All expectations use the same correct conditional law of the next mark
given the entire incoming history. No independence of losses and gains,
or of either from the winner, is assumed. Since P'_u<=H_u,

    E Phi_1(P'_U)-Phi_1(P)
      <= [E(ell_U-g_U)-E(H_U-delta)_+]/delta.

Thus a sufficient nonnegative charge is the positive part of the right
side, and it is at most [E(ell_U-g_U)]_+/delta. In particular nonpositive
mean net loss does suffice for k=1. One can also prove nonpositive drift
when the mean net loss is positive, if the overshoot term compensates it.

For example delta=7/25, P=delta/2, H=3delta with probability1/4 and
H=0 otherwise gives mean net loss7/100, mean overshoot7/50, and potential
drift-1/4. These values are realizable as fractions of finite hit subsets;
the example is an algebraic check, not a selected-lattice transition.
The checker verifies (9) pointwise for the finite subset fixtures and
this exact rational mixture.

To use the overshoot term subtractively, its expectation needs a lower
bound under the same law. Replacing witness H by actual P' in only that
term is not an equality; using a valid lower bound for the witness term
is safe. This specialization avoids unnecessary high-power conditions,
but neither the required mean net loss nor the overshoot correction has
been bounded at the production selected histories.
