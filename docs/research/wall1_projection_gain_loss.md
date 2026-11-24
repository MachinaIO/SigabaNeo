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
Phi(P+E[ell−g])−Phi(P). The capped function is neither globally convex nor
globally concave. Nor does E[ell−g]<=0 alone imply nonpositive potential drift.

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
