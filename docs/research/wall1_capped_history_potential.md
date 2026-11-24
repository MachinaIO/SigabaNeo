# Capped void powers: a draw-14 seed and the remaining conditional charge

The capped potential eliminates the separate high-power initialization
obligation for the draw-14 observable covered by Part442. It uses the actual
unconditional selected-state first moment supplied by pointwise projection
domination. It does not establish the later-history conditional drift.

## Seed under the original matrix law

Fix delta=0.280 and k=24, and define for 0<=P<=1

    Phi_delta(P)=min(1,(P/delta)^24).                       (1)

Pointwise,

    1{P>=delta} <= Phi_delta(P) <= P/delta.                (2)

Indeed for P<=delta, (P/delta)^24<=P/delta; for P>=delta,
1<=P/delta. Equality at P=delta is included in the bad event.

The Part442 certificate supplies, for the actual draw-14 void P_14 at the
certified radius and under the original uniform matrix law,

    E[P_14/delta] <= D_14,   D_14=1.9704509e−12.           (3)

This is stronger than a statement only about Pr[P_14>delta]. Its provenance
is the raw empty-candidate certificate and pointwise domination by the actual
projection. The frontier source normalizes its baseline by
1/(0.280*partial_exp) and its degree24 transfer by
(12!)²/(0.280*mu^24). Thus the raw certificate bounds the expected empty-mark
fraction divided by delta before the final Markov interpretation. The Part442
certificate upper endpoint is1.970450899541598349754851061493e−12, below the
safe D_14 above. See [matroid packing](wall1_matroid_packing.md) and
`scripts/wall1_draw14_frontier.py`; this note does not rerun production.

Consequently,

    E Phi_delta(P_14) <= D_14.                             (4)

There is no conditioning on the selected projection, no assumption that its
residual map is uniform, and no survival-probability denominator. A bound only
on Pr[P_14>=delta] would not imply (4): a deterministic P_14=delta/2 has zero
tail probability but positive potential2^(−24).

The observable and radius must match (3). This seed does not cover a smaller
physical radius or another selected-cylinder statistic without a separate
pointwise comparison. It also does not contradict the raw-restart small-radius
obstruction, which concerns a different state/radius.

## Stopped conditional bridge, counting draw14 exactly once

Let F_i contain the entire actual incoming history. Write P_i for its actual
void fraction at the specified current radius, and let tau be the first index
in {14,...,T} with P_i>=delta, with tau=T+1 if absent. Suppose c_i>=0 is
F_i-measurable and on {tau>i}, for i=14,...,T−1,

    E[Phi_delta(P_(i+1)) | F_i] <= Phi_delta(P_i)+c_i.      (5)

All expectations use the original probability space. Define
Z_i=Phi_delta(P_(min(i,tau))). After a hit, Z_i=1 and has zero increment.
Before a hit, its conditional increment is at most c_i. Finite telescoping
therefore gives

    Pr[exists i in {14,...,T}: P_i>=delta]
      <= E Z_T
      <= D_14 + sum_(i=14)^(T−1) E[1_(tau>i)c_i].          (6)

This handles tau=14: Z_14=1 on an initial hit and that hit is already paid
inside E Z_14<=D_14. One must not additionally union-bound a draw14 failure
term D_14 after using (6). The c_i here are in normalized potential units;
unlike the earlier raw-power formulation, no extra delta^(−24) multiplies
their sum.

For the specified remaining allocation3.922e−12, a sufficient condition is

    sum_i E[1_(tau>i)c_i] <= 1.9515491e−12,                (7)

since3.922e−12−1.9704509e−12=1.9515491e−12 exactly.
Using the rounded1.951e−12 leaves a strict margin. This is a required charge
budget, not an established estimate. All other failure terms must already
be accounted for in the allocation to which3.922e−12 refers.

## A strictly weaker actual-winner target

The [winner-coupled replica construction](wall1_winner_coupled_replicas.md)
provides a deterministic p'_u<=H_S(u), with one fresh u, actual winner,
projection, and radius shared throughout. Monotonicity of (1) gives

    E[Phi_delta(P_(i+1)) | S]
       <= |H|^(-1) sum_(u in H)
                  min(1,(H_S(u)/delta)^24).               (8)

Here the marked group H is finite, and the incoming state S is fixed under
conditioning on the full history. A sufficient new geometric lemma is

    |H|^(-1) sum_u min(1,(H_S(u)/delta)^24)
         <= (P_i/delta)^24 + c_i                         (9)

on {tau>i}; there P_i<delta, so its right-hand potential is uncapped.
This retains the winner-dependent projection gain and moving radius.

The target (9) is weaker than bounding the raw24th witness moment by
P_i^24+delta^24 c_i: the clipped left side discards oversized branch values.
This difference can matter even when the same charge is allowed. For example,
let P_i=delta/2 and let the next witness value be1 with probability2^(−24),
otherwise0. Its expected capped potential equals the current potential,
whereas its expected raw normalized24th power is larger by delta^(−24).
This abstract scalar fixture compares the two sufficient conditions; it is
not asserted to be an actual BKZ transition.

Clipping must occur after the replicas have been averaged over auxiliary
marks for each fixed u. In particular (8) is the finite sum of
min(1,(m_u/(|H| delta))^24), where m_u is the witness miss count. It is not an
ordinary24-replica polynomial and cannot be replaced by independent u's or
by clipping a pre-averaged mean. Existing raw moment bounds remain valid
upper bounds after clipping but may fail to exploit the improvement.

## Prior stops, gates, and the unproved obligation

If an earlier part of the algorithm has already stopped, define this process
only on its alive event and extend its potential by zero on previously
terminated paths whose outcome is harmless or separately charged. At draw14,

    E[1_alive Phi_delta(P_14)] <= D_14

still follows from (2)--(3) and nonnegativity. No conditioning or division by
Pr[alive] is needed. Subsequent drift charges must likewise carry the alive
and pre-hit indicators. If a prior termination is itself an uncharged failure,
extending it by zero does not bound that failure; it needs its own charge.

A corridor gate cannot simply erase paths when they leave the corridor. Either
prove the gate is preserved, charge its relevant exit event separately, or
make it an absorbing bad state with potential1 and include the resulting
conditional increment in c_i. Conditioning on future survival to obtain a
fresh-column law or a favorable drift is invalid.

The only initialization conclusion here is (4) for the matching Part442
observable. What remains is a small total conditional geometric charge in
(5) or the sufficient actual-winner formulation (9), under every relevant
incoming full-history law or an appropriately stopped averaged estimate.
Fresh unused-column uniformity is required for the finite uniform-u expression;
revisiting already exposed columns needs a separate conditional-law argument.
No such charge estimate, later-history bound, or full BKZ proof is supplied.

## Exact verification

Run `python3 docs/research/scripts/wall1_capped_history_potential.py`.
All452 rational seed and two-step stopped-tree checks pass. Additional exact
assertions cover initial threshold equality, a clipped-versus-raw separation,
the insufficiency of a tail-only seed, sharpness of (2) using a mixture on
{0,delta}, and the budget subtraction. The trees use nonuniform transition
probabilities and charges conditioned at each node; they do not assume a
uniform selected-history law. They validate the algebra, not premise (9).

## Choice of exponent after the first-moment seed

The seed comparison(2) holds for every k>=1, including k=1.
[Linear capped transport](wall1_linear_capped_transport.md) connects this
choice to the existing two-height bound and a multiplicative stopped
budget. It needs only a conditional first-moment sufficient criterion,
which is still unproved on actual selected histories.

## Updated sufficient allocation from the sharper compensator remainder

The [sharp correlation MGF accounting](wall1_sharp_correlation_mgf.md) retains
the same early events and draw14..404 observable, but reduces its proved
compensator remainder. It permits a later-history allocation of4.049e-12,
so the corresponding sufficient additive charge in(6) is2.0785491e-12.
The old3.922e-12 allocation and1.9515491e-12 subtraction above remain valid
conservative choices. Neither charge estimate is proved. This update does
not count draw14 twice or absorb uncharged gate failures.

The further early-block refinement in that same note keeps delta=.280
and reduces the compensator remainder below8.850e-14. Its corresponding
later-history allowance is5.0075e-12, leaving3.0370491e-12 after the seed.
This is the sharper same-threshold sufficient allocation; its actual drift
premise remains unproved.
