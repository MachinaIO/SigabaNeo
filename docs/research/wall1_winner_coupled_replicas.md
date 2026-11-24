# Actual-winner coupled replicas and the remaining conditional lemma

This note proves a deterministic projection witness bound and its exact replica
identity. It formulates, but does not prove, the conditional geometric estimate
needed for selected-history transport. The winner, radius, and fresh column
are shared across every replica; none is replaced by an independent copy.

## Precise finite marked transition

Condition on the complete incoming algorithmic history S before exposing the
next column. Let M subset K be full lattices in a Euclidean space E, with finite
mark group H=K/M of order h. Assume the next mark U is uniform on H conditional
on this entire history. This is justified for a fresh unused independent column
in the documented restart filtration. It is not asserted for revisited columns,
lookahead conditioning, or conditioning on future success.

Choose representatives k_v in K for each mark v, with k_0=0. Fix a canonical
nearest representative y(v) in k_v+M, resolving ties deterministically. For
u in H form the graph lattice

    W_u=(M,0)+Z(k_u,1) subset E direct-sum R.

Let w_u be the algorithm's actual primitive nonzero selected vector in W_u,
s_u=||w_u||, and Q_u the orthogonal projection onto w_u-perp. For the actual
algorithm this is a shortest winner with its specified tie rule, but the
witness inequality below needs only membership, nonzero length, and projection.
Let b_u>=0 be the actual outgoing radius; it may depend arbitrarily on u and
its winner. If tie-breaking uses additional random coins, include them in the
conditional experiment and share their realized values across replicas.

Define Ktilde_u=(K,0)+W_u and the outgoing finite mark group

    H'_u=Q_u Ktilde_u / Q_u W_u.

Because w_u belongs to W_u, its line is rational relative to both lattices;
the projected groups are lattices. The map

    f_u:H -> H'_u,   v -> Q_u(k_v,0) modulo Q_u W_u

is a surjective homomorphism. It is well-defined because changing k_v by M
changes its projection by Q_u W_u. Surjectivity follows from the definition
of Ktilde_u. Thus all fibers have equal size and uniform marks on H push
forward to uniform marks on H'_u, even if the map has a nontrivial kernel.
Let d'_u(v) be the nearest distance of this projected coset. The actual outgoing
void fraction is exactly

    p'_u = h^(-1) sum_v 1{d'_u(v)>b_u}.                    (1)

There is no extra kernel factor in (1).

## Finite projection witnesses retain the winner gain

Fix a finite nonempty integer height set J, measurable from S. Including zero
is useful but not required for the following inequality. There is no requirement
that the heights be distinct modulo q or satisfy |j|<=b_u: projection can
shorten a lift whose original length exceeds the test radius.
For u,v in H and j in J put

    z_j(u,v)=(y(v+ju),j),
    T_j(u,v)=||z_j(u,v)||²
                 − <z_j(u,v),w_u>²/s_u².                 (2)

Since y(v+ju)−k_v−j k_u belongs to M, the difference
z_j(u,v)−(k_v,0) belongs to W_u. Hence Q_u z_j(u,v) is a representative of
the outgoing marked coset f_u(v), and

    d'_u(v)² <= T_j(u,v)=||Q_u z_j(u,v)||².

Define the finite witness miss indicator and its fraction by

    I_S(u,v)=product_(j in J) 1{T_j(u,v)>b_u²},
    H_S(u)=h^(-1) sum_v I_S(u,v).                          (3)

Then, branchwise and without any law for the selected winner,

    p'_u <= H_S(u).                                       (4)

The comparison is in this direction because these are only finitely many
representatives, not every lattice lift. Nearest incoming representatives
need not give nearest outgoing projections. Enlarging J, or retaining more
representatives per height, can improve (4). Closed hit balls correspond to
the strict inequalities in (3), so boundary ties are handled consistently.

Unlike a conservative radius-cap bound, (2)--(4) retain both the actual
winner-dependent radius b_u and the actual gain <z_j,w_u>²/s_u². They apply
also to horizontal winners; their gain may then be inadequate, but the
inequality itself does not fail.

## Exact shared-column replica identity

For every positive integer k,

    E_U[H_S(U)^k | S]
      = h^(-(k+1)) sum_(u,v_1,...,v_k in H)
                         product_(a=1)^k I_S(u,v_a).      (5)

Proof: expand the kth power of the finite sum (3), and then average the one
fresh uniform u. Repeated v_a are included. Equivalently, conditional on u,
the test marks V_1,...,V_k are independent uniform auxiliary marks, while
u, w_u, Q_u and b_u are shared. These auxiliary marks are counting variables;
they are not additional raw columns exposed to the algorithm.
Together (4)--(5) give an exact, finite upper-bound target for the actual
conditional outgoing kth moment.

Replacing the shared u by independent u_a gives instead

    (E_U H_S(U))^k,

which is at most E_U H_S(U)^k by Jensen and can be strictly smaller. It is
therefore an invalid substitution in this upper bound. The winner and radius
must also not be independently resampled for different replicas.

## The uncapped sufficient bridge

Part443's [capped potential](wall1_capped_history_potential.md) supplies a
stronger usable initialization: the draw14 first-moment certificate bounds
its initial potential directly. The uncapped formulation below remains valid,
but its separate high-power seed is no longer needed for the capped route.


Let F_i be the actual incoming history filtration, P_i its actual void fraction
at the current radius, and B_i={P_i>=delta}, with delta>0. The next state must
be exactly the marked append/select/project transition above, so that
P_(i+1)=p'_(U_i), with its actual next radius. A sufficient new lemma is:
for reachable histories S_i before the first B_i,

    h_i^(-25) sum_(u,v_1,...,v_24 in H_i)
                       product_a I_(S_i)(u,v_a)
           <= P_i^24 + c_i,                              (6)

where c_i>=0 is F_i-measurable. The useful claim would include a bound on
the expected stopped accumulated c_i, not merely their existence. Setting
c_i to the positive excess makes (6) tautologically true but supplies no
probability estimate. No such small-charge estimate is established here.

For completeness, suppose (6) is established for i=i0,...,T−1, and define
tau as the first index in [i0,T] with P_i>=delta (T+1 if none). By (4)--(6),
the nonnegative process P_(min(i,tau))^24 has expected increments bounded by
E[1_(tau>i)c_i]. Finite telescoping therefore proves

    Pr[exists i in [i0,T]: P_i>=delta]
      <= delta^(−24) (E P_(i0)^24
                       + sum_(i=i0)^(T−1) E[1_(tau>i)c_i]). (7)

Thus the two concrete application obligations are an initial moment under the
actual selected state law at i0, and a stopped-charge estimate for (6).
A desired history budget epsilon_hist requires the parentheses in (7) to be
at most delta^24 epsilon_hist. The budget must also leave room for the separate
draw-14 contribution. A fixed-ball moment under a different law is not the
initial moment in (7), and the raw-restart small-radius obstruction prevents
assuming that such a seed is already tiny at the raw initial lattice.

A gate restricting to a corridor or favorable history must be included in the
stopping construction and its exit probability charged separately, unless its
preservation is proved. Equation (7) does not condition for free on remaining
inside that gate or on eventual algorithmic success.

## Relation to current kernels and obstructions

For a fixed u, (2) involves w_u selected through all competing-vector tests.
Expanding (5) over candidate winners is legitimate only if the selection
indicators are retained. Dropping them is a positive upper bound but introduces
an uncontrolled sum over possible winners. Current fixed-chart Gaussian and
cumulant estimates do not bound that sum or justify making the residual map
uniform after selection. The height conditions in (3) are joint projected
quadratic inequalities involving one selected direction, not independent
ball incidences under the existing fixed-reference law.

The conservative-cap rectangular shell example does not refute (6): its
actual winner/projection transition is not controlled by that example, nor is
reachability established. The planar winner example shows why the retained
inner-product term can help in a special subclass. Transcript and collision
counterexamples exclude dropping competitor information or converting
fixed-time estimates to a maximal bound without conditional control; they
do not disprove (6) for reachable histories.

## Exact checks on actual small marked lattices

Run `python3 docs/research/scripts/wall1_winner_coupled_replicas.py`.
It uses M=a q Z subset K=a Z, q=3,5,7, a=1 or1/4, and actual shortest winners
in W_u={(a x,j):x=u j modulo q}. The vector (a q,0) bounds the search radius,
so enumerating |x|,|j|<=q is complete for these a<=1. Exact comparisons select
the shortest vector and verify its primitivity in the graph basis.
The projected lattice has spacing a q/s_u and the marked distance squared is

    d'_u(v)² = a² |j_u v|_q²/s_u².

The script checks (4), quotient-fiber multiplicities (including horizontal
winners with nontrivial kernel), and (5) for k=1,2,3,24. It passes270 actual
winner branches,216 exact replica moment checks, and27 nontrivial-kernel cases.
It uses squared toy radii1/4,1, and4/(1+s_u²); these test winner-dependent
radii but are not asserted to equal the production BKZ radius law.

A strict countercheck uses q=5,a=1,J={−1,0,1},b²=1/4. The five witness miss
counts are4,4,2,2,4. Hence the correct24th moment is

    [3*(4/5)^24+2*(2/5)^24]/5,

whereas independently resampling u in each replica gives (16/25)^24.
The former is more than127 times the latter. The script verifies the exact
fractions and their strict inequality. The finite examples validate the
identities and expose this conditioning error; they do not prove (6).
