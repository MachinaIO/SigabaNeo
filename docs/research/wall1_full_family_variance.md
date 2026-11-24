# Full-family collision energy and the small-g crossing

The [Fourier density extension](wall1_fourier_density_extension.md) supplies
many witnesses, but normalizing their number by an arbitrary geometric
subselection does not establish concentration. Uniform thinning cannot even
improve relative variance on average. Retaining the full family removes this
unnecessary choice and exposes the actual collision quantity.

## Thinning identity

At a fixed entry satisfying the old-minimum gate, let a full candidate family
have A>1 points and multiplicities b_u on the m=h−1 nonzero marks. Set
nu=A/m and V=sum_u b_u²/m−nu². For a uniformly chosen L-subset, independent
of the fresh mark, write V_S for its variance over the nonzero marks. Then

    E_S V_S = L(L−1)/(A(A−1)) V
              + L(A−L)/(A−1) (1/m−1/m²).

This follows by expanding the squared multiplicities, using inclusion
probabilities L/A for one point and L(L−1)/(A(A−1)) for two distinct points.
With R=V/nu², normalization by the subset mean L/m gives

    E_S V_S / (L/m)² = R + (A−L)/(L(A−1)) (m−1−R) >= R.

The last inequality uses sum b_u²≤A², hence R≤m−1. Thus large candidate
count alone supplies no concentration gain. A specially chosen subset might
have smaller variance, but no such guarantee follows from a geometric
ordering. This is a statement about finite multiplicities, not a construction
of a bad reachable BKZ history.

## What the actual full-family estimate must bound

Use all nonzero points of K in the radius-squared 1.21g²−2 ball (the smaller
Fourier cell also suffices). On G={h>1, lambda_1(M)>1.1g}, all labels are
nonzero. Let S be this finite family and put

    w(v) = #{x in S : x+v in S},
    B = A + sum_{v in M, v!=0} w(v),
    V = B/(h−1) − (A/(h−1))².

Only differences with 1.1g<||v||≤2sqrt(1.21g²−2) can contribute. The
expected normalized collision expression along actual selected histories,
not the size A itself, is the missing estimate. This is the same exact
collision mechanism already identified in
[Part 217](wall1_long_winner_ceiling.md); no independence of labels is used.

The [selected pair evaluator](wall1_selected_pair_collision.md) connects this
quantity to mixed full/quotient gates and groups pairs by their finite-field
difference span. Exact geometric fixtures rule out replacing selected
incidences by unselected probabilities or assuming every collision decreases.

At each entry i, Cauchy–Schwarz gives the conditional bound

    P(s_i>1.1g_i | history)
      <= 1_Gi (h_i−1)/h_i * V_i/(V_i+nu_i²),
    nu_i=A_i/(h_i−1).

The zero mark gives a unit-height vector, and a hit in S gives a vector
strictly shorter than 1.1g_i. The period gate may also be used to set this
bound to zero when 1.1g_i≥q.

## Charge the number of long winners, not their union

The [existing scalar count argument](wall1_long_winner_routes.md) proves
that a small-g crossing (g_j<34.807 for some incoming draw j=396,...,406)
requires at least 100 strict long winners among draws 1,...,405. Consequently

    P(crossing) <= (1/100) sum_i E[
        1_Gi (h_i−1)/h_i * V_i/(V_i+nu_i²)].

This uses only the pathwise count implication, conditional Cauchy–Schwarz,
and linearity of expectation. It does not require independence across draws
or a uniform conditional ceiling. Extra predictable gates may restrict the
joint crossing event, but excluded histories need a separate bound.

For comparison with the preceding fixed-mean proposal mu=10^16, let
T_i=E[1_Gi 1_{U_i!=0}(Z_i−mu)²] for that proposed subfamily. The simpler
second-moment inequality gives

    P(crossing) <= sum_i T_i/(100 mu²).

Thus sum_i T_i≤405*4000mu would give the same 1.62e-12 bound that previously
required sum_i T_i≤405*40mu for the much stronger any-long-winner event.
Both moment hypotheses remain unproved. The full-family expression above
is preferable because it does not introduce a thinning choice and retains
the sharper ratio V/(V+nu²).

This result concerns the small-g crossing only. It does not bound a
capped-void-potential exit or complete the BKZ theorem.

## Verification

`python3 docs/research/scripts/wall1_full_family_variance.py` checks 2637
exact thinning identities and 474 occupancy bounds over finite count
vectors. An independent audit verified the general identity and the
100-winner crossing scope. These checks do not evaluate production V_i.
