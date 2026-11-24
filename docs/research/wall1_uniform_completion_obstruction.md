# Exact extremal uniform affine-slice occupancy

Let q be an odd prime, 1<=d<=n, and B_R be the residues in F_q^n whose centered integer
representatives have Euclidean norm at most R. For every affine d-plane U,

    |U intersect B_R| <= C_d(R),
    C_d(R) = #{z in Z^d: |z_i| <= (q-1)/2, sum z_i^2 <= R^2}.

This uniform bound is optimal: equality holds for the coordinate d-plane
through zero. To prove the upper bound, choose d coordinate functionals whose
restrictions to the direction of U are independent. Their joint restriction
is injective on U. Taking these coordinates cannot increase the norm of the
centered representative. Their images therefore lie in the set counted by
C_d(R). The lower bound is the coordinate-plane construction itself. This
argument concerns input residue occupancy, not integer representative
multiplicity or the probability of joint output incidence.

In particular, with b=min((q-1)/2, floor(R/sqrt(d))),

    any cap valid for all affine d-planes >= (2b+1)^d.

Thus sharper volume estimates, theta optimization or exact lattice-point
counting cannot drive a uniform occupancy cap arbitrarily low.

## Consequence for the present two-relation terms

Hold all anchor bounds and chart counts fixed, and replace only the uniform
completion cap M in a numerical envelope term A*M^k. Any replacement valid
for all affine d-planes leaves that term at least A*(2b+1)^(d*k). This is a
lower bound on the numerical expression produced by this restricted method,
**not a lower bound on any failure probability or actual incidence count**.

The companion script uses the production radius formula, q=3329 and downward
rounded snapshots from `/tmp/wall1_all_rank_frontier.log`:

- size18/rank9/c4, crossing t5/a3, k7: log10 term >10.832;
- size19/rank11/c4, crossing t9/a3, k6: log10 term >39.947;
- size24/rank12/c5, crossing t9/a4, k10: log10 term >212.809.

With d=r-1, all three expressions remain above 1e-12 even with the best
possible uniform cap. This does not exclude a different complete cover,
a stronger anchor estimate, an occupancy bound restricted to realizable
anchors, or an average weighted by actual anchor incidence. It does exclude
closing these particular terms solely by replacing the present ball-volume
cap with a better bound valid for every affine plane. No assertion is made
that the extremal coordinate plane is attained by an anchor in these strata.

The calculation uses interval arithmetic, checks the integer cube radius
against both endpoints, and makes no change to production bounds. Run
`python3 docs/research/scripts/wall1_uniform_completion_obstruction.py`.
The retained output is `/tmp/wall1_uniform_completion_obstruction.log`.
