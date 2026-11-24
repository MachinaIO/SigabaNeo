# Exactly cubic grids are exceptional after freeze 20

For the prescribed exact width506, height-one forward restart with uniform
systematic rank400 input over q=3329, the probability that
K_f=P_(F_f-perp) Z^(505+f) is isometric to Z^505 at any freeze21<=f<=406
is less than10^(-1152). This excludes a specific class of states, not
all states with positive drift or all unsuccessful histories.

## Cubic projections force coordinate frozen spaces

Suppose K=P Z^N is isometric to Z^505, where P is an orthogonal
projection of rank505. Each Pe_i is a lattice vector of length at most1,
so its length is either0 or1. Length0 means e_i belongs to ker P;
length1 means e_i belongs to im P, by the orthogonal decomposition of
e_i. Thus ker P is a coordinate space. Its dimension f specifies a set
I of f coordinate axes. This applies in any ambient orientation of the
orthonormal basis of K; it does not assume a prescribed projected frame.

For the systematic syndrome map sigma=[I_400 A] on Z^(505+f), let
r=rank_Fq(sigma_I). Projection off those coordinate axes yields

    det K=1, [K:M]=q^(400-r), det M=q^(400-r).

These are the existing projected-section identities. In particular a
lower bound D_f>=exp(L_f) on the retained determinant forces
r<=k_f=400-ceil(L_f/log q).

## The determinant recurrence is unconditional

Use the existing rank506 Hermite cap gamma506<=56.2142 from
[the finite Hermite certificate](wall1_hermite_caps.md). A height-one
window has determinant D and contains the period (0,q), since qK is
contained in M. Its actual shortest length is at most
min(q,sqrt(56.2142)*D^(1/506)). Dividing D by that primitive length gives

    L_0=400 log q,
    L_f=max(L_(f-1)-log q,
            (505/506)L_(f-1)-(1/2)log(56.2142)).

This recurrence does not require survival, a dual-minimum gate, or
conditioning on a favorable event. The additional coordinate-minor bounds
in [the integrality note](wall1_integrality_bound.md) are separate
high-probability statements; they are not needed here. This application
reuses the existing Hermite certificate rather than proving a new cap.

## Union over every possible coordinate choice

Fix I with f coordinates, b of them among the400 identity columns.
If b>k_f the rank event is impossible. Otherwise a containing k_f-space
must contain those b independent columns. The number of such spaces is
at most2 q^((k_f-b)(400-k_f)), by the finite Grassmannian product bound.
The factor2 is valid because
product_(j>=1)(1-q^(-j))^(-1)<=1/(1-1/(q-1))<2.
The other f-b columns are independent uniform vectors, and land in a
specified space with probability q^(-(400-k_f)(f-b)). Consequently

    Pr(rank(sigma_I)<=k_f)
       <=2 q^(-(400-k_f)(f-k_f)).

Union over I and freezes gives the upper bound

    2 sum_(f=21)^406 binom(505+f,f)
             q^(-(400-k_f)(f-k_f)).                     (1)

The original input matrices at different prefixes need not be independent.
The union is taken before any selector is applied and includes all coordinate
sets, so it also covers adaptive frozen spaces. Conditioning on a selected
history is neither used nor justified by (1).

## Numerical certificate and scope

`scripts/wall1_cubic_history_exclusion.py` imports the existing outward-
interval determinant recurrence. For each of386 freezes it verifies both
sides of the integer threshold determining k_f. It then proves by exact
integer arithmetic that the corresponding term of (1) is less than
10^(-1155). Their sum is less than386*10^(-1155)<10^(-1152).

For example, the minimum quotient ranks at freezes21,52,375,404,406 are
380,349,125,111,110. These are unconditional consequences of this
determinant recurrence, not the stronger late rank floors that also use
the coordinate-minor event. Floating point only proposes threshold
integers; interval comparisons certify them. No Lean formalization is
claimed.

An independent proof audit and70-digit interval evaluation confirmed the
argument and the conservative10^(-1152) ceiling. The unrounded union
bound has log10 between-1155.1759608060 and-1155.1759608059, dominated
by freeze52. The checker above deliberately uses the simpler, weaker
per-term integer certificate rather than depending on that decimal value.

This probability bound can charge the event of an exactly cubic retained
grid by its probability when bounding a capped potential. It does not
charge nearly cubic grids, other noncubic states, or a sum of arbitrary
uncapped multiplicities. It does not prove a multiplier on the complement.
The selected-history void estimate required for the full BKZ proof remains
open. The Part457 example is already excluded deterministically by its
much smaller determinant; (1) excludes a broader cubic class in probability.
