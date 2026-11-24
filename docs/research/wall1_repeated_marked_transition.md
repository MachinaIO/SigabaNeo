# Exact repeated marked-lattice transitions

This supplies executable transition mechanics for repeated finite experiments.
It does not supply the high-dimensional concentration or tail estimates needed
to complete the BKZ proof. The independently sampled fresh-column model is
explicit; no unexposed randomness is assumed for reused columns.

## State and shortest selection

Represent K in a lattice basis by a rational positive-definite Gram matrix G
of rank d. Let B:F_q^d -> F_q^m be surjective, with q prime, and let M be the
integer vectors whose labels vanish modulo q. Then det M=q^m sqrt(det G).
Select an actual shortest nonzero v in M, orienting its first nonzero coordinate
positively and resolving ties lexicographically in this state's basis.

A complete finite shortest search uses squared radius
R²=q² min_i G_ii, since q times every basis vector belongs to M. The coordinate
bounds |z_i|²<=R²(G^(-1))_ii follow from Cauchy--Schwarz in the G metric.
Exact integer square-root bounds therefore enumerate a box containing a
shortest vector; the code minimizes the rational squared length in that box.
This is a small-dimensional enumeration algorithm, not an efficient production
SVP oracle.

Write v=t*w, with w primitive in Z^d. The least positive integer s with
s*w in M is the order of Bw: one when Bw=0 and q otherwise. Minimality
forces t=s. In particular, the selected vector can be nonprimitive in K even
though it is primitive in M. Dividing by its coordinate gcd without adjusting
the quotient would lose this distinction.

## Projected coordinates, labels and determinant

Choose a unimodular S whose first column is w, using integer Bezout steps.
Put Q=S^T G S. The remaining projected basis columns have Gram matrix

    G'_ij=Q_ij-Q_i0*Q_0j/Q_00,  i,j>0.

The actual new mark group is

    PK/PM = K/(M+Zw) = F_q^m / span(Bw).

When Bw is nonzero, choose a nonzero pivot coordinate p and map a syndrome y
to (y_i-(Bw)_i*y_p/(Bw)_p) over i!=p. Apply this map to the remaining columns
of BS. Otherwise retain those columns unchanged. The resulting B' remains
surjective and has m'=m-1 or m'=m, respectively. The exact finite checker
verifies, for every retained coordinate residue, that its new label is zero
if and only if some lift along w has old label zero.

Let e=1 if Bw!=0 and zero otherwise. Then

    det(PM)=q^(m-e)*sqrt(det G)/||w|| = det M/||v||.

The code verifies this identity after squaring, so no irrational numerical
approximation is needed. It also verifies unimodularity, the first column of
S, and surjectivity of B'.

## Fresh append and probability propagation

For fresh U uniform in F_q^(m') conditional on the full old history, append
one orthogonal unit coordinate. The state becomes

    Gram = diag(G',1),  labels = [B' | -U].

The height-zero kernel is PM, and integer height is surjective, so the append
preserves det(PM) and restores width d. Each branch receives the current
history mass divided by q^(m'), using the post-projection mark dimension.
A trivial quotient has one branch, not q branches. Equal exact states may
be merged by adding their rational masses; no uniform distribution over the
set of terminal states is imposed. The tie rule is attached to each tracked
basis and is deterministic before the next fresh draw.

## Finite repeated checks and limitation

The checker starts from G=I_3 and the nine equally likely label rows
B=(1,-a,-b) over F_3. It performs three shortest/project/fresh-append
transitions. The numbers of distinct tracked states after those steps are
18, 36, and 63. At every step their exact rational masses sum to one; all
shortest searches, projected quotient checks, and determinant identities pass.
The mark rank remains one along this initial experiment's three steps.

A separate thin marked direction, G=diag(1/100,1,1) and B=(1,0,0), forces
the shortest vector 3e1. Its projection has no remaining marks; the fresh
append is Z^3. This tests a real rank drop and the single trivial-quotient
branch rather than asserting rank drops occurred in the preceding tree.

Run `python3 docs/research/scripts/wall1_repeated_marked_transition.py`.
Independent mathematical review verified the primitive-direction distinction,
quotient map, determinant identity and fresh-branch law. These mechanics can
support longer finite selected-history experiments. They do not bound the
production selected Gram matrices, prove a drift inequality, or extrapolate
small-dimensional probabilities to width506. No Lean formalization is claimed.
