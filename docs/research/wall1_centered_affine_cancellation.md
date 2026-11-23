# Centering before bounding affine graph moments

The coloop cancellation and the pruned moment identity are now Lean-formalized;
the rank-count majorant below remains a paper lemma. This is not a completed BKZ proof.
It gives a different counting target from the absolute factorial-moment error in
[Part 250](wall1_affine_void_moments.md). All candidate sets below are fixed before
drawing the matrix. No selected projected candidate set is treated as fixed.

## Exact cancellation

Let q be prime, let F be a uniformly random linear map from F_q^(d+1) to F_q^m,
and put p=q^(-m). For a fixed point z=(x,y), set u_z=(1,y) and
I_z=1{F(u_z)=x}. For an ordered k-tuple t=(z_1,...,z_k), allowing repetitions,
let r(S) be the rank of the u_j for j in S. Let c(S) indicate that the assignment
u_j -> x_j, j in S, extends linearly. Equivalently, the rank of (1,y_j,x_j)
equals r(S). The empty set has rank zero and is consistent. Define

\[
 W(t)=\sum_{S\subseteq[k]}(-p)^{k-|S|}c(S)p^{r(S)}.
\]

Then the exact affine incidence formula and expansion of the product give

\[
 W(t)=\mathbb E\prod_{j=1}^k(I_{z_j}-p).                 \tag{1}
\]

Suppose some index j satisfies
u_j not in span{u_l : l != j}; in matroid language j is a coloop of this
indexed list. Then **W(t)=0**, regardless of the output coordinates x_l.
Indeed, conditional on the entire restriction of F to the span of the other
inputs, F(u_j) is still uniform in F_q^m. The conditional mean of I_{z_j}-p
is zero, and every other factor is measurable with respect to that restriction.
This argument also covers inconsistent assignments among the other points.
An index repeated in the input list cannot be a coloop.

There is also a direct pairing proof within (1). Pair S not containing j with
S union {j}. Independence gives r(S union {j})=r(S)+1 and
c(S union {j})=c(S), so the two summands cancel exactly.

## A count that respects the cancellation

Let S_0 be a fixed finite candidate set, C=|S_0|, Z=sum_z I_z and mu=Cp.
For k>0, write T_k for the ordered tuples in S_0^k having no coloop in their
augmented **input** list. Then

\[
 \mathbb E(Z-\mu)^k=\sum_{t\in T_k}W(t).                \tag{2}
\]

In particular, for even k and C>0,

\[
 \Pr(Z=0)\le\mu^{-k}\sum_{t\in T_k}\max(W(t),0)
 \le\mu^{-k}\sum_{r\ge1}2^k p^r\,T_{k,r},             \tag{3}
\]

where T_{k,r} counts the tuples in T_k of augmented input rank r. To prove the
last inequality, removing k-|S| vectors lowers rank by at most k-|S|. Thus
k-|S|+r(S)>=r([k]), and each absolute summand in (1) is at most p^r.
There are 2^k subsets. The first inequality follows because the even power
is nonnegative and equals mu^k on Z=0; discarding negative tuple contributions
can only increase its expectation.

The last bound is deliberately coarse. Equation (2), or the positive parts in
(3), is the useful exact target. In particular, inconsistent output patterns
cannot simply be deleted: their centered contribution need not vanish. Nor can
input rank be replaced by full-point rank when deciding which tuples cancel.

For k=2 this recovers the expected distinction. Different augmented inputs are
independent and cancel. Equal inputs with distinct outputs give W=-p^2, while
a repeated point gives W=p(1-p). Both kinds have input rank one and no coloop.

## A sharper bound from full-support relation counts

The following additional identities are paper proofs with exact finite checks;
this section is not yet Lean-formalized. Assume m>=1, put Q=q^m and p=1/Q,
and retain all repeated entries of the indexed tuple. Let U have columns u_j.
A block relation is a tuple a=(a_1,...,a_k) with a_j in F_q^m such that

\[
 \sum_j u_j(a_j)_i=0 \quad\text{for each }1\le i\le m.
\]

Let D be the number of these relations with every block a_j nonzero. Let D_0
count those also satisfying the single scalar equation

\[
                         \sum_j a_j\mathbin{\cdot}x_j=0.
\]

Then there is an exact rational identity

\[
                W(t)=p^k\frac{qD_0-D}{q-1}.                \tag{4}
\]

Here D_0 imposes **one scalar equation**, not m separate equations. One can
interpret (4) by character orthogonality, but the following proof uses only
finite linear algebra and inclusion-exclusion.

If blocks outside S must vanish, the space of relations has dimension
m(|S|-r(S)), so its cardinality is Q^(|S|-r(S)). The scalar output pairing
vanishes identically on this space exactly when c(S)=1: this says each output
row belongs to the row space of U restricted to S, equivalently the prescribed
outputs extend linearly. Otherwise its kernel has index q. Inclusion-exclusion
therefore gives

\[
\begin{aligned}
D&=\sum_{S\subseteq[k]}(-1)^{k-|S|}Q^{|S|-r(S)},\\
D_0&=\sum_{S\subseteq[k]}(-1)^{k-|S|}
       q^{m(|S|-r(S))-(1-c(S))}.
\end{aligned}                                                   \tag{5}
\]

When c(S)=0 the relation space is nonzero, so the exponent in the second line
is nonnegative. In qD_0-D, inconsistent subsets cancel, and each consistent
subset contributes (q-1) times its first-line term. Multiplication by p^k
recovers exactly (1), proving (4).

Since 0<=D_0<=D, (4) implies

\[
       -\frac{p^kD}{q-1}\le W(t)\le p^kD.                 \tag{6}
\]

Select r pivot columns of U. Every block relation is determined by its k-r
nonpivot blocks. Requiring all those blocks to be nonzero already leaves at
most (Q-1)^(k-r) possibilities; the pivot nonzero requirements can only reduce
this number. Consequently

\[
          |W(t)|\le p^kD\le p^r(1-p)^{k-r}.              \tag{7}
\]

This removes the factor 2^k from the earlier termwise majorant. The left side
of (6) is stronger still for negative terms when q>2. For a consistent full
output assignment D_0=D, so W=p^kD>=0. A coloop forces its block in every
relation to be zero, hence D=0, recovering the previous cancellation.

For an input circuit (rank k-1 with no coloop), its scalar kernel is spanned
by one vector c with every c_j nonzero. Block relations have a_j=c_j v, and
full support is equivalent to v!=0. Thus D=Q-1. If sum_j c_j x_j=0, all these
relations have zero pairing. Otherwise the zero-pairing relations number
Q/q-1. Therefore the exact circuit contribution is

\[
 W(t)=
 \begin{cases}
 p^{k-1}(1-p),&\text{consistent outputs},\\
 -p^k,&\text{inconsistent outputs}.
 \end{cases}                                                \tag{8}
\]

The negative case may be discarded in an upper bound for a moment, without
charging its absolute value. This permission applies to circuits as proved in
(8), not to arbitrary inconsistent tuples.

For even k>0, equation (3) can consequently be sharpened to

\[
 \Pr(Z=0)\le\mu^{-k}\sum_{r\ge1}p^r(1-p)^{k-r}T_{k,r}.
                                                               \tag{9}
\]

More sharply, separate the no-coloop rank-(k-1) tuples: their contribution is
exactly p^(k-1)(1-p) times the compatible count minus p^k times the incompatible
count. This is an algebraic improvement, not a bound on either count at width 506.

### Extension-field refinement of the negative bound

Identify the output vector space with K=F_(q^m) using any F_q-linear isomorphism.
The uniform affine coefficients then become independent uniform K elements.
The columns u_j have entries in the base field, so their rank over K is still r;
output consistency over K is equivalent to simultaneous consistency of the m
base-field output rows. The block relations above are exactly ker_K(U), so D
does not change. Write E_0 for the number of its full-support vectors satisfying
the **K-valued** equation sum_j a_j x_j=0, using multiplication in K.
This is different from the scalar dot-product condition defining D_0.

The same inclusion-exclusion proof, now over K, gives

\[
 E_0=\sum_{S\subseteq[k]}(-1)^{k-|S|}
       Q^{|S|-r(S)-(1-c(S))},\qquad
 W(t)=p^k\frac{QE_0-D}{Q-1}.                              \tag{10}
\]

Consequently the stronger one-sided bound is

\[
                 -\frac{p^kD}{Q-1}\le W(t)\le p^kD.      \tag{11}
\]

The upper bound (7) is unchanged. Circuit contributions in (8) attain both
extremes of (11). General inconsistent tuples need not be negative: with q=3,
m=1, use the tuple ((0,0),(0,0),(1,0),(1,0)). Its centered product has expectation
1/27>0, although the full output assignment is inconsistent. Thus (8) cannot
justify deleting every inconsistent tuple.

## What this changes and what remains open

Taking absolute factorial-moment errors before centering loses the cancellation
above. Direct evaluation of that older majorant at draw 13 gives about 41.55
already at order 10, and about 2.532e31 at order 12. These are unusable upper
bounds, not lower bounds on the true failure probability. An improvement must
bound the surviving patterns in (2) more sharply; increasing the order alone
does not justify an improvement.

The follow-up [input-fiber analysis](wall1_affine_fiber_moments.md) proves a
stronger limitation: at draw 13, even exact counts T_{k,r} make the normalized
rank-only majorant (9) exceed 10^6977. Thus improving those counts alone is not
a viable way to use (9). Candidates sharing one input must first be aggregated
with their signed contributions, or output compatibility must otherwise be retained.
Even an improved moment bound for the fixed raw ball cannot overcome the draw-16 raw coverage obstruction
in Part 250. Later draws still require projection-aware counts or a stronger
probabilistic lower bound on the actual radius. The selected-history target for
draws 13--404 and the separate score/horizontal/prefix obligations remain open.

## Exact verification

Run `python3 docs/research/scripts/wall1_centered_affine_cancellation.py`.
It compares (1) with direct averages over every affine map, checks coloop
cancellation, and checks the sharper (4)--(8), all with integer and rational arithmetic.
It independently enumerates full-support relations and checks both inclusion-exclusion
counts in (5), including every nonzero output-pairing fiber. It also checks (10)--(11);
for the two-output fixture it implements F_4=F_2[t]/(t^2+t+1) explicitly and
independently enumerates its zero and nonzero field-valued pairing fibers.
The four fixtures over
q=2,3,5 cover 1490 tuple multisets, including 799 forced zeros,
multiple output rows, incompatible targets, repeated points through order eight,
and a six-point input circuit. Symmetry makes one multiset representative
sufficient for these finite tuple tests. These regressions do not constitute
a general formal proof.

## Lean verification

`AffineGraphMoments.lean` now proves `centeredProduct_zero_of_separator` by
averaging over translations of the uniform design in a separating input direction.
`centeredProduct_zero_of_coloop` constructs that direction from nonmembership in
the span of the remaining augmented inputs. Neither theorem assumes output
compatibility or distinct tuple entries.

`central_moment_no_coloops` proves (2), with W represented by its exact finite
expectation, for every order including zero. `void_le_no_coloop_sum` connects
this identity to the eighth-moment void bound at the true mean C/q^m for a
nonempty fixed candidate list. The formalization allows repeated list entries;
for a set count, use an injective enumeration.

File compilation and all thirteen printed axiom checks pass with only `propext`,
`Classical.choice`, and `Quot.sound`. The subset-rank expression for W in (1),
the positive-part and rank-count majorants in (3), and a usable numerical bound
on the surviving tuples are not part of these new Lean theorems. The fixed-list
restriction remains: the candidate list cannot depend on the same design being
averaged over.
