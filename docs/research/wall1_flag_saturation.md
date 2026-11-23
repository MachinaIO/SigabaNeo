# Exact saturation weights and collision moments

Part 264 conditioned only on containing a fixed flag. A selected primitive flag
also satisfies Gamma=L(A) intersect U. This note computes that additional
condition exactly, including its joint law with collision equations. Shortestness
and the quantitative sum over selected histories still remain open.

## Arithmetic prefilter

Let Gamma be a fixed rank-r subgroup of Z^(m+d), U its real span, and
Lambda=U intersect Z^(m+d). Because q Z^(m+d) is contained in every graph lattice,

\[
             \Gamma=L(A)\cap U\quad\Longrightarrow\quad q\Lambda\subseteq\Gamma.
                                                               \tag{1}
\]

A proposed flag violating (1) has zero selection probability and can be discarded.
Assume (1). Reduction modulo q identifies E=Lambda/qLambda with an r-dimensional
subspace of F_q^(m+d). Indeed, if lambda=qz lies in Lambda, then z lies in U and
hence in Lambda. Thus Lambda intersect qZ^(m+d)=qLambda.
Let F=Gamma/qLambda be its subspace and t=dim F. The preimage of F in Lambda is
exactly Gamma. Let pi be projection to the d input coordinates, and put s=dim pi(E).

For A uniform, write K_A={(Ay,y):y in F_q^d}. Containment requires F subset K_A.
If pi is not injective on F, containment is impossible. Otherwise it has probability
q^(-mt), by the fixed-flag equations of Part 264. On that event,

\[
 \Gamma=L(A)\cap U\quad\Longleftrightarrow\quad E\cap K_A=F.    \tag{2}
\]

For a saturated flag, the number of raw labels lost under projection is therefore
[Lambda:Gamma]=q^(r-t), and the projected mark group has size q^(m-r+t).
In particular r-t>m is impossible. Here t is the rank of the flag's input columns
whenever containment is possible; it need not equal the real rank r.

## Saturation probability under containment

Define S(E,F)=Pr(E intersect K_A=F | F subset K_A), for graphic F (pi injective).
Set a=r-s. Then

\[
 S(E,F)=
 \begin{cases}
 \displaystyle\prod_{j=0}^{s-t-1}(1-q^{a+j-m}),&r-t\le m,\\
 0,&r-t>m.
 \end{cases}                                                   \tag{3}
\]

An empty product is one. To prove (3), use the syndrome map f_A(x,y)=x-Ay.
Its restriction to E has the fixed a-dimensional injective image of
E intersect (F_q^m times {0}). After containment kills F, choose s-t input
directions in pi(E) completing pi(F). Their images under A are still independent
uniform output vectors. Thus the remaining s-t syndrome vectors are independent
uniform modulo the fixed a-dimensional image. Injectivity on E/F requires these
vectors to extend that image independently. The successive probabilities are
1-q^(a+j-m), proving (3). If E/F has dimension r-t>m, injectivity is impossible.
No shortest-vector assumption enters this calculation.

## Joint law with collision constraints

The candidate set C is fixed by the proposed flag and its radius. For any finite
list D of ordered candidate differences, put G=span(F,D) modulo q, u=dim G.
The event that all these differences collide is G subset K_A. Conditional on
F subset K_A, the joint probability of saturation and all these collisions is

\[
 Q_E(F;D)=
 \begin{cases}
 q^{-m(u-t)} S(E+G,G),&\pi|_G\text{ injective and }E\cap G=F,\\
 0,&\text{otherwise}.
 \end{cases}                                                   \tag{4}
\]

Non-graphic G cannot lie in K_A. If E intersect G contains more than F, saturation
is impossible. In the remaining case, imposing G costs q^(-m(u-t)). On that event,
(E+G) intersect K_A=G is equivalent to E intersect K_A=F: subtract the G component
of any vector in the first intersection. Formula (3) now proves (4).

Let w_delta be the number of ordered pairs in C having difference delta modulo q,
including the diagonal, and let J be their collision count. Then, conditional on
containment of F, the exact unnormalized saturated moments are

\[
 M_1=\sum_\delta w_\delta Q_E(F;\{\delta\}),\qquad
 M_2=\sum_{\delta,\epsilon}w_\delta w_\epsilon
                        Q_E(F;\{\delta,\epsilon\}).           \tag{5}
\]

They equal E[J 1_sat | contain] and E[J^2 1_sat | contain]. If S(E,F)>0, the
mean and variance under both containment and saturation are

\[
                \mu=M_1/S,\qquad \sigma^2=M_2/S-\mu^2.         \tag{6}
\]

Thus Part 264's one-sided bound can be applied with these moments and the exact
outer flag weight q^(-mt) S(E,F). The threshold is unchanged:
tau=25 |C|^2/(18 q^m). If tau>mu, the resulting contribution is at most
q^(-mt) S sigma^2/(sigma^2+(tau-mu)^2); otherwise the trivial contribution is
q^(-mt) S. A zero S removes the flag entirely. One must not multiply S by the
old containment-only tail bound: the two events are generally dependent.

This refines the flag union bound by retaining saturation exactly. It still
requires a complete family of possible selected flags and radii, and does not
retain shortestness comparisons. No width-506 sum or improvement on the remaining
3.922e-12 history allowance is established here.
In particular, when there is no mark-group loss, r=t and E=F, so S=1 and
saturation imposes no extra restriction beyond containment. The correction cannot
by itself control that class of flags; shortestness or another geometric estimate
is still essential for the unresolved probability sum.

## Basis implementation at the actual modulus

`scripts/conditional_graph_space.py` implements the conditional law without
enumerating points of a finite-field subspace. Raw vectors use output-first
coordinates (x,y); the internal fixed-constraint matrix uses (y,x), so RREF
pivots expose the input rank. Any pivot in an output column makes containment
inconsistent. Otherwise, eliminating the input pivots from each candidate gives
its residual (free input, output) vector in dimension m+d-t. This is the
complement construction of Part 264, performed by exact arithmetic modulo q.

The remaining map is uniform from d-t free input dimensions to m outputs.
The image of E modulo F is represented by a residual RREF basis E_bar.
For imposed residual constraints G, the implementation returns zero when G is
not graphic or E_bar intersect G is nonzero. Otherwise it returns

\[
 q^{-m\dim G}\prod_{j=0}^{s-\dim G-1}(1-q^{a+j-m}),\qquad
 s=\dim\pi(E_{\rm bar}+G),\quad a=\dim(E_{\rm bar}+G)-s,
\]

with zero when dim E_bar>m. This is (4) after quotienting out F. Joining bases
and checking intersections use rank identities; no q^rank point set is built.
The API assumes a prime modulus and canonical RREF bases for its state arguments.

The three-dimensional selected-moment checker now uses this representation in
its actual exclusion and collision paths. The older subspace-enumeration checker
independently compares the basis implementation against the formula and all graph
matrices on its 511 nested-space cases, including saturation losses.

`python3 docs/research/scripts/wall1_graph_space_large.py` also checks q=3329,
m=400,d=117,t=12, so the raw dimension is 517 and the residual dimension is 505.
It imposes eight independent additional input directions and verifies all 37
degree-at-most-two states, with probabilities q^(-400 j), the exact truncated
expression 1-8p+28p^2, impossible-output pruning, saturation probabilities, and
RREF invariance under changing generator order. These are algebraic fixtures,
not actual selected flags or complete competitor lists of the restart.

Thus the field-point enumeration obstacle in the evaluator is removed. The
number of generated basis states, geometric candidates and selected flags can
still be enormous. No width-506 probability bound follows from this implementation.

## Finite verification

[Selected flag moments](wall1_selected_flag_moments.md) retain shortestness as
well, by a finite competitor list and nonnegative weighted inclusion--exclusion.
That refinement still lacks a width-506 aggregate bound.

`python3 docs/research/scripts/wall1_flag_saturation.py` exhausts all nested
subspaces F subset E with graphic F for (q,m,d)=(2,1,2),(3,1,2),(2,2,2).
For all 511 cases it enumerates the graph matrices directly, checks containment
and saturation probabilities, and compares both moments in (5) with direct
collision counts. There are 14468 joint-moment terms, including impossible
saturation, certain saturation, and probabilities strictly between zero and one.
This is a paper derivation with finite checks, not a Lean formalization or an
independent audit of the general argument.
