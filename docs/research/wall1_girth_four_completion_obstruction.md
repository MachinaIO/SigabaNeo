# Girth-four completions after a connected spanning anchor

For the size19/rank11/c4 leader, the H13 anchor already spans the full
rank-eleven augmented input space. Six dependent positions remain. The
following general lemma shows that connectivity and girth four alone
cannot substantially reduce completions of a span with large ball occupancy.
It complements the uniform-cap obstruction and does not estimate the actual
weighted anchor law.

## Exact deterministic bounds

Let A consist of m>=2 distinct points in an affine space U over F_q. Assume
its augmented matroid is connected, has girth at least four, and spans U.
Let C be any finite candidate subset of U containing A, and let L=|C|.
Write G_k(C,A) for the number of ordered k-point extensions from C whose
union with A still has girth at least four and is connected. Then

    product_(j=0)^(k-1) max(0,L-q*binomial(m+j,2))
       <= G_k(C,A) <= L^k.                                  (1)

Proof. A new point violates distinctness or creates an affine three-point
circuit exactly when it lies on a secant line through two existing points.
The union of these lines has at most q*binomial(m+j,2) points. Endpoints
are included, so this bound also excludes repeated points. Intersecting
with C can only reduce the number of forbidden candidates. Apply this
conditional lower bound successively along every admissible prefix.

Connectivity imposes no further deletion. Every new augmented vector lies
in the span of the old connected matroid and is nonzero. A minimal linear
representation gives a circuit containing the new element and old elements,
so it joins their connected component. The whole span and rank stay fixed.
This remains true after each extension. This argument uses the full-rank
connected anchor hypothesis; it is not asserted for a disconnected or
nonspanning seed.

If L>=q*binomial(m+k-1,2), the product inequality gives

    G_k(C,A)/L^k >= 1-q*sum_(j=0)^(k-1) binomial(m+j,2)/L.    (2)

For q=3329, m=13, k=6 the numerator is exactly 2,273,707. Thus a large
candidate occupancy cannot be reduced by orders of magnitude merely by
imposing these two combinatorial properties. Equation (1) is a lower bound
on the number of admissible completions, hence an obstruction to an
unsupported small upper bound; it is not a failure-probability lower bound.

## A centered-ball anchor of the actual H13/r11/c4/t9/o3 shape

In the coordinate ten-plane over F_3329, let e1,...,e10 be the standard
basis and take the ordered points

    0, e1, e2, e1-e2, e3,...,e10,
    v=(e1-2e2+e3+...+e10)/8.

Division by eight is in the finite field. The two relations are

    a=(1,1,-1,-1,0,...,0),
    b=(1,1,-2,0,1,1,1,1,1,1,1,1,-8).

Both are balanced. Omitting positions 3 and 12 (zero-based) leaves
0,e1,...,e10, so augmented rank is eleven and these relations span the
entire relation code. Every relation outside span(a) has all nine new
coordinates nonzero, so its support is at least nine; a has support four.
Thus girth is exactly four. The fundamental circuits a and b overlap and
together cover all thirteen positions, proving connectivity. The crossing
b has precisely three old positions and nine new positions.

The centered representative of 1/8 is -416. Hence v has nine entries -416
and one entry 832, with squared norm 2,249,728. Every anchor point is in
the radius2933 centered ball. The same coordinate plane contains the whole
cube [-927,927]^10 inside that ball, since 10*927^2<=2933^2. All anchor
points themselves lie in this cube. Its candidate count is

    L=1855^10=482435368539828315713126962890625.

Apply (1) to this cube. There are at least

    (1-4.713*10^-27)*L^6

ordered six-point completions preserving girth four and connectivity.
The log10 of this lower count is approximately 196.100634837. Against the
current M_10^6 completion cap with log10 approximately 210.496058227, this
is about 14.3954 decimal orders below that cap. Thus a uniform repair using
only the radius, affine dimension, this anchor shape, girth four and
connectivity cannot justify an arbitrarily tiny completion cap.

This coordinate construction embeds in the full input space by zero
padding. Choosing the zero affine output map makes its input-ball points
valid joint-ball points as well, but that map has its own incidence weight;
its existence says nothing about typical maps or weighted averages.

## Scope relative to the current restricted residual

The displayed anchor has the same H13/r11/c4/t9/o3 shape as the current
leader. **Membership in the residual after every D24-six and other anchor
exclusion has not been audited here.** Shape and girth alone do not imply
that membership. Consequently this note does not claim a counterexample
to a proposed bound exploiting those additional exclusions, nor to an
estimate using the actual Gaussian/incidence weights of anchors.

The general lemma (1) applies to any connected spanning anchor, including
an anchor in the restricted residual once that membership is established.
What remains unknown there is the actual ball occupancy L and its weighted
law. As the weighted-completion note explains, conditioning on the whole
full-rank anchor leaves a singleton reference plane. To improve its
completion factor one must control that occupancy or average over varying
anchors with their actual weights. Applying a random independent-plane law
would not follow from connectivity or girth four.

## Verification

Run `python3 docs/research/scripts/wall1_girth_four_completion_obstruction.py`.
It checks (1) against exact ordered two-completion counts for eight centered
ball fixtures over F5 and F7, then checks the q3329 anchor, its modular
relations, spanning basis, centered norms, cube containment, and the exact
rational product bound for six completions. The general proofs above are
paper proofs, not Lean formalization. Production is unchanged.
