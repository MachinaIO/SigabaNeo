# A complete rank-ten D32 cover with two crossing sizes

This extends the rank-nine crossing argument to rank ten. Both a crossing
with two new points and a crossing with three new points are necessary in
the cover. It does not multiply the rank-nine envelope by a free-point mean
and assert completeness. This worker does not edit production.

## Coverage from a fundamental-circuit graph

Fix a connected rank-ten component of girth at least six containing a
D32 two-six anchor on ten positions, of rank eight. Choose a deterministic
independent eight-position basis B of this anchor and extend it to a basis
of the component by two new elements E. In a represented matroid the
bipartite graph joining a nonbasis element to the basis elements in its
fundamental circuit is connected whenever the matroid is connected.
Otherwise every fundamental dependence stays within one graph component,
so the representation splits as a direct sum, contradicting connectivity.

The anchor is connected, so its ten positions and all of B belong to one
connected part of that graph. Some fundamental circuit must join an element
of E to B: take the first edge crossing the cut between B and E through a
nonbasis vertex. More explicitly, connectivity of the graph implies a
nonbasis vertex whose fundamental support meets both parts of the basis.
That vertex cannot be an anchor position, since anchor positions lie in
span B. Its circuit uses a nonempty subset of E of size one or two, some
old positions in B, and the nonbasis point itself. Thus the number t of
new positions in the crossing is 2 or 3. Its old support size a satisfies
6-t<=a<=8 by girth six.

The union of the anchor and this crossing has 10+t positions and rank
7+t. For t=2 one further independent point extends it to rank ten; for
t=3 it already has rank ten. Each case therefore exposes exactly thirteen
positions before completing the remaining points in the rank-ten affine
span. No assumption of a two-point crossing in every component is used.

Fix the new support, the old subset of the deterministic B, and one
normalized nonzero new coefficient. The balanced affine relation satisfies
one further linear equation. Consequently the number of coefficient charts
is at most

    C_t=sum_(a=6-t)^8 binomial(8,a)*q^(t+a-2),  t=2,3.

Ignoring nonzero constraints only enlarges this bound. For fixed supports,
normalization and the chosen B specify a unique chart for each relation
line. Distinct witnesses or different choices of B-extension may cover the
same component; their sum is a union bound. We do not divide by a claimed
witness multiplicity. The event can be partitioned by a deterministic
choice of t=2 witness when available, and otherwise t=3, if disjoint event
classes are desired; the displayed sums remain valid overcounts of these
classes.

## Third projected height and the complete short-line split

Use the two balance-preserving affine representatives and the projected
integer minimum 3/4 from `wall1_six_ten_projection.py`. Their squared GS
lengths are (6,16/3), with nearest-plane squared radius 17/6. An independent
integer short row has nonzero entries at every one of the t new positions,
since its new restriction is proportional to the crossing restriction.
Its old projection cannot vanish: the old anchor is saturated, so one
could subtract an integer anchor combination and obtain a nonzero modular
relation supported on t<6 new positions, violating girth. The short cutoff
is less than q, ensuring this new restriction stays nonzero modulo q.
Thus its third squared projected height is at least t+3/4.

If there is no new norm-six line, rounding along the old two rows gives an
integer representative with squared norm less than eight whenever the
third height is less than 8-17/6=31/6. The rounded row is still balanced,
still has all new positions nonzero, and remains independent. Girth six
and parity of a balanced integer squared norm would then force norm six,
a contradiction. This proves the complete no-six third-height bound 31/6.

If a new norm-six line exists, it is unit on six positions, including all
t new ones. Its remaining 6-t old positions are arbitrary among ten. Each
such line, together with the saturated old anchor, has a unit three-row
minor (an old unit minor and a new unit coordinate). Hence it generates
the saturated rank-three plane and determines at most one coefficient
chart for the fixed old basis and new support. With x=<a,v>, y=<b,v>,
its Gram determinant is

    D=192-6*x^2+4*x*y-6*y^2,

and its third squared GS length is D/32. The existing H12/t2 counts are
reused unchanged. For H13/t3 there are binomial(10,3)*10=1200 candidates
per affine type. The standalone script checks all minors, then excludes
codes with girth below six by finding any plane through column pairs that
contains at least eight of the thirteen columns. All minors have magnitude
below seven, so these rank and vanishing tests agree over Q and F_3329.
The maximum count per determinant over the two affine types gives uniform
witness upper counts, not an assertion of exact distinct-code counts.

## Full kernels and extension factors

Let J_t(z) be the same full cutoff-24 modular Gaussian ball kernel as in the
rank-nine note, now on H=10+t positions and rank=7+t, with three relation
GS factors (6,16/3,z). In particular beta=(7+t)N/(2(10+t)R^2); neither
beta nor the modular normalization is copied unchanged from H12 to H13.
The checks 32*24^4<q^2 and (10+t)*24^2<q^2 hold. The tail
exp(-24^2*alpha/2)*theta(alpha/2)^3 and every periodic correction are kept.
Define, using the corresponding short-line counts n_(t,D),

    W_t=min(C_t*J_t(t+3/4),
            sum_D n_(t,D)*J_t(D/32) + C_t*J_t(31/6)).

For a component of size h and rank ten, let M be a uniform bound on the
number of ball candidates in an affine nine-dimensional slice. One may
use the coarse q^9 bound or the existing proved `completion_bound(s,9)`.
The complete D32 cover is

    binomial(h,10)*163800*M^(h-13) *
      [binomial(h-10,2)*(h-12)*mu*W_2
        +binomial(h-10,3)*W_3].

Here mu is the existing free independent point mean. The t2 term selects
its one extra independent point explicitly; t3 has none. Both terms leave
h-13 dependent points, hence the identical completion exponent. This
conservative cover omits any multiplicity division by the number of
possible independent extensions.

To compare with an actual complete selected envelope, remove D32 from the
rank-ten two-relation residual while retaining the existing D27 exclusion,
and add back **both** the existing rank-ten D27 cover and this whole D32
cover. Minimize that sum with the previous complete envelope. A local
improvement of J_3 alone would not justify a global improvement.

## Reproduction

Run `python3 docs/research/scripts/wall1_six_ten_rank_ten.py`.
It enumerates both H13 affine types, retains every tail, and compares
complete selected rank-ten/girth-six envelopes at sizes 18,19,20,24.
The log is `/tmp/wall1_six_ten_rank_ten.log`.


## Verified values and remaining scope

All 1200 candidates in each H13 affine type pass the girth test. The uniform
componentwise counts are
`{138:48,144:72,154:132,160:92,168:168,170:152,176:64,184:120,186:348,192:80}`.
Their sum may exceed 1200 because maxima are taken separately by determinant.

For h=18,19,20,24 the complete candidate improves the actually available
rank-ten/girth-six envelope with log10(new/old)=-5.80201222930701 to the
shown precision. At h=19 the parts relative to the old envelope have log10
values -5.80201223 (restricted residual), -47.01123645 (D27 addback),
-84.81272878 (D32 t2), and -85.95575184 (D32 t3). The revised bound is
therefore controlled by the residual after both exclusions, not an omitted
D32 branch. In these parameters `completion_bound(s,9)` selects q^9, so the
ball-slice variant gives no additional improvement; the coarse completion
cover yields the same conclusion.

These are stratum-envelope comparisons. The parent must independently
review the crossing argument and integrate both addbacks before using a
recomputed all-strata size-19 total. Nothing here closes selected-history
conditioning or a BKZ cost theorem.
