# Integer projection certificate for the eleven-position determinant31 anchor

The rank9/girth4 residual after Part377 is led by t7/overlaps1 and3.
Before removing this determinant31 family from any two-relation cover,
a complete replacement must bound its extensions. This note proves the
projection lemma needed for that construction; it does not remove any
family or change the numerical residual bound.

Let U be the span in R^11 of

    a=(1,1,1,1,0,0,0,0,0,0,0),
    b=(1,0,0,0,1,1,1,1,1,1,1),

and let P be orthogonal projection onto U-perp. Then

    min { ||Pz||^2 : z in Z^11, Pz != 0 } = 21/31.

Indeed the Gram matrix is [[4,1],[1,8]], with determinant31 and inverse
(1/31)[[8,-1],[-1,4]]. Writing x=<a,z>, y=<b,z>, one obtains

    31 ||Pz||^2 = 31 ||z||^2 - 8x^2 + 2xy - 4y^2.

For the coordinate vector e0 this expression is21, so the asserted value
is attained. To prove the lower bound over ALL integer vectors, not just
a bounded search, use nearest-plane rounding in the lattice Za+Zb. Its
squared GS lengths are4 and31/4. Subtracting an integer combination of
a,b leaves a vector z' with the same projection and with squared parallel
component at most (4+31/4)/4=47/16.

If 0<||Pz||^2<21/31, then

    ||z'||^2 < 47/16+21/31 = 1793/496 < 4.

Thus z' has integer squared norm at most3, and every coordinate is0,+1,-1.
There are exactly sum_(k=0)^3 choose(11,k)2^k=1563 such vectors. Exact
integer evaluation of the displayed quadratic form gives nonnegative
values throughout, with minimum positive value21, a contradiction.
This proves the lower bound for arbitrary integer z.

The actual balanced norm-four/eight witnesses on eleven positions are
signed coordinate permutations of this canonical plane. Their supports
share one position; orient the second row to agree there, then flip each
coordinate sign to make every nonzero entry positive. The column types
are one(1,1), three(1,0), seven(0,1). The script checks all420 balanced
witnesses and constructs this isometry explicitly. Signs are used only
for the Euclidean projection statement, not to assert preservation of
affine balance in a coefficient enumeration.

For a further integer relation with t new nonzero coordinates and a
nonzero old projection modulo U, its squared projected height is at
least t+21/31. The nonzero-old-projection premise must be established by
the crossing/extension construction; it is not automatic for every row.
For balanced relations in the original coordinates, subtracting the
balanced anchor rows preserves balance. If all new norm-four relations
are excluded and the rounded relation remains outside the anchor plane,
its squared norm is at least6 (girth four excludes norm2). The same
rounding argument then gives height at least6-47/16=49/16. These bounds
are ingredients for a future complete extension cover, with the removed
norm-four exceptions explicitly added back.

For the planned Poisson cutoff,31*24^4<3329^2 is checked exactly. This
arithmetic check alone is not a proof of the entire lifting or probability
argument. The current contribution is the projection lemma and its shape
coverage; no full extension cover is yet connected, no additional class
is excluded, and no new Lean formalization is claimed.
