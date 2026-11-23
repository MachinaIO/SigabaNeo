# Projection minimum for the nine-position determinant44 anchor

The current selected size17/rank8/girth4 cover is dominated by the triangular
anchor's three-new norm-four extension. To retain that full configuration
when counting further relations, use its nine-position rank-six anchor.
This note establishes the geometry needed for that next extension; it does
not yet connect a new completion envelope to the production calculation.

Take the integer rows

    a=(1,1,-1,-1,0,0,0,0,0),
    b=(0,0,1,1,-1,-1,0,0,0),
    c=(1,0,0,0,0,0,1,-1,-1).

Their Gram matrix is G=[[4,-2,1],[-2,4,0],[1,0,4]], with determinant44
and adjugate [[16,8,-4],[8,15,-2],[-4,-2,12]]. Let P be their real span.
For integer v, put x=<a,v>, y=<b,v>, z=<c,v>. Then

    44 ||projection_(P perpendicular)(v)||^2
      =44||v||^2-16x^2-16xy+8xz-15y^2+4yz-12z^2.

The minimum positive projected squared length over all integer v is6/11.

Proof: the row lattice has squared Gram--Schmidt lengths4,3,11/3.
Nearest-plane rounding within P subtracts an integer combination of the
three rows and leaves the parallel component with squared length at most
(4+3+11/3)/4=8/3. If the nonzero perpendicular component had squared length
below6/11, the rounded integer vector would have squared norm below
8/3+6/11=106/33<4. Every integer vector of squared norm below four has
entries0,+1,-1 and at most three nonzero entries. Exhaustively evaluating
the displayed integer expression on all835 such vectors gives zero or a
value at least24. This contradicts a projected length below24/44=6/11.
The vector e_0 attains24/44, proving equality. This rounding argument is
the bridge from a finite calculation to every integer vector.

The certificate `scripts/wall1_d44_projection.py` also verifies all90 affine
triangular three-new norm-four witnesses. Choose a norm-four old row
containing the attached coordinate and another avoiding it, and orient
the rows to give inner products -2,1,0. Their signed projective column
multisets match the displayed canonical rows exactly. Thus a coordinate
permutation and coordinate sign changes carry every such plane to P.
These transformations preserve the integer lattice and Euclidean norm,
so the same projection minimum and rounding bound apply uniformly.

For a further crossing on t new positions, a nonzero old projection would
therefore contribute at least6/11, giving a candidate fourth squared height
t+6/11. Families excluding further norm-four or norm-six rows can instead
use the rounding bounds6-8/3=10/3 or8-8/3=16/3. Connecting these bounds
still requires the modular lifting, fourth-relation tails, a complete
coefficient cover and its complementary-family accounting. A prospective
cutoff20 satisfies44*20^4<3329^2, but that inequality alone does not prove
the full extension bound. No new numerical residual improvement or Lean
formalization is claimed in this note.

The subsequent connection, including the complementary-family cover, is
recorded in `wall1_d44_extension.md`. The geometric certificate above is
unchanged.
