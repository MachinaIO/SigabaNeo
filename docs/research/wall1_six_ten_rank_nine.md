# Rank-nine crossing cover for the ten-position determinant32 anchor

The existing rank-eight anchor has ten positions, two norm-six rows with
Gram determinant32, and at most163800 labelled witnesses per fixed support.
Its two balance-preserving representatives and projected minimum3/4 are
proved in `wall1_six_ten_anchor.md` and `wall1_six_ten_projection.py`.
This note extends the complete cover to whole-support rank nine only.

## The crossing pair

Contract an independent eight-point basis of the anchor. A connected support
of rank nine has quotient rank one. A crossing fundamental circuit may
therefore be chosen with two new points and a nonzero old part. The same
crossing argument used by the existing general anchor covers bounds the
number of normalized coefficient choices by

    C = sum_(a=4)^8 binomial(8,a) q^a.

Girth six requires at least four old positions in the circuit. A nonzero
old part supported on the independent anchor basis has nonzero projection
off the old relation plane. Thus the third squared GS height is at least
2+3/4=11/4. The old plane has nearest-plane squared radius17/6. In the
absence of new norm-six lines, rounding gives third height at least
8-17/6=31/6. Girth six excludes balanced norms below six, and balanced norms
are even. The two new coordinates stay nonzero when rounding old rows.

## Short-line enumeration

A new balanced norm-six row is unit on six positions, including the two
new points and four old points: binomial(10,4)*10=2100 lines per old affine
type. The shape (2,-1,-1) is excluded by girth six. For x=<a,v>,y=<b,v>,

    D = 192-6x^2+4xy-6y^2.

All three-row minors have magnitude below7, and a unit minor exists. Hence
the basis is saturated, and rank tests over Q agree with rank tests over
F_3329 for every column subset. Girth at least six is equivalent to no
nonzero coefficient row vanishing on seven or more of the twelve columns.
Enumerate planes through pairs of independent columns and count their
contained columns. This is exhaustive: a vanishing set of rank two contains
such a pair; a set of rank one can be extended by a column outside its line,
since the whole matrix has rank three. Thus no exceptional low-rank set is
missed. Each type retains1908 lines.

Componentwise upper counts over the two affine types are

    {120:72,128:54,138:288,144:96,154:128,160:52,
     168:196,170:264,176:172,184:172,186:408,192:132}.

These are uniform witness upper counts, not a claim of an exact plane count.
Every retained line fixes at most one crossing coefficient chart for a fixed
independent anchor basis. The exact third squared GS height is D/32.

## Complete cover

Let J(z) be the rank-three complete modular Gaussian ball bound on twelve
positions, rank nine, squared GS lengths (6,16/3,z), and cutoff24. The check
32*24^4<3329^2 supports the unchanged short-plane lifting; every complementary
tail and periodic term is retained. Write

    W = min(C J(11/4), sum_D count[D] J(D/32) + C J(31/6)).

For h labelled points the complete crossing cover is

    binomial(h,10)*163800*binomial(h-10,2)*W*q^(8(h-12)).

There are no additional independent points (rank nine is already reached);
each remaining point has at most q^8 affine-slice choices. This intentionally
keeps crossing-witness multiplicities as overcounts.

Production applies this only at rank nine. It removes the D32/H10 two-six
family from the two-relation cover, adds this entire cover and the existing
D27/H9 cover required by the same restricted residual, and minimizes with the
previous complete bound. Rank eight retains its previous one-point cover;
all other ranks retain their old coverage. This is not a completed global
probability estimate or a Lean formalization.

Run `python3 docs/research/scripts/wall1_six_ten_rank_nine.py` for the4200
exact short-line, minor and girth checks.
