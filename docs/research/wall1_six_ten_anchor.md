# Rank-eight extension cover for two-six determinant32 anchors

After Part383, rank8/girth6 is led by two norm-six rows on ten positions,
sharing two coordinates and having inner product+/-2. Treat this as a
rank8 anchor, with all remaining points dependent on its span.

## Projection certificate

After signed coordinate changes, take a=(1,1,1,1,1,1,0,0,0,0) and
b=(1,1,0,0,0,0,1,1,1,1). Their Gram matrix is[[6,2],[2,6]] with determinant32.
For x=<a,z>,y=<b,z>, squared orthogonal projection has numerator

    32||Pz||^2 = 32||z||^2-6x^2+4xy-6y^2.

The squared GS lengths6,16/3 give nearest-plane squared radius17/6.
If an integer vector had positive projected squared length<3/4, subtracting
an integer combination of a,b would give squared norm<17/6+3/4=43/12<4.
All1161 integer vectors of squared norm<=3 have projection numerator0 or
at least24. A shared-coordinate unit vector attains24. This proves
projected squared minimum3/4 for ALL integer vectors, not only the search.

For affine balance, two representatives suffice: the two shared signs
agree, or they oppose. The script checks all780 balanced norm-six pairs
with first support fixed: each is a coordinate permutation of one of the
two balanced representatives, up to simultaneous row negation after
orienting their dot product positively. This map preserves balance for
extension rows. There are at most choose(10,6)*780=163800 anchor witnesses;
duplicate descriptions are deliberately retained as an upper bound.

## One dependent point

A least-labelled outside point yields a relation with a nonzero old part
on an independent eight-point basis, hence nonzero old projection. The
third squared GS height is at least1+3/4=7/4. A new balanced norm-six row
has unit support6 because girth six excludes its support-three shape.
For each affine anchor type there are10 choose(10,5)=2520 lines using the
new point. Their three-row determinant is

    D=192-6x^2+4xy-6y^2.

Compute all165 three-column minors and all462 six-column complements.
A unit minor always exists and all minor magnitudes are<7. Requiring each
complement to have rank3 excludes exactly the row spaces with a nonzero
relation supported on at most5 positions, over both Q and F_3329.
The componentwise upper counts across the two affine types are

    {120:162,138:80,144:216,168:132,170:90,
     176:176,184:212,186:354,192:112}.

These are witness bounds, not distinct-plane counts. Unit minors justify
third squared GS height D/32. Outside the new norm-six family, balance
and girth six force squared norm>=8. Rounding with radius17/6 therefore
gives height>=8-17/6=31/6.

Each complete kernel has first squared GS lengths6,16/3, then the specified
third height. For eleven positions the augmented rank is8, relation
dimension3, and cutoff24 satisfies32*24^4<3329^2. Every complementary tail
and periodic correction is retained. The unextended anchor uses dimension2
and cutoff40. With C=sum_(a=5)^8 choose(8,a) q^(a-1), minimize the
unrestricted C-weighted dependent kernel with the sum of the counted
norm-six kernels and the C-weighted height31/6 kernel. Call the result W.

The complete rank8 envelope at size h is choose(h,10)*163800 times

    min(J0*q^(7(h-10)), W*q^(7(h-11))).

The distinguished outside point is the least label, so no position-choice
factor is needed. Each subsequent point has at most q^7 affine-slice
choices. The production path removes determinant32 only from the c6,
union10 two-six cover, adds this entire envelope and the previously
required determinant27 anchor cover, and minimizes with the earlier full
bound. The new excluded residual is used ONLY at rank8, for sizes15..24;
other ranks retain their prior full bounds.

The checks cover1161 projected vectors,780 affine anchor maps and5040
balanced extension lines with exact minor/rank tests. This is paper-level
work with exact checks, not new Lean formalization or a completion of the
global residual target or adaptive BKZ distribution bridge.
