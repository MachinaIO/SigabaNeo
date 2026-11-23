# Four-pair anchor: projection minimum and balanced patterns

The rank5 triangular residual after Part380 is dominated by determinant32
extensions, whose relation equations become four equal signed pair sums.
The other two-new-point determinant kernels are more than seven decimal
orders smaller. The next proposed cover treats the eight-point, rank5
four-pair configuration as an anchor and retains a further dependent point.
This note proves its geometric and combinatorial prerequisites only.

For the canonical unsigned pair sums, take rows

    a=(1,1,-1,-1,0,0,0,0),
    b=(0,0,1,1,-1,-1,0,0),
    c=(0,0,0,0,1,1,-1,-1).

Their Gram determinant is32, their squared GS lengths are4,3,8/3, and
the adjugate is [[12,8,4],[8,16,8],[4,8,12]]. Let P be projection onto
the orthogonal complement of their span. That complement is the orthogonal
direct sum of the four within-pair difference directions and the all-ones
direction. Consequently, for EVERY real vector z,

    ||Pz||^2 = (1/2) sum_(i=0)^3 (z_(2i)-z_(2i+1))^2
                           + (1/8)(sum_(j=0)^7 z_j)^2.

For integer z, a nonzero pair difference gives squared projection at least
1/2. If all differences vanish, the total sum is even; a nonzero projection
then again has squared length at least1/2. The vector(1,1,0,0,0,0,0,0)
attains1/2. This proves the minimum over all integer vectors directly.

For later norm exclusion, nearest-plane rounding in the three-row anchor
has squared radius(4+3+8/3)/4=29/12. As an independent finite certificate,
a hypothetical smaller projected length rounds to squared norm less than
29/12+1/2=35/12<3. All129 integer vectors of squared norm<=2 are checked
using the adjugate and the direct projection identity. For a crossing
relation on t new positions, nonzero old projection therefore gives
height>=t+1/2. If new norm-four relations are covered separately, affine
balance and girth four give height>=6-29/12=43/12 after rounding. The
crossing construction must supply the nonzero old-projection premise.

There are105 pairings of eight labelled positions. For each pairing write
the relations as equality of four signed pair sums. Affine balance requires
the sum of the two signs in every pair to be equal. If this common sum is
+/-2, all signs agree, giving one row space up to global sign. If it is0,
each pair has opposite signs, giving2^4/2=8 row spaces. Thus there are
nine balanced patterns per pairing and945 in total. Their projective column
groups identify the pairing, so different pairings cannot yield the same
code. Within one pairing, equality of signed pair sums identifies the
relative orientations up to a common sign. Exact row-space enumeration
also checks945 distinct patterns at both q=7 and q=3329.

Every three of the four projective directions have a unit minor. Coordinate
sign changes preserve Euclidean geometry and therefore transfer the
projection bound to every pattern. They are NOT used to transport affine
balance; the nine-pattern count treats that constraint explicitly. The
cutoff arithmetic32*24^4<3329^2 is checked for the proposed extension
kernel, but no full lifting/counting cover is claimed from that inequality
alone.

No determinant32 family is removed from the current production bound yet.
The next step must connect a complete dependent/crossing extension cover
and add it back before using any restricted triangular residual. Current
numerical bounds remain those of Part380. No new Lean formalization or
complete BKZ proof is claimed.
