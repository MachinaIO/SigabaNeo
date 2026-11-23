# Complete extension cover for eleven-position determinant31 anchors

Use the projection certificate in wall1_eleven_d31_projection.md for a
balanced norm-four/eight anchor on eleven positions. Its augmented rank
is9. There are at most choose(11,4)*420=138600 anchor witnesses, since the
first support has four positions and the earlier exact check enumerates
all420 balanced partners for it. This is a witness upper bound; duplicate
plane representations need not be removed.

For t new positions, use the complete Poisson kernel with squared GS
lengths4,31/4,t+21/31. Its relation dimension is3, its augmented rank is
11+t-3, and the cutoff is24;31*24^4<3329^2. The complementary Gaussian
tail and all periodic-coordinate errors remain. For t=0 use the original
two-row kernel and cutoff40. The scalar Gaussian parameter is chosen for
the actual rank and total number of positions, as for the existing
rank-two anchor covers.

For t<=4, cover new norm-four relations by at most3 choose(11,4-t)
witnesses with the unrestricted kernel. For all remaining coefficient
choices use height max(t+21/31,49/16). This follows from nearest-plane
rounding and the absence of a new balanced norm-four row; girth four
also excludes norm2. Taking the minimum with the unrestricted complete
coefficient cover preserves every family. For t>4 no extra split is used.
Call this coefficient-weighted bound W(t,C), and call the unextended
anchor kernel J0.

For a support of size h and augmented rank r, multiply by
A=choose(h,11)*138600. When r=9, take the minimum of

    A J0 q^(8(h-11))

and the least-outside-point cover

    A W(1, sum_(a=3)^9 choose(9,a) q^(a-1)) q^(8(h-12)).

There is no factor for choosing the least outside point. Its old basis
coefficients cannot all vanish, and any nonzero vector on that independent
basis has nonzero projection modulo the anchor relation plane, supplying
the hypothesis of the projection lemma.

For r>9, the existing crossing-circuit construction uses t>=2 new points,
k=r-t-8 additional independent representatives, and coefficient bound
C=sum_(a=max(1,4-t))^9 choose(9,a) q^(t+a-2). Its contribution is

    A choose(h-11,t) choose(h-11-t,k)
      W(t,C) mu^k q^((r-1)(h-r-3))/(k+1).

The nonzero old part on the anchor basis again gives the required
nonzero old projection. Sum the t>=3 terms. For t=2 retain the minimum
of this crossing bound and the existing complete unmarked/marked
parallel-class covers, with anchor rank9. The cover is zero for r<9.
It is also zero for r=h-2: a proper anchor already has nullity2, so every
outside point would be a coloop, contradicting connectedness.

The implementation extends the existing seven/ten-position anchor
module with these eleven-position parameters. The new exclusion flag
removes only determinant31 entries at union11 in the two-relation
short-pair cover. The production path adds the COMPLETE new anchor cover
to that residual and to every previously required removed-anchor cover,
then takes the minimum with the previous full upper bound. Diagnostics
reconstruct the actually selected sum, including this added-back term.
No excluded-only result is used as a full probability bound.

This extends the paper-level counting and Poisson argument; it is not
new Lean formalization. The global residual target and the adaptive BKZ
selected-block distribution bridge remain separate open obligations.
