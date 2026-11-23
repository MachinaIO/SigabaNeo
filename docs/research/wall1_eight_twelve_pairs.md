# Short-pair cover for twelve-position girth-eight planes

After Part371 the leading size17 stratum is rank10/girth8. Its two-relation
sum is led by t4/overlap7, on twelve positions. The preceding kernel uses
the general squared GS lower bounds(8,6).

Every balanced integer row of squared norm8 or10 and support at least8
is unit. Indeed a coefficient of absolute value at least2 leaves at most
four or six further unit entries respectively, giving support at most5
or7; two coefficients of absolute value2 give still smaller support.
Balance gives equally many positive and negative entries in the unit case.

For two independent unit rows spanning a plane with full support12,
each projective column-direction group has size at most4, since cancelling
it yields a nonzero row and girth is at least8. If their squared norms are
8 and10, they share6 positions. The equal-sign and opposite-sign groups
have sizes(6+dot)/2 and(6-dot)/2, so |dot|<=2. For squared norms10 and10,
they share8 positions and the same argument forces dot=0.

For squared norms8 and8, retain the general complete kernel(8,6), but
count the exceptional planes by their short witnesses. There are
L=35 choose(12,8)=17325 balanced unit norm-eight lines up to sign, so at
most choose(L,2)=150069150 unordered pair witnesses. Independent pairs
remain independent modulo3329: a nonzero integer minor has absolute
value at most2. A pair specifies at most one normalized coefficient chart
for the prescribed supports. The count deliberately includes ineligible
supports and multiple witnesses for one plane; it is an upper bound.

Outside this exceptional family, a reduced first row of norm squared8
has second norm squared at least10. If it is10, the inner-product bound
gives second GS squared length>=19/2. If it is>=12, Gauss reduction gives
at least12-4^2/8=10. A reduced first row of norm squared10 has height>=10
when the second also has norm squared10, and at least12-5^2/10=19/2
otherwise. A first norm squared>=12 uses the general bounds(12,9).
Thus the complete cover is

    min(1,choose(L,2)/Q) K(8,6)^N
      + K(8,19/2)^N + K(10,19/2)^N + K(12,9)^N.

Here Q is the existing coefficient count. Every K retains the original
cutoff14 tail and periodic corrections. The implementation takes the
minimum with the preceding complete bound. No coefficient class is dropped.

The exact script checks representative first rows against all balanced
second rows: 2450 eligible(8,8),2688 eligible(8,10),1500 eligible(10,10)
pairs, and all17325 norm-eight lines. Coordinate permutations and global
sign account for every possible first unit row. The geometric argument
supplies the coverage beyond these finite checks. The result is not yet
Lean formalized and does not prove the full size17..24 residual or the
adaptive BKZ distribution bridge.
