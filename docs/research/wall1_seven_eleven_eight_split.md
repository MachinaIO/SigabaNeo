# Rare norm-eight pairs on eleven positions at girth seven

After Part373, the largest size17 stratum is rank9/girth7. The two-relation
candidate is selected, with t4/overlap6 dominating its sum. This has eleven
positions. The preceding short-pair GS bound is(8,55/8).

A balanced norm-eight row of support at least seven must be unit on eight
positions: non-unit norm-eight shapes have support at most five. Thus
there are L=35 choose(11,8)=5775 possible lines up to sign. Two independent
lines determine at most one normalized coefficient chart for the fixed
prescribed supports. They remain independent modulo3329, since some
nonzero integer two-by-two minor has absolute value at most2. Therefore
at most choose(L,2)=16672425 pair witnesses cover every plane whose first
two squared minima are8. This overcounts ineligible supports and multiple
witnesses per plane; it is not an exact plane count.

For completeness, unit norm-eight rows covering eleven positions share
five positions. Girth seven bounds every projective column-direction
group by4, so their shared sign groups(5+dot)/2,(5-dot)/2 imply |dot|<=3.
This recovers the existing second squared GS lower bound55/8. In fact
exact girth seven forces |dot|=3, because the two exclusive groups both
have size3 and at least one group must have size4.

Outside the two-norm-eight family, a first squared minimum8 has second
squared norm at least10; Gauss reduction gives height>=10-4^2/8=8. A first
squared minimum at least10 uses the general bounds(10,15/2). Consequently
use the complete cover

    min(1,choose(L,2)/Q) K(8,55/8)^N + K(8,8)^N + K(10,15/2)^N,

minimized with the preceding complete kernel. All cutoff14 tails and
periodic terms are retained inside each K. No saturation claim for the
short pair is needed: the old complete short-pair kernel already bounds
its plane, and the pair is used only to count coefficient charts.

The exact script verifies all5775 short lines and624 full-support reduced
partners of a representative first row with exact girth seven. Every
first row is a coordinate permutation and sign change of the representative.
These checks support the counting and geometric arguments above. This is
not new Lean formalization and does not close the size17..24 remainder
or the adaptive BKZ distribution bridge.
