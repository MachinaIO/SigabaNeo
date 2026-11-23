# Girth-filtered dependent extensions of triangular anchors

Part323 leaves the rank4/girth4 triangular same-rank term among the
largest size16 contributions. Retain one dependent point and refine
Part321's additional norm-four branch by imposing girth four.

Fix the old four-supports {0,1,2,3} and {2,3,4,5}. Enumerate all balanced
norm-four rows a,b on them with |<a,b>|=2. These are precisely the five
signed triangular patterns used by the existing anchor cover. Every
triangular anchor is obtained from one by a coordinate permutation and
row signs. The enumeration therefore preserves the affine condition;
individual coordinate sign changes are not used to identify the cases.

For each pattern enumerate all60 balanced norm-four lines v nonzero on
the new seventh coordinate. Put d=<a,b>, x=<a,v>, y=<b,v>. The three-row
Gram determinant is

    D=48-4x^2+2dxy-4y^2.

Test all35 complementary four-column supports for rank three. A failed
test is equivalent to a nonzero codeword of support at most three, so
is incompatible with girth four. All three-column minors have absolute
value below seven, making the rank test identical over Q and every
prime field q>=7. A unit minor exists in each candidate, proving that
its rows generate the full integer lattice of their real plane.

The equal-pair-sum pattern has24 surviving witnesses, all with D=32.
Each of the four oriented-difference patterns has18 witnesses with D=32
and6 with D=48. Use the uniform upper counts24 and6 for all five patterns.
Their sum30 is a deliberate per-stratum overcount; each pattern has24
actual survivors. No division by code multiplicity is used.

The old squared Gram--Schmidt lengths are4 and3. The primitive third
row gives third squared height D/12, hence at least8/3 for all survivors.
Replace the exceptional term60*J_generic by24*J_32+6*J_48. Each J_D keeps
the full long tail and periodic corrections. Keep the nonexceptional
coefficient bound times J_no4 unchanged, and take the minimum with the
former unpartitioned cover. Only the one-point dependent branch changes;
the crossing and marked-pair terms retain the existing safe cover.

The exact regression covers300 lines and35 complementary supports per
line, all unit-minor assertions and the multiplicities of the five
patterns. This counting step is connected to the full triangular
component envelope. It is not Lean formalized and does not itself
establish the complete residual budget or adaptive BKZ history law.

## Verified outcome

The classification and full cumulant probe pass, including2106 exact
transfer and connected-support checks. Transfer through fifteen is
below3.419e-13. With the reference/error cap9.131e-13, a sufficient
remaining condition is now

    sum_(h=16)^24 L_h^* U_h + Pr(max_(i=15)^404 b_i>.280) <= 2.6669e-12.

The allocation totals3.9219e-12<3.922e-12. This remaining condition is
unproved. The size16 triangular part has weighted log10 -14.40256,
while the complete residual is -3.40933, dominated by rank8/girth4 at
-3.41793. Thus controlling the triangular family alone is insufficient.
The through24 envelope remains about3.34e232 and selected-history
estimates are still open. No complete draw14 exit or BKZ theorem follows.
