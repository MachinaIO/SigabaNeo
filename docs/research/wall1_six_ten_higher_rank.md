# Complete D32 crossing covers at ranks eleven and twelve

The rank-ten fundamental-circuit argument extends to ranks r=11 and r=12
provided all crossing sizes t=2,...,r-7 are included. This note and its
standalone script leave production unchanged. In particular, the method
here is explicitly restricted to t<=5 and is not asserted for higher ranks.

Fix a connected girth-six component containing the ten-position rank-eight
D32 anchor. Extend a deterministic eight-position anchor basis to a basis
of the component by r-8 new positions. Connectivity of the fundamental
circuit graph forces a nonbasis vertex whose circuit meets both the old
basis and the new basis. If it uses k new basis elements, it supplies
k+1=t new positions including the vertex itself. Thus 2<=t<=r-7.
The crossing has a old coefficients with 6-t<=a<=8. Normalize one new
coefficient and impose the affine balance equation. The same chart upper
count is

    C_t=sum_(a=6-t)^8 binomial(8,a)*q^(t+a-2).

The anchor plus crossing has H=10+t positions and rank 7+t. Extend it to
rank r with extra=r-7-t independent points. This exposes H+extra=r+3
positions, leaving h-r-3 dependent positions. Union over all such witnesses
is complete; no division by a witness multiplicity is used. One can make
the underlying event cases disjoint by selecting the first available t and
then a deterministic witness, but the bounds deliberately overcount choices.

## Third-height and short-line certificates

The old plane is saturated, with integer projected minimum 3/4 and
nearest-plane squared radius 17/6. Every new independent short relation
has all t new coordinates nonzero. If its old projection vanished,
saturation would allow subtraction of an integer old-plane vector,
leaving a nonzero relation supported on t positions. Because t<=5 and
girth is six, this is impossible. The short-cutoff coefficients have
magnitude below q, so the new relation remains nonzero modulo q.
Therefore its third squared projected height is at least t+3/4.

In the absence of a new norm-six line, nearest-plane rounding gives the
additional height bound 31/6, as in the rank-ten proof. Thus the no-six
complement may use max(t+3/4,31/6). For t=5 this is 23/4, rather than the
weaker 31/6; the generic bound is always retained in a complete minimum.

A new norm-six line has six unit entries, including all t new entries and
6-t old entries. Its number of candidate lines per affine anchor type is
binomial(10,6-t)*10: 450 for t=4 and 100 for t=5. The script checks both
balance-preserving old affine types. The two old rows and this row have a
unit minor, hence define a saturated integer rank-three plane. All minors
have magnitude below seven. Girth at least six is checked by excluding
any plane containing at least H-5 columns, using normals to independent
column pairs; these tests have identical ranks over Q and F_3329.
For each retained row,

    D=192-6*x^2+4*x*y-6*y^2,
    x=<a,v>, y=<b,v>,

and the third squared GS height is D/32. Taking the maximum count at each
determinant over the two affine types gives uniform witness upper counts.
Such a row determines at most one coefficient chart for each fixed old
basis and new support. The existing t2 and t3 counts are reused unchanged.

For t>=6 a relation supported entirely on the new positions can obey girth
six. The proof that the old projection is nonzero then fails. Neither the
height t+3/4 nor this complete higher-rank cover is claimed in that regime.

## Complete bound and selected-envelope comparison

Let J_t(z) be the full rank-three relation kernel on H=10+t positions,
rank=7+t, with squared GS heights (6,16/3,z). Its beta is
(7+t)N/(2(10+t)R^2). Use cutoff24 and retain the entire long-vector theta
tail and all periodic corrections. The unchanged lifting inequalities
32*24^4<q^2 and H*24^2<q^2 hold through H=15. Define

    W_t=min(C_t J_t(t+3/4),
       sum_D count_(t,D) J_t(D/32)
          + C_t J_t(max(t+3/4,31/6))).

With M_(r-1) the existing uniform affine-slice candidate count, a complete
D32 cover is

    binomial(h,10)*163800*M_(r-1)^(h-r-3) *
      sum_(t=2)^(r-7) binomial(h-10,t)
        *binomial(h-10-t,r-7-t)*mu^(r-7-t)*W_t.

The script compares `no32 residual + D27 addback + full D32 cover` with the
previous complete minimum of the unrestricted envelope and the
`no27 residual + D27 addback` envelope. Every t contribution is displayed,
so an improvement is not inferred from an unused internal kernel.

Reproduce with
`python3 docs/research/scripts/wall1_six_ten_higher_rank.py`.
The log is `/tmp/wall1_six_ten_higher_rank.log`.


## Results

All 450 t4 candidates in each affine type pass the checks; the componentwise
upper counts are `{160:6,168:64,170:88,176:84,184:80,186:80,192:66}`.
Both t5 affine types retain all 100 candidates, with counts
`{184:20,186:80}`. These are 1100 exact witness checks in total.

For h=18,19,20,24, the complete rank-eleven/girth-six candidate has
log10(new/old)=-5.71179279529848 to the displayed precision. At rank twelve
the ratio has log10 approximately -6.99893119587e-8: essentially no useful
improvement because the previous selected envelope is already controlled
by another residual family. The new D32 cover is complete in both ranks;
its usefulness must be assessed against the actual outer minimum.

`envelopes(s)` returns `(bounds_by_(h,r), terms_by_(h,r,t))` and uses the
stored exact counts without repeating their enumeration. Parent integration
must retain the D27 addback and recompute the all-strata bounds. No global
failure probability or adaptive-history conclusion follows from these
stratum ratios alone.
