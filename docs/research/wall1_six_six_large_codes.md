# Prescribed norm-six pairs on ten and eleven positions

The size17 rank9/girth6 diagnostic is led by c=6,t=5, especially overlap5.
Refine the two-norm-six family on ten and eleven positions.

At girth six every norm-six row has six unit entries. If two such rows
have union H=10 or11, their exclusive groups each have size H-6 (four
or five) and their overlap has size12-H (two or one). The only projective
column groups large enough to yield a six-support row are the two exclusive
groups. Therefore the prescribed first six-circuit must be one of the
two norm-six lines. Fix its support and enumerate its ten balanced signs.
The independent row is nonzero on all H-6 new coordinates.

For H=10 the dot product is0 or+/-2 and determinant36 or32. For H=11
it is+/-1 and determinant35. Exclusive-coordinate minors are units,
so the exact second squared heights are D/6. The exclusive group sizes
also show girth at least six; no other short-support family is assumed away.

Normalize the first balanced line, eliminate its first coordinate from
the second row, and normalize at the first new coordinate. For each
prescribed old overlap, test the scalars that cancel an old coordinate
and deduplicate the resulting plane keys. Exact counts are:

    H=10:
      overlap2: determinant32:52, determinant36:48
      overlap3: none
      overlap4: determinant32:52
      overlap5: determinant36:240
    H=11:
      overlap1: determinant35:100
      overlap2,3,4: none
      overlap5: determinant35:100

Counts and primitive minors are checked at q=7,17,3329; the bound uses
q=3329. Permutations cover other choices of the prescribed positions.
Replace the broad two-six count by the sum of these complete weighted
D/6 kernels, retaining every cutoff36 tail and periodic layer. All
one-six, no-six and other-support terms remain unchanged. The minimum
with the previous complete envelope is retained. This is not a Lean
formalization or a complete adaptive BKZ proof.

The two-six refinement alone has negligible aggregate effect: size17
weighted log10 remains3.7239228142. We next refine the one-six family;
this by itself does not establish that it is the dominant loss.
On eleven positions, an independent norm-eight row at girth six must
have eight unit entries (the other shape has support five). With the
norm-six row it has three shared positions, three first-exclusive and
five second-exclusive positions. Only the five-column group can be
cancelled to give support six, so the prescribed first six-circuit is
the norm-six row itself. Dot products are +/-1 or+/-3, giving determinants
47 or39. Unit exclusive minors again establish primitivity.

The same prescribed-support enumeration, including deduplication of
alternate norm-eight rows in one plane, gives:

    overlap1,2: none
    overlap3: determinant39:95, determinant47:255
    overlap4: determinant47:340
    overlap5: determinant47:850.

These counts and unit minors pass at q=7,17,3329. For all remaining
one-six planes the second squared minimum is at least ten; Gauss
reduction gives second squared height>=10-9/6=17/2. Replace the one-six
term by the sum of the exact39/6 and47/6 kernels plus the full old
one-six coefficient count times the17/2 kernel, taking the minimum with
the old bound. Every tail and periodic layer remains. Two-six and
no-six cases remain separately covered.

The one-six refinement also has negligible effect on the total, which
remains at weighted log10 about3.7239217501. Therefore a further refinement
targets the no-six family. At girth six a norm-eight row must have eight
unit entries, since the alternative has support five. Two such rows on
H positions share16-H positions; their larger shared sign class has size
(16-H+|dot|)/2. Cancelling it must leave at least six positions. For H<=9
this is impossible. At H=10 it forces |dot|<=2, and at H=11 odd parity
together with Gauss reduction forces |dot|<=3.

Accordingly, if the first squared minimum is eight, the second squared
height is at least8 for H<=9 (the second minimum is then>=10),15/2 for
H=10, and55/8 for H=11. If the first minimum is>=10, use heights10,15/2.
Add these two complete kernels to cover the cases, taking the minimum
with the old no-six bound. For girth five only the H=11 improvement is
used: a support-five norm-eight row paired with a unit row then shares
only two positions, giving |dot|<=3 as well. This is the previously
verified mixed-shape argument. All cutoff14 tails, periodic layers and
coefficient counts remain. The norm-eight pair regression now checks
the girth-six implications explicitly.

The final complete probe passes2106 cumulant regressions. Transfer through
sixteen stays below3.459e-13 (about3.45843794473e-13). Size17's weighted
residual log10 is2.8696922990; rank9/girth6 leaves the five largest strata,
and rank8/girth3 now leads at2.5550235891. Through24 remains about1.05489e232.
The remaining2.6629e-12 allocation and adaptive BKZ bridge remain unproved.
Logs: `/tmp/wall1_girth_six_no_six.log` and
`/tmp/wall1_girth_six_no_six_cumulants.log`. These are upper envelopes,
not actual failure-probability estimates.
