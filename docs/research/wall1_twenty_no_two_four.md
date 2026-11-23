# Conditional D20 one-point cover after two-four addbacks

This refines the rank-six/girth-four D20-eight-position addback. It requires
that the complete global cover already includes all six-position triangular
and orthogonal two-four anchors, and all seven-position shared two-four
anchors. The existing triangle plus other-two-four addbacks provide that
union, even when the latter is conditioned on absence of triangular anchors.

## Containment and retained count

Use either of the two existing balanced D20 anchor representatives, extended
by a zero coordinate:

    a=(1,1,-1,-1,0,0,0,0,0),
    b=(1,1,0,0,1,-1,-1,-1,0), or
    b=(1,0,-1,0,1,1,-1,-1,0).

Let v be a balanced norm-four row with nonzero ninth coordinate, in a
girth-four rank-three extension. All such rows are four signs with sum zero,
so the script enumerates them completely. Write x=<a,v>, y=<b,v>. Their
Gram determinant is D=80-6x^2+4xy-4y^2. Existing girth filtering and unit-minor
checks are repeated without modification.

If the supports of a and v intersect, the girth filter forces intersection
one or two. Intersection one gives a seven-position shared two-four anchor.
Intersection two gives a six-position orthogonal or triangular two-four
anchor, according as x=0 or |x|=2. All these complete codes are absent once
we condition on absence of the previously covered two-four events. These
claims are verified for all eligible rows of both anchor types, with no
floating-point calculation.

Otherwise v has three old nonzero entries inside the four coordinates
exclusive to b, so x=0 and |y| is one or three. If |y|=3 then D=44 and
w=b-sign(y)*v is a balanced norm-four row. Also <a,w>=2 and its support
union with a has size six. Thus it too gives a triangular anchor and is
excluded. The only possible retained determinant is D=76, from |y|=1.

For the first anchor type the b-only signs are (+,-,-,-); for the second
there are two plus and two minus signs. Choose the three old support
coordinates of v, then its balanced signs up to global sign. There are
three choices per triple. In the first type, the triple of three minus
coordinates contributes three |y|=1 lines, while each of the other three
triples contributes two: total nine. In the second type each of four triples
contributes two: total eight. Therefore nine is a uniform upper count.
Counting witnesses instead of deduplicated codes is harmless for this bound.

All enumerated rank-three lattices have a unit minor, proving saturation
in their rational span. The triangular/orthogonal/shared subanchors use
unit-minor pairs as in their existing classifications. The same minor and
support tests are valid at q=3329, since all minors have absolute value below
seven. No new lattice approximation or tail truncation is introduced.

## Valid integration

For an explicitly restricted D20 family excluding the previously covered
two-four events, replace only the t=1 rare coefficient sum

    sum_D UPPER_COUNTS[D]*code_bound(s,1,one_point_determinant=D)

by

    9*code_bound(s,1,one_point_determinant=76).

Keep the coefficient-weighted `no_new_norm_four` term and the minimum with
the original unsplit bound. Keep the same-rank minimum and every completion
factor. All retained code bounds include their original cutoff tail and
periodic terms. Other t branches may retain their old overestimates.

This is conditional: do not make the replacement in an unconditional D20
caller. The triangle and other-two-four addbacks must remain in the global
cover. Their union covers every deleted event, so no additional addback is
needed beyond those existing terms. Removing a code means removing its
entire event here, including its tail; it does not mean dropping tail terms
from any retained code.

## Verification and numerical diagnostic

Run `python docs/research/scripts/wall1_twenty_no_two_four.py`.
It certifies both representative types, all girth filters and saturation,
prints retained counts 9 and 8, and compares the actual rank-six size-17
same-rank and one-point candidates. Its log is
`/tmp/wall1_twenty_no_two_four.log`.

Only this new script and note were created; the production evaluator was
not modified. The global full-cover improvement requires integration and
reevaluation, and is not inferred merely from the local replacement.

The verified size-17 rank-six weighted log10 values are:

| Candidate/component | log10 upper bound |
|---|---:|
| original same-rank candidate | 14.7454542282098 |
| original selected one-point candidate | -10.9829902734304 |
| its D44 rare contribution | -10.9829902734304 |
| conditional D76 rare contribution | -72.5842812277450 |
| unchanged no-new-four contribution | -67.1837600008223 |
| conditional selected candidate | -67.1837582739421 |

Thus the original D20 addback is genuinely masked by the covered D44 event,
and after the conditional replacement the unchanged no-new-four term becomes
the local bottleneck. These are bounds for the conditional D20 component;
prior triangle/other addbacks remain indispensable in the full result.
