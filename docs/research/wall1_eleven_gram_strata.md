# Eleven-position norm-four/eight planes

Consider the one-norm-four family with a prescribed first four-circuit C
and seven new positions. The unique norm-four line must be supported on C:
every independent codeword is nonzero on all seven new positions. An
independent short affine row cannot have squared norm six. At squared
norm eight it must have seven new unit entries and one old unit entry.
The other norm-eight integer shape has support five and is impossible.

Fix the old singleton j. There are three balanced first four-lines and
35 balanced second eight-lines up to sign. Their dot product is plus/minus
one, so their Gram determinant is31 and the second squared height is31/4.
An old-exclusive coordinate and a new coordinate give a unit minor;
therefore the pair generates the primitive integer plane.

In a combination of the two rows, the old support is either the singleton
j (zero coefficient on the first row), its three-position complement
(the coefficient that cancels j), or all four positions. Thus a prescribed
proper overlap of size one or three fixes j and admits exactly105 planes;
an overlap of size two admits none. These are planes, not multiplicities:
the first norm-four line is unique, and adding a nonzero multiple of it
cannot preserve the singleton old support of the norm-eight row.

The exact modular enumeration normalizes the first line, eliminates its
first coordinate from the second row, and deduplicates. It checks the
counts at q=7,17,3329. The production code uses105 complete determinant31
kernels for overlaps one and three, none for overlap two, plus the full
previous coefficient count at second squared height9. All cutoff tails
and periodic layers are retained. Two-four and no-four families are
unchanged, and the minimum with the previous bound is taken.

The first full probe shows this count refinement alone has negligible
impact: size17 weighted log10 changes from6.5674552429 to6.5674551925.
This rules out the rare one-four count as the main source of loss in the
current c=4,t=7 term. Logs: `/tmp/wall1_eleven_exact.log` and
`/tmp/wall1_eleven_exact_cumulants.log`.

## The no-four/no-six family

For the same eleven-position union, consider a Gauss-reduced integer
basis whose minimum squared length is at least eight. A norm-eight affine
row is either balanced on eight unit positions or, up to sign and
permutation, (2,1,-1,-1,-1), on five positions. If two norm-eight rows
cover all eleven positions, they cannot both have support five.

If both have support eight, their overlap is five, so their dot product
is odd. Gauss reduction bounds its absolute value by four, hence by
three. If one has support five, the overlap is two; the absolute dot
product is at most2+1=3. Thus in both cases the second squared height is
at least55/8. If the first minimum is eight and the second at least ten,
the second height is at least8, which is stronger. If the first minimum
is at least ten, use heights10 and15/2.

Replace only the no-four/no-six term by the smaller of its old bound and
the sum of the Nth powers of complete kernels with heights(8,55/8) and
(10,15/2). Retain the original cutoff14 tail and periodic layers in each
kernel. The norm-six families and all coefficient counts are unchanged.
The proof applies to both c=3 and c=4 when the union has eleven positions.

The regression checks2718 reduced full-support partners for representatives
of both norm-eight shapes, in addition to the earlier girth-seven/eight
checks. Coordinate permutations and global sign cover the other first
rows; no affine type is silently omitted.

These are component estimates, not a completed BKZ theorem, and have not
been formalized in Lean.

The combined interval probe passes all2106 exact cumulant regressions;
through sixteen is about8.78532709126e-13, below9.583e-13. Size17's weighted
residual log10 is6.5613125771, still led by rank9/girth4 at6.2768767598.
Through24 remains about1.61354e232. Logs:
`/tmp/wall1_eleven_no_six.log` and
`/tmp/wall1_eleven_no_six_cumulants.log`.

Neither refinement materially closes the residual gap. Raw two-relation
terms are not the whole selected envelope: the latter minimizes several
complete covers with additional short-anchor charges. The next diagnostic
must separate those cover contributions before interpreting a large raw
term as the bottleneck of the final bound. The sizes17..24 plus later-history
allocation2.0505e-12, adaptive projected-block bridge, and full BKZ proof
remain open. No actual failure probability is inferred from these envelopes.
