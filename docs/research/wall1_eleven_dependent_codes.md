# One-point norm-four extensions of the determinant31 anchor

The complete anchor cover from Part379 is too large at rank9. Refine its
one-point exceptional norm-four term by the full three-row Gram determinant.
Use the balanced representative on twelve positions

    a=(1,1,-1,-1,0,0,0,0,0,0,0,0),
    b=(1,0,0,0,1,1,1,-1,-1,-1,-1,0).

Every balanced norm-four/eight anchor of this type maps to this representative
by a permutation and global sign changes of its rows. Orient both rows
positively at their unique shared position; then the other three old signs
are one positive and two negative, and the seven new signs are three
positive and four negative. Permuting these sign groups constructs the
map. Unlike arbitrary coordinate sign changes, this preserves affine
balance for every extension row. The script checks all420 anchors.

A balanced norm-four extension v using the final new position uses three
old positions. There are3 choose(11,3)=495 such lines up to sign. Put
x=<a,v>,y=<b,v>. Their three-row Gram determinant is

    D = 124 - 8x^2 + 2xy - 4y^2.

For each line, the script computes all220 three-column minors. A unit
minor always exists, proving saturation of the integer row lattice.
All minors have absolute value less than7, so every nonzero minor remains
nonzero modulo3329. A nonzero relation of support at most3 exists exactly
when some nine-column complement has rank less than3. Checking all220
such complements therefore excludes precisely the candidates incompatible
with girth at least4, over both the rationals and the current finite field.
The retained witness counts are

    D:     84  86  88  92  96 104 108 110 114 116 120 124
    count: 36  18  30  34  51  48  15  15  30  90 103  13.

In particular, all determinant52 and54 candidates violate the girth
condition. These counts are extension-line counts; summing them is a
valid plane cover even when several lines describe the same extended
plane. Unit minors justify squared GS heights4,31/4,D/31 for each case.

Replace only the one-point exceptional norm-four term by the sum of the
complete kernels with these counts and heights. Every cutoff24 tail and
periodic-coordinate correction remains in each kernel. Keep the same
coefficient-weighted no-new-four term, all larger extensions and all
other anchors. The production path still adds this entire anchor cover
back to the excluded residual and takes the minimum with prior full
bounds. This classification is not new Lean formalization and does not
complete the global residual or adaptive BKZ proof.
