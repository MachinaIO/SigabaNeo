# Six-position girth-three determinant23 anchor

The remaining size17 rank8/girth3 envelope is led by c=3,t=3. Its
one-norm-four term dominates; after the determinant20 exclusion, the
remaining short plane in the exact six-position table has determinant23.
Independent norm-eight witnesses for that determinant describe the same
planes as the norm-six witnesses, as verified by the existing exact table.

On six positions, a norm-four/norm-six pair with dot product of absolute
value one must have a three-position norm-six row. A six-unit row would
overlap the four-row in four positions and have an even dot product.
The three-position row overlaps in one coordinate; its coefficient of
absolute value two must be outside the four-support. Up to signs and
permutation use

    a=(1,1,1,1,0,0), b=(1,0,0,0,2,1).

The pair has a unit minor, so it generates its primitive integer plane.
The Gram matrix [[4,1],[1,6]] gives squared heights4,23/4. Fundamental
triangles have squared sides4,6,8 and squared circumradius48/23.

Suppose an integer vector has positive squared projection less than7/23.
Round its old-plane component using this covering radius. The resulting
integer representative has squared norm below(7+48)/23=55/23<3, hence
at most two. Exact evaluation of the Gram-inverse formula

    ||v||^2 - (6<a,v>^2 - 2<a,v><b,v> + 4<b,v>^2)/23

on the73 vectors of squared norm at most two gives zero or at least7/23.
This proves the minimum for all integer vectors; the finite check alone
would not suffice without the rounding reduction.

There are360 primitive affine witnesses on a fixed six-position set:
15 four-supports, three balanced first signs, four shared positions and
two choices for which new coordinate has magnitude two. Enumeration uses
the original balanced rows and verifies the count and unit minors.

Use the complete girth-three extension cover with size6, rank4 and360
witnesses. The third height is at least t+7/23. After explicitly covering
new norm-four lines, the remaining height is also at least6-48/23=90/23.
Retain the cutoff26 tail (23*26^4<3329^2), periodic layers, crossing and
marked-pair coefficients, and same-rank/no-coloop cases. Rational maxima
are computed exactly before interval conversion.

Only the determinant23 term of the exact c=3,H=6 table is excluded under
the new flag. This cover and every previously removed girth-three anchor
are added back before minimizing with the old complete candidates. The
new geometry is not Lean formalized and does not complete the BKZ proof.

The full probe passes2106 cumulant regressions. Transfer through sixteen
stays below3.459e-13 (about3.45843793353e-13). Size17's weighted residual
log10 is2.5734857935; rank8/girth3 leaves the five largest strata and
rank8/girth4 now leads at2.4604219177. Through24 remains about1.05489e232.
The remaining2.6629e-12 allowance and adaptive projected-block bridge are
unproved. Logs: `/tmp/wall1_six_twenty_three.log` and
`/tmp/wall1_six_twenty_three_cumulants.log`. These are upper envelopes,
not actual failure-probability estimates.
