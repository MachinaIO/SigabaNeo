# Five-position two-norm-four anchor

After removing the determinant20 one-four family, size17 rank8/girth3
is dominated by c=3,t=2,a=2. Its one-four and no-four contributions are
negligible relative to the two-four term. The present cover addresses
exactly that remaining family.

Two balanced norm-four lines covering five positions overlap on three.
Their inner product has absolute value one or three. The latter produces
a relation supported on two positions by adding or subtracting the rows,
contradicting girth three. Thus the Gram determinant is15. After signs,
permutation and a row sign, a representative is

    a=(1,1,1,1,0), b=(1,1,-1,0,1).

A unit minor proves primitivity. The Gram matrix [[4,1],[1,4]] has squared
basis heights4,15/4. Its fundamental parallelogram splits into triangles
with squared sides4,4,6, whose squared circumradius is8/5.

To prove the projected integer lattice has positive squared minimum at
least1/3, suppose a vector had positive projected squared length below1/3.
Subtract a nearest point of the integer anchor lattice within the old
plane. Its squared norm would be below1/3+8/5=29/15<2. The resulting
integer vector is therefore zero or a signed coordinate unit. These11
possibilities have projection zero or squared length at least1/3, as
verified by the exact Gram inverse. This finite certificate, together
with the rounding argument, proves the assertion for all integer vectors.

There are60 unordered affine row-pair witnesses covering a fixed
five-position set. The enumeration starts with all15 balanced norm-four
lines, rejects support-two differences, and checks primitive minors for
every retained pair. Witness counting may overcount planes, which is safe.

Use the complete girth-three extension cover with size5, rank3 and60
witnesses. A third relation with t new nonzero coordinates has projected
squared length at least t+1/3. When additional norm-four relations are
absent, the affine even-norm condition and girth three force squared norm
at least six after rounding, giving the additional lower bound6-8/5=22/5.
Cover the extra norm-four families explicitly before using this restriction.
Third-code tails use cutoff29, since15*29^4<3329^2; all periodic layers
and the original anchor tail remain.

The exclusion flag removes only the two-four coefficient in the c=3,H=5
split. The complete candidate adds this anchor cover and both previously
removed determinant20 covers back before minimizing with the old bounds.
No family is omitted. The production path uses the new candidate, not
only a standalone geometry check. This is not Lean formalized and does
not prove the complete adaptive BKZ theorem.

The completed interval run passes2106 cumulant regressions. Transfer
through sixteen remains below9.583e-13 (about8.78527726940e-13). Size17's
weighted residual log10 is5.0640383603. Rank8/girth3 is now4.0047986582;
the leading stratum is rank10/girth3 at4.5572011555. Through24 remains
about1.61354e232, and the remaining2.0505e-12 allocation is unproved.
Logs: `/tmp/wall1_five_fifteen.log` and
`/tmp/wall1_five_fifteen_cumulants.log`. These are upper envelopes, not
actual failure-probability estimates.
