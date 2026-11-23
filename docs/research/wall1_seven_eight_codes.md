# Exact norm-eight witnesses on seven positions

After the preceding refinements, the largest rank8/girth4 residual has
c=4,t=3. Its one-norm-four cover still used the loose count of all short
line pairs for the squared-norm-eight subfamily.

On seven coordinates a balanced norm-eight row has support five and shape
(2,1,-1,-1,-1), up to sign and permutation. Paired with a norm-four row and
full union seven, it shares two positions with that row. The projective
column group outside the norm-four support has size three; the exclusive
group of the norm-four row has size two, and each shared group has size
at most two. Thus the plane has a unique four-support direction, which
must be the prescribed first circuit C. This justifies fixing the first
norm-four support during enumeration, even though t=3 by itself does not
force every norm-four line to lie on C.

The exact normalized code counts are:

| Old overlap | Determinant | Count |
|---|---|---|
| 1 | any | 0 |
| 2 | 23 | 14 |
| 2 | 28 | 18 |
| 2 | 31 | 10 |
| 2 | 32 | 18 |
| 3 | 23 | 42 |
| 3 | 31 | 30 |
| 3 | 32 | 54 |

`scripts/wall1_seven_eight_codes.py` verifies these counts at q=7,17,3329.
All three new entries are nonzero, with at least two unit entries; combined
with a unit old entry this gives a unit minor, so squared second height
D/4 is valid. A determinant23 norm-eight witness has inner product +/-3
with the norm-four row; subtracting the signed first row gives squared norm
six. Hence those planes are already covered by the existing determinant23
norm-six family and are omitted from the new norm-eight sum. The existing
seven-position determinant23 exclusion and separate anchor addback remain
in force.

Sum the remaining exact norm-eight kernels, the retained norm-six family,
and the full prior coefficient count times the height-nine remainder.
Every cutoff-40 tail and periodic term remains. Compare with the old upper
bound and keep the smaller. The no-four family is unchanged. These local
counts do not resolve the residual target or the adaptive BKZ bridge, and
are not yet Lean formalized.

## Two norm-six rows in the no-four family

The norm-eight refinement alone has little numerical effect. A second
refinement applies to the separate no-four family when it contains two
independent norm-six rows. Girth four forces both rows to be unit on six
positions. Full support on seven positions means they share five entries,
with one exclusive entry each. After Gauss reduction their inner product
d is odd and |d|<=3. The shared equal-sign and opposite-sign projective
groups have sizes(5+d)/2 and(5-d)/2. Girth four requires each group to
have size at most three; therefore |d|<=1 and hence |d|=1.

The two exclusive columns give a unit minor. Thus the Gram determinant is
35 and the second squared Gram--Schmidt height is35/6, rather than the
previous generic9/2. The script `scripts/wall1_seven_six_pair_height.py`
verifies360 full-support reduced pairs under the girth condition. Counts,
cutoff-36 tails, periodic terms and other families remain unchanged; only
this two-six kernel uses the stronger height.
