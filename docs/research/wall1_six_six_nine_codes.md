# Two norm-six relations on nine positions

The size17 decomposition after Part328 is led by rank8/girth6 and
rank9/girth8, rather than the short girth3/4 configurations controlling
size16. Refine the rank8/girth6 c=6,t=3 terms by enumerating their rare
two-norm-six planes.

At girth six, a norm-six integer affine relation must be balanced with
six +/-1 entries; the three-support (2,-1,-1) shape is excluded. Two
independent such relations whose union has size nine overlap in three
positions. Their inner product is +/-3 or +/-1, giving Gram determinant
27 or35. Both have exclusive unit coordinates, so they generate a
primitive integer plane. After the first squared length six, the second
squared Gram--Schmidt length is D/6.

Every support-six direction in the plane is itself a balanced norm-six
line. To see this, group the columns by projective direction. The two
exclusive groups have size three. The overlap group is either one group
of size three (dot product +/-3), or groups of sizes two and one (dot
product +/-1). A combination with support six must cancel a group of
size three. This yields one of the two generators, or, in the first
case, their signed sum/difference with six +/-1 entries. Thus the fixed
first six-circuit may be enumerated among the ten balanced sign lines;
no prescribed-support plane is missed by that restriction.

For each such first row, enumerate every balanced norm-six second row
nonzero on the three new positions. Canonically normalize the first new
coordinate and eliminate the first old coordinate. Test every critical
scalar at which an old coordinate vanishes, requiring the old support
to be exactly the prescribed overlap. The exact code counts are:

| Old overlap size | D=27 | D=35 |
| --- | ---: | ---: |
| 3 | 28 | 72 |
| 4 | 0 | 96 |
| 5 | 0 | 240 |

The enumeration verifies these counts at q=7,17,3329, checks a unit minor,
and tests that every complementary four-column matrix has rank two.
The last condition verifies that no codeword has support at most five.
Different short witnesses are deduplicated by the canonical plane key.

Replace only the two-norm-six summand by the positive weighted sum of
complete Gaussian plane bounds with squared heights6 and D/6, divided
by the same coefficient count. Keep the one-norm-six and no-norm-six
families unchanged, including their coefficient factors. Preserve the
existing cutoff36 long tail and every periodic layer, and take the
minimum with the previous two-short-line bound. This applies only at
c=6,t=3 and does not change other girths or support sizes.

The exact enumeration supports this paper-level bound; it is not Lean
formalized. Size16 admission does not imply size17 admission, and the
later selected-history law and full BKZ theorem remain separate obligations.

The complete cumulant probe passes2106 exact regressions. After this
refinement the former rank8/girth6 and rank9/girth6 strata are no longer
among size17's largest five; rank9/girth8 becomes the largest. Transfer
through sixteen is about8.7976400422e-13, below the retained9.583e-13 cap.
This does not admit size17 or establish the remaining2.0505e-12 allocation.
