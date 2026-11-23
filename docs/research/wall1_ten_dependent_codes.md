# One-point extensions of the ten-position determinant28 anchor

The determinant28 anchor has two affine sign types. Fix
a=(1,1,-1,-1,0,0,0,0,0,0,0), with the final coordinate new. Representatives
for the second row are

    (1,1,0,0,1,1,-1,-1,-1,-1,0),
    (1,0,-1,0,1,1,1,-1,-1,-1,0).

Their shared old coefficients respectively have equal and opposite signs.
Permutations within the sign groups and a global row sign cover all the
balanced affine pairs of determinant28. This classification uses the
original affine signs, not the all-positive geometric representative.

Enumerate the360 balanced norm-four lines with nonzero final coordinate
for each type. For a third row v, let x=<a,v>, y=<b,v>. Its three-row Gram
determinant is

    D=112-8x^2+4xy-4y^2.

The third squared height is D/28. Every tested triple has a unit minor,
so the rows give a primitive integer basis of their real span. All minors
have absolute value below7. To impose girth four, require all165 sets of
eight columns to have rank three. Otherwise a nonzero row combination
is supported on at most the three omitted columns. The test therefore
excludes exactly the forbidden short-support codewords, over Q and every
prime field q>=7, including3329.

The exact valid counts, indexed by D, are:

    equal-sign:    {68:8,76:16,80:104,84:4,96:52,104:88,108:68,112:8}
    opposite-sign:{68:12,76:18,80:84,84:12,96:66,104:84,108:54,112:18}

Use the componentwise maximum as a uniform upper bound for either type:

    {68:12,76:18,80:104,84:12,96:66,104:88,108:68,112:18}.

Counting witnesses rather than distinct planes can only increase the
bound. Replace the old360-fold unrestricted one-point kernel with the
sum of these complete D/28 kernels. Retain the full coefficient count
times the no-new-norm-four kernel, whose height is at least26/7. Thus
planes not represented by a new norm-four row remain covered. All tails,
periodic layers and the minimum with the previous complete bound remain.

`wall1_ten_dependent_codes.py` checks720 lines, both sign types, primitive
minors, and all165 complementary supports for each line. The production
one-point extension path uses the resulting constants. This is not Lean
formalized and is not a complete BKZ proof.

The complete interval run passes2106 cumulant regressions. Transfer through
sixteen stays below9.583e-13 (about8.78528900488e-13). Size17's weighted
residual log10 is5.6966479238. Unlike the preceding unrestricted anchor
cover, this refinement removes rank8/girth4 from the five largest strata;
rank8/girth3 now leads at5.5854684520. Through24 remains about1.61354e232,
so neither the remaining2.0505e-12 allocation nor the adaptive projected
BKZ bridge is proved. Logs: `/tmp/wall1_ten_dependent.log` and
`/tmp/wall1_ten_dependent_cumulants.log`. These are upper envelopes, not
actual failure-probability estimates.
