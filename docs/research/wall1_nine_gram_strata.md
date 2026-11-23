# Nine-position short-pair Gram strata

The size16, rank8, girth4 diagnostic after Part 315 is dominated by the
two-relation terms c=4,t=5 with overlaps a=1,2,3. This note refines those
terms by enumerating all rare short planes on their nine positions.

Fix the first four-support C and the prescribed old overlap A contained
in C. Enumerate its three balanced norm-four lines u, and all balanced
integer lines v of squared norm six or eight that are nonzero on all
five new positions. Normalize the first new coordinate to one and
subtract the multiple of u making the first old coordinate zero. This
gives a canonical key for the modular plane, with u retained in the key.
Test every critical scalar -v_i/u_i on C; these are exactly the scalars
where u's combination with v can have a proper old support. Keep the
key if that support is the prescribed A.

The exhaustive counts at q=3329 (also checked at 7 and 17) are:

| Old overlap size | Determinant 23 | Determinant 31 |
| --- | ---: | ---: |
| 1 | 30 | 0 |
| 2 | 0 | 50 |
| 3 | 30 | 150 |

For squared norm six, the line has five new and one old nonzero
coordinates, all equal to +/-1, hence dot product with u is +/-1 and
Gram determinant 23. For squared norm eight, the eligible lines have
eight +/-1 coordinates: five new and three old. Their inner products
with u are +/-1 or +/-3, giving determinant31 or23. The alternative
norm-eight shape with support five has zero old part and cannot yield
a proper nonempty old support when combined with u, so is ineligible.

The determinant23 planes from norm-eight witnesses are exactly those
already counted by norm-six witnesses: if |<u,v>|=3, subtract the
appropriate sign of u to get squared norm six. Equality of the canonical
key sets is checked explicitly. They are counted only once in the table.
Permutation invariance makes the counts apply to every prescribed A
of the indicated size; the coefficient/position cover already supplies
the appropriate choose(4,a) factor.

Every eligible short pair has an old coordinate where only u is nonzero
and a new coordinate where only v is nonzero. Both entries are units.
It therefore has a unit minor and spans a primitive integer plane. Its
second squared Gram--Schmidt height, after u, is D/4. The rare Gaussian
terms can use theta(4 alpha)*theta((23/4) alpha) or the corresponding
31/4 factor. The full long-vector tail and all periodic aliases remain.

Planes containing neither independent norm-six nor norm-eight lines
retain the existing second squared-height bound nine. Their full old
coefficient count is retained as an upper bound; it is not inferred
by subtracting rare counts. Thus the replacement is a positive cover
of every plane, and remains valid under the existing short-anchor
exclusion flags. It refines only c=4,t=5; every other term is unchanged.

The implementation is in the general two-relation evaluation, so both
the unrestricted and restricted component covers use these counts.
The enumerator checks all witnesses and critical scalars, rather than
random samples. This is a paper/computer-assisted counting step, not a
Lean theorem, nor a proof of the remaining selected-history estimates.

## Outcome

The full size16 weighted residual log10 is 0.9864437503. The leading
rank/girth strata are (5,4) at log10 0.9347002749, (8,4) at 0.0234528635,
and (6,4) at -1.6115400964. This rules out the previous nine-position
rare-plane overcount as the current leading term; low-rank extensions
still require substantially stronger estimates.

The full cumulant probe passes its 2106 exact regressions and retains
transfer through fifteen below 1.557e-12. The residual sufficient
condition remains 1.4518e-12 for sizes16..24 plus later histories.
The through24 envelope is about 3.97e236 and is ineffective. These
large upper bounds neither prove failure nor establish the required
small failure probability. The full BKZ goal remains open.
