# Two norm-six rows with a prescribed five-circuit

The size17 rank8/girth5 residual is dominated by c=5,t=3: two relations
on eight positions. Refine only its two-norm-six family.

At girth five, norm-six affine integer rows must have six unit entries;
the (2,-1,-1) shape has support three and is excluded. Two such rows with
full union size eight share four positions and have two exclusive positions
each. Their inner product is0,+/-2 or+/-4. If its absolute value is four,
cancelling the shared positions gives support four, contradicting girth
five. If the dot product is zero, the two shared ratio classes each have
size two; all projective column groups then have size two, so the minimum
support is six. Such a plane cannot contain the prescribed five-circuit.
Therefore the inner product has absolute value two, Gram determinant32,
and second squared height32/6=16/3. Exclusive-coordinate minors are units,
so these rows form a primitive basis of the integer plane.

For the concrete prescribed first support {0,1,2,3,4} and new support
{5,6,7}, enumerate every pair of balanced norm-six lines on eight positions.
Require the new columns to be collinear, cancel them, and require the
resulting first relation to have exactly the five old positions as support.
Normalize its first coordinate. For each prescribed proper overlap,
cancel an omitted old coordinate, test the full support, and normalize
the second row after eliminating its first coordinate. Deduplicate the
resulting plane keys. This gives:

    overlap2: 0 planes; overlap3: 36 planes; overlap4: 36 planes.

The zero case also follows from the projective groups: the three shared
columns with equal ratios give the unique minimum-support five-line.
There cannot be a second distinct five-line with the prescribed overlap2.
All counts, determinant32 and unit minors are checked at q=7,17,3329;
the actual bound requires q=3329. Coordinate permutations cover other
choices of the fixed supports.

Replace the old broad pair count and height9/2 by these exact counts
and height16/3. Retain every cutoff36 tail and periodic layer. The
one-norm-six and no-norm-six families remain unchanged, and the minimum
with the old complete envelope is retained. This is not a complete BKZ
proof and has not been formalized in Lean.

The complete probe passes2106 cumulant regressions. Transfer through
sixteen remains below9.583e-13 (about8.78527577387e-13). Size17's weighted
residual log10 is4.4620948830; rank8/girth5 is no longer among the five
largest strata. Rank6/girth4 now leads at4.1346162982. Through24 remains
about1.05489e232. The remaining2.0505e-12 allocation and adaptive BKZ
bridge are unproved. Logs: `/tmp/wall1_five_six_pair.log` and
`/tmp/wall1_five_six_pair_cumulants.log`. These are upper envelopes, not
actual failure-probability estimates.
