# Girth-four rare planes on six positions

After Part324 the leading size16 rank8/girth4 terms have c=4,t=2 and
old overlap2 or3. Their one-norm-four branch previously counted rare
short planes without fully exploiting the prescribed supports and girth.

Fix C={0,1,2,3}, new positions {4,5}, and old overlap A={0,...,a-1}.
Enumerate all balanced norm-four lines u on six positions and balanced
norm-six/eight lines v. Test that the new two-column restriction has
rank one, and that annihilating it gives exactly support C. Annihilate
an old coordinate outside A and require exactly support A union {4,5}.
Normalize these two relations as in Part322 to obtain canonical plane keys.

Additionally test every complementary triple of columns for rank two.
A failed test is exactly a nonzero codeword on at most three positions,
which is forbidden by girth four. All two-column minors have absolute
value below seven, so the rank test is identical over Q and prime fields
q>=7. Enumerate the45 balanced norm-four lines and test membership in
the plane; retain only codes with one such line. The two-short-line
family remains in its separate existing cover.

The exact plane counts, verified at q=7,17,3329, are:

| Old overlap | D=24 | D=28 | D=31 | D=32 |
| --- | ---: | ---: | ---: | ---: |
| 2 | 12 | 0 | 24 | 8 |
| 3 | 0 | 36 | 72 | 24 |

The determinant24 codes come from norm-six witnesses; the other entries
come from norm-eight witnesses. Every eligible pair has a unit minor,
so it is a primitive integer plane and the second squared height after
the norm-four row is D/4. No index correction is silently discarded.

Use the positive sum of these counts times the complete fixed-plane
Gaussian bounds, divided by the existing total coefficient count.
Codes containing neither an independent norm-six nor norm-eight line
retain their old full coefficient count and second squared height nine.
Retain the long-vector tail, periodic layers, no-four family and
two-short-line family unchanged, and take the minimum with the previous
complete one-four bound. This changes only c=4,t=2.

In particular, determinant20/23 candidates visible before girth filtering
are not eligible here. They can occur in the girth-three family studied
in Part322; its cover is not removed or changed by this restriction.
The distinction prevents using the girth-four improvement for inputs
that merely have a prescribed four-support relation.

This is exhaustive finite counting connected to the analytic envelope,
not Lean formalization or a complete proof of adaptive BKZ behavior.

## Verified outcome

The enumeration at all three moduli and the complete cumulant probe pass,
including2106 exact regressions. Transfer through fifteen remains below
3.419e-13, with sufficient residual allocation2.6669e-12 still unproved.

Size16's full weighted residual log10 is -5.5307084029. Its rank8/girth4
part is now -9.8477666465, while rank8/girth3 dominates at -5.5360339823,
followed by rank7/girth3 at -7.4467122016. The improvement therefore
addresses the intended family, but does not resolve the girth-three
remainder. The through24 envelope is still about1.63e232. These large
positive upper envelopes do not give lower bounds on actual failure,
and the full residual and adaptive selected-history proof remain open.
