# Exact four/six short pairs on seven positions

Refine the c=4,t=3 one-norm-four contribution from Part 308. Suppose its
code also contains an independent norm-six row. Girth four forces that
row to be balanced +/-1 on six positions. The norm-four row is balanced
on four positions. Their full support union is seven, so their overlap
has three positions and their inner product has magnitude one or three.

Magnitude three would make their suitably signed difference another
norm-four vector (6+4-2*3=4), contradicting the exactly-one-norm-four
class. Hence the inner-product magnitude is one. Their Gram--Schmidt
squared lengths are 4 and 6-1/4=23/4, stronger than the previous height
five. Exclusive coordinates give a unit minor, so they generate the
saturated plane; the fixed-plane theta bound applies directly. Keep the
same cutoff-40 long tail and positive periodic correction.

The coefficient ratios on the three overlapping positions have a two/one
sign split. The cancelling mixed directions therefore have weights five
and six, and all other mixed directions have weight seven. Thus the sole
weight-four direction is the norm-four row itself: it must be the
prescribed first circuit C.

Fix C={0,1,2,3}. Enumerate its three balanced sign patterns and all balanced
six-support rows whose union with C is {0,...,6}. Test the prescribed
second support {0,...,a-1,4,5,6}. All support changes occur at projective
parameters 0,+1,-1,infinity. The exhaustive counts at q=3329 are

    a=1: 0 witnesses; a=2: 14 witnesses; a=3: 42 witnesses.

The same counts hold in the q=7 and q=17 regression. A witness determines
the code, and each prescribed proper support determines at most one
projective coefficient row. Witness counts therefore upper-bound the
normalized coefficient pairs, even if different witnesses described the
same code. This replaces the generic K4*K6 count only for the norm-six
part; norm-eight and no-short-second-line parts remain included.

This is a finite exhaustive classification over the actual field with a
coverage proof and interval integration. It is not a Lean formalization
or a complete residual, selected-history, or BKZ proof.

## Eight-point fixed-first-line refinement

The seven-point refinement barely changes the full envelope. The next
diagnostic identifies t=4, overlaps one and two, as the larger terms.
Here H=8 and Part 295 forces the only norm-four direction to be the
prescribed first four-circuit. Enumerate its three balanced patterns and
all independent integer rows of squared norm six or eight. Every new
coordinate must be nonzero. Part 302's integer shape enumeration is
exhaustive for these norms and girth four.

Normalize the extra row so that its first new coordinate is one, then
subtract a multiple of the first circuit to set old coordinate zero to
zero. Together with the normalized first circuit this uniquely identifies
the code. For each old coordinate i, the only possible parameter making
it zero is -v_i/C_i; checking those four parameters exhausts every proper
old overlap. Deduplicate codes for each prescribed old support.

At q=3329 the exact counts for overlaps a=1,2,3 are

    independent norm six:  0, 30, 42;
    independent norm eight: 60, 13, 60.

The q=7 and q=17 regressions agree. Norm-eight counts may also include
codes with an independent norm-six row, so using them for the no-norm-six
norm-eight class is a safe upper cover. The existing height and tail
bounds are unchanged; only the rare coefficient counts are replaced.

The seven-point change alone leaves size fifteen near 9.88e-11. Including
the eight-point exact counts lowers its full residual weighted log10 to
-11.30167 (about 4.99e-12). Its no-double-short diagnostic is about 2.05e-12.
Neither number closes the complete residual: the full size-fifteen bound
alone still exceeds the entire remaining 2.4692e-12 budget, which must
also cover sizes sixteen through twenty-four and later selected histories.
