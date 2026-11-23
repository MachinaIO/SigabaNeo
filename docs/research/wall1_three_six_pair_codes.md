# Two norm-six lines with a prescribed three-circuit

After the five-position short-anchor covers, size17 rank8/girth3 is led
by c=3,t=5: a prescribed three-circuit and five new positions. Its
norm-four family is empty. Refine its two-norm-six contribution.

An affine norm-six integer line has either six unit entries or the
three-position shape (2,-1,-1). Two three-position rows cannot cover
eight positions. Two six-unit rows on eight positions have four shared
coordinates and two exclusive coordinates each. Their projective column
classes have size at most four, so every nonzero row combination has
support at least four. They cannot contain the prescribed three-circuit.
Thus a pair spanning the code must contain one three-position row.

That three-position row must be the prescribed first circuit: any
independent row is nonzero on all five new positions. The second norm-six
row has five new unit entries and one old unit entry. The inner product
has absolute value one or two according to which old coordinate it meets.
Consequently the Gram determinant is35 or32, with second squared height
35/6 or16/3. An old-exclusive unit coordinate and a new unit coordinate
give a unit minor; the rows are a primitive basis of the integer plane.

Enumerate the three primitive norm-six lines on the fixed first support
and all balanced second lines nonzero on the five new coordinates.
Normalize the first coordinate by its actual inverse (it can be two),
eliminate it from the second row, normalize at the first new coordinate,
and deduplicate. Test the prescribed old overlap using all possible
coordinate-cancelling scalars. For each fixed overlap of size one or two,
there are10 determinant32 planes and20 determinant35 planes. This is
checked over q=7,17,3329, including the unit minors. The concrete bound
uses3329; permutations handle the other fixed support choices.

Replace only the broad two-six term by these two complete weighted kernels,
with all cutoff36 tails and periodic layers retained. One-six and no-six
families and all other supports remain unchanged. Take the minimum with
the old complete envelope. This is not a Lean formalization or a complete
adaptive BKZ proof.

The full interval probe passes2106 cumulant regressions. Transfer through
sixteen stays below3.459e-13 (about3.45843794477e-13). Size17's weighted
residual log10 is3.7239228388, now led by rank9/girth6 at3.6548825537.
Rank8/girth3 is2.5550235891. Through24 remains about1.05489e232. The
remaining2.6629e-12 allowance and adaptive BKZ bridge remain unproved;
these are upper envelopes, not actual failure probabilities. Logs:
`/tmp/wall1_three_six_pair.log` and
`/tmp/wall1_three_six_pair_cumulants.log`.
