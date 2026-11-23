# Sign-sensitive weights for nine-position determinant31 planes

The rank8/girth4 residual after Part382 is led by t5/overlaps3 and2. The
norm-ten remainder is already split; the counted norm-four/eight
Gram-determinant31 family remains.

Let a be the unit norm-four row on C and b a norm-eight row covering all
five new positions. Determinant31 gives |<a,b>|=1. A non-unit balanced
norm-eight row has support at most5; if it covers the new positions it
has no old entry and inner product0. Therefore b is unit on eight
positions, sharing three positions with a. Orient b so <a,b>=1. Of the
three shared positions, two products a_i b_i are+1 and one is-1.

Assign weights5/6 to the two agreeing shared positions,5/12 to the
opposing shared position,13/12 to the old-exclusive position, and7/6 to
each of the five new positions. Their sum is9. In metric diag(1/w),

    <a,b>_w = 2/(5/6)-1/(5/12) = 0,
    ||a||_w^2 = 372/65,
    ||b||_w^2 = 318/35.

The coordinate-weight product times the Gram determinant is
19724215/559872>31. The old-exclusive coordinate and any new unit
coordinate give a unit minor, so the pair is a basis for its integer
plane. All300 balanced witnesses are verified with rational arithmetic.
The weights depend only on the actual witness; no assumption about
preserving affine balance under arbitrary coordinate flips is used.

The complete Poisson kernel uses prefactor
((5/6)^2(5/12)(13/12)(7/6)^5)^(-1/2), the two weighted theta lengths, and
scale6/7 in both the cutoff40 complementary tail and periodic-coordinate
corrections. This is valid because max(w)=7/6 and the weighted quadratic
form is at least6/7 of the unweighted form. The total weight preserves
the original Markov exponential and Gaussian parameter. The unweighted
short-plane lifting cutoff is unchanged.

Only union9,determinant31 uses this refinement, and only when its complete
bound is smaller. Both the short-pair split and the later norm-ten split
use the same helper, as do diagnostics. All counts, other determinants,
unclassified remainders and added-back anchor families remain. This is
not yet Lean formalized and does not complete the global residual or
adaptive BKZ proof.
