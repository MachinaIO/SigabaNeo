# Norm-eight minimum with a four-circuit on eleven positions

Consider the no-four/no-six relation-plane family with c=4 and seven new
positions. Every nonzero relation either lies on the four-coordinate circuit
C or is nonzero on all seven new coordinates, whose restriction has rank
one. A balanced squared-norm-eight row cannot have full support on C:
its only shape on at most four positions is (2,-2), of support two.
Hence a shortest norm-eight row a is unit on all seven new and one old
coordinate.

Take a Gauss-reduced independent second row b, so |<a,b>|<=4. For squared
norm B<=10 its new part is either zero or +/-the new part of a, since
a has unit new entries and a multiple of absolute value two already has
new squared norm28.

If B=8 and the new part is nonzero, b has one unit old entry. The old
difference after cancellation has support at most two and cannot generate
the full-support circuit C. If the new part is zero, a balanced norm-eight
row on C again has support two. Both cases are impossible.

If B=10 and the new part is nonzero, b has old squared norm three, hence
three unit old entries. The absolute inner product with a is at least
7-1=6, contradicting Gauss reduction. Therefore b lies entirely on C.
Its balanced shape is (2,-2,1,-1), up to signs and permutation, so its
inner product with a has absolute value at most two. Its perpendicular
squared length is at least10-4/8=19/2. If B>=12, the general Gauss bound
gives at least12-16/8=10, which is stronger.

Thus all norm-eight-minimum planes have squared GS bounds(8,19/2).
The other minimum class keeps(10,15/2). The production code sums these
two complete kernels, retaining cutoff-14 tails and periodic corrections,
and compares with its previous complete bound.

`scripts/wall1_four_eleven_eight.py` checks all reduced pairs of these small
norms having proportional new parts and a full-support old difference.
All1680 accepted pairs have second norm ten on C, and Gram determinant
at least76; equality is attained. This is an auxiliary finite check of the
argument above. No new Lean formalization or complete BKZ claim is made.

The full regression shows that this norm-eight improvement has negligible
effect on the current residual. The norm-ten class cannot be improved by
simply raising its uniform second height: take

    a=(2,-2,1,-1,0,0,0,0,0,0,0),
    b=(1,-1,1,0,-1,-1,-1,-1,1,1,1).

Both rows are balanced, have squared norm ten and inner product five, and
have a unit minor. The saturated integer plane has minimum squared norm
ten because its quadratic form is10(u^2+uv+v^2). Its projective column
group sizes are7,2,1,1, so its girth is four. The second squared height
15/2 is attained. Further improvement must isolate such rare planes or
strengthen their counting, not assert a larger uniform height.

## Isolating the reduced norm-ten pairs

Every reduced norm-ten pair in this family admits a norm-ten generator on
C. If either row already lies there this is immediate. Otherwise both
rows are unit on seven new and three old positions. Orient their new parts
to agree. Their old supports must cover C and thus overlap in two places.
The inner product is at least7-2=5, and Gauss reduction requires it to be
at most5. Equality follows, with opposite signs at both shared old entries.
Their difference is supported on all four old positions and has squared
norm20-2*5=10. The pair formed by this difference and one original row
is a unimodular basis change.

Enumerate all balanced norm-ten first rows on C and all balanced norm-ten
second rows nonzero on the seven new coordinates. A unit old entry and
unit new entry give a unit minor. After normalization modulo the first
row and deduplication, `scripts/wall1_eleven_ten_pairs.py` gives:

    overlap1: no planes;
    overlap2: {75:70,84:140,91:140,100:140};
    overlap3: {75:210,84:420,91:420,96:1344,99:1344,100:420}.

Keys are Gram determinants and values are plane counts for the prescribed
supports. All counts agree at q=7,17,3329. Every classified kernel uses
squared heights10,D/10. In the remaining minimum-ten family the second
squared minimum is at least twelve, yielding height12-25/10=19/2.
The minimum-at-least-twelve family has heights12,9. Add these two complete
remainder kernels with their full coefficient count and the normalized
rare-plane kernels, and take the minimum with the previous height15/2
bound. The minimum-eight family retains its height19/2 bound. Every
cutoff-14 tail and periodic layer remains in place.
