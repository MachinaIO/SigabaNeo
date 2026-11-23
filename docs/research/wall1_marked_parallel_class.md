# Retaining one pair inside a parallel class

In the no-large-crossing branch of Part 303, let an anchor have size s,
rank d, pattern count P and normalized count A. Its contraction has k=r-d
parallel classes of size at least two, plus loops. For k>=1 choose two
positions from any class.

The two quotient vectors are proportional, so their dependence modulo
the anchor yields a relation with two nonzero new coefficients and an
old part supported in a fixed anchor basis X. This old part is nonzero:
otherwise the two full augmented points would be scalar multiples, and
their leading coordinate one would make them equal, contrary to distinct
positions. Girth four forces at least two nonzero old coefficients.
Thus Part 293 or 299's specialized two-new-position count T applies.

The chosen class is now represented by that pair. Its additional positions
may be any number j, each with at most q^d affine-slice choices. The other
k-1 classes still have size at least two. Define

    M_d(n,k) = sum_(j=0)^n choose(n,j) q^(d*j) B_d(n-j,k),

where B_d is Part 303's weighted loop/class count. The cover becomes

    choose(h,s) P choose(h-s,2)
    * [sum_(a=2)^d choose(d,a) q^a] T mu^(k-1)
    * M_d(h-s-2,k-1).

The two-point relation is normalized by one new coefficient; the affine
sum constraint leaves at most q^a choices. Choosing a pair may count a
support repeatedly, which is allowed. Once the enlarged anchor is fixed,
the remaining class representatives are independent modulo it; each
contributes mu. Additional positions in the marked class are counted
inside the smaller span of the original anchor and its representative,
not the unrestricted enlarged full span.

Use the minimum of this cover, the previous parallel cover, and the
previous two-new-position crossing cover within the no-large-crossing
branch. Add the large-crossing envelope as before. All three short-anchor
types use this construction, preserving their respective T bounds.

The marked-class recurrence

    M_d(n,k) = (q^(d-1)+(k+1)q^d) M_d(n-1,k)
                 +(n-1)q^d M_d(n-2,k-1)

with M_d(0,0)=1 checks the sum formula. There are 306 exact recurrence
checks, alongside the previous 760 unmarked checks.

At size fifteen the triangular weighted contribution is below 1.88e-13
(log10 about -12.72684), down from about 2.59e-6. The full residual weighted
log10 is still -5.00138 (about 9.97e-6): the no-double-short remainder
dominates. This result bounds one family, not the complete residual or
the draw-14 exit probability. The full BKZ and selected-history proofs
remain open; no Lean formalization of this argument is claimed.
