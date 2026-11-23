# Parallel contraction for larger short-anchor supports

Generalize Part 292 from h=14 and a six-point rank-four anchor to any
h<=24 and the three existing short-anchor types. Write s for anchor size,
d for anchor rank, and k=r-d for the quotient rank.

Fix an anchor basis X. If any extension of X to a support basis has a
crossing fundamental circuit with at least three new positions, use the
existing t>=3 crossing cover. Otherwise Part 292's pivot proof applies
unchanged: a pure quotient edge joining two basis positions can be pivoted
through a mixed column to produce just such a forbidden crossing.
Consequently the contraction is a direct sum of loops and k parallel
classes. Connectedness excludes singleton classes because they would be
coloops. The implication requires absence of large crossings in every
basis extension, not just one.

Let n=h-s. Choose l loops and partition the other positions into k classes
of size at least two. Fix the least label as the representative of each
class. The independent representatives contribute mu^k. Every remaining
class point has at most q^d affine-slice choices, and each loop at most
q^(d-1). For a normalized anchor count A and P anchor patterns the bound is

    choose(h,s) P A mu^k B_d(n,k),
    B_d(n,k) = sum_(l=0)^(n-2k) choose(n,l) S_2(n-l,k)
                         q^(d(n-l-k)+(d-1)l).

The empty sum is zero, expressing impossibility when n<2k. In particular,
the no-large-crossing branch vanishes in high quotient rank. The recurrence

    B_d(n,k) = (q^(d-1)+k*q^d) B_d(n-1,k)
                 +(n-1)q^d B_d(n-2,k-1)

with B_d(0,0)=1 independently checks the finite sum. Its terms correspond
to inserting a loop, adding a point to a class, or forming a new pair.

The full cover is the t>=3 envelope plus the minimum of this parallel
bound and the previous t=2 envelope. The latter covers the no-large-crossing
branch because some crossing exists whenever r>d. Taking the minimum
within that branch is therefore valid. The anchor-rank and nullity-two
cases remain unchanged. Apply this to (s,d,P)=(6,4,75), (6,4,180), and
(7,5,630), preserving the specialized two-new-point code bounds.

Verification includes 81 exact partition counts, 760 weighted recurrence
identities through n=18, and the existing 2,593 connected-graph checks
with 137 pivot witnesses. The full interval and cumulant regressions pass.

At size fifteen the triangular weighted log10 improves from -3.51556 to
-5.44209; the full residual weighted log10 improves from -3.28929 to
-3.67322 (about 2.13e-4). This remains far above the residual budget.
The no-double-short remainder, especially girth six, now dominates.
Larger residuals and selected histories remain unresolved; no complete
BKZ or Lean proof is claimed.
