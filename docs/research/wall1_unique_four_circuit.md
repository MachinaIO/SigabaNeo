# A unique four-circuit gives a stronger six-column Gaussian bound

**Follow-up:** [Part 283](wall1_short_relation_shapes.md) further stratifies short
relation codes and counts equal-pair-sum configurations directly. It extends the
admitted cumulant transfer to size thirteen; the numerical accounting below
records the earlier size-twelve stage.

This paper refinement brings the draw-14 full-incidence cumulant transfer through
size twelve below 4.871e-13. It uses a stronger Gaussian bound when a six-column
relation code has exactly one weight-four projective direction, and removes
provable witness multiplicities in the completion count. Components of size
13--24, their mixtures, later histories and the other BKZ obligations remain
unresolved. The result is not a complete draw-14 bound or a Lean proof.

## At least k+1 basis extensions

If a matroid M has no coloops, neither does M/A for any contracted set A:
for e outside A, deletion of e leaves the rank of M unchanged, and therefore
also leaves rank(M/A) unchanged. A rank-k matroid without coloops has at least
k+1 bases. Fix a basis B. For each b in B, some element outside B can replace b,
since b is not a coloop. These k new bases are distinct, as are they from B.

Consequently, in a connected full-support count, each valid fixed anchor has at
least k+1 basis-position extensions, where k is the remaining rank. The old
upper count summed all such extensions. Divide that upper count by k+1. This
does not assume uniform multiplicity or divide by an average: every counted
configuration has at least that many extensions. In Part 278's notation:

- one-circuit anchor: k=r-c+1, divisor r-c+2;
- two-circuit anchor: k=r-c-t+2, divisor r-c-t+3.

For k=0 the divisor is one, including the fixed-position uniform strata.
Loop elements in the contraction cause no problem.

## Partitioning the c=4, t=2 case

For a connected girth-four support, distinguish two families.

1. Some two four-circuits have a six-element union of rank four. Use that pair
   as the two-relation anchor. Either circuit can be first, giving at least two
   ordered witnesses on the same union. Divide this particular anchor count by
   two in addition to the basis-extension divisor.
2. No such pair exists. Apply the outside-span witness of Part 279 to any
   shortest four-circuit. If t=2, its six-element union cannot have a second
   four-circuit. Otherwise that circuit and the first would give family 1.
   Its second circuit therefore has size five, with overlap a=3.

A nonzero independent relation on this six-element union must use both outside
positions, because those two columns of the two-row relation matrix are parallel
and nonzero. Thus any other weight-four relation gives precisely the excluded
second four-circuit on the union. In family 2 the two-dimensional relation code
has exactly one projective direction of Hamming weight four.

For t>=3 keep the existing bounds, even though they may also count family 1.
These extra nonnegative counts are harmless. This is why the modified sum covers
every support while allowing a factor one half only on the c=4,t=2,a=2 term.
The c=4,t=2,a=3 term is now restricted to the unique-four-circuit case.

## Short vectors in the relation code lie in a real plane

Let C be a two-dimensional code in F_q^6, q=3329, whose nonzero words have
Hamming weight at least four, with exactly one projective weight-four direction.
Assume every codeword has coordinate sum zero. These properties hold for the
eligible affine relation matrices just described.

Choose centered integer representatives v of its words and put L=14. Since

\[
                 L^3<q,\qquad L^2<q,\qquad 6L^2<q^2,
\]

all words with norm at most L lie in a real subspace of dimension at most two.
If three were linearly independent over the reals, one nonzero integer
three-by-three minor would be divisible by q, since their reductions have rank
at most two. Their Euclidean three-volume would then be at least q, but at most
L^3 by Hadamard's inequality, a contradiction.

Each short representative has integer coordinate sum zero: its sum is a
multiple of q of absolute value at most sqrt(6)L<q. The real subspace W that
they span is therefore contained in the sum-zero hyperplane.

If W has dimension two, choose independent short vectors a,b. The index of
Za+Zb in the saturated lattice Lambda=W intersect Z^6 is the gcd of their
two-by-two minors. It is at most norm(a)norm(b)<=L^2<q and hence coprime to q.
Thus reduction of every vector of Lambda belongs to C. The same argument in
rank one uses the gcd of the coordinates of a short generator. This saturation
step is needed; real-plane containment alone does not justify a code constraint
on every lattice vector.

## A theta bound for the short-vector lattice

In rank two choose a shortest nonzero lattice vector b_1 and a basis completion
b_2 reduced so that |<b_1,b_2>|<=norm(b_1)^2/2. The second vector is at least
as long as the first. Squared norms in the sum-zero integer lattice are even.
The first vector has squared norm at least four: it is short, nonzero modulo q,
and has at least four nonzero coordinates.

If norm(b_1)^2=4, norm(b_2)^2 cannot also be four. Both would then be weight-four
codewords in distinct projective directions: a nonzero two-by-two minor has
absolute value at most four, so their reductions cannot be proportional. This
contradicts uniqueness. Thus norm(b_2)^2>=6 and its squared perpendicular height
is at least 6-4/4=5.

If norm(b_1)^2>=6, the squared perpendicular height is at least
3 norm(b_1)^2/4>=9/2. Iterated Gaussian summation in this basis, bounding each
shifted one-dimensional sum by its unshifted value, therefore gives

\[
 \Theta_\Lambda(\alpha)\le
 \begin{cases}
 \theta(4\alpha)\theta(5\alpha),&\|b_1\|^2=4,\\
 \theta(6\alpha)\theta((9/2)\alpha)
       \le\theta(5\alpha)\theta(4\alpha),&\|b_1\|^2\ge6 .
 \end{cases}                                                \tag{1}
\]

The rank-one and rank-zero cases satisfy the same bound. This bounds all short
code representatives by a single expression, without enumerating coefficient
matrices.

## Controlling the remaining codewords

Write S_C(alpha)=sum_(v in C) exp(-alpha norm(v_centered)^2).
The general girth-four six-column bound from Part 261, applied directly to the
centered Gaussian, is

\[
 S_C(\alpha)\le\theta(4\alpha)\theta(3\alpha)
                         +q^2e^{-\alpha q^2/4}.              \tag{2}
\]

The columns have direction multiplicity at most two, so they split into two
triples of distinct directions. Holder and the previously proved odd-level-set
rearrangement give (2); nonwrapping pairs are bounded by the infinite triangular
Gaussian sum, and wrapping pairs have u^2+v^2>=q^2/8.

Use half the exponent for the tail beyond L. Equations (1)--(2) imply

\[
 S_C(\alpha)\le\theta(4\alpha)\theta(5\alpha)
 +e^{-\alpha L^2/2}
       \left[\theta(2\alpha)\theta((3/2)\alpha)
                              +q^2e^{-\alpha q^2/8}\right].  \tag{3}
\]

For the positive Fourier Gaussian use the same notation as Part 261:
T_beta=sqrt(pi/beta), A=pi^2/beta, alpha=A/q^2 and
delta=2 exp(-A/4)/(1-exp(-2A)).
Since F_beta(u)<=T_beta(exp(-alpha u_centered^2)+delta), (3) yields

\[
 U_{\rm unique}(\beta)=T_\beta^6
 \left[\frac{\text{right side of (3)}}{q^2}
                   +\sum_{j=1}^{6}{6\choose j}\delta^j\right]. \tag{4}
\]

The added terms follow by expanding the product and bounding each main Gaussian
factor by one. This retains the periodic tails; it is not a continuum-only
approximation. Use (4) only for the eligible unique-four-circuit coefficient
pairs, before bounding their number by the existing q^5 envelope. Other
coefficient pairs use the separate paired branch.

## Actual draw-14 accounting

Apply (4), both multiplicity divisors, and Part 281's exact factorial-cumulant
transfer C to the current full-incidence bounds. Outward interval arithmetic
proves the transfer from all circuits/rank-two components through size 24 and
all other components through size twelve is

\[
                         \mathcal C(B)<4.871\,10^{-13},       \tag{5}
\]

where B denotes the nonnegative activity upper bounds for those admitted
classes. The cutoff-eleven value is below 2.548e-21. The known monomial degrees
are unchanged, so the previous negative-power justification for substituting
the mean floor still applies.

Let U_h denote the true full-incidence activity of the omitted components:
size 13--24, rank at least three and nullity at least two. Define the remaining
mixed charge

\[
                  M=\mathcal C(B+U)-\mathcal C(B)\ge0 .
\]

Then C(F)<=4.871e-13+M. A sufficient remaining history requirement is

\[
                   M+\Pr(\max_{15\le i\le404}b_i>0.280)
                                             \le2.5217\,10^{-12}. \tag{6}
\]

It implies C(F)<=3.0088e-12 and hence the premise of Part 281's cumulant-error
bound. Under that premise,

\[
                      \Pr(b_{14}>0.280)<1.4002\,10^{-12}+M.  \tag{7}
\]

The constants in (6)--(7) sum to 3.9219e-12, below the earlier 3.922e-12
allowance. This is conditional on the still-unproved remainder requirement;
neither (5) alone nor the small cumulant error is a full draw-14 failure bound.
The existing envelope including size thirteen is still very large.

## Verification

Run python3 docs/research/scripts/wall1_unique_four_circuit.py for:

- 17792 exact no-coloop contraction basis-count checks;
- 9594 relation-code classifications, including 3426 unique and 6168 paired cases;
- 3225 reduced integer Gram inequalities;
- six exact rational finite-code theta inequalities.

The finite-code theta tests use q=17 and a correspondingly admissible cutoff;
the actual q=3329, cutoff-14 estimate is evaluated by the general two-relation
and factorial-cumulant scripts. Run
python3 docs/research/scripts/wall1_factorial_cumulants.py
to recompute the actual bounds, the existing 240 transfer identities and 1866
connected/cumulant-error checks. Finite tests do not replace the general
arguments above. No independent audit or Lean certification is claimed.
