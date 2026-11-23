# Independent audit: ball-slice completion and the six-point D24 cover

Verdict: both proposed refinements are valid in their current production scope,
assuming the earlier fixed-code Fourier/lifting and connected-support counting
lemmas. No counterexample, missing multiplicity factor, or missing addback was
found. This is an audit of the new steps, not a completed BKZ proof or a fresh
full cumulant run.

## Ball-slice completion

For any affine d-plane U in F_q^k, choose d coordinate positions giving an
isomorphism from its direction space to F_q^d. Projection onto these coordinates
is injective on U, including its affine offset. Coordinatewise centered lifting
commutes with this projection. The relevant points therefore inject into
Z^d intersect B_d(R). Unit cubes have disjoint interiors and lie inside
B_d(R+sqrt(d)/2), proving

    # {y in U : ||[y]||<=R} <= min(q^d,V_d(R+sqrt(d)/2)^d).

For d=0 there is at most one point, as implemented. The real volume need not be
rounded down: a nonintegral upper bound on an integer count is valid. A rigorously
enclosed radius and volume also preserve the upper-bound interpretation.

The production quantities count distinct input residues with Bernoulli incidence
J_y, rather than every integer representative separately. A feasible raw ball
candidate gives a centered input lift of norm <=R, since coordinatewise centering
and deleting output coordinates cannot increase norm. After a valid input basis
and its output images are fixed, the remaining dependent inputs lie in a fixed
affine (r-1)-plane; for each, its conditional incidence is at most one. Thus the
uniform bound M_(r-1) can replace q^(r-1) pointwise. Repetition for k redundant
inputs gives M_(r-1)^k even if the previously fixed basis varies with the counted
configuration. No independence of a selected plane and the input distribution
is asserted.

In `wall1_general_two_relations.draw14_bounds`, the replacements occur only at
final one-circuit and two-relation completions, with exponents h-r-1 and h-r-2.
Coefficient-chart factors, anchor incidence normalizers, basis-extension powers
of mu and basis multiplicity divisors are unchanged. Pointwise improvement does
not invalidate those divisors: every original valid witness is still counted
before its completion sum is enlarged to this new uniform bound. The completion
constant is independent of the substituted mean mu. Invalid anchors included
by a later positive Gaussian relaxation need not define a span; the bound is
applied to valid fixed-rank anchors first.

## D24 anchor geometry and balance

The representative has a=(1,1,-1,-1,0,0),
b=(1,-1,1,-1,1,-1), Gram diag(4,6). A coordinate in supp(a) and one of the two
b-only coordinates give a unit minor; the old integer plane is saturated.
Its orthogonal fundamental rectangle has covering radius squared <=(4+6)/4=5/2.
If an integer vector had positive squared projected length <1/3, subtraction
of a nearest old-plane lattice point would leave norm squared <17/6<3.
The exhaustive 73 vectors of norm squared <=2 are all the possibilities, and
each has projection zero or >=1/3. This upgrades the finite check to a statement
about every integer vector. Balanced norm-four rows and unit norm-six rows
with zero inner product have exactly the four sign pairs (1,1),(1,-1),(-1,1),
(-1,-1) on the first support, and opposite signs outside it. Consequently
permutations and global row signs cover all 180 counted affine witnesses while
preserving balance of every extension.

A crossing fundamental row has a nonzero old coefficient vector supported on
an independent four-point anchor basis. It cannot lie in the old relation plane.
Each of its t new coordinates is nonzero. In the lifted rank-three lattice the
primitive outside generator therefore has height >=t+1/3. The reduction of this
generator is independent of the old plane by the earlier lifting lemma; the
nonzero old-class condition survives replacing it by any independent code row.

For the no-new-norm-four family, height <7/2 would, after old-plane rounding,
produce an integer row of norm squared <6. It is balanced because its coordinate
sum is a multiple of q with absolute value <sqrt(6H)<q in the production range.
Girth four forbids nonzero support below four, and balanced squared norms are
even. The only remaining possibility is a norm-four row outside the old plane,
excluded in this family. Thus height >=7/2 is justified. Original short rows
inside the old plane are not excluded by this reasoning.

A new norm-four row is unit on four positions and nonzero at all t new positions.
There are at most 3*choose(6,4-t) such lines for t<=4. Each line determines at
most one normalized coefficient code relative to the fixed anchor basis.
Using the generic complete kernel for each of these witness lines and the full
coefficient count for the complement is valid, though it can overcount.

The extension cutoff is 26, with 24*26^4<3329^2. Nonzero four-minors divisible
by q would have volume <=sqrt(24)*26^2<q, so short representatives span at most
three real dimensions. Saturation of that lifted lattice has index prime to q
and reduces into the coefficient code, as in the old lifting argument. The
unextended cutoff40 also satisfies sqrt(24)*40<q, preventing an additional
short real direction outside the old plane. All full positive tails and periodic
terms are retained. The relevant balance inequalities hold for every H=6+t
used by the production loop, including its precomputed bounds.

## Cover factors and production addback

For rank r=4, fixing the least outside point gives coefficient bound
sum_(a=3)^4 choose(4,a)q^(a-1). There is no point-choice factor for that point;
the remaining h-7 points have at most q^3 choices each. Taking the minimum
with the unextended anchor bound remains complete.

For r>4, connectedness gives a crossing fundamental circuit meeting both the
fixed anchor basis and its basis extension. With t new points its union rank
is t+3, so extra=r-t-3. Girth four requires a>=max(1,4-t). The coefficient bound
is sum_a choose(4,a)q^(t+a-2). Position factors are choose(h,6)*180,
choose(h-6,t), and choose(h-6-t,extra). The residual completion exponent is
(r-1)(h-r-3), and the existing contraction multiplicity is extra+1. These
match `envelope`. The t=2 part is minimized with the old parallel and marked
covers only after the t>=3 parts are retained, just as required by the
no-large-crossing dichotomy. Rank r=h-2 has a proper nullity-two anchor and
would force all outside positions to be coloops; its connected stratum is zero.

The new `exclude_six_d24` flag removes only determinant24 from the exact
c=4,H=6 table. Its production candidate uses the corresponding excluded
residual plus every earlier required anchor cover and the new complete
`six_d24[h,r]` cover. The old full candidate remains an alternative in the
minimum. Therefore deletion is not used as a free unconditional improvement.
The raw excluded calculation alone must continue to be treated as restricted.

## Verification

During this audit the dedicated checks were rerun:

* 1164 exact affine-plane centered-ball/pivot-injection cases over F3 and F5;
* 73 short projected-vector checks for the D24 plane;
* 180 balanced saturated D24 affine-anchor witnesses.

All passed. No existing file was edited, no new Lean theorem was added, and no
numerical claim about the current full residual is inferred from these checks.
