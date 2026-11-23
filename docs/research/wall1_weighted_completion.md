# Weighted completion through affine-span collision energy

This gives an alternative to a worst-case ball-slice bound: control the weighted
completion moment by an exact reference moment and the collision energy of two
weighted basis descriptions. No independence of a selected span is assumed.
The first-moment estimate is sharp in an exact fixed-anchor example. The same
method applies to powers and falling factorials, but estimating the needed
energies and reference moments at the production parameters remains open.

## 1. An exact weighted-span inequality

Let B be the centered radius-R input ball in F_q^n, or any fixed finite set.
Let Omega be a finite reference family of affine d-planes, of size L, and put
C(U)=|B intersect U|. A configuration X contains the fixed anchor, any additional
basis, and any other data retained in its weight. Let w(X)>=0, let U(X) belong
to Omega, and assume Z=sum_X w(X)>0. Repeated descriptions of the same plane
are allowed and must retain their actual weights. Define

    W(U) = sum_(X: U(X)=U) w(X),
    E = sum_(X,X') w(X)w(X') 1{U(X)=U(X')}
      = sum_U W(U)^2,
    chi = L E/Z^2 - 1.                                           (1)

For every real function f on Omega, let mu_f and v_f be its mean and variance
under the uniform reference law. Then

    | E_w f(U(X)) - mu_f | <= sqrt(v_f * chi),                    (2)

or, without normalization,

    sum_X w(X)f(U(X)) <= Z mu_f + sqrt(v_f*(L E-Z^2)).             (3)

Proof: the actual reference-density ratio is ell(U)=L W(U)/Z. Its mean is one
and E_uniform[(ell-1)^2]=chi by (1). The difference of means is exactly
E_uniform[(ell-1)(f-mu_f)]. Apply Cauchy–Schwarz. This holds for arbitrary
weights, including actual joint-incidence weights that depend on the complete
basis. It does not replace those weights by an independent random-plane law.

The collision event in (1) has an algebraic test. If X and X' each specify an
affine basis of rank r=d+1, their planes agree if and only if the concatenation
of their augmented vectors (1,y) has rank r. Thus E is a weighted *same-span
rank-collision sum*. Any unused decorations or output data in X must still be
summed with their true weights. Counting undecorated bases uniformly instead
would calculate a different E.

This is not a bound based only on the support size of a selector. It identifies
one concrete quantity whose upper bound would certify a gain over the uniform
completion cap. If mu_f<T and v_f>0, it suffices to prove

    L E/Z^2 - 1 <= (T-mu_f)^2/v_f                                (4)

to obtain E_w f<=T. An upper bound on chi is needed; its nonnegativity alone
provides no useful improvement.

## 2. Unrestricted affine-plane reference: closed first two moments

Take Omega to be all affine d-planes in F_q^n. Write Q=q^n, N=|B| and p=q^d/Q.
For a fixed point, containment probability is p. For two distinct points it is
p(q^d-1)/(Q-1): conditional on containing the first, the direction of the second
is contained in a uniform d-dimensional linear subspace with that probability.
Counting ordered independent vectors proves this ratio directly. Consequently

    mu_C = p N,
    v_C = p(1-p) N(Q-N)/(Q-1).                                  (5)

These formulas depend only on N, not on the shape of B. When Q=1 the space is
deterministic and the variance is zero; production has Q>1. Applying (2) gives

    E_w C <= min(M_d, pN+sqrt(v_C*chi)),                          (6)

where M_d is the existing uniform ball-slice bound. In a fixed-anchor application,
this unrestricted reference can pay a needless cost for conditioning on the
anchor; the next section removes that cost exactly.

## 3. Fixed-anchor reference and angular occupancy energy

Fix an affine a-plane S=s0+V0, and let Omega consist of all affine d-planes
containing S, where a<=d<=n. Put D=n-a and k=d-a. Every U in Omega is the preimage
of a unique k-dimensional linear subspace W of the quotient F_q^n/V0 after
translating s0 to zero. Choose quotient coordinates once; this does not assume
any Euclidean invariance of the ball.

Let b_v count points of B with quotient v. In particular b_0=|B intersect S|.
For each projective direction ell in the D-dimensional quotient put

    T_ell = sum_(v nonzero in ell) b_v.

Then pointwise, including all multiplicities within quotient fibers,

    C(U) = b_0 + sum_ell T_ell 1{ell subset W}.                   (7)

For a uniform k-subspace W, put

    p1 = (q^k-1)/(q^D-1),
    p2 = p1*(q^k-q)/(q^D-q)  (k>=2),                            (8)

and p2=0 for k<2. When D=0 the reference has one member and C is deterministic.
For D>=1, p1 is the containment probability of a direction; p2 is the joint
probability for two distinct directions. To prove (8), count ordered independent
vectors inside W and in the entire quotient; transitivity follows by extending
an independent list to a basis, with no probabilistic assumption on X.
Set T=sum T_ell and A=sum T_ell^2. Then

    mu_C = b_0+p1*T,
    v_C = p1*(1-p1)*A + (p2-p1^2)*(T^2-A).                     (9)

For D=1 there is at most one direction, so T^2-A=0; the convention p2=0 avoids
a zero denominator. Both formulas include k=0 and k=D. The second term may be
negative and must not be discarded when claiming an exact variance. The geometry
now enters through the projective fiber energy A, rather than an unjustified
random orientation of S.

Use this reference in (1)–(3), with the actual basis-extension weights conditional
on the fixed anchor data. The same-span test can equivalently be performed on
quotient basis vectors, where their concatenated rank must equal k. One may
apply (3) for each anchor separately and then sum its nonnegative upper bounds;
there is no assumption that the anchors have a uniform distribution.

## 4. Higher completion moments: a mean is not enough

Production has several redundant positions and requires E_w[C^j], or a suitable
distinct-completion count. In general (E_w C)^j is a **lower** bound on E_w[C^j]
for j>=1, so the first-moment improvement cannot be raised to the jth power.
Apply (2) with f=C^j instead, using its own reference variance. There is an exact
rank-enumerator expression for every required reference moment under the
fixed-anchor law.

For t>=0 define

    rho_t = product_(i=0)^(t-1) (q^k-q^i)/(q^D-q^i)  if t<=k,
            0                                      if t>k,
    rho_0=1.                                                     (10)

A fixed quotient t-subspace is contained in W with probability rho_t. This
again follows by counting ordered independent lists. For j>=1 let A_(j,t)
count ordered j-tuples from B, repetitions allowed, whose quotient images span
a t-dimensional space. Then

    M_j := E_uniform[C^j] = sum_t A_(j,t)*rho_t.                  (11)

Indeed C^j counts exactly these ordered tuples whose quotient span lies in W.
Therefore the valid power-moment bound is

    E_w[C^j] <= min(M_d^j, M_j+sqrt((M_(2j)-M_j^2)*chi)).         (12)

For falling factorials use distinct ordered tuples instead. Let D_(j,t) be their
rank counts and F_j=sum_t D_(j,t)rho_t, with F_0=1. The elementary overlap identity

    (C)_j^2 = sum_(i=0)^j choose(j,i)^2 i! (C)_(2j-i)             (13)

gives its exact second moment. The coefficient chooses the shared positions
in the two ordered lists and their matching. Thus

    E_w[(C)_j] <= F_j + sqrt(chi *
      (sum_i choose(j,i)^2 i! F_(2j-i) - F_j^2)).                (14)

Actual completions exclude previously used points. If every configuration forbids
exactly m distinct points lying in B intersect U(X), with m fixed, the number of
available points is exactly C(U(X))-m, regardless of the identities of those
points. Thus (C-m)_j IS a function of U and (2) applies to it. No independence
of the forbidden identities is required. Such a completion statistic need only
be defined on the actual weighted support; for reference averaging one can use
(max(C-m,0))_j, which agrees there and remains a nonnegative integer count.
If the reference also guarantees C>=m, the untruncated expression suffices.
A varying number of forbidden points, or points not all in B intersect U, would
instead require recording the intersection cardinality. Using (C)_j remains a
valid overestimate when exclusions are ignored. The separate pinned-completion
counting lemma is not claimed here.

Equations (10)–(14) cover production orders j=5,6,10 in principle. They require
reference moments up to order 2j, and (1) still requires weighted span collisions.
They are exact finite reductions, not an efficient evaluator or a numerical
bound at those parameters.

## Full-anchor degeneracy in the leading production branches

For the leading h=18,19,24 branches with anchor size H=r+2, the two-relation
anchor already has augmented input rank H-2=r. Its affine span S therefore has
dimension a=r-1, equal to the full support's affine dimension d. There are no
extra basis points: r-H+2=0. In the fixed-anchor reference, k=d-a=0 and Omega
contains exactly S. Even if many decorated descriptions X remain, all have
U(X)=S. Consequently

    L=1, E=Z^2, chi=0, C(U)=C(S),
    M_j=C(S)^j, v_(C^j)=0, E_w[C^j]=C(S)^j.                    (16)

The quotient rank formula gives the same result: rho_0=1 and rho_t=0 for t>0,
so only tuples already lying in S contribute. This is a proof of degeneracy,
not a favorable random-geometry estimate. The fixed-full-anchor CS bound is
an identity and yields no average geometric gain for these leading branches.
If m distinct already-used points belong to B intersect S, the exact same
conclusion holds for the remaining count C(S)-m and its falling factorials.

To gain in these branches one must either bound the deterministic occupancy
C(S) for each eligible anchor, or average over varying anchors using a common
reference and pay their actual induced tilt. Setting chi=0 separately after
fixing each anchor and then replacing its occupancy by an unconditional mean
would be invalid. The toy fixed-anchor improvements below have k>0; they do
not overcome this production degeneracy.

## 5. Exact examples and sharpness

For q=5 in F_5^2 take the centered ball R^2=2, with nine points. Give each ordered
pair of distinct ball points weight one and use its affine line as U(X). This
is a genuine geometry-dependent basis distribution. The 30 reference affine
lines have occupancy histogram

    C=0:4 lines, C=1:6, C=2:12, C=3:8.

Since each line has C(C-1) eligible ordered bases, Z=72 and E=336. Consequently

    mu_C=9/5, v_C=24/25, chi=17/18,
    E_w C=8/3,
    mu_C+sqrt(v_C*chi)=9/5+sqrt(68/75)<69/25=2.76.

The existing ball-slice cap in this example is M_1=2sqrt(2)+1, about 3.828,
not five; five is only the coarser q^d cap. Thus (6) supplies a strict improvement
without pretending the basis-induced line is uniformly random. The exact maximum
occupancy is three, but the weighted estimate even beats that worst-case value.

Now fix the anchor S={0}, choose one nonzero ball point with weight one, and
span its line with zero. The six reference lines through zero have occupancies
three on four lines and one on two. The weighted selector is supported on the
four lines with occupancy three. Here

    mu_C=7/3, v_C=8/9, chi=1/2, E_w C=3,
    mu_C+sqrt(v_C*chi)=3.                                       (15)

Thus the fixed-anchor first-moment inequality is attained by an actual
ball-conditioned basis selection, despite being nonuniform. This shows both
that the method can work and that its selection penalty cannot be omitted.
More generally the legal density tilt ell=1+t(C-mu_C), when nonnegative,
saturates (2): chi=t^2 v_C and the weighted mean is mu_C+t v_C.

## 6. Remaining application obligation

The current general two-relation bound evaluates valid anchor and basis
configurations with their joint-incidence weights, then uses M_(r-1)^j for
completion. Replacing that step by (12) or (14) requires, for each retained
anchor family, rigorous estimates of the corresponding weighted rank-collision
energy E and of the reference moments. Outputs already determined by a basis,
coefficient restrictions, and witness multiplicities belong to w and cannot be
discarded inside chi. The new formulas exhibit precisely where selection enters;
they do not assert it is small. A full exact computation of E is not automatically
cheaper than the original connected-incidence count.

For leading branches whose full span is already fixed by the anchor, (16)
shows that this reference has no averaging power at all. For nondegenerate
extensions, the fixed-anchor angular energy (9) is enough only for j=1. Production j=5,6,10
needs the higher rank enumerators in (11)–(14), or another rigorous bound on those
reference moments. No estimate for these actual high-dimensional quantities is
proved here, and there is no new global residual, selected-history, or BKZ bound.
The smaller toy numbers are not forecasts of the improvement at q=3329.

## Verification

Run `python3 docs/research/scripts/wall1_weighted_completion.py`.
All arithmetic is exact integer/rational. The script checks 29,920 ordered
basis-pair rank-collision tests; 1,290 fixed-anchor projective direction-pair
cases; the first and second reference moments; the first four power and
factorial rank-enumerator moments in the q=5 planar anchored fixture; the
factorial-square identity for j=1,2; and weighted CS bounds for both C^j and
(C)_j at j=1,2,5,6,10 in seven fixed-anchor fixtures. It also verifies exact
sharpness of the linear tilt and (15). An additional 1,570 exact checks cover k=0 with
weighted duplicate descriptions, powers j=1,2,5,6,10, and all forbidden subsets
of each fixed size on sets of up to eight points; their identities vary while
the remaining cardinality stays C-m.

Log: `/tmp/wall1_weighted_completion.log`. No production evaluator or existing
proof file was edited. These are paper proofs with finite exact checks, not
Lean formalization.
