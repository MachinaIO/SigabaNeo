# Additive overlap energy and a sharp conditional power bound

This refines the two-layer power bound using a statistic of the actual incoming
marked lattice. It proves a conditional inequality, not the missing estimate of
that statistic along selected BKZ histories. The multi-height method is separate:
this note keeps only heights zero and one and controls their overlap distribution.

## Exact statistic, without a selected-winner distribution

Condition on the entire incoming history and retain the fresh-column hypothesis
of [the two-layer transition](wall1_two_layer_power_drift.md). Write H=K/M for
the finite abelian mark group, h=|H|, D for its nearest-distance function, and
B>=1 for a history-measurable lower bound on every outgoing test radius. Set

    A={v:D(v)>B}, C={v:D(v)>sqrt(B²−1)},
    p=|A|/h, r=|C|/h, X(u)=|A intersect (C−u)|/h.

The actual outgoing void satisfies p'_u<=X(u)<=p, for any selected primitive
winner. For p>0 put Y=X/p. Then E Y=r and 0<=Y<=1. Define the difference
multiplicity R_A(d)=#{(a,a') in A²:a−a'=d}, and similarly R_C. Double counting
ordered pairs in the intersection proves the exact identity

    E X² = h^(-3) sum_d R_A(d) R_C(d),
    eta = Var(Y) = h^(-3) sum_d R_A(d)R_C(d)/p² − r².       (1)

This is cross additive energy, not an independence assumption on the sets.
With normalized Fourier coefficients hat f(chi)=h^(-1)sum_v f(v)conj(chi(v)),
finite character orthogonality gives equivalently

    p² eta = sum_(chi != 1) |hat 1_A(chi)|² |hat 1_C(chi)|². (2)

Thus a bound on their common nontrivial Fourier mass suffices. The universal
variance bound is 0<=eta<=r(1−r). The intersection lower bound further gives
Y>=L=max(0,(p+r−1)/p), hence eta<=(r−L)(1−r): take expectations in
(Y−L)(1−Y)>=0. This improves the universal bound when p+r>1, but does
not supply the needed history-specific small-energy estimate.
For any positive integer k the exact higher overlap identity is

    E X^k = h^(-k−1) sum_(a_1,...,a_k in A)
                         |intersection_j (C−a_j)|.        (3)

Repeated a_j are included, since this is an ordinary power moment.

## Sharp conversion from variance to the 24th moment

For every real k>=2, 0<r<1, and 0<=eta<=r(1−r), define

    b=r−eta/(1−r),
    F_k(r,eta)=[eta+(1−r)² b^k]/[eta+(1−r)²].             (4)

Then E Y^k<=F_k(r,eta). This is the best upper bound using only the mean,
variance, and interval [0,1]. For r=0 or r=1 the variable is deterministic;
use F_k=r^k. If p=0 the outgoing void is zero.

Proof. For f(x)=x^k, let

    Q(x)=f(b)+f'(b)(x−b)+K(x−b)²,
    K=[f(1)−f(b)−f'(b)(1−b)]/(1−b)².

Taylor's integral remainder divided by (x−b)² equals
k(k−1) integral_0^1 (1−t)(b+t(x−b))^(k−2) dt.
For x in [0,1] it is at most its value at x=1, since k>=2. Hence f<=Q,
including x<b. The law supported on {b,1} with mass
eta/[eta+(1−r)²] at 1 has exactly the prescribed mean and variance.
It agrees with Q at both support points. Expectations of the quadratic Q
are determined by those two moments, proving (4) and sharpness.
The claim is not made for 1<k<2.

Consequently the actual conditional transition obeys

    E[(p'_U)^k | incoming history] <= p^k F_k(r,eta).       (5)

At zero variance this gives p^k r^k; at maximal variance it recovers p^k r.
This interpolates using an exact geometric statistic of the incoming lattice.

## How much energy control would offset the shell loss?

Let P>0 be the incoming void at its actual current radius and a=p/P.
The sufficient power-drift condition is

    a^24 F_24(r,eta)<=1.                                  (6)

Since b<=r and the denominator in (4) is at least (1−r)²,
F_24<=r^24+eta/(1−r)². Thus a convenient sufficient variance budget is

    eta <= (1−r)² [a^(-24)−r^24].                         (7)

It is meaningful when ar<=1. Jensen gives E Y^24>=r^24; if ar>1,
no refinement of this overlap moment alone can establish (6). Actual projection
could still reduce the void further, which (5) deliberately does not exploit.
For the previously proposed conditional value r=0.28:

| Shell ratio a | Sufficient eta budget from (7) |
|---|---:|
| 1.10 | 0.05263087000046114 |
| 1.30 | 0.000955046544291536 |
| 1.64 | 0.0000036175341229623103 |

These are conditional requirements, not measured statistics of a BKZ history.
The last shell ratio is illustrative of a substantial loss; neither r=0.28 nor
these ratios have been established jointly at a reachable history. The older
bound p^24 r tolerates only a<=r^(-1/24), about 1.05447 at r=0.28.

## Actual lattice balls can saturate the two-moment bound

A high mark rank and central symmetry do not by themselves provide further
moment savings beyond (4). Here is an actual nearest-distance construction,
not an arbitrary radial profile. For odd q>=5 let epsilon=1/100 and set

    M=q Z direct-sum epsilon Z^399,
    K=  Z direct-sum (epsilon/q) Z^399.

Then H is (Z/qZ)^400. With centered residues j_i, the squared distance is

    D(j)²=j_1²+(epsilon/q)² sum_(i=2)^400 j_i².

The inactive contribution is at most 399 epsilon²/4<0.01. Take B²=1.01.
Exactly A consists of marks with j_1 not in {0,1,−1}, and C consists of
marks with j_1 !=0. Both are centrally symmetric complements of genuine
lattice distance balls. They depend on one mark coordinate despite rank 400.

Here p=(q−3)/q and r=(q−1)/q. Over uniform U,

    Y=1                         with probability 3/q,
    Y=(q−4)/(q−3)               with probability (q−3)/q,
    eta=3/[q²(q−3)],
    E Y^24=3/q+(q−3)/q * ((q−4)/(q−3))^24 = F_24(r,eta).

For q=5 this moment is 0.6000000238418579 (eta=0.06), while the crude
bound is 0.8. For q=3329 it is about 0.9928155001159314 even though eta is
about 8.139e−11: r is itself close to one. The number of inactive coordinates
does not create independent overlap savings. This is not a claim that the
example is a reachable BKZ state or has the required corridor determinant,
Gram–Schmidt profile, or selected winner. Those extra constraints may exclude
it. It does prove that mark rank, symmetry, and unrestricted lattice-ball
geometry alone cannot improve the sharp two-moment bound.

## Verification and remaining obligation

Run `python3 docs/research/scripts/wall1_overlap_energy_drift.py`.
It checks 102 actual rectangular marked lattices/radii (q=3,5,7; dimensions
one and two), exact difference energy and moments 2,4,24, the majorant on
rational grids, exact two-point extremizers, the rank-400 constructions, and
the displayed sufficient budgets. All 1411 exact assertion groups pass.
Floating-point output is presentation only; assertions use rational arithmetic.
The proofs above establish the unrestricted statements, not the finite tests.

Application still requires a conditional, history-valid estimate of (1) or (2),
together with p/P and r at the moving radii. Fresh-column uniformity must hold
under the chosen filtration; revisiting exposed BKZ columns is not covered.
An initial power-moment bound and stopping transfer also remain necessary.
No new selected-history failure probability, cost certificate, or Lean theorem
is claimed here.
