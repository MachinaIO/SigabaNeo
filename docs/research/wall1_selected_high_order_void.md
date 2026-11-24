# High-order void certificates with one shared next mark

Part 470 shows why the scalar second-moment certificate need not resolve a
very small void probability. This note supplies a finite high-order replacement
and an exact route to its selected factorial moments. It does not establish
those moments at width 506 or complete the BKZ history bound.

## A binomial reference polynomial

Fix an integer L>=1, 0<p<1 and 0<=t<=L. Set o=p/(1-p) and define

    K_j(z) = sum_{a=0}^j binom(z,a) binom(L-z,j-a) (-1/o)^a,
    D_t = sum_{j=0}^t binom(L,j) o^j,
    P_t(z) = (sum_{j=0}^t o^j K_j(z))/D_t.

All binomial expressions in z are polynomials. The generating function is
(1+u)^(L-z)*(1-u/o)^z. For X~Bin(L,p), the expected product of two such
generating functions is (1+uv/o)^L. Comparing coefficients proves

    E K_j(X)K_k(X) = 1_{j=k} binom(L,j) o^(-j),
    P_t(0)=1,                 E P_t(X)^2=1/D_t.

Thus 1_{z=0}<=P_t(z)^2 for every real z. Orthogonal expansion and
Cauchy--Schwarz also show that this is the least reference squared norm
among degree-at-most-t polynomials with value one at zero.

Let c_j=Delta^j(P_t^2)(0)/j!, so P_t(z)^2=sum_{j=0}^{2t}c_j(z)_j.
For ANY event E and integer count Z in [0,L], let a=Pr(E) and
M_j=E[1_E(Z)_j]. Then the exact, unconditional identity is

    E[1_E P_t(Z)^2]
      = a/D_t + sum_{j=1}^{2t} c_j [M_j-a(L)_j p^j].       (1)

Selection need not be independent of Z. The reference p need not equal
an actual success probability. Verified bounds
|M_j-a(L)_j p^j|<=epsilon_j give the void upper bound

    Pr(E,Z=0) <= a/D_t + sum_{j=1}^{2t}|c_j|epsilon_j.     (2)

Keeping signed corrections or proving cumulant cancellations may improve
on (2). Parameters and candidate count must be fixed on the stratum where
(1) is used; an adaptive choice requires its own partition or argument.

## Factorial incidences preserve the shared fresh column

Fix a proposed chronological flag, its base (E_0,F,S), and a finite list
of L candidate representatives in the actual quotient. Let D be a set of
J distinct nonzero heights modulo q and let U be the single fresh uniform
quotient mark. On U!=0 define

    I_i = 1_{lambda(z_i) in {jU:j in D}},     Z=sum_i I_i.

Distinct heights give disjoint events for each candidate, because U!=0.
Consequently (Z)_k is the sum over ordered distinct candidate indices and
all assignments of heights of their joint hit indicators. Candidate indices
remain distinct even if representatives or quotient labels coincide.

Write a quotient candidate as (x_Q,y). Extend the original residual map by
ONE additional input coordinate whose image is U. A hit lambda(z_i)=j_i U
is precisely the quotient graph equation (x_Q,y,j_i). All simultaneous hits
use that same coordinate. Append zero to old full competitor equations and
fixed E_0,F vectors. The auxiliary S-component of the new column is unused
and integrates to one. Thus the existing fixed-quotient evaluator computes
each joint term with the old full selection constraints preserved.

For every term, impose U!=0 by subtracting the same incidence with the
additional quotient equation (0,...,0,1), namely U=0. Apply the full selected
competitor exclusion to both terms, retaining its coefficients. This gives
exact unconditional M_k for the event consisting of the selected flag and
U!=0. In particular M_0=(h-1)/h times the selected-flag mass, for h=|K/M|>1,
by freshness conditional on the complete old history. It is not a new
uniform-law assertion after selecting the next winner.

If the candidates are genuine projected points of norm at most R and the
chosen integer heights satisfy R^2+max_j j^2<c^2 with c>1, Z>0 supplies a
next-lattice vector shorter than c. The zero mark also supplies a height-one
unit vector. Hence (2) bounds the joint next-winner tail on this selected
flag. The strict radius margin, complete flag selection, and coverage of
all relevant flags are still required. For a trivial quotient the tail at
c>1 is zero directly.

## Exact checks and what their numbers mean

`scripts/wall1_binomial_void_kernel.py` verifies 126 binomial kernel cases,
1224 polynomial evaluations and 1008 selected transfer identities, including
non-binomial laws. Independent mathematical review verifies the general
orthogonality and transfer arguments.

For the REFERENCE values K=3329^2-1, L=58*K and p=J/K, the least t giving
1/D_t<1.951e-12 is 11,8,7,6,5 for J=1,2,4,8,16 respectively. All comparisons
use exact rational arithmetic. These are not computed candidate counts or
moments in the production history. The comparison tolerance is the rounded
whole remaining history allowance, not a per-transition allocation. Summing
flag contributions and connecting the resulting tails to stopped drift must
still respect that total allowance. A degree-t kernel needs moments through
2t; in particular the single-height reference needs moments through 22.

The checker also measures sensitivity. If all relative moment errors satisfy
|M_j-a(L)_j p^j|<=a*epsilon*(L)_j p^j, the error term is at most a*epsilon*S,
where S=sum_{j>=1}|c_j|(L)_j p^j. At J=1,t=11 the available common tolerance
is about 3.2831e-19; at J=8,t=6 it is about 4.7418e-16. These are sufficient
precision requirements for this absolute-error transfer, not proven errors
or necessary requirements for every possible proof method.

Increasing J cannot be treated as a free increase of the mean. Even the
volume surrogate in dimension 505 at c=30.5 gives common-radius gain

    J*((c^2-J^2)/(c^2-1))^(505/2)

strictly below one for every integer J=2,...,30, as checked by squaring and
exact rational comparisons. This is a volume diagnostic, not a lattice
point-count theorem. Real candidate counts and all radius constraints must
be supplied before using the favorable multi-height reference numbers.

`scripts/wall1_shared_mark_factorial.py` checks the incidence construction
on q=3, two output coordinates and the partial gate A!=0. Its four candidate
indices and two heights give unconditional moments

    (M_0,...,M_4)=(64/81,64/81,8/27,0,0).

All 81 rank-assignment terms agree with direct enumeration of all 81 (A,U)
pairs. A two-axis joint event has shared-mark mass zero, whereas independent
marks would give 32/729. The gate is not a complete winner/history event.
Independent review also verified the single-column construction, unused
S-component and nonzero-mark subtraction. The flag must be chronological
and contain no lookahead into the new column. The parent reran both checkers.
No production moment-error envelope, later
history charge bound, or Lean proof is supplied by these finite checks.


Part 472's [fresh-mark elimination](wall1_shared_mark_elimination.md) rewrites
the joint hit terms using only old quotient collisions. On the necessary old
minimum gate, geometrically nonzero candidates of radius less than c cannot
have zero labels. This makes the first factorial-moment error exactly zero
for p=J/(h-1); higher-order selected errors remain unproved.
