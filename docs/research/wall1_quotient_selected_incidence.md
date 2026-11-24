# Selected incidence terms in the actual quotient

This extends the existing fixed-flag rank evaluator to constraints that live
only in the marked quotient. Full competitor membership and quotient-label
collisions are different events. Keeping them separate gives exact terms for
the selected mixed-moment certificate; their high-dimensional sum remains open.

## Two independent rank computations

Fix an admissible stratum (E,F,S) from
[the quotient law](wall1_fixed_quotient_law.md). In output coordinates
V=S direct-sum Q write A=(A_S,T), with dim S=s=dim E-dim F and dim Q=m-s.
For a raw vector z=(x_S,x_Q,y), put z_S=(x_S,y), z_Q=(x_Q,y). Let G be a
finite list of additional full-graph equations and D a list of quotient-only
equations (x_Q,y). Then the unconditional joint probability is

    P(G;D) = Pr(E_S intersect graph(A_S)=F_S,
                G_S subset graph(A_S))
             * Pr(E_Q,G_Q,D subset graph(T)).            (1)

The first factor is the existing saturated incidence probability in output
dimension s; the second is ordinary consistent-system incidence in output
dimension m-s. They are independent map components. Equivalently evaluate
the first conditional on containing F_S and the second conditional on
containing E_Q, and multiply by both containment probabilities. Include
all consistency checks and the possible extra intersection with E_S.

The projection E->E_S is injective on an admissible stratum, since its
kernel would be a pure output vector of E outside S. Thus exact kernel F_S
forces the S-component image to have dimension s and hence equal S. This
justifies using the existing saturation evaluator for the first factor.
Zero-dimensional components are allowed. If Q=0, all quotient labels vanish.

For candidates z,z' and a nonzero scalar t, define their quotient equations

    d_t=(x'_Q-t*x_Q, y'-t*y),  d_0=(x_Q,y).

The nonzero scalar collision term with the full equations G imposed is

    P(G;{d_t})-P(G;{d_t,d_0}).                          (2)

The subtraction removes zero labels. Adding d_t to G instead would impose
an extra S-component equation and count a different, generally smaller event.
Formula (1) is an unconditional mass including the stratum; it must not be
multiplied by that stratum weight a second time.

## Selected moments and rigorous truncation

For a proposed chronological flag, use the finite competitor list from
[selected flag moments](wall1_selected_flag_moments.md). On its containment
and saturation event, exact selection is absence of every full-graph
membership event in this list. For a subset I of competitors, let G_I be
the corresponding full equations. Formula (1) with D empty gives its base
mass. The first nonzero candidate moment uses

    A_N(I)=sum_z [P(G_I;empty)-P(G_I;{lambda_z=0})].

The ordinary collision moment A_J(I) uses (2) with t=1 and all ordered
candidate pairs. The scalar collision moment A_C(I) sums (2) over all
t!=0 as well. Candidate multiplicities are retained. These are exact
expectations of nonnegative counts times the imposed competitor events.

Full inclusion--exclusion yields the joint selected moments a,n,j,c_sc,
including the stratum probability. Odd-degree Bonferroni truncations give
lower bounds on n; even-degree truncations give upper bounds on a,j,c_sc.
The justification is pointwise: multiply the truncated avoidance indicator
by the corresponding nonnegative count before taking expectation. Although
the implementation of each term uses a zero-label subtraction, the complete
count being bounded is nonnegative. No independence assumption is used.

Set d=r(q-1)j+(1-r)c_sc for a scalar spectral bound 0<=r<=1. The
[selected-moment certificate](wall1_scalar_collision_certificate.md) bounds
the joint next-tail contribution for h>1 by

    ((h-1)/h)*[a-(q-1)*n^2/((h-1)*d)]                  (3)

when d>0, with the zero-coverage convention otherwise. Therefore verified
bounds a<=a_U, n>=n_L>=0, d<=d_U with d_U>0 give a sufficient upper bound
by substituting a_U,n_L,d_U on the right. These are bounds on joint moments,
not unselected moments with a selection mass multiplied in afterward.
Clip a negative odd-order bound for n to zero. If d_U=0, use coverage
lower bound zero and tail upper bound ((h-1)/h)*a_U. A negative resulting
bracket from purported bounds signals an inconsistency in those inputs.
For h=1 the next mark is zero and its height-one unit makes the tail at
c>1 empty; no division by h-1 is used.

The next-column uniformity and radius assumptions of that certificate
remain necessary. For a complete argument one must cover the canonical
selected flags, sum their actual disjoint contributions, and control any
discarded range. No useful truncation degree or width506 aggregate estimate
is established here.

## Finite lifts and actual quotient multiplicities

For fixed Gamma=L intersect U and Lambda=U intersect Z^n, the existing
[half-open Gamma strip](wall1_flag_occupancy.md) gives exactly
kappa=[Lambda:Gamma] raw representatives of every projected integer point.
With actual quotient labels V/S, those representatives all share one label.
Consequently the point counts in this certificate satisfy

    N=kappa*N', J=kappa^2*J', C_sc=kappa^2*C'_sc,

where primes count distinct projected points. Their common factors cancel
from the deterministic spectral certificate. Thus a fixed finite raw
cylinder can be used without arbitrarily choosing one representative.

The earlier raw-syndrome identity J_raw=kappa*J' counts different labels
and must not be substituted here. To omit the zero actual class, discard
every raw syndrome in S, not just the zero raw syndrome. Quotient zero-label
subtraction in (2) implements exactly that requirement.

## Implementation and verification scope

`scripts/fixed_quotient_graph_space.py` composes the two existing basis-based
`ConditionalGraphSpace` calculations. Callers supply coordinates with S
first in the output block; it does not infer the selected flag or quotient.
The distinct full and quotient constraint arguments preserve their meaning.

Run `python3 docs/research/scripts/wall1_fixed_quotient_incidence.py` for
finite-field enumeration checks and algebraic fixtures at q3329. The latter
test rank probabilities at the concrete modulus and dimensions, not actual
geometric competitor lists or the production failure budget. The product
formula and its zero-label subtraction received independent proof review.

The completed tests verify478 base strata against all81 small-field maps,
3346 additional full/quotient joint incidences and956 nonzero scalar
collisions. A two-competitor avoidance fixture additionally verifies the
complete selected moment sums and odd/even count bounds; it is an algebraic
fixture, not a claim that those two competitors encode a production winner.
At q3329,m400,d117,s12 the evaluator checks full incidence q^(-400),
quotient incidence q^(-388), and nonzero scalar collision
q^(-388)-q^(-776) exactly. Independent review also approved the truncation
and lift-multiplicity arguments. None of these tests evaluates the complete
geometric competitor lists or the selected-history sum at width506.

## End-to-end check with actual shortest selection

The width9,q3 example from [the fixed quotient note](wall1_fixed_quotient_law.md)
has L_A={(x,j):x=Aj mod3}, A in F_3^8, and proposed winner -3e_1.
Its complete selection event can be encoded by the6305 full membership
events (x,1) in L_A, where x ranges over centered eight-vectors with at
most seven nonzero entries. Every such vector has squared norm at most8.
Their absence is exactly the event that all entries of A are nonzero,
which, including all norm-three ties, is exactly selection of -3e_1.
This uses the complete shortest-vector argument, not a sampled competitor list.

Each event says A=x. Distinct competitors therefore have incompatible output
values for the same input1; all intersections of order two or higher vanish.
For every candidate count W the full selected expansion is consequently

    E[W*1_selected] = E W - sum_x E[W*1_{A=x}].

The checker `scripts/wall1_actual_selected_incidence.py` evaluates these
terms through `FixedQuotientGraphSpace`, with the same two fixed quotient
candidates (b,0),(d,-1) used in the selection-bias example. It separately
checks the result by direct shortest selection on all6561 raw columns.
This exercises complete selection, full versus quotient constraints,
nonzero-label subtraction and the mixed-moment bound in one computation.

The completed calculation gives joint moments
(a,n,j,c_sc)=(256,512,516,520)/6561, exactly matching direct enumeration.
The resulting conditional mixed-moment coverage lower bound is128/71045.
The generic incidence calls are cached by their exact constraint spans;
no sampled competitor or floating-point probability is used. The parent
reran the checker successfully. The exact selection-event compression and
its degree-one exclusion identity received independent mathematical review.

The special mutual exclusivity is a one-input property. General width506
competitors can impose compatible equations on many different input
directions. Their higher-order terms do not vanish by this argument, and
the enormous geometric lists are not constructed by this test. No scalable
selected-history computation or production probability is claimed.

## Overlapping actual-selection events

The checker `scripts/wall1_overlapping_selected_incidence.py` removes the
mutual-exclusivity restriction in a second finite example. Let q=3,
m=d=3 and w=(-1,-1,0,-1,0,0). Containment of w fixes the first column
of A to a=(1,1,0), with probability 1/27. Here E=F=span(w), S=0.
Put B={0, +/-e_1, +/-e_2, +/-e_3, +/-a}. There are twenty forbidden
events: either remaining column belongs to B (eighteen events), or the
two columns are equal up to sign (two events).

On all 729 first-column-conditioned matrices, absence of these events
is exactly selection of w under squared-norm, then signed lexicographic
ordering. The independent shortest-vector check enumerates all 232
nonzero integer vectors of squared norm at most three. This list is
complete because a coordinate of absolute value two already contributes
four. Exactly 18*16=288 matrices select w.

For full inclusion-exclusion, keep a dictionary c(G) of signed integer
coefficients indexed by canonical constraint spans. Initially c(F)=1.
For each forbidden vector b, replace each term c(G) by c(G) at G and
-c(G) at span(G,b), combining identical spans. An inconsistent span can
be discarded because its incidence event is empty. Induction on the
processed events proves that this dictionary represents the product of
their avoidance indicators, pointwise, on the base stratum. Consequently
it can be integrated against any candidate count using the joint evaluator.
This is a complete expansion; merging different degrees would not preserve
a degree-truncated Bonferroni calculation without also retaining degree.

The example finishes with 102 spans (ranks 1,2,3 have counts 1,20,81).
A compatible two-event intersection has probability 1/19683, so higher
intersections cannot be dropped. Using the six raw coordinate vectors as
quotient candidates, the evaluator and direct enumeration both give

    (a,n,j,c_sc) = (288,1728,1728,1728)/19683
                 = (32/2187,64/729,64/729,64/729).

These are unconditional masses, including the first-column constraint.
The parent reran the exact checker successfully. This verifies actual
selection with compatible overlaps; it supplies no bound on the number
of spans or the geometric competitor count at production width 506.

## Certified partial competitor exclusion

Let H be the complete finite competitor list for a fixed proposed flag,
B its base containment and saturation event, and P any subset of H.
Write E_P for absence of the events in P and E for absence of all H.
For a fixed nonnegative candidate count W define the unconditional terms

    M_W(P) = E[1_B 1_{E_P} W],
    R_W(P) = sum_{b in H\P} E[1_B 1_{E_P} 1_b W].

The pointwise union bound, multiplied by the nonnegative count, proves

    max(0, M_W(P)-R_W(P)) <= E[1_B 1_E W] <= M_W(P).       (4)

Any certified upper bound for R_W may replace it. This is exclusion of an
arbitrary subset of competitors, not truncation by intersection degree.
Both terms can be evaluated by the full grouped expansion for E_P: for
R_W add each remaining competitor equation to each grouped span before
integrating W. All signed coefficients must be retained. In particular,
substituting individual upper incidence estimates into a signed sum is
not valid without sign-aware interval arithmetic.

Use (4) with W=1,N,J,C_sc. Set a_U=M_1(P), take n_L from the lower
bound for N, and set d_U=r(q-1)M_J(P)+(1-r)M_C(P). Substitution into
(3) gives a certified tail upper bound, with its existing zero-denominator,
fixed quotient, fresh next-mark and radius conditions. Candidate counts
must be the same functions throughout the partial events; they cannot be
redefined after each exclusion. There is no division by survival mass.
For nested processed subsets, upper moments decrease. Running maxima of
lower bounds and running minima of valid tail bounds are also valid.

A coarse alternative avoids weighted residual evaluation. For L candidates
counted with multiplicity, N<=L and J,C_sc<=L^2: a pair of nonzero labels
has at most one matching nonzero scalar. Therefore a certified bound
eta >= sum_{b in H\P} Pr(B intersect E_P intersect b) gives
R_N<=L*eta and R_J,R_C<=L^2*eta. Dropping E_P yields a weaker valid eta.
This alternative may be far too large; it is not an assertion that the
unprocessed geometry has small mass.

Independent mathematical review verified (4), the mixed-moment substitution
and unconditional normalization. At width 506 a complete competitor cover
and a useful residual bound are still required. If the remainder dominates
M_N, the lower bound is zero and this route gives no coverage improvement.

The exact checker `scripts/wall1_partial_exclusion_certificate.py` tests all
21 prefixes of the twenty-event overlapping example, for all four moments.
Every interval contains the independently enumerated selected moments;
upper monotonicity and running lower envelopes pass. Already P empty gives
n_L=1156/19683 and a witness-based tail upper bound
12194510/351282501, below the no-coverage bound 26/729. With all events
processed, the bound is 448/59049. Each selected matrix has six distinct
nonzero scalar label lines, so this terminal value equals the miss mass
for these signed witnesses together with the always-covered zero mark.
It is not asserted to equal the full shortest-vector tail: additional
geometric witnesses may cover more marks. The parent reran the checker.
