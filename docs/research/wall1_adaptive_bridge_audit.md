# Adaptive linear transcripts: the exact bridge and its limitation

This note verifies a separate approach to the selected-prefix problem: retain
all linear information exposed by an adaptive algorithm, rather than replacing
its selected lattice by an independent lattice. The bridge below is exact, but
it does not give the outstanding width-506 history bound. It adds no Lean theorem.

## 1. A deferred-decisions theorem that allows adaptive queries

Let A be uniform among maps F_q^d -> F_q^m. Fix the private coins of an algorithm
independent of A. At a node of its decision tree the algorithm chooses a vector
y using only earlier answers, receives the **entire** answer Ay, and may stop
using only these answers. Fix any reachable, positive-probability transcript

    tau = ((y_1,x_1), ... , (y_k,x_k), stop),
    V_tau = span(y_1,...,y_k),  r_tau = dim V_tau.

Then its fiber is exactly

    {A : Ay_j = x_j for all j},                                      (1)

and has size q^(m(d-r_tau)). Its probability is q^(-m r_tau).
Conditional on tau, the restriction to any fixed complement W of V_tau is a
uniform linear map W -> F_q^m, independent of the already prescribed map on
V_tau. The complement is allowed to depend on tau: it is fixed on that fiber.

**Proof.** One inclusion in (1) follows from recording the answers. Conversely,
any map satisfying all the recorded equations follows the same first node and,
inductively, gives the same answer and therefore follows the same next node and
stopping decision. On V_tau the consistent equations specify a unique map.
Extend a basis of V_tau to the input space. The remaining d-r_tau images may be
chosen independently in F_q^m. This proves the count and conditional law.
In particular, a new query outside V_tau has a uniform answer, whereas a query
inside V_tau is already determined. This also proves the result at an adaptive
stopping time by applying it separately to each leaf. No independence between
queries is assumed. For randomized algorithms the argument applies after
conditioning on the independent coins, or with those coins included in tau.

This theorem is stronger than a fixed-list rank formula in that queries and
stopping may be adaptive. It is weaker than an assertion about a shortest-vector
history: recording a winner does not record the full answers to its rejected
competitors. Mixing transcript fibers can change the law.

## 2. Exact test for discarding the rejected competitors

Fix a consistent flag-containment event E, such as AY=X. Identify its remaining
uniform map with T in a finite set Omega. Let S be the event that the flag is
actually selected, including all shortestness, tie, and saturation tests. Put

    ell(t) = Pr(S | E, T=t),   s = average_t ell(t) > 0.

Private randomness, if any, is integrated out in ell. For every t,

    Pr(T=t | E,S) / Pr(T=t | E) = ell(t)/s.                        (2)

Thus the old uniform residual-map law survives **if and only if** ell is
constant on Omega. This is a necessary and sufficient condition, not a
consequence of the selected flag having small rank.

For a deterministic selector, ell is an indicator. If selection is nontrivial
inside E (0<s<1), the conditional residual map is necessarily nonuniform. Its
exact total variation distance from the old uniform law is 1-s, and its maximum
density ratio is 1/s. For an event B with p=Pr(B|E),

    max(0,(p+s-1)/s) <= Pr(B|E,S) <= min(1,p/s).                  (3)

Proof: the intersection B intersect S has mass between max(0,p+s-1) and
min(p,s). Dividing by s gives (3); (2) follows directly from Bayes' formula.
The total variation formula follows by summing the density difference on S
and its complement. Bounds (3) are attained whenever sets with the indicated
intersection sizes exist; no smaller universal multiplicative loss is possible.

The uniformity criterion can also be applied to a *coarser* residual variable Z:
replace ell(t) by Pr(S|E,Z=z). Nontrivial selection may preserve a truly unused
coordinate even though it changes the whole residual map. Consequently the
failure of global uniformity does not preclude the legitimate fresh-column
argument already used for the restart's incoming mark.

## 3. A shortest-vector example and an invertibility pitfall

For every odd prime q consider

    L_(a,b) = {(x,y,z) in Z^3 : x = ay+bz mod q},

with a,b uniform. Order sign pairs by squared norm and then the lexicographically
smaller signed vector. The proposed winner w=(0,0,-1) is contained precisely when
b=0. Among integer vectors of squared norm one, (-1,0,0) never belongs,
(0,-1,0) belongs precisely when a=0, and precedes w. Every nonzero integer vector
has squared norm at least one. Therefore w is globally selected exactly when
b=0 and a!=0. Its primitive generator gives saturation automatically.

Containment leaves a uniform on F_q. Selection leaves a uniform on F_q minus
{0}. Here s=(q-1)/q, total variation is 1/q, and the maximum density ratio is
q/(q-1). The winner has input rank one but its rejected competitor tests the
other input direction. There is no unexplored input direction in this example.
Adjoining an independent third input coefficient c that is never inspected
leaves c uniform even after this same selection event. This explicitly separates
the useful fresh-variable law from the invalid uniform selected-state law.
The q=3 case is consistent with the earlier selected-collision example in
[Selected flag moments](wall1_selected_flag_moments.md); this is not claimed
as a new counterexample to BKZ itself.

A separate finite-field check shows why a change-of-basis argument needs a
bijection of the **sample space**, not merely an invertible matrix at each input.
For uniform a in F_q set u(a)=a^(-1) if a!=0, and u(0)=1. Each multiplier u(a)
is invertible, but a*u(a) equals one with probability (q-1)/q. Hence data-dependent
invertibility alone does not preserve a uniform ensemble. This is an elementary
analogue, not a claim that this multiplier implements an integer BKZ operation.

## 4. What this approach would have to prove for the actual restart

For the incoming state at draw i, [Flag occupancy](wall1_flag_occupancy.md)
constructs a selected cylinder C_i and collision count J_i. The deterministic
certificate is

    720 q^400 J_i <= 1000 |C_i|^2  =>  b_i <= 0.280.               (4)

The fresh next mark remains uniform given the incoming history. It does not
make the history's retained lattice, cylinder, or radius independent of the old
matrix. The remaining task is an estimate for the actual selected-history law,
including Pr(max_(15..404) b_i > 0.280). The Part 384 shared residual allocation
is 2.6629e-12 for this term together with the remaining draw-14 contribution;
it is not a budget proved for the history term alone.

There are two valid ways to use this audit, each with a concrete unproved step:

* **Complete linear transcripts.** Implement the exact selection computation as
  full linear queries and retain its leaves. Theorem (1) gives each leaf's
  probability and unused-map law, but one must bound the expectation of the
  bad-history indicator or certificate over all leaves. A computation which
  reads the full matrix has r_tau=d and no unused randomness. Refining the
  transcript does not by itself improve the selected geometry.
* **Compressed winner history.** Keep the flag and its competitor exclusions.
  Formula (2) gives the exact correction. One must bound an event-specific
  selected numerator or prove an adequate likelihood bound for the particular
  statistic. Dropping competitors and asserting ell constant is refuted above.
  A generic bound 1/s is only useful if its loss fits the actual probability
  budget; neither that fact nor such a bound at width 506 is supplied here.

The existing [conditional collision law](wall1_flag_collision_law.md) and
[selected moments](wall1_selected_flag_moments.md) already retain the flag
weights and competitor exclusions. They provide exact finite expressions;
their aggregate width-506 estimate remains open. The Lean files
`ConditionalGraphProbability.lean`, `SelectedCollisionCertificate.lean`, and
`SelectedBonferroni.lean` cover respectively fixed-system rank probabilities
and finite selected-certificate inequalities. Reading their statements does
not establish the missing geometric identification or numerical history sum.

Thus this independently checked approach gives an exact criterion for when
deferred decisions can close the bridge, and rules out an unjustified shortcut.
It does not improve the current numerical remainder, prove a BKZ profile, or
supply a completed selected-history estimate.

## 5. Reproducible exact verification

Run `python3 docs/research/scripts/wall1_adaptive_bridge_audit.py`.
The script uses only integer and rational arithmetic for q=3,5,7. It checks:
all leaves of an adaptive query/stop rule against their full affine fibers;
every fresh direction at those leaves against the uniform output law; every
subset event in the shortest-vector example against (3); the exact total
variation and maximum-density formulas; the unused-coordinate marginal; and
the data-dependent invertibility counterexample. These are finite checks of the
paper proof, not a high-dimensional BKZ calculation or formal verification.
