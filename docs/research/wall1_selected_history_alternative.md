# A stopped-potential route for selected histories, and its exact obstruction

This investigates avoiding a sum over all selected flags by controlling a
process along the actual history. It proves a finite stopped-drift lemma and
exhibits a graph-lattice collision counterexample to the shortcut from
fixed-time moment bounds to a time-uniform martingale bound. It does not
prove the required BKZ drift inequality or an impossibility of BKZ success.

## 1. A sufficient certificate without enumerating flags

Let F_0 subset ... subset F_T be the actual information filtration, including
all information needed to determine the current selected lattice, cylinder,
radius, and statistic being used. Let B_i be an F_i-measurable bad event.
Suppose Phi_i is nonnegative, integrable, F_i-measurable and Phi_i>=1 on B_i.
Suppose further that c_i>=0 is F_i-measurable and, before the first bad event,

    E[Phi_(i+1) | F_i] <= Phi_i + c_i,             0<=i<T.       (1)

Then, with tau the first bad index (T+1 if none),

    Pr(any B_i) <= E Phi_0 + sum_(i=0)^(T-1) E[1_(tau>i)c_i]
               <= E Phi_0 + sum_(i=0)^(T-1) E c_i.             (2)

No Markov-state assumption, independence of selected flags, or count of
possible histories is needed. The filtration must be the one for which
(1) is actually established; it cannot be chosen afterward to hide selection
information while still treating the bad event as observable.

**Proof.** Z_i=Phi_(min(i,tau)) is adapted. On tau<=i it has zero next
increment; on tau>i its conditional increment is at most c_i by (1).
Thus E Z_T <= E Phi_0 + sum_i E[1_(tau>i)c_i]. On tau<=T, Z_T=Phi_tau>=1;
on its complement Z_T>=0. Therefore the probability of a hit is at most
E Z_T. This proves (2) by a finite telescoping sum. There is no optional-
stopping limit or bounded-increment hypothesis hidden in this argument.

Equation (1), rather than a list of fixed-time expectations, is the new
obligation. A low-dimensional summary could be used if its proposed drift
bound holds conditionally on the *full* history. It need not be Markov, but
a drift formula under an unrelated distribution for that summary is not enough.

## 2. Exact connection to the current occupancy certificate

Use the selected-cylinder quantities from `wall1_flag_occupancy.md`:
N_i=|C_i|>0, J_i=sum_c n_(i,c)^2, and h=q^400. The deterministic identity
and Cauchy--Schwarz give

    b_i <= 1 - N_i^2/(h J_i),
    D_i := (18/7)*(h J_i/N_i^2 - 1) >= 0.                    (3)

Consequently b_i>0.280 implies D_i>1. The bad-history event is therefore
contained in the event that D_i exceeds one at some required draw. Applying
(2) with Phi_i=D_i would be valid if its conditional drift were proved.
The current cylinders contain zero, so N_i>0; in any variant allowing an
empty candidate set it must be treated as a separate bad event.

More generally choose an actual-history potential Phi_i=P_i(J_i,N_i) which
is nonnegative and at least one when 720 h J_i>1000 N_i^2. A centered square
or a higher-order nonnegative polynomial can be used; the normalization may
depend on the current state. One would then need to prove (1) for that
*normalized state-dependent potential* under the actual append-and-select
transition. For draws15 through404, a concrete sufficient condition is

    E Phi_15 + sum_(i=15)^403 E[1_(tau>i)c_i] <= epsilon_hist.  (4)

The chosen epsilon_hist must fit the current shared remaining allocation
after the draw14 error is paid. No value of epsilon_hist is certified here.
One must not assign the whole shared budget to (4) while also spending it
on the unfinished draw14 terms.

This formulation avoids an explicit global flag enumeration. It replaces
that enumeration by a uniform or averaged **conditional transition** estimate.
The complete-transcript lemma in `wall1_adaptive_bridge_audit.md` supplies
fresh unused linear randomness when its hypotheses hold, but does not itself
prove (1), because both the next cylinder and its normalization are selected.

## 3. A graph-lattice counterexample to the fixed-time shortcut

Let q>=3 be prime and let a be uniform in F_q. Consider the genuine graph
lattice

    L_a = {(x,y) in Z^2 : x=a*y mod q}.

For t=0,...,q-1 choose the two-point candidate set
C_t={(0,0),(t,1)}. Its quotient labels are 0 and t-a. Hence its ordered
collision count and associated nonnegative statistic are exactly

    J_t=2+2*1_(a=t),       Z_t=(q/2)*(J_t-2)=q*1_(a=t).       (5)

For every fixed t, E Z_t=1. Nevertheless max_t Z_t=q with probability one.
Thus fixed-time nonnegative mean-one bounds do not supply a supermartingale
or a bound Pr(max Z_t>=q)<=1/q. This is a collision-statistic example, not
an arbitrary unrelated adapted-selection paradox.

There are two distinct failures to check:

* If the filtration records no information about a, Z_t is not measurable
  and the first collision is not a stopping time: {tau<=0}={a=0} is neither
  empty nor the whole sample space.
* If collision answers are observed so that Z_t is adapted, the process
  is not a supermartingale. After misses at0,...,t, the current Z_t is zero
  while E[Z_(t+1)|all those misses]=q/(q-t-1)>0.

The counterexample uses deterministic candidate sets and repeated queries
of the same latent linear direction. It does not claim that these sets are
BKZ-selected cylinders, or that BKZ cannot satisfy a stronger drift theorem.
It does show that the fixed-candidate collision laws already in the project
cannot be promoted to a stopped maximal guarantee without a new condition.

There is also an exact wealth obstruction. For any filtration making these
collision events observable, a nonnegative supermartingale M_t satisfying
M_t>=q whenever a=t must have E M_0>=q. Stop at the first collision, which
occurs surely. The same finite stopped-increment argument gives
q<=E M_tau<=E M_0. Therefore no such process can start with mean one.
Adaptation cannot be repaired merely by assigning the name 'martingale' to
the family of fixed-time witnesses.

## 4. Why the uncentered first-moment potential is too expensive

Even in an ideal fixed-candidate reference model, Phi_i=D_i from (3) is
unlikely to give the tiny required budget. Suppose N fixed points have
pair-collision probability1/h (as for distinct input residues under a
uniform affine hash). Then

    E J = N + N(N-1)/h,
    E D = (18/7)*(h-1)/N.                                    (6)

For example, N/h=58 and h>=3329 give E D>0.04, already far larger than a
10^-12-scale allocation before paying any drift. This is an exact statement
about that reference model and the *linear* potential D. It is not the
expectation of an actual selected cylinder, and not a lower bound on failure
probability or on all possible potentials.

Thus a useful version of (4) would need a centered/higher-order potential
whose initial expectation is tiny, plus control of its conditional drift.
The existing high-order fixed-ball calculations address an initial or fixed
law; they do not automatically control this drift through selected projection
steps. This is the precise remaining analytical requirement for this route.

## 5. Verification and scope

Run `python3 docs/research/scripts/wall1_selected_history_alternative.py`.
It checks (5) exactly for q=3,5,7,11, including the conditional law after
misses; verifies (2) on twelve nontrivial finite binary-tree potential cases;
and checks (6) by exhaustive label assignments for twelve small cases.
All arithmetic is integer or rational, with no sampling.

The general proofs are the finite conditional-expectation arguments above.
The script is a regression check, not a high-dimensional probability proof.
No production envelope, BKZ algorithm, Lean file, or existing research note
is modified. The result is a concrete sufficient conditional-drift theorem
and a verified obstruction to a tempting unsupported inference; no new
numerical selected-history bound is obtained.
