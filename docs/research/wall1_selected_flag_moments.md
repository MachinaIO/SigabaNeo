# Retaining shortestness in the flag collision bound

Parts 264--265 give collision moments under containment and saturation of a fixed
flag. This note retains its actual shortest-vector comparisons as well. The result
is a finite signed sum with rigorous even-order upper bounds. It does not yet
evaluate the sum over flags at width 506.

## A finite list encoding exact selection

Fix the proposed chronological raw flag w_1,...,w_r, with the support appropriate
to each append, and assume its full subgroup Gamma is saturated in L(A). A prefix
of this basis is then saturated in its span as well: any lattice point in the
prefix span lies in Gamma and has zero coordinates in the later basis directions.
Let P_(j-1) project off the preceding flag, v_j=P_(j-1) w_j, and s_j=||v_j||.

At step j take all integer vectors z supported in the current raw prefix, reduced
in the preceding Gram--Schmidt half-open intervals, for which P_(j-1)z is nonzero
and precedes v_j under the actual signed shortest-pair comparison. Compare squared
norm first and then the lexicographically smaller of p and -p in the original
ambient frame; orient the proposed v_j by that same rule. Opposite competitors
may be merged since their membership events are identical.
The list is finite, because each such vector satisfies

\[
 \|z\|^2\le s_j^2+\tfrac14\sum_{h<j}s_h^2.                  \tag{1}
\]

Reduction along previous flag vectors preserves graph membership, support, and
the projected vector. Thus a projected competitor in the lattice has a representative
on this list. Conversely membership of any listed representative supplies a
competitor preceding the proposed winner. Equal-length ties are included precisely
when the signed comparison precedes the proposed pair. Hence, under containment
and saturation, the flag is selected exactly when none of the listed vectors
belongs to L(A), simultaneously at all its steps. This equivalence follows by
induction through the actual appends, not by treating windows as independent.

Pad these competitors to the final raw dimension and reduce them modulo q. Let
B be the finite list of distinct membership events. Proportional nonzero residues
give the same event and may be merged; the zero residue gives a forced event and
makes the proposed selection impossible. Further identifications under the flag's
containment equations are allowed but not necessary.

## Selected moments from the rank formula

Use E,F and Q_E(F;D) from [Part 265](wall1_flag_saturation.md), and its fixed
candidate set C for the next void radius. Write w_delta for ordered candidate-pair
difference multiplicities. For a subset T of B define

\[
 A_0(T)=Q_E(F;T),\qquad
 A_1(T)=\sum_\delta w_\delta Q_E(F;T\cup\{\delta\}),
\]
\[
 A_2(T)=\sum_{\delta,\epsilon}w_\delta w_\epsilon
                      Q_E(F;T\cup\{\delta,\epsilon\}).       \tag{2}
\]

These are the conditional expectations of J^k times saturation and all membership
events in T, conditional only on containing F (with J^0=1). Inclusion--exclusion
therefore gives the exact selected moments

\[
 E[J^k1_{\rm selected}\mid F\subseteq K_A]
        =\sum_{T\subseteq B}(-1)^{|T|}A_k(T),\quad k=0,1,2.   \tag{3}
\]

All terms on the right use the finite-field rank formula, with augmented constraints;
there is no assumption of independence of competitors or of selection and collisions.

For any real c and integer k>=0, define the even truncation

\[
 U_{2k}(c)=\sum_{\substack{T\subseteq B\\|T|\le2k}}(-1)^{|T|}
               [A_2(T)-2cA_1(T)+c^2A_0(T)].                  \tag{4}
\]

It is a rigorous upper bound on E[(J-c)^2 1_selected | contain]. For a sample with
n forbidden events present, the truncated indicator is
sum_(j=0)^(2k) (-1)^j binom(n,j). It is one at n=0; at n>0 it is
binom(n-1,2k)>=0, with binomial coefficients beyond their range taken as zero.
Multiply this pointwise upper bound by the nonnegative quantity
(J-c)^2 1_sat and average to obtain (4). Truncating A_1 or a signed polynomial
without this nonnegativity argument would not justify the same inequality.

## Selected contribution to the remaining history bound

Put tau=25 |C|^2/(18 q^m) as before. For any c<tau,

\[
 \Pr(\mathrm{selected},J>\tau\mid\mathrm{contain})
       \le\frac{U_{2k}(c)}{(\tau-c)^2}.                      \tag{5}
\]

On J>tau, (J-c)^2>(tau-c)^2, so this follows directly from (4).
The flag's unconditional contribution is bounded by q^(-mt) times (5), and may
also be clipped by its exact selected mass from (3) or a valid upper bound on
that mass. A complete sum over canonical flags and the required draws now retains
shortestness rather than discarding it as in Part 264. The candidate radius must
be the actual radius determined by the proposed flag, or a justified smaller one.

The list B, its subset sums, and the number of flags can be enormous. This formula
does not provide a polynomial-time evaluator or a numerical bound at width 506.
In particular, no useful truncation order or aggregate geometric estimate for
(4)--(5) has yet been proved at the required parameters. The remaining 3.922e-12
history allowance and the other BKZ success obligations are still open.

## Grouping the subset sum without losing the truncation bound

Every A_k(T) depends on T only through G=span(F,T). Let c_j(G) count the
j-element subsets processed so far that generate G over F. Start with c_0(F)=1.
For each competitor b, retain each old c_j(G) (exclude b) and add it to
c_(j+1)(span(G,b)) (include b). These integer updates group the exact expression

\[
 \sum_{j=0}^{2k}(-1)^j\sum_G c_j(G)
                   [A_2(G)-2cA_1(G)+c^2A_0(G)].              \tag{6}
\]

Here A_l(G) means the same conditional moment with all equations in G imposed.
Keeping the degree j is essential for preserving the even Bonferroni bound;
grouping only by G and then truncating by rank would be a different expression.
At a fixed requested cutoff, degrees beyond that cutoff need never be stored.

A state can be discarded if G is not graphic or E intersect G is larger than F.
Every extension of such a state still has joint saturation probability zero,
including after adding the collision equations in A_1 and A_2. This is exact
pruning, not removal of small signed terms. A nonzero coefficient must not be
discarded merely for being numerically small.

The reusable implementation is `scripts/span_exclusion.py`; the selected-moment
checker now uses it and separately checks its coefficients by direct subset
enumeration. On the 102 planar fixtures, the original expression has 5364 subset
moment evaluations; grouping and exact pruning require 144 distinct span moment
evaluations instead. These are counts for these fixtures, not a width-506 scaling
claim. The [basis implementation](wall1_flag_saturation.md#basis-implementation-at-the-actual-modulus)
now quotients out the fixed constraints and uses RREF bases in the three-dimensional
checker, instead of enumerating field points. The number of reachable subspaces
can still be enormous, and the sum over
flags is unchanged. This does not close the remaining probability estimate.

## An integer-valued certificate using the parity of collisions

For occupancies n_c, J=sum_c n_c^2 and N=sum_c n_c satisfy J=N modulo 2.
Consequently, for every integer a of the opposite parity to N,

\[
                         g_a(J)=(J-a)^2-1\ge0.                \tag{7}
\]

This is a pointwise statement on every design, not a property merely of the
selected distribution. Let T be the least integer strictly above tau having
the same parity as N. Choose a<=T-3 with the opposite parity. On J>tau,
J>=T and g_a(J)>=g_a(T)>0. Thus the selected-tail estimate becomes

\[
 \Pr(\mathrm{selected},J>\tau\mid\mathrm{contain})\le
 \frac{\sum_{S\subseteq B}(-1)^{|S|}
       [A_2(S)-2aA_1(S)+(a^2-1)A_0(S)]}{(T-a)^2-1}.          \tag{8}
\]

Every even degree truncation of its numerator remains an upper bound by the same
pointwise Bonferroni argument: multiply by the nonnegative g_a(J) 1_sat.
This strengthens the class of usable degree-two certificates beyond squares.
The strict-tail rounding and the parity restriction on a are essential; an
arbitrary real center would not give (7). The minimum of any collection of these
valid bounds, the square bound, and a selected-mass upper bound is still valid.

The integer improvement is useful in finite examples but has not been shown to
give the required improvement when N and J are enormous at width 506.

## Exact verification

`python3 docs/research/scripts/wall1_selected_flag_moments.py` checks planar graph
lattices for q=3 and q=5. It enumerates proposed primitive flags, including flags
that never win, forms all signed shorter-or-tie-preceding competitors, and verifies
selection against direct shortest-vector enumeration for every matrix. It then
checks (3) for all three moments, (4) at every even cutoff, and (5), at three
projected radii. All 102 flag/radius cases pass. Geometry, probabilities and moments
use exact rational arithmetic.
This is not a high-dimensional probability estimate or a Lean formalization.
`python3 docs/research/scripts/wall1_span_exclusion.py` additionally checks every
subset of the seven nonzero vectors of F_2^3 from every base subspace, with and
without upward-closed pruning, and includes forced and repeated events. Degree
cutoffs zero, one and two are verified against the corresponding full coefficients.

### Residual randomness and a complete first-selection sum in dimension three

`python3 docs/research/scripts/wall1_selected_flag_3d.py` tests the graph
L_(a,b)={(x,y,z):x=ay+bz mod q}, for q=3 and q=5. It enumerates every signed pair
of squared norm at most three and verifies that every design has a member there.
Since this list includes every integer vector up to that bound, its first member
is the global shortest pair. The proposed rank-one flags have primitive integral
generators, so E=F and saturation is automatic under containment. Containment
leaves q equiprobable matrices, rather than determining the matrix as in many
planar fixtures.

For each of 96 flag/radius cases, the checker compares the three selected moments
from grouped rank formulas against direct enumeration, and verifies every even
truncation for both the square and parity certificates. At each radius the selected
flag probabilities sum exactly to one. It also sums the selected tail bounds and
checks them against both the actual occupancy exit and the certificate-failure
event; these are kept distinct throughout. The radii squared are 1/4, 3/4, 1, and 2.

Twenty cases exhibit a change in collision mean after selection. For example,
q=3, w=(0,0,-1), R^2=1 imposes b=0. The containment mean is 29/3. Signed ties
select this w only for a=1,2, of conditional probability 2/3, and its selected
mean is 9. The excluded a=0 design has collision count 11. This explicitly checks
that containment moments cannot simply be relabeled as selected moments.

At q=3 and R^2=1, the summed variance bound is 864/13201 although the true exit
probability is zero. The parity certificate (8) proves a zero upper bound as well:
the relevant counts lie at consecutive same-parity values. At q=5 and R^2=2,
the parity refinement gives the bound 17/150 while the direct exit probability
is 1/25, so it does not make the certificate uniformly exact. These are exhaustive
small-dimensional results, not estimates for any draw of the width-506 restart.

## Lean scope of the parity certificate

[SelectedCollisionCertificate.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/SelectedCollisionCertificate.lean)
formalizes the occupancy parity identity, nonnegativity of (J-a)^2-1 on the
opposite parity, monotonicity beyond the center, positivity of the denominator,
and the selected tail-count bound. `selected_occupancy_tail` applies the bound
to the existing `CosetOccupancy.collisionCount`, allowing the finite label type
to depend on the history. Its selected subset is arbitrary, so the theorem does
not introduce a conditional independence premise.

The formal theorem uses an integer tail threshold T and the condition a+2<=T;
the paper's opposite-parity choice a<=T-3 is a sufficient specialization.
It bounds counts on a finite selected subset. Dividing both sides by the size
of a nonempty uniform sample space gives its probability interpretation.
The RREF implementation, competitor-list geometry and numerical selected-history
sum are not formalized by this module. The basic conditional rank-increment formula
is separately formalized in
[ConditionalGraphProbability.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/ConditionalGraphProbability.lean).

[SelectedBonferroni.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/SelectedBonferroni.lean)
now formalizes the nonnegative weighted inclusion--exclusion bound at every even
cutoff. It starts from the alternating binomial identity, identifies binomial
coefficients with counts of present subsets, and reorders the finite sums into
actual intersection weights. `selected_parity_tail` combines that expansion with
the parity polynomial and its positive tail denominator. Its hypotheses say that
the hit list lies in the finite competitor index set and that the collision count
has the required parity on the sample set. No independence is assumed.

This closes the finite inequality layer of (8), including even truncations, in Lean.
Identifying the actual BKZ competitors with these abstract hit lists, connecting
the conditional graph law to these particular intersection weights (including
saturation), and bounding the total over width-506 selected flags remain separate,
unproved connections.

## Mixed-cumulant expression for the negative weighted term

[Mixed cumulant identity](wall1_mixed_cumulant_identity.md) expands
E[Q f(N)] exactly in mixed factorial cumulants and forward differences.
For nonnegative f it gives a lower envelope from two-sided mixed bounds
and univariate factorial moments under the same law. This supplies an
algebraic route to the negative Bonferroni term, not the missing numerical
competitor/cylinder estimates. Raw unconditioned bounds cannot be reused
as conditional inputs without proof.
