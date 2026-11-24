# A conditional power drift from the actual two-layer transition

This extends the two-layer first-moment inequality in
[the drift recursion](wall1_drift_recursion.md) to every positive power at least
one. It applies conditional on the entire incoming history, without a law for
the selected winner. It does not yet control the actual moving-radius shell.

## Conditional transition lemma

Fix the entire incoming history. Let M be contained in K, with finite mark
group H=K/M of order h, and D(v) the nearest distance in mark v. The next
column supplies U uniform on H. The algorithm selects any primitive winner
w(U) in W_U=(M,0)+Z(u0,1), and Q_U projects off this winner. Denote the
outgoing void fraction, evaluated at a possibly U-dependent radius b(U), by
p'_U(b(U)). As in the existing transition, it is the uniform fraction of old
marks v whose projected coset has distance greater than b(U). Uniform
pushforward remains valid when the mark quotient has a kernel.

Suppose a history-measurable B>=1 satisfies b(u)>=B for every u. Define

    p = Pr_v[D(v)>B],       r = Pr_v[D(v)>sqrt(B^2-1)].

Then, for every real k>=1,

    E_U[p'_U(b(U))^k | full incoming history] <= p^k r.       (1)

In particular this statement is simultaneous for horizontal and
nonhorizontal winners and does not require the winner height coprime to q.

Proof. Put A={v:D(v)>B} and C={v:D(v)>sqrt(B^2-1)}, so A is contained
in C. For a fixed u, consider the available lifts (y(v),0) and
(y(v+u),1), where y is a nearest representative. If either has norm at most
B, its projection also has norm at most b(u). Thus the outgoing miss set,
pulled back to H, is contained in A intersect (C-u). Write

    X(u)=|A intersect (C-u)|/h.

We have 0<=p'_u<=X(u)<=p. Double counting pairs (v,u) gives E_U X(U)=pr:
(v,v+u) is uniform on H squared. Therefore X(u)^k<=p^(k-1)X(u), giving
(1). If p=0 the result follows directly, with no use of a zero power.
Winner selection may depend arbitrarily on u: only contraction of norm by
its orthogonal projection was used. All ties can be retained by using
closed balls and strict miss inequalities.

This uses precisely the actual append/select transition, not a replacement
random lattice model. Its hypothesis about U holds after conditioning on
the past exposed columns and algorithmic history, before exposing the next
independent column. Conditioning on future success or all future columns
would invalidate that fresh-column hypothesis. This is a no-lookahead scope:
the incoming filtration must leave the next raw column independent and
unexposed. Ordinary BKZ transitions that revisit already exposed columns
are not covered by this fresh-column argument without a separate
conditional-law proof.

## Explicit sufficient high-order stopped drift

Fix delta>0. Let P_i denote the actual incoming void at its current test radius b_i.
Choose B_i, measurable from the incoming history, below every outgoing
branch test radius. Set p_i=p_i(B_i), r_i=p_i(sqrt(B_i^2-1)). A sufficient
condition for the power P_i^k to have nonpositive conditional drift is

    p_i^k r_i <= P_i^k.                                     (2)

This is a concrete radial-shell condition; it is not assumed to hold.
For P_i>0 it is equivalent to

    (p_i/P_i)^k r_i <= 1.

For example, if p_i<=a_i P_i and r_i<=rho_i with predictable bounds,
then the conditional drift multiplier is at most a_i^k rho_i. If this
multiplier is at most one at every history before the first exit, the
nonnegative stopped power (P_i/delta)^k gives

    Pr[exists i<=T: P_i>=delta] <= E[(P_0/delta)^k].           (3)

For P_0=0, (2) must still be verified: the ratio version cannot be used.
If (2) fails, a valid additive drift charge is

    c_i = max(0, p_i^k r_i-P_i^k)/delta^k.

The stopped-potential lemma in
[selected history alternative](wall1_selected_history_alternative.md)
then adds the expected stopped sum of these c_i to the right side of (3).
No union over possible flags is present. The statistic here is a power of
the **void fraction**, not a power of J or a Charlier point-count polynomial;
initial bounds for those statistics need an explicit transfer to E[P_0^k].

## Why this does not close the current history estimate

At unchanged physical radius, the zero layer already gives branchwise
void contraction, and (1) additionally gives the conditional power factor r.
The actual transition instead rescales g to g'=g*s^(-1/506) and uses
b(u)=sqrt((1.10*g')^2-1). For a history-measurable winner cap s<=S, an
available lower radius is

    B=sqrt((1.10*g*S^(-1/506))^2-1),

provided it is at least one. This is the same cap comparison already used
in the drift-recursion note. Thus the lower-radius hypothesis of (1) is
available there, but the required shell control (2) is not established.
At its draw-129 corridor endpoints, that note gives B around 553.128 and
633.185 while old radii are around 560.330 and 641.602. The profile at the
old radius alone gives no upper bound on p_i or r_i at these smaller radii.
The earlier shell analysis remains the missing input.

For k=24 and a proposed r_i<=0.28, condition (2) allows only
p_i/P_i <= (1/0.28)^(1/24), approximately 1.05447. This number is a
conditional sufficient shell tolerance, not a measured shell ratio.
If the actual desired observable uses a different smaller radius, insert
that radius and its branchwise lower bound instead; the historical 1.10g
example does not identify it automatically with the later b_i observable.

## Exact finite checks

Run `python3 docs/research/scripts/wall1_two_layer_power_drift.py`.
The script exhausts nested A,C subsets in cyclic groups of sizes 2 through 7
and checks (1)'s exact overlap identities for k=1,2,4,12,24. It also chooses
actual shortest primitive winners for the one-dimensional marked lattices
qZ contained in Z, q=3,5,7,11, and checks the pulled-back projected miss-set
inclusion and power inequalities at B^2=1,2,4,9. The paper argument proves
the all-dimensional result; these finite checks only test its implementation
and conventions. There is no new numerical selected-history failure bound,
no cost bound, and no Lean formalization in this note.

## Capped-potential refinement

The [capped convolution note](wall1_two_height_convolution.md) retains
X<=p before averaging: E Phi(P')<=(pr/delta)min(1,p/delta)^(k−1).
This agrees with the uncapped conversion when p<=delta and is sharper
when p>delta. It does not resolve the moving-radius shell premise above.
