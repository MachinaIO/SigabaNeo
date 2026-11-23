# How much Haar comparison loss does radius 26 allow?

For an intrinsic Haar lattice of rank 504, the probability of a minimum below 0.47 times its own Gaussian heuristic lies between $2.73080\cdot10^{-166}$ and $2.73081\cdot10^{-166}$. The physical event in Part 183 has a random normalization. Using the audited determinant floor and integrating over the length of the shortest vector gives a **physical Haar-parent upper bound of $3.33667\cdot10^{-60}$**. At the target $4\cdot10^{-7}$ this leaves room for a factor of $3329^{15.06928}$, even at the floor. The missing estimate is the mass of the same plane event under the finite selected law.

## Intrinsic Haar shape and rank

Write $V_j=\pi^{j/2}/\Gamma(1+j/2)$ and $G_j=V_j^{-1/j}$. A rank-$j$ lattice of covolume $D$ has Gaussian heuristic $G_jD^{1/j}$. In the width-506 restart, a fresh window has rank 506, the retained $M=H_{406}$ has rank 505, and $P_{x^\perp}M$ has rank **504**. Here $x$ is the designated shortest vector of $M$. Set $E=\{\lambda_1(P_{x^\perp}M)\le26\}$. A primitive line in the quotient lifts to a saturated plane in $M$ containing $x$, since $x$ is primitive. Thus $E$ is exactly existence of such a plane with quotient spacing at most 26. The additional $3.210\cdot10^{-14}$ discrepancy in Part 183 applies to replacing $E$ by the terminal event at draw 407. [Part 183 and audit](wall1_terminal_tail_047.md#audit) · [Part 184 and audit](wall1_penultimate_projection.md#audit)

For Haar probability on unimodular lattices of rank $m\ge3$, let $N$ count primitive sign pairs in the ball of radius $cG_m$. The primitive Siegel formula gives $u_m(c)=\mathbb E N=c^m/(2\zeta(m))$ exactly. The second moment and Markov bounds give
$$
 \frac{u_m(c)}{1+u_m(c)}
 \le \Pr(N\ge1)\le u_m(c).
$$
Closed and open balls agree in Haar probability because the expected number of primitive vectors on the boundary is zero. The sign-pair factor and the cancellation $V_mG_m^m=1$ both matter. [Primitive Siegel formula](https://doi.org/10.3934/jmd.2025015) · [primitiveBallPairs_hit_lower](../../SigabaNeo/Lib/Lattices/Research/Wall1/HaarMinimumLower.lean)

| Haar rank $m$ | Enclosure for the hit probability at $c=0.47$ | $\log((4\cdot10^{-7})/u_m)$, rounded | Same log in base 3329 |
|---:|---:|---:|---:|
| 504 | $(2.73080,2.73081)\cdot10^{-166}$ | 366.493 | 45.188 |
| 505 | $(1.28347,1.28348)\cdot10^{-166}$ | 367.248 | 45.281 |
| 506 | $(6.03234,6.03235)\cdot10^{-167}$ | 368.003 | 45.374 |

There is a second Haar experiment. Begin with a Haar **parent** of rank $b=m+1$ and project off its shortest vector. For this selected quotient at $c$ times its *own* GH, the Part 105 upper bound is
$$
 \frac{V_b}{4\zeta(b)\zeta(m)V_m}(2c^2/\sqrt3)^m .
$$
At $c=0.47$ this is below $2.538\cdot10^{-301}$ for $b=505$ and $6.466\cdot10^{-302}$ for $b=506$. Shortestness restricts which parent radii can accompany a short quotient. The Lean theorem `part105` bounds an **oriented primitive mark count** with a parent radius cutoff and a strict normalized transverse cutoff. The shortest-selection estimate also uses the two surviving signs and the radius restriction. The separate Haar window template concerns existence of a qualifying mark under reselection. [Part 105 and audit](wall1_selection_law.md) · [TransverseMinimumBound.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/TransverseMinimumBound.lean) · [HaarWindowTemplate.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/HaarWindowTemplate.lean)

## The physical event at a fixed parent determinant

Put $b=505$, $m=504$, $r=26$, $D=\det M$ and $s=\|x\|$. The projected determinant is $D/s$. On $E$, round a lift of a shortest quotient point by a multiple of $x$. The rounded lift is nonzero and has squared norm at most $r^2+s^2/4$, hence $s\le A=2r/\sqrt3$. Thus the actual relative cutoff is $r(V_ms/D)^{1/m}$. The quoted $26/54.95253$ uses a full-row model scale for a rank-505 terminal lattice. It supplies no pathwise value for this rank-504 quotient.

Let $D_*=\exp L_{406}$, with $L_0=400\log3329$ and $L_i=\max(L_{i-1}-\log3329,(505/506)L_{i-1}-\tfrac12\log56.2142)$. The audited recurrence gives $D\ge D_*$. On $E$ the relative cutoff is therefore at most $c_*=r(V_m A/D_*)^{1/m}\in(0.81527477,0.81527479)$. Comparing the **normalized quotient** on the enlarged fixed event at $c_*$ gives a Haar sign-pair mean in $(9.91264,9.91267)\cdot10^{-46}$ and a sufficient log-loss budget of $10.96037$ in base 3329. [Determinant recurrence and scale audit](wall1_restart_passes_test.md#audit) · [Physical radii in Part 183](wall1_terminal_tail_047.md)

One can retain the dependence on $s$ and improve this budget. At fixed $D$, sample a rank-$b$ Haar unimodular parent and dilate it by $D^{1/b}$. In the primitive incidence integral, the mean number of **unoriented** parent marks in $[s,s+ds]$ is $bV_b s^{b-1}ds/(2\zeta(b)D)$. Given a mark in this integral, its normalized transverse shape is Haar. Its physical quotient of determinant $D/s$ has expected primitive sign-pair count $V_m r^m s/(2\zeta(m)D)$ in the radius-$r$ ball. Every shortest-mark witness contributes at least one to the resulting joint count with $s\le A$. Counting all primitive marks in that range and integrating gives
$$
 \Pr_{\mathrm{Haar},D}(E)
 \le B(D):=
 \frac{b}{b+1}\frac{V_bV_m A^{b+1}r^m}{4\zeta(b)\zeta(m)D^2}.
$$
This uses the primitive incidence product before imposing the winner condition. The extra factor $s$ in the integrand comes from the physical quotient determinant. Homogeneity gives a check on both powers since $b+1+m=2b$. [Marked incidence and transverse shape](wall1_selection_law.md#the-marked-haar-calculation)

In particular $B(D_*)\in(3.33665,3.33667)\cdot10^{-60}$. This bounds the reference probability even if one first draws the **actual** $D$ and then samples Haar shape at that determinant. The sufficient log-loss budget $\log_{3329}((4\cdot10^{-7})/B(D_*))$ lies in $(15.06928,15.06929)$. The fixed-ratio budget in the table and this physical budget correspond to different reference events. Neither calculation estimates the probability of sampling a particular shape in the finite chain.

## What averaging a mark reveal establishes

The normalized shapes reachable through draw 406 form a finite set. They have total selected mass one and Haar mass zero. Consequently a finite likelihood-ratio bound on **all shape events** is impossible even after averaging the histories. Comparison on the single radius event is compatible with this observation. The zero-draw example in the Part 139 audit obstructs conclusions about relative radii from pathwise and Haar-only facts. Its physical minimum stays large. [Part 108](wall1_first_tour.md) · [Part 139 and audit](wall1_lyapunov.md#audit)

There is an exact typical-factor calculation for a coarsened reveal. Fix a history $S$. A uniform finite mark $U$ determines a label $Y=f_S(U)$ with probabilities $p_y>0$ over $k$ attained labels. Compare its joint law $P$ to the reference $R$ which draws the same mark and independently a label of the same marginal law. The joint density is $L=\mathbf1_{y=f_S(u)}/p_y$. Direct summation gives
$$
 \mathbb E_P[L\mid S]=\mathbb E_R[L^2\mid S]=k,\qquad
 P(L>T\mid S)\le k/T.
$$
For a horizontal/vertical label $k\le2$ on every history. Even allowing an arbitrary incoming history distribution shared by $P,R$, Cauchy–Schwarz gives $P(C)^2\le 2R(C)$ for any joint event of history, mark and binary label. For example, if one label occurs on a single mark out of $h>1$, the consistent singleton has $P$-mass $1/h$ and $R$-mass $1/h^2$. Thus the mean factor at most two coexists with an event-specific factor $h$. For a named winner, $k$ counts distinct winners and can be much larger. The two-label comparison still draws the old lattice from its selected law. A Haar probability cannot be substituted for $R(C)$ in this inequality. [Part 157, Lemmas 1 and 3 and audit](wall1_bounded_bias.md)

**A finite reference for the actual plane event.** Keep the true state distribution at the start of a suffix of $d$ draws ending at 406. At each subsequent step, take a fresh uniform mark at the reference state and toss an independent fair coin. For heads choose the shortest horizontal vector of that window, for tails the shortest vector of nonzero height. Use the original signed tie ordering within each type. Both types exist. Their minimizers are primitive, since an integer division in the window would give a shorter vector of the same type. Apply the usual projection and mark update. At the end, apply the original designated-shortest-vector plane test to the retained lattice. Call this explicitly finite law $R_d$.

Couple the two processes with the same raw columns. Conditional on the entire actual path, the probability that all $d$ coins match its winner types is exactly $2^{-d}$. On that event the paths coincide by induction, including their tie choices. Consequently, for this very observable,
$$
           P(E)\le 2^d R_d(E),\qquad 1\le d\le406 .
$$
This gives a full-suffix comparison with loss $2^{406}=e^{281.4\ldots}$, below the proposed nominal loss. It works because the reference still computes the winning representative *within* a type from the same mark. Part 157's independent named-winner reference draws the exact representative from another mark. Its sharp factor $Q$ remains applicable there.

For $d=406$ the sufficient reference target is $R_{406}(E)\le(4\cdot10^{-7})2^{-406}\simeq2.42037\cdot10^{-129}$. The reference still projects along data-dependent shortest directions at every step. The Haar bounds above supply no estimate on $R_d(E)$, and off the matching paths the forced winners can even change the determinant trajectory. As arithmetic for comparison, $\log_2((4\cdot10^{-7})/B(D_*))\in(176.32,176.33)$; using that second budget would require a separate estimate on the reference. A two-way split alone cannot turn it into a Haar process.

For Part 157's draw-406 example the prescribed prefix has probability $Q^{-510}$ and its exceptional winner conditional probability $1/Q$, where $Q=3329^{400}$. The combination contributes only $Q^{-511}$ to an indicator. This single history neither exhausts nor bounds the histories with a short plane. The uniform Voronoi-section theorem transports the measure on a specified set of marks; its statement leaves the size of the winning subset as input. [Part 157, Proposition 2](wall1_bounded_bias.md) · [VoronoiMarkLaw.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/VoronoiMarkLaw.lean)

For a raw candidate with its last invertible coefficient at the final pivot, membership pins the mark. On a compatible invertible positive-height branch the joint mass is $N(S)/Q^{511}$, where $N(S)$ counts raw prefixes for the recovered state. The branch mass times the unconditional membership probability would be $N(S)/(Q^{511}|H(S)|)$. Large $|H(S)|$ thus increases the error from assuming independence on a compatible branch. Summing correctly still requires the masses of the compatible selected parents. The winner-alignment audit also gives a counterexample at smaller width to inferring a short raw relation from the two length cutoffs alone. [Part 184 and audit](wall1_penultimate_projection.md#audit) · [InverseBranch.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/InverseBranch.lean) · [Winner-alignment audit](wall1_winner_alignment.md#audit)

**Open conjecture.** For the unconditioned width-506 restart, $\Pr(E)\le4\cdot10^{-7}$. The physical Haar calculation quantifies the room for a comparison. The finite comparison gives a loss within the nominal fixed-ratio budget, but the reference plane probability remains unevaluated. Equivalently, using the canonical finite sum in Part 184 and its audited raw and dual exits, a sufficient upper bound on the sum is $3.9999566953\cdot10^{-7}$. Its selected weights remain unevaluated. This budget is for $E$ itself.

## Numerical checks

The enclosures use 180-decimal-digit outward interval arithmetic, $c=47/100$, $V_0=1$, $V_1=2$, $V_j=2\pi V_{j-2}/j$, and $1\le\zeta(j)\le1+2^{-j}(1+2/(j-1))$ by integral comparison. All 406 maxima in the determinant recurrence had disjoint candidate intervals. For each intrinsic row both $u_m/(1+u_m)$ and $u_m$ fit inside the displayed interval. As an exact finite check of the mark calculation, enumeration of a singleton label and its complement on 7 and 11 equiprobable marks gave mean factor 2 in both cases and joint singleton probabilities $1/7$ versus $1/49$ and $1/11$ versus $1/121$, respectively. A second exact check used the planar graph $u\equiv ah\pmod q$ with uniform $a$ for $q=5,7,11$. Enumerating $|u|,|h|\le q$ includes each type minimum because the horizontal axis has length $q$ and the centered height-one lift has length below $q$. The quotient spacing after removing a primitive winner $v$ is $q/\|v\|$. For squared cutoff 16 the actual and coin-forced probabilities were respectively $(4/5,9/10)$, $(4/7,11/14)$ and $(4/11,15/22)$. The matching coin reproduced the original signed winner for every mark. These are checks of the comparison on small graphs.

## Audit

**Verdict — SOUND.** The fair-coin coupling proves the stated finite comparison. Its full 406-draw loss exceeds the certified physical-radius budget. The probability of the selected plane event remains open.

**Haar benchmarks.** The retained parent has rank 505, so removing its primitive shortest line gives rank 504. With $u=0.47^{504}/(2\zeta(504))$, both $u/(1+u)$ and $u$ lie in $(2.73080,2.73081)\cdot10^{-166}$. The intrinsic log-loss allowance is $\log((4\cdot10^{-7})/u)=366.49272836\ldots$, which accounts for the nominal $e^{365}$ in the brief. For the physical event, the marked parent density carries one factor $1/D$ and the transverse sign-pair mean carries $s/D$. Shortestness restricts $s\le 52/\sqrt3$. Integrating $s^{505}$ gives the factor $505/506$ in $B(D)$. Independent interval arithmetic with factorial ball volumes and 406 determinant updates gives $\log D_*=891.78636503\ldots$ and $B(D_*)=3.3366580972\ldots\cdot10^{-60}$. The guaranteed comparison factor from this bound is therefore $e^{122.21833455\ldots}=3329^{15.06928438\ldots}$, or $176.32378516\ldots$ bits of loss. The actual Haar probability could be smaller. Lean rechecked `part105` with `propext`, `Classical.choice` and `Quot.sound`. Its statement counts oriented primitive marks with a strict normalized transverse cutoff. The physical bound also uses the marked product law, sign pairing and the radius restriction. [Part 105](wall1_selection_law.md) · [Lean statement](../../SigabaNeo/Lib/Lattices/Research/Wall1/TransverseMinimumBound.lean)

**Finite reference.** Conditional on the actual raw columns and initial state, the winner types form a fixed string. Independent fair coins match it with probability $2^{-d}$. At each matching step the common raw column gives the same mark, and the common signed tie order selects the same vector within that type. Induction gives $R_d(E)\ge 2^{-d}P(E)$. Independent exact enumeration at squared cutoff 16 reproduced $(P,R_1)=(4/5,9/10),(4/7,11/14),(4/11,15/22)$ for $q=5,7,11$, respectively, with matching signed winners at every residue. Each enumeration covered the closed disk of radius $q$, which contains a shortest vector of each type. The separate singleton-label calculation gave mean likelihood ratio two for both seven and eleven marks. Part 157's named-winner comparison uses another mark to choose the representative. [Part 157](wall1_bounded_bias.md#audit)

**Consequence for the target.** The coin loss is $2^{406}=e^{281.41775530\ldots}$. Even a hypothetical estimate $R_{406}(E)\le B(D_*)$ would leave the resulting upper bound above $4\cdot10^{-7}$ by a factor $e^{159.19942075\ldots}$. The coupling requires $R_{406}(E)\le 2.4203699467\ldots\cdot10^{-129}$ to certify the target on its own. The finite reference still selects vectors using each mark, and its off-match histories can have different determinants. Its plane probability has no established Haar bound here. Parts 184–185 leave the selected finite sum unevaluated. Part 183's $3.210\cdot10^{-14}$ discrepancy applies only when transferring to draw 407. [Part 183](wall1_terminal_tail_047.md#audit) · [Part 184](wall1_penultimate_projection.md#audit) · [Part 185](wall1_winner_alignment.md#audit)
