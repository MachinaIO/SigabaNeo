# Local comparison at physical radius 26

A width-506 restart state can force the radius-26 plane event for **every choice of the next 103 marks**. Another reachable state has the same determinant, maximal mark order, and unique signed shortest vector, yet the all-zero continuation misses the event. Both examples have 105 nonzero initial graph columns. Removing the sparse family of Part 144 therefore leaves an obstruction to comparison uniform over the remaining states. Part 184's stronger raw exit does remove these particular examples. The probability of the event after that exit remains open.

## The physical budget

Use the independent $400\times105$ restart followed by 406 independent columns, with Part 108's signed ambient tie rule. Write $M$ for the retained rank-505 lattice, $x$ for its designated shortest vector, and $p=\lambda_1(P_{x^\perp}M)$. The event is $E=\{p\le26\}$. A primitive quotient vector lifts with $x$ to a basis of a saturated plane. Draw 407 has yet to occur. Part 117's additive coupling bound for transfer from this marginal restart to the original first pass already exceeds the requested probability. [First-tour law](wall1_first_tour.md) · [Restart coupling](wall1_idea_round2.md) · [Part 183 audit](wall1_terminal_tail_047.md#audit)

Put $b=505$, $m=504$, $r=26$, $A=2r/\sqrt3$, and let $V_j$ be the volume of the unit ball in dimension $j$. On $E$, reducing a quotient lift along $x$ gives a nonzero vector of squared length at most $r^2+\|x\|^2/4$. Shortestness yields $\|x\|\le A$. For a Haar parent of determinant $D$, count all primitive sign pairs of length $s\le A$, each weighted by the number of primitive quotient sign pairs of length at most $r$. Every hit contributes at least one. The incidence density of the first pair is $bV_b s^{b-1}/(2\zeta(b)D)$. Its transverse Haar lattice has determinant $D/s$, so its conditional mean count is $V_m r^m s/(2\zeta(m)D)$. Integration gives the physical upper bound
$$
 h(D):=\Pr_{\rm Haar,D}(E)\le
 B(D):=\frac{bV_bV_m A^{b+1}r^m}{4(b+1)\zeta(b)\zeta(m)D^2}.
$$
This derivation keeps the physical cutoff fixed as the quotient determinant changes. [Part 105 incidence calculation](wall1_selection_law.md) · [Quotient slack](wall1_quotient_slack.md)

Put $q=3329$, $Q=q^{400}$, and $D_*=\exp L_{406}$. The audited winner cap and determinant update give $L_0=400\log q$ and
$$
 L_i=\max\{L_{i-1}-\log q,\ (505/506)L_{i-1}-(\log 56.2142)/2\}.
$$
Hence $D\ge D_*$ on actual paths. For $\tau=4\cdot10^{-7}$, independent outward interval evaluation gives the following enclosures. [Determinant floor audit](wall1_restart_passes_test.md#audit)

| Quantity | Enclosure |
|---|---:|
| $L_{406}$ | $(891.78636503,891.78636505)$ |
| $B(D_*)$ | $(3.33665809,3.33665811)\cdot10^{-60}$ |
| $\log(\tau/B(D_*))$ | $(122.21833,122.21834)$ |
| $\log_q(\tau/B(D_*))$ | $(15.06928438,15.06928440)$ |
| $\log_2(\tau/B(D_*))$ | $(176.32378,176.32380)$ |
| $q^{15}B(D_*)$ | $(2.28043991,2.28043993)\cdot10^{-7}$ |

A proved comparison at loss $q^{15}$ could also pay additive exits totaling $1.71956\cdot10^{-7}$. At factor two per step, 175 steps fit under the specified $q^{15}$ cap and 176 fit under the full budget with zero exits. The full coin factor is $2^{406}=\exp(281.41775\ldots)$. Even for a shorter suffix the coupling only gives $P(E)\le2^tR_t(E)$: require each independent coin to match the actual winner type, which has conditional probability $2^{-t}$ given the actual path. The coin reference starts from the selected block-start law and computes the shortest representative within each type. The Haar bound above supplies no estimate of $R_t(E)$. The determinant floor applies to actual paths and hence to a Haar reference matched to their determinants. [Finite coin reference](wall1_quotient_slack.md) · [Part 157, Lemma 3](wall1_bounded_bias.md)

## A block-start obstruction for the physical plane event

**Projection criterion.** Suppose the retained lattice at the start of a suffix of length $t$ has $t+2$ linearly independent vectors of length at most 26. Then $P(E\mid S)=1$. Each append embeds the old lattice isometrically. Projecting off one line has a kernel of dimension at most one on the span of the witnesses and cannot increase their lengths. After $t$ projections their images span at least two dimensions. Projecting off the terminal $x$ leaves at least one nonzero image of length at most 26. This works for every sequence of marks and projected lines. A deterministic good-state claim giving conditional probability strictly below one must exclude the whole set $\{\lambda_{t+2}(M_{406-t})\le26\}$ whenever $t+2\le505$.

**Two reachable block starts.** Fix $1\le t\le103$. In both initial graphs use columns $a_j e_j$ in the first 105 of the 400 output coordinates, with $a_1=1$. In the first graph put $a_j=2$ for $2\le j\le t+2$ and set every remaining coefficient to 40. In the second graph put $a_j=40$ for all $j\ge2$. Prescribe zero raw columns for the first $406-t$ appends. The initial graphs split orthogonally into 295 copies of $q\mathbb Z$ and 105 factors of the form
$$
 K_a=\{(u,v)\in\mathbb Z^2:u\equiv av\bmod q\}.
$$
Reversing the graph sign convention reflects the input axes of both graphs. For $a=1,2,40$ the only shortest pair in $K_a$ is $\pm(a,1)$. Indeed any competitor in the closed ball of squared radius $1+a^2$ has $|v|\le a$, hence $|av|\le1600<q/2$. For $v\ne0$ its squared length is at least $(1+a^2)v^2$, with equality only at the centered representative. For $v=0$ every nonzero choice has length at least $q$.

On each prescribed append the unique shortest line is the fresh unit axis, so its removal preserves the old graph. Both block starts have $D=Q$ by the index of the graph congruence, and $|H|=Q$ because their horizontal intersection is $q\mathbb Z^{400}$. Both have the same unique shortest line and the same signed generator of length $\sqrt2$. In the first graph $t+2$ orthogonal vectors have length at most $\sqrt5$, so the criterion applies on every suffix. In the second graph choose the all-zero suffix. Every win is vertical of height one. After projecting off $x$, the first factor has spacing $q/\sqrt2$ by its area $q$, and every other two-dimensional factor has minimum $\sqrt{1601}$. Thus the terminal quotient minimum is $\sqrt{1601}>26$. In the first graph on exactly the same suffix it is $\sqrt5$. For $104\le t\le406$ the two graphs of the $t=1$ construction still give opposite answers along a prescribed all-zero suffix of length $t$; only the fixed-continuation assertion is used in this longer range.

Each prescribed raw block-start history costs $Q^{-(511-t)}$, and the all-zero continuation costs $Q^{-t}$. For $t\le103$ the first conditional hit probability equals one and the second is at most $1-Q^{-t}$. The first graph already lies outside the Part 144 family of at most 103 nonzero columns, since all 105 initial columns are nonzero. Its short raw vectors do place it within Part 184's raw exit. The original-pass $q^{-511d}$ cubic cylinder of Part 109 concerns a relative minimum and has physical spacing $q$. Its mass supplies no upper bound on the total mass of other exceptional starts. Requiring full original mark rank as a good-state condition would itself discard more than 0.72982006 of the marginal restart mass by the first suffix step. [Part 109](wall1_terminal_mixing.md) · [Part 144 audit](wall1_horizontal_core.md#audit) · [Finite chain and audit](wall1_finite_chain.md#audit)

## Coarsening the inverse branch to one bit

Even the scalar $p$ has no finite likelihood ratio on all Borel sets against determinant-matched Haar. Its support under the chain is finite. At fixed $D$, a Haar observation at a specified $p_0>0$ requires a primitive parent mark of norm at most $2p_0/\sqrt3$ whose transverse lattice hits the sphere of radius $p_0$. The transverse mean count on that sphere vanishes by primitive incidence. Integrating over $D$ preserves zero mass. The argument survives conditioning the finite law on any positive-mass set of histories. For the single hit indicator the ratio on the hit is just $P(E)/P_{\rm ref}(E)$ when the denominator is positive. Atomicity places no bound in either direction on that ratio. [Part 163, Proposition 1](wall1_restart_haar_ratio.md)

At a vertical step one can determine exactly what happens to mark order when the winner height $k$ is coprime to $q$. Write $v=(l_v+k\tilde u,k)$ in the window, with $l_v$ in the old lattice $L$. If a horizontal mark represented by $y$ dies under projection, $(y,0)$ differs from a window vector $(l+j\tilde u,j)$ by a real multiple of $v$. Comparing heights fixes that multiple and gives $ky=kl-jl_v\in L$. The kernel on $H$ is killed by both $k$ and $q$, hence is trivial. Since the next mark group is the image of $H$, the order is preserved exactly. This transports the incoming group, whose rank is history dependent. It gives no lower bound on the fraction of its marks passing a geometric test. [Marked transition](wall1_first_tour.md) · [Inverse branch](wall1_inverse_branch.md)

Let $S$ be the framed parent before draw 406, $h_S=|H(S)|$, and $N(S)$ the number of the $Q^{510}$ raw prefixes reaching it. Let $A_S\subseteq H(S)$ contain the marks whose output passes $E$, including horizontal branches, and put $k_S=|A_S|$. One mark has $Q/h_S$ raw completions per prefix, so
$$
 P(E)=\sum_S\frac{N(S)}{Q^{510}}\frac{k_S}{h_S}. \tag{1}
$$
On a coprime positive-height branch covered by Part 176, the embedded output and oriented winner recover $S,u$. Its raw multiplicity is exactly $N(S)Q/h_S$. Forward counting proves (1) on every sector. [Part 108](wall1_first_tour.md) · [Part 176 audit](wall1_inverse_branch.md#audit)

Fix a raw candidate $z$ with invertible last coefficient at column 511, and write $I_z$ for membership. At each prefix reaching $S$, exactly one final raw column gives membership. Its mark $u_z(S)$ is common to those prefixes: the old graph relation gives $c_{511}u_z(S)=[P(b,c_{<511})]$ in the old torus with Part 184's sign convention. For $k_S>0$ this gives the exact factor on the radius event,
$$
 \frac{P(E\cap I_z\mid S)}{P(E\mid S)P(I_z\mid S)}
  =\mathbf1_{\{u_z(S)\in A_S\}}\frac{h_S}{k_S}. \tag{2}
$$
The numerator is the indicator divided by $Q$, and the denominator is $k_S/(Qh_S)$. If $k_S=0$ both vanish. For a compatible individual inverse branch the ratio is $h_S$. Coarsening to $k_S$ passing marks divides it by exactly $k_S$. A uniform bound $h_S/k_S\le q^{15}$ on compatible hits would require $k_S\ge h_S/q^{15}$ there. Mark uniformity gives no such lower bound, and (2) still compares two finite probabilities. For Part 184's canonical raw lift, additional prefix-dependent tests must be kept inside the fiber. Part 185's width-three counterexample also prevents deducing a short raw relation just from the two length cutoffs and shortest selection. [Part 184 audit](wall1_penultimate_projection.md#audit) · [Part 185 audit](wall1_winner_alignment.md#audit)

## The outstanding probabilistic estimate

Write $\mu_t$ for the actual block-start law, $p_t(S)=P(E\mid S)$ and $h_t(S)=\mathbb E[h(\det M)\mid S]$ for the reference matched to the actual terminal determinant. The smallest additive allowance making the comparison at factor $C=q^{15}$ valid on **every subset of block starts** is exactly
$$
 \delta_t(C)=\sum_S\mu_t(S)[p_t(S)-Ch_t(S)]_+ .
$$
Indeed the set where the bracket is positive realizes the supremum of the differences of the two masses. In particular, if $J_t=\{\lambda_{t+2}(M_{406-t})\le26\}$ then the projection criterion gives $\delta_t(C)\ge(1-CB(D_*))\mu_t(J_t)$ for $t+2\le505$. An additive exit can pay for these positive differences only to the extent that their total mass allows. Comparison on the single global event needs only the signed average. Neither the cylinder probabilities nor the branch multiplicity bound this average. Part 184 independently pays less than $4.249\cdot10^{-12}+8.147\cdot10^{-14}$ for its raw and dual exits, leaving the sufficient target $3.9999566953\cdot10^{-7}$ on its canonical selection sum. Part 183's draw-407 discrepancy applies to a different event. **Conjecture.** The marginal restart satisfies $P(E)\le4\cdot10^{-7}$. The weighted count (1) and the comparison on surviving histories remain open.

Numerical checks used 130-decimal-digit interval arithmetic, $V_0=1$, $V_1=2$, $V_j=2\pi V_{j-2}/j$, and $1\le\zeta(j)\le1+2^{-j}(1+2/(j-1))$ by integral comparison. All 406 maxima had disjoint input intervals. Integer disk enumeration in the three graph factors gave just the two stated minimizers in each closed disk. Rational comparison of the factor minima after projection gave squared minima 5 and 1601 for all 103 pairs. As an exact check of (2) with nontrivial fibers, take two equiprobable prefixes indexed by $i=0,1$, a uniform raw column $(a,b)\in\mathbb F_3^2$, mark $a$, and pin the column $(1,i)$. Among the 18 completions each mark occurs six times, and both membership hits have mark one. A passing set containing one and having $k$ marks has joint-to-product ratio $3/k$.

## Audit

**Verdict — SOUND.** Both block starts are reachable in the marginal restart, and Part 184's raw exit removes every continuation of both prescribed prefixes. The estimate $P(E)\le 4\cdot10^{-7}$ remains open.

**The 103-draw test.** Each prescribed prefix fixes 105 initial columns and 303 zero appends, so has mass $Q^{-408}$. A zero append adds an orthogonal unit axis to a graph of minimum $\sqrt{2}$. Removing its unique shortest line returns that graph. The 105 planar determinants and 295 horizontal spacings give $D=q^{400}$, and the horizontal intersection $q\mathbb Z^{400}$ gives $|H|=q^{400}$. Exact enumeration of the closed disks $u^2+v^2\le 1+a^2$ in $K_a$ found only $\pm(a,1)$ among nonzero points for each of $a=1,2,40$. The first factor therefore gives the same designated shortest vector in both states.

The first graph starts with 105 independent vectors of length at most $\sqrt{5}$. Each append preserves their current images, and each line projection removes at most one dimension from their span. After 103 draws and the terminal projection at least one image survives, still of length at most $\sqrt{5}$. This proves the assertion for every continuation. On the common zero continuation the projected first factor has squared spacing $q^2/2$. Taking the minimum over the remaining orthogonal factors gives squared quotient minima 5 and 1601, respectively. The same exact calculation checked every $1\le t\le103$. In the raw graph with Part 184's plus sign, $(-e_1,e_1)$, extended by zeros in later inputs, satisfies the congruence and has squared norm 2 on both prefixes. It triggers the radius-250 exit regardless of the unread columns. [Part 108](wall1_first_tour.md) · [Part 184 audit](wall1_penultimate_projection.md#audit)

**Physical budget.** Independent outward interval arithmetic using factorial ball volumes separated the two candidates in all 406 determinant updates. It gave $B(D_*)=3.33665809721\ldots\cdot10^{-60}$ and $\log_{3329}(\tau/B(D_*))=15.06928438827\ldots$. Thus $15.0693$ is a rounded exponent. At the integer exponent 15 the reference charge is $2.28043991909\ldots\cdot10^{-7}$ and the additive room is $1.71956008090\ldots\cdot10^{-7}$. These figures use the rank-505 Haar parent and rank-504 quotient at physical radius 26. [Part 186 audit](wall1_quotient_slack.md#audit)

**Coarsening.** Given a framed parent, the $k_S$ passing marks have $k_S Q/h_S$ raw completions per prefix. Membership of the specified candidate pins one raw completion per prefix, and the old graph congruence fixes its mark across all prefixes with that parent. For $k_S>0$, the conditional joint-to-product ratio is therefore $h_S/k_S$ on compatibility and zero on incompatibility. A singleton recovers Part 176's branch factor on its coprime positive-height sector. The forward count includes horizontal winners as well. Exact enumeration of the two-prefix example verified all 21 combinations of a pinned mark and a nonempty passing set. Applying this identity to Part 184's canonical selection still requires its prefix-dependent tests and parent weights. The two cylinders give no estimate for their weighted sum after the exits. [Part 176 audit](wall1_inverse_branch.md#audit) · [Part 184 audit](wall1_penultimate_projection.md#audit)
