# The canonical pair and the shortest-vector void at radius 26

The large-radius part of Part 162's Haar argument has **no support** for the proposed first vector in the penultimate lattice. On a hit its length is at most 0.937430 times that lattice's Gaussian heuristic. At every such fixed radius an unconditioned determinant-matched Haar lattice has an empty open ball with probability at least $1-3.373\cdot10^{-15}$. The relevant void is conditional on a marked pair. In the finite chain, membership of a fixed pair can determine the last two columns exactly. The remaining conditional probability averages two deterministic shortest-line tests over compatible prefixes. Neither the fresh-mark law nor void preservation estimates this average. [Part 153](wall1_neargh_vertical.md) · [Part 162](wall1_upper_band_quotient.md) · [Part 186](wall1_quotient_slack.md)

## Where the Haar argument changes

Use the unconditioned width-506 marginal restart. After 406 appends let $P$ project off the frozen lines, $M=P L(A)$ have rank 505, and $x$ be its designated signed shortest vector. Write $t=\|x\|$ and $p=\lambda_1(P_{x^\perp}M)$. The event is $E=\{p\le26\}$. A shortest quotient generator lifts to $w\in M$ with longitudinal component of length at most $t/2$. Since $w$ is nonzero, $t^2\le\|w\|^2\le p^2+t^2/4$. Thus on $E$ the saturated plane has area $tp$ and
$$
 t\le T:=52/\sqrt3.
$$
This holds for all ties and for horizontal as well as vertical branches. [Part 184](wall1_penultimate_projection.md)

Let $V_j$ denote unit ball volume, $D=\det M$, and $g(D)=(D/V_{505})^{1/505}$. With Part 186's terminal determinant floor $D_*$, interval arithmetic gives
$$
30.02221399<T<30.02221400,\qquad
32.02610188<g(D_*)<32.02610189,\qquad T/g(D)\le T/g(D_*)<0.93742955 .
$$
For **each fixed** $0<u\le T$, the Haar mean number of primitive sign pairs in the open $u$-ball is $V_{505}u^{505}/(2\zeta(505)D)$. Any nonempty open ball containing a nonzero lattice point contains a primitive one. Markov therefore gives
$$
 \Pr_{\mathrm{Haar},D}(\lambda_1<u)
 \le \tfrac12 (T/g(D_*))^{505}<3.373\cdot10^{-15}.
$$
In particular splitting the possible $t$ at $1.05g(D)$ gives an empty upper interval. Splitting lower, at $u\le T$, bounds the high side by an unconditioned void whose probability is almost one. These calculations do not evaluate the void under incidence with a fixed plane. [Haar primitive incidence](wall1_selection_law.md)

Part 162 splits on the **preceding rank-506 window winner**, in a relative band with different gates. Its $0.00152687$ is a lower bound on a Haar *mean count* when the first selection is dropped. Its $4.361\cdot10^{-11}$ is an upper bound on the selected Haar *event probability*, obtained by adding a low-strip incidence estimate and a high-strip void estimate. There is no product of a plane probability and a void probability in that proof. For the present physical event the Haar upper bound is already $B(D_*)<3.33666\cdot10^{-60}$ from the small-flag incidence integral and the cutoff $T$. The missing step is comparison to the finite law. [Part 162 and audit](wall1_upper_band_quotient.md#audit) · [Part 186 and audit](wall1_quotient_slack.md#audit)

## The two-column conditioning law

A canonical pair covering $E$ can be defined *from the selected frame*. Choose $x$, the designated signed shortest point in the quotient, and its shortest lift $w$ in $M$, with ambient lexicographic ties. Lift $x,w$ separately to shortest raw representatives with the same tie convention. Calling this pair $Z(A)$, both representatives have squared norm at most $406q^2/4+T^2$ on $E$ by reverse rounding. A pair chosen solely because it spans a saturated raw plane need not witness $E$ even when $E$ occurs. [State-counting draft](wall1_state_counting.md)

Fix a possible pair $z=(z_1,z_2)$ in advance. Write $d_j\in\mathbb F_q^2$ for row $j$ of its two input columns and $U\in\mathbb F_q^{400\times2}$ for its horizontal residues. Let $I_z$ denote joint raw membership, $V=\mathbb F_q^{400}$ and $Q=|V|$. The condition on the raw columns is $\sum_{j=1}^{511} a_jd_j=-U$, where $a_jd_j$ is an outer product. Write $r_j=\dim\operatorname{span}(d_j,\ldots,d_{511})$, with $r_{512}=0$. A consistent pair has $\Pr(I_z)=Q^{-r_1}$. This includes pairs of input rank zero or one.

**Conditional transition.** Reveal columns in chronological order. At a prefix of length $j-1$ compatible with $I_z$, there are exactly $Q^{512-j-r_j}$ completions. If $r_j=r_{j+1}$, every value of $a_j$ is possible with equally many completions. If $r_j=r_{j+1}+1$, there is exactly one possible $a_j$. Indeed, project each residual row equation modulo the span of the later rows. In the second case the coefficient of the surviving class of $d_j$ specifies each entry of $a_j$. In the first case every choice leaves a consistent later system. Its completion count is the same for every such choice by rank-nullity.

In particular, if $d_{510},d_{511}$ are independent, the first 509 columns retain their unrestricted uniform law, then both remaining columns are determined. For any individual append at a determined column, given the raw prefix and $I_z$, the induced mark is a point mass, at total variation distance $1-1/|H(S)|$ from the unrestricted uniform mark. At a free column the conditional uniform mark law does hold, but the resulting frame is a function of that mark. There is no extra draw when $x$ and its quotient line are selected. Part 176's inverse recovers a parent and mark for a recorded coprime positive-height winner. Its mass still contains the probability of reaching the parent. [Part 108](wall1_first_tour.md) · [Part 176 and audit](wall1_inverse_branch.md#audit) · [Part 187](wall1_local_comparison.md)

For example, in the independent-last-two case let $f_z(a_{1:509})$ be the unique completed design. For compatible membership the exact conditional good-hit probability is
$$
 Q^{-509}\sum_{a_{1:509}\in V^{509}}
 \mathbf1\{E,\ G,\ Z=z\}\big(f_z(a_{1:509})\big),
$$
where $G$ imposes Part 184's raw minimum and dual floors. On each completion the tests include $Pz_1=x$, the designated shortest quotient point being $P_{x^\perp}Pz_2$, its length cutoff, and the lift conventions. An open ball void alone misses earlier signed ties. Dropping the second shortest test can give an upper bound for a fixed candidate, but loses the disjoint canonical count if one sums all candidates.

## An exact finite check

Take one graph append with $q=5$, two horizontal coordinates, two initial columns $a,b$, and final column $c$. In horizontal-then-input order fix $z_1=(-1,0,0,1,0)$ and $z_2=(0,-1,0,0,1)$. Joint membership fixes $b=(1,0)$ and $c=(0,1)$ and leaves $a$ uniform on 25 values. Select the window winner $v$, then $x$ in its quotient, then the designated shortest line modulo $x$, all with signed ambient ties. Use cutoff $\sqrt2$ in the final quotient.

| Outcome conditional on the fixed pair's membership | Prefixes |
|---|---:|
| Quotient misses the cutoff | 16 |
| Quotient hits, but the fixed pair fails one of the designated-line tests | 7 |
| Quotient hits and the fixed pair gives both designated lines, up to sign | 2 |

For $a=0$ the zero column supplies the unique unit line. The two marked lines win successively in its quotient. For $a=(2,2)$ the first window winner is $z_1$ itself, so its projection vanishes. The enumeration tested all $25^3$ raw designs for membership and used rational orthogonal projections on the 25 compatible designs. The two independent marks of squared norm two imply $\|v\|^2,\|x\|^2\le2$. Every final hit has a raw lift of squared norm at most $2+2/4+2/4=3$, so the list of signed integer vectors through squared norm three covers all winning comparisons at the cutoff. In particular $9/25$ is the conditional hit probability and $2/25$ is the conditional probability for the prescribed lines. This example tests the distinction between the two events, at its own ranks and radius.

## What the exits and slack establish

Part 153 compares a void in the rank-506 append to the incoming minimum at $0.954$ times the window heuristic. If the old minimum clears that threshold, a fresh mark preserves the void with probability greater than $1-8.938011\cdot10^{-10}$. This is a lower bound on preservation before conditioning on membership. It supplies neither an upper bound on the frequency of the old histories nor an estimate for the void at $\|Pz_1\|$ in the selected rank-505 output. Part 172 bounds an **unconditional** dual-floor exit by $8.147\cdot10^{-14}$. On surviving histories its complementary rank-503 section bounds the plane area from below by $D(R/\sqrt{\gamma_{503}})^{503}$ for dual floor $R$. That inequality gives no frequency for qualifying sections. The exit may be charged once before splitting by the canonical pair. Its unconditional bound cannot be assigned to each conditioned fiber. [Void preservation](wall1_neargh_vertical.md) · [Dual floor](wall1_transference.md)

Precisely, with $D_z=\{E,G,Z=z\}$ the missing finite mass is
$$
 \Pr(E\cap G)=\sum_{z:\Pr(I_z)>0}Q^{-r_1(z)}\Pr(D_z\mid I_z).
$$
The sum runs over the finite raw annulus of Part 188. The disjointness comes from selecting $Z$ after the frame is known. Proving this sum at most $3.9999566953\cdot10^{-7}$ suffices after the raw and dual exits. A comparison bounding this good mass by $3329^{15}B(D_*)$ would give less than $2.28045\cdot10^{-7}$ before exits. The allowed factor is a budget, with no established inequality connecting these measures. **Conjecture.** The marginal restart satisfies $\Pr(E)\le4\cdot10^{-7}$. The fixed-pair conditioning law identifies the prefix average required for this route and leaves its numerical bound open. [Part 184 audit](wall1_penultimate_projection.md#audit) · [Part 187 audit](wall1_local_comparison.md#audit)

The numerical scale check used 80-decimal-digit outward interval arithmetic, $V_0=1$, $V_1=2$, $V_j=2\pi V_{j-2}/j$, and all 406 determinant-floor updates of Part 186. The two alternatives in each maximum had disjoint intervals. The unrounded upper majorant $(T/g(D_*))^{505}/2$ lay in $(3.37272443,3.37272445)\cdot10^{-15}$.

## Audit

**Verdict — SOUND.** The pathwise cutoff, the fixed-pair conditioning law and the finite counts hold for the unconditioned width-506 restart. The bound on the finite probability of $E$ remains conjectural.

**Radius and void.** Reducing a lift of a shortest quotient point along $x$ gives $3t^2/4\le p^2$, including equality and ties. An independent 100-decimal-digit outward interval calculation used factorial formulas for $V_{504}$ and $V_{505}$. All 406 recurrence comparisons separated, with 20 period-cap and 386 Hermite-cap updates. It gave $T=30.02221399786\ldots$, $g(D_*)=32.02610188328\ldots$ and $T/g(D_*)=0.9374295412933\ldots$. Thus every hit is strictly below $0.937430\,g(D)$. Here an empty ball means that the open ball **centered at the origin** contains no nonzero lattice point. At fixed $D\ge D_*$ and $0<u\le T$, primitive sign-pair counting bounds its nonemptiness probability by $(T/g(D_*))^{505}/2=3.37272443994\ldots\cdot10^{-15}$. The unrounded ratio matters since $0.937430^{505}/2$ exceeds $3.373\cdot10^{-15}$. Part 162 splits on a different winner in rank 506. Its large-radius term gives no thinning estimate here, and the fixed-radius Haar calculation supplies no void probability conditional on a marked pair.

**Conditional columns.** For independent $d_{510},d_{511}$, form the invertible matrix $C$ with these two rows. For every one of the $Q^{509}$ prefixes there is exactly one solution,
$$
 [a_{510}\ a_{511}]=\left(-U-\sum_{j=1}^{509}a_jd_j\right)C^{-1}.
$$
All completions had equal mass before conditioning, so the prefixes are uniform under $I_z$. The prefix and $I_z$ together determine the frame, both signed shortest-line comparisons and all lift ties. Membership alone leaves the prefix random. For general input rank, the suffix map has rank $r_j$ in each horizontal row. Its fiber on a compatible prefix has size $Q^{512-j-r_j}$, verifying the uniform and forced transition cases.

**Exact finite check.** Independent enumeration tested all $25^3=15{,}625$ designs. On the 25 member designs it used rational orthogonal projections, signed ambient lexicographic ties, and all integer vectors of squared norm at most four. The note's reverse-rounding bound of three already covers every final candidate at the closed cutoff. The counts were 16 misses, seven hits failing at least one prescribed line, and two hits realizing both lines up to sign. The last two have $a=(0,0)$ and $(4,0)$ modulo five. This tests the line event; the canonical raw-pair event also imposes the shortest-lift ties.

**Finite probability budget.** The same interval calculation gave $B(D_*)=3.33665809721\ldots\cdot10^{-60}$ and $3329^{15}B(D_*)=2.28043991909\ldots\cdot10^{-7}$. Charging the raw and dual exits once leaves exactly $3.9999566953\cdot10^{-7}$ as a sufficient good-hit budget. Each good design selects one ordered pair, so the disjoint sum has the stated membership weights. Neither Part 153's fresh-mark preservation bound nor Part 188's raw congruence count evaluates the conditional selected fraction. Part 183's draw-407 discrepancy is separate from this draw-406 event.
