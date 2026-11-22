# The window void on a penultimate vertical win

At selection 406 the lower window cutoff acts, up to probability $8.938011\cdot10^{-10}$, as a test of the **incoming old minimum**. Once the old lattice clears that cutoff, the fresh draw almost surely clears it too. Even exact conditional independence from the retained-plane test at that point would give essentially no reduction from the void factor. A finite one-step example below has two voids among seventeen marks, and both pass the retained-plane test. The width-506 history average in Part 151 remains open.

## The conditional void at width 506

Use the marginal restart and fix the history $S$ just before selection 406. Write $M$ for the incoming rank-$d$ lattice, $d=505$, $b=d+1$, $D_-=\det M$, $g=G_bD_-^{1/b}$, $c=0.954$, and $u=cg$, where $G_j=V_j^{-1/j}$ and $V_j$ is unit ball volume. The fresh mark $U$ is uniform on the history's finite subgroup $H$. For a lift $\tilde U$, the window is $W=(M,0)+\mathbb Z(\tilde U,1)$. Let $v$ be the signed winner, $k$ its absolute height, $s=\|v\|$, and $L=\pi_{v^\perp}W$. On $L$ set
$$
 h=G_d(D_-/s)^{1/d},\quad t=\|x\|=\lambda_1(L),\quad
 \ell=\lambda_1(\pi_{x^\perp}L),\quad
 B=\{1<t\le\sqrt{1+c^2h^2},\ \ell<ch\,t^{-1/d}\},
$$
using the designated signed shortest $x$. This is a joint event in the output of selection 406. The independent plant and draw 407 do not enter. [Part 108](wall1_first_tour.md) · [Part 117](wall1_idea_round2.md) · [Part 151 and audit](wall1_penultimate_tail.md)

**Proposition 1 (the fresh void has almost no thinning effect).** Put $A=\{\lambda_1(M)\ge u\}$, $V=\{s\ge u\}$ and $\epsilon=8.938011\cdot10^{-10}$. Then $V\subseteq A$, and for **every** event $C$ of the next draw, even one using the selected plane,
$$
 0\le\Pr(A\cap C\mid S)-\Pr(V\cap C\mid S)
 \le \mathbf1_A\,\epsilon.                                      \tag{1}
$$
On $A$, the total variation distance between the mark law and the mark law conditional on $V$ is at most $\epsilon$. In particular $\Pr(V\mid S)>0.999999999106$ on $A$. These claims concern the mark before conditioning on a vertical win.

*Proof.* The old lattice embeds horizontally, so $s\le\lambda_1(M)$. On $A\setminus V$ we have $s<u\le\lambda_1(M)$, forcing a vertical winner for any tie rule. Part 151's positive-height first moment gives uniformly in $S$
$$
 \Pr(k>0,\ s\le u\mid S)\le
 \tfrac12 J_b c^b\Theta(z)^d<\epsilon,\qquad
 z=u\sqrt{2\pi/b}>3.42155 ,
$$
where $J_b=e^{b/2}(2\pi/b)^{b/2}/V_b$ and $\Theta(z)=1+2e^{-\pi z^2}/(1-e^{-3\pi z^2})$. Intersect $A\setminus V$ with $C$ to get (1). On $A$, write the original mark law as the mixture of its restrictions conditional on $V$ and $V^c$ with weights $p$ and $1-p$. Their disjoint supports give distance exactly $1-p$ from the law conditional on $V$, including distance zero when $p=1$. ∎ [Part 151, §2, vertical selection](wall1_penultimate_tail.md) · [Positive-height first moment, equation (4)](wall1_vertical_multiplicity.md)

For the closed band in the question, take $C=B\cap\{k>0,\ s\le1.097193g\}$. Equation (1) shows that replacing the lower-band void by $A$ changes its joint probability by at most $\epsilon\Pr(A)$ after averaging. For Part 151's strict lower endpoint the same difference bound holds using $A'=\{\lambda_1(M)>u\}$ and $V'=\{s>u\}$: on $A'\setminus V'$ the winner is again strictly shorter than the old minimum. The upper endpoint in Part 151 is already strict on $B$ by its rounding inequality. This is a comparison of two ways of writing the residual. The short-vertical exit is already included in Part 151's budget.

The distinction also holds in the Haar benchmark. At determinant $D_-$ a Haar window has expected primitive sign-pair count $c^{506}/(2\zeta(506))$ below $cg$. Thus its probability of a nonvoid is at most $2.242\cdot10^{-11}$ by Markov's inequality. This benchmark gives no estimate for $\Pr(A)$ under the selected-history law. [Part 107](wall1_lit_random_bases.md) · [Haar selection law and audit](wall1_selection_law.md)

**An exit measurable before the draw.** The portion of case (b) on histories with $g\ge203.888$ has probability at most $1/816000$. To see this, set $N=910$, $n'=510$ (105 initial columns and 405 already appended), $q=3329$, and
$$
 R_0=q^{-1}\left[(q^{510}/(408000 V_{910}))^{1/910}-\sqrt{910}/2\right].
$$
The selected dual $M^*$ is contained in the raw graph dual. A raw dual vector of length strictly between zero and $R_0<1$ has the form $(p,w)/q$ with $p\not\equiv0\pmod q$: otherwise $w\equiv0$ as well and the vector would be integral. For each fixed such pair, membership has probability $q^{-510}$ from the 510 independent column congruences. Unit cubes centered on integer points of the ball of radius $qR_0$ fit in the ball of radius $qR_0+\sqrt{910}/2$. The expected number of nonzero raw dual vectors below $R_0$ is consequently at most $1/408000$. Every hit includes both signs, so the probability is at most $1/816000$. This first moment is over the marginal design before selection 406. [Part 142, Theorem C](wall1_dual_cusp.md)

Off that exit, the rank-505 Hermite cap applied to $M^*$ gives $R_0\le\lambda_1(M^*)\le C D_-^{-1/505}$ for $C=\exp(1016.893214923/505)$. Hence $g\le G_{506}(C/R_0)^{505/506}<203.888$. With $V_{910}=\pi^{455}/455!$, outward interval evaluation gives $0.19999458051<R_0<0.19999458052$ and puts the upper majorant for $g$ in $(203.88761744,203.88761745)$. If this exit is used to restrict the vertical history average, its charge must come out of the shared residual allowance. [Rank-505 cap](wall1_hermite_caps.md)

## A finite mark with positive dependence

**Proposition 2.** In a rank-four one-step window with a prime-order uniform mark, every winner can have height one, and the window void can imply the full retained event $B$. In the example of order 17,
$$
 \Pr(V)=2/17,\qquad \Pr(B)=8/17,\qquad \Pr(V\cap B)=2/17>16/289.
$$
Both draws in the intersection have $s/g<1.097193$. The example tests an implication of the one-step geometry on general marked lattices. It makes no reachability claim for the width-506 restart.

*Construction and proof.* Put $a=11/10$. In the three old coordinates take
$$
 M=\{(am,an,10z):m,n,z\in\mathbb Z,\ m\equiv n\pmod 2\}.
$$
For $p=17$ take $H$ generated by $(2a/p,0,0)+M$; it has order $p$. Include $p=2$ as a second enumeration. Up to reflection, mark $j$ has shortest representative $(y,0,0)$ with $y=2a\min(j,p-j)/p\in[0,a]$. Indeed another point on the same axial line is spaced by $2a$; every off-axis translate has norm at least $a$. At $y=a$ the tied nearest representatives are equivalent by old-coordinate signs and interchange. The height-one candidate has length $s=\sqrt{1+y^2}<\sqrt2a=\lambda_1(M)$ and $s<2$. Hence it beats every horizontal candidate and every higher layer. Ties at height one give isometric quotients.

Projection along this winner maps the old first-axis unit to a vector of norm $1/s$ perpendicular to the other two old axes. Because the winning height is one, the projected old lattice generates the quotient. In isometric coordinates this gives
$$
 L=\{(am/s,an,10z):m\equiv n\pmod2\}.
$$
Its planar summand has shortest length $t=a\sqrt{1+s^{-2}}$. For odd $m,n$ the minimum squared norm is $a^2(1+s^{-2})$. For a nonzero even pair it is $4a^2/s^2$, which is larger since $s^2\le 1+a^2<3$. A nonzero last coordinate costs at least 10. Every shortest vector therefore generates a primitive planar line. Its projected planar complement has spacing equal to the planar determinant divided by $t$, giving $\ell=2a^2/(st)<10$. This proves the three length formulas for any signed ties.

Here $D_-=20a^2$, $g=(D_-/V_4)^{1/4}$, and $h=(D_-/(sV_3))^{1/3}$. All marks satisfy $1<t<\sqrt{1+c^2h^2}$ and $s/g<1.097193$. The following are the full counts, using the same $c$ and the same strict plane test as in $B$.

| $p$ | Values of $\min(j,p-j)$ giving $V$ | Values giving $B$ | Marks in $V\cap B$ |
|---:|:---|:---|---:|
| 2 | 1 | 1 | 1 of 2 |
| 17 | 8 | 5, 6, 7, 8 | 2 of 17 |

One can see the direction of dependence directly. Since $\ell=2a^2/(st)$ and $ch\,t^{-1/3}=c(D_-/(V_3st))^{1/3}$, the plane passes exactly when $(st)^{2/3}>2a^2/[c(D_-/V_3)^{1/3}]$. But $st=a\sqrt{1+s^2}$ increases with $s$. In this example the same displacement that lengthens the winner makes the plane test easier. ∎

## Verification and remaining estimate

A scratch enumeration used rational coordinates and successive exact orthogonal projections for all 19 marks of the two examples. It enumerated raw vectors of squared norm at most 4, independently selected each minimum by squared norm and signed coordinates, and matched all three squared-length formulas on every mark. The ball suffices: the formulas give $s<1.5$, $t,\ell<1.56$, so a third-stage shortest vector lifts by rounding twice to squared norm at most $1.56^2+1.56^2/4+1.5^2/4<4$. The second-stage check needs only the last rounding along $v$. The integer ranges $|k|,|n|\le2$, $|m|\le4$, $z=0$ include this ball since $|am+ky|\le2$ and $y\le a$.

For the cutoffs, 70-decimal-digit outward-rounded interval arithmetic used $V_3=4\pi/3$ and $V_4=\pi^2/2$. At $p=17$, $s/g$ is in $(0.9067208,0.9067209)$ at index 7 and $(0.9672551,0.9672552)$ at index 8. The signed plane margin $\ell-ch\,t^{-1/3}$ is in $(0.0141192,0.0141193)$ at index 4 and $(-0.0166994,-0.0166993)$ at index 5. Every test in the table separated strictly. At width 506, substituting $z=3.42155$ and $V_{506}=\pi^{253}/253!$ encloses the first-moment majorant in $(8.93801023,8.93801024)\cdot10^{-10}$; $\Theta$ decreases with $z$. The Haar sign-pair upper bound $c^{506}/2$ is in $(2.24102,2.24104)\cdot10^{-11}$.

**Remaining gap (Part 151 conjecture).** The joint allowance is $\Pr(H_{\rm old})+\Pr(V_{\rm mid})\le0.0089999976$. For case (b), the finite law gives exactly $|H|^{-1}$ times the number of marks satisfying the vertical winner, band, retained minimum and plane tests on the same draw, averaged over $S$. For each fixed positive winning height $k$, its winning representative determines $kU$ and hence $U$, because $k$ is invertible modulo $q$. The retained lattice $A_v(M+\mathbb Z\lambda/k)$ and its two shortest-vector selections use that same mark. Proposition 1 controls the cost of replacing the void by the old-minimum test, but neither the mass of those old histories nor their selected plane-hit rate has been bounded here at the requested scale. The example precludes a general product upper bound from Voronoi uniformity alone. Parts 148 and 150 estimate multiplicities on the subsequent terminal draw, a different observable. [Part 139](wall1_lyapunov.md) · [Part 142, Theorem B and audit](wall1_dual_cusp.md) · [Part 148](wall1_vertical_multiplicity.md) · [Part 150](wall1_shortened_lines.md) · [Part 151](wall1_penultimate_tail.md)

## Audit

**Verdict — SOUND.** Both propositions, the single-time dual exit, and every printed numerical enclosure check out under Part 117’s marginal restart law. No correction is required. The width-506 selected-history average remains open.

**Conditioning at selection 406.** Fix the incoming history $S$. The horizontal embedding gives $V\subseteq A$, and $A$ is already determined by $S$. On $A$, failure of $V$ forces $k>0$ and $s<u$. Thus the difference in (1) is exactly $\Pr(C\cap(A\setminus V)\mid S)$, even when $C$ tests the plane selected by this mark. Writing $p=\Pr(V\mid S)$, the mark law and its restriction conditioned on $V$ have total variation distance exactly $1-p$ (the event $V^c$ attains it). The Part 151 recursion through step 405 gives $z>3.42155721$ and $u<3184.109<q$. At the conservative $z=3.42155$ the positive-height majorant is below $8.93801024\cdot10^{-10}$, so $p>0.999999999106$. This comparison precedes conditioning on a vertical win. For Part 151’s strict lower endpoint, $\lambda_1(M)>u$ together with $s\le u$ still forces a vertical winner, including equality at $s=u$. The rounding bound on $B$ gives $s/g<1.097193$ at the other endpoint.

**Large window GH.** Before draw 406 there are 510 independent columns in ambient dimension 910. For a raw dual vector $(p,w)/q$ of length in $(0,R_0)$, $p\bmod q$ is nonzero and the congruence $w=-A_{\rm raw}^{\mathsf T}p\pmod q$ costs $q^{-510}$. The cube bound counts signed vectors, so every nonempty ball of such vectors contributes at least two. The expected count is at most $1/408000$, giving hit probability at most $1/816000$. The selected dual is contained in the raw dual for each realized history, even though its subspace depends on the columns. Outside the raw hit, the Hermite cap gives $g\le G_{506}(C/R_0)^{505/506}$. Independent 80-decimal-digit interval arithmetic, using $V_j=2\pi V_{j-2}/j$, gave $R_0\in(0.1999945805175,0.1999945805176)$ and a GH majorant in $(203.8876174449,203.8876174450)$. Thus every history with $g\ge203.888$ is covered, including equality. The Haar sign-pair majorant $c^{506}/2$ lies in $(2.2410296607,2.2410296608)\cdot10^{-11}$.

**Exact rank-four enumeration.** A separate scratch calculation used the original lifts $2aj/p$ for all 19 marks. It enumerated the raw squared-norm ball through 4 and projected with exact rational dot products for every tied shortest $v$ and every tied shortest $x$. Rounding first along $x$ and then along $v$ gives a raw lift of a third-stage minimizer with squared norm at most $\ell^2+t^2/4+s^2/4<4$, so the ball covers all three selections. Every branch gave the stated $s^2,t^2,\ell^2$. Interval comparisons confirmed the length test and upper band for every mark and all four printed boundary intervals. At order 17, $V$ holds at $j=8,9$ and $B$ at $j=5,\ldots,12$. Their intersection has probability $34/289$, exceeding the product $16/289$ by $18/289$. At order 2, precisely $j=1$ passes both tests. This establishes positive dependence in the finite example.

**Remaining estimate.** Write $C=B\cap\{k>0,\ s<1.097193g\}$ and $A'=\{\lambda_1(M)>u\}$. On $g<203.888$, replacing the strict window void by $A'$ in $V_{\rm mid}$ gives the upper bound
$$
\mathbb E_S\!\left[\mathbf1_{\{g<203.888\}\cap A'}\,
  \frac{\#\{U\in H(S):C(S,U)\}}{|H(S)|}\right].
$$
The overestimate on these histories is at most $\epsilon\Pr(g<203.888, A')$. If the discarded histories are charged using $1/816000$, that charge, the displayed average and $\Pr(H_{\rm old})$ must fit the shared sufficient allowance $0.0089999976$. The short-vertical exit is already in Part 151’s decomposition. The winning representative oriented to positive height determines $kU$ modulo $M$, and each possible winning $k$ is invertible modulo $q$ by Part 148’s height reduction. Hence the plane and the winner in the count use the same mark. Neither the toy intersection nor the terminal multiplicities in Parts 148 and 150 evaluate this average.
