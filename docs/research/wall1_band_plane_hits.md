# Selected plane hits above 0.97 times window GH

At width 506, the Part 159 first moment reaches the remaining allowance at **0.984890155625…** times window GH. A sharper count pays for winners through **0.975 GH** with probability less than **0.000003885638**, below the old charge through 0.97 GH. It pays for winners through **0.990 GH** with probability less than **0.008801064**, which leaves much less for the other events. The joint estimate across the whole band remains open.

There are two distinct obstructions. First, even the *exact* expected number of positive-height vectors in the shell from 1.004 to 1.097 GH exceeds 74 on every history outside the large-GH exit. Second, a specified positive-height candidate determines the fresh mark. Its probability of having no shorter competitor, conditional on its presence and the history, is zero or one. The estimates and exact counts below quantify both effects.

## Setting and budget

Fix the marginal restart for plain LWE $(511,512,3329)$, CBD(3). Just before draw 406 the incoming lattice $M$ has rank $d=505$ and determinant $D$. Write $b=d+1$, $q=3329$, $c=477/500$, $V_j=\pi^{j/2}/\Gamma(1+j/2)$, and $g=(D/V_b)^{1/b}$. Given the history $S$, the mark $U$ is uniform on $H=K/M$, where $K=P_E\mathbb Z^{910}$ and $E$ is the retained subspace. The window is $W_U=(M,0)+\mathbb Z(\widetilde U,1)$. Its designated signed shortest vector has length $s=\rho g$ and absolute height $k$. After projecting off it, the designated signed minimum has length $t$. Write $p$ for the minimum after projecting off that second vector. The two gates are
$$
 1<t\le\sqrt{1+c^2 h^2},\qquad p<ch\,t^{-1/d},\qquad
 h=g\left(\frac{V_b}{\rho V_d}\right)^{1/d}.
$$
The plant and draw 407 do not enter these statistics. The event here requires $k>0$. Write $P_{>w}$ for the unconditional mass passing both gates with $g<203.888$ and $w<\rho\le1.097193$. Write $H_{\rm old}$ for residual (a) of Part 151. The large-GH exit costs at most $1/816000$. Before charging any lower vertical strip, the remaining shared budget is $B_*=0.0089999976-1/816000$. After the published $0.000004038879$ charge, the rounded-down allowance is $A=0.00899473323$. [Restart law, Part 108](wall1_first_tour.md) · [Residual split, Part 151 and Audit](wall1_penultimate_tail.md) · [Part 159 and Audit](wall1_plane_hit_rounding.md)

## Where the published first moment crosses

Let $g_0$ be the step-405 lower bound for $g$ from Part 151, with $32.1855367820<g_0<32.1855367821$. Define
$$
 z(w)=wg_0\sqrt{2\pi/b},\quad
 \Theta(z)=1+\frac{2e^{-\pi z^2}}{1-e^{-3\pi z^2}},\quad
 J_b=\frac{e^{b/2}(2\pi/b)^{b/2}}{V_b},\quad
 M_0(w)=\tfrac12 J_b w^b\Theta(z(w))^d.
$$
**Proposition 1.** The following are enclosures for the unique roots of $M_0(w)$ at the indicated levels on $[0.97,1.097193]$.

| Level | Lower endpoint | Upper endpoint |
|---|---:|---:|
| $A$, using the stated remaining allowance | 0.984890155625034663 | 0.984890155625034665 |
| $B_*$, replacing the previous cumulative charge | 0.984891029426215074 | 0.984891029426215076 |
| One | 0.994102802043760458 | 0.994102802043760460 |

*Proof.* Part 159, equation (4), counts all positive-height window vectors with norm at most $wg$ and uses the monotonicity of $\Theta$ to replace $g$ by $g_0$ in that factor. The height is then invertible modulo $q$ on the good histories. For monotonicity in $w$, put $x=\pi z(w)^2$. The magnitude of the negative contribution to $d\log M_0/d\log w$ is at most $4dxe^{-x}(1+2e^{-3x})/(1-e^{-3x})^2$. It is below $10^{-10}$ at $0.97$ and decreases thereafter. The positive contribution is 506. Interval substitution at the endpoints gives the claimed crossings. On this interval $1<\Theta(z(w))^d<1+3.10\cdot10^{-14}$. At $w=1$, $M_0(w)$ lies between 19.94174 and 19.94176. At $w=1.097193$, it exceeds $4.8192\cdot10^{21}$. Thus the growing factor is $w^{506}$, the volume scaling for **candidate** winner lengths. This calculation measures neither the density of selected winners nor the number of plane witnesses. Both gates were discarded before taking the moment. ∎

The two budget conventions differ because $M_0(w)$ already counts the entire lower ball. Subtracting two upper bounds at $w$ and $0.97$ would not bound the shell between them.

## A sharper first moment for the lower strip

**Theorem 2.** On every history with $g<203.888$ and for $0.97\le w\le1.097193$, the expected number $N_{\le w}$ of positive-height vectors of norm at most $wg$ satisfies
$$
 \mathbb E[N_{\le w}\mid S]\le Cw^{506},\qquad 1.42274374393<C<1.42274374394.
 \tag{1}
$$
Here $C$ is the explicit upper-sum constant below. This improves on the Gaussian majorant by resolving radial energy in bins. All vertical selected hits through $w$ are covered, including the previously charged lower strip.

*Proof.* Put $R=wg$, $z=R\sqrt{2\pi/b}$ and $\Lambda=K\times\mathbb Z$. For every integer $1\le k\le R<q$, multiplication by $k$ permutes $H$. Hence the conditional expectation of the candidate count equals $|H|^{-1}$ times the number of $(y,k)\in\Lambda$ in the ball with $k>0$. For any nonnegative radial majorant, this is at most half its total sum on $\Lambda$, divided by $|H|$, by sign symmetry. The extended sum is only an analytic majorant. No random-mark law is used at heights divisible by $q$. Also $|H|\det\Lambda=D$.

For $a=b/2$ let $X(v)=a-\pi\|v\|^2/z^2$. Inside the ball, $X\ge0$. Choose $T=8$, $\delta=1/2$, $f(u)=(\sin(Tu/2)/(Tu/2))^2$ with $f(0)=1$, and $L=(\sin(T\delta/4)/(T\delta/4))^2$. For $j\delta\le X<(j+1)\delta$, the $j$th summand in
$$
 \frac{e^X}{L}\sum_{j\ge0}e^{-j\delta}f\big(X-(j+1/2)\delta\big)
 \tag{2}
$$
is at least one, since $f\ge L$ within half a bin. The sum is nonnegative everywhere. Its Fourier representation uses
$$
 f(u)=\frac1T\int_{-T}^T(1-|\tau|/T)e^{i\tau u}\,d\tau,
$$
which follows by integrating the triangular weight. For each bin, take absolute values after applying Poisson summation to its complex Gaussian. For $\eta=1+i\tau$ the Fourier transform of $e^{-\pi\eta\|v\|^2/z^2}$ is $z^b\eta^{-b/2}e^{-\pi z^2\|\xi\|^2/\eta}$. This follows by analytic continuation of the real Gaussian identity in $\Re\eta>0$. The resulting absolute lattice sum is bounded by
$$
 \frac{z^b}{\det\Lambda}(1+\tau^2)^{-b/4}
 \Theta\!\left(\frac{z}{\sqrt{1+\tau^2}}\right)^b.
$$
Indeed $K^*=E\cap\mathbb Z^{910}$ injects into $d$ integer coordinates by restricting to a nonzero minor of a basis matrix of $E$. Restriction does not increase lengths. Together with the height coordinate this bounds the dual Gaussian by a product of $b$ one-dimensional sums. Each is at most $\Theta$ by $n^2\ge1+3(n-1)$ for $n\ge1$. Absolute convergence of the Gaussians, compact frequency support and the geometric bin weights justify the sums and integrals. [Poisson summation and the Gaussian transform](https://cseweb.ucsd.edu/classes/wi24/cse206A-a/LecGaussian.pdf)

Set $z_m=z(0.97)$ using $g_0$ as in Proposition 1. Since $z\ge z_m$, multiplying (2) by the count normalization gives (1) with the following finite upper sum. Let $n=4096$, $h_0=T/n$, $x_j=jh_0$, $y_j=(j+1)h_0$. Define
$$
 C=\frac{J_b}{T L(1-e^{-\delta})}
 \sum_{j=0}^{n-1}h_0(1-x_j/T)(1+x_j^2)^{-b/4}
 \Theta\!\left(\frac{z_m}{\sqrt{1+y_j^2}}\right)^b .
 \tag{3}
$$
This bounds the integral bin by bin since its first two frequency factors decrease and its theta factor increases. The scale identity is $e^a z^b/D=J_b w^b$. Outward evaluation of (3) gives the stated enclosure. ∎

| Upper ratio $w$ | Upper charge for the whole lower strip | Sufficient allowance left for $P_{>w}+\Pr(H_{\rm old})$ |
|---:|---:|---:|
| 0.975 | 0.000003885638 | 0.00899488647 |
| 0.985 | 0.000678983651 | 0.00831978845 |
| 0.990 | 0.008801063430 | 0.00019770868 |

The last column rounds $B_*-Cw^{506}$ down using (3) before rounding the middle column. These are alternative cumulative decompositions. The large-GH exit is charged once in each. At the published lower-strip charge of $0.000004038879$, (1) covers at least $0.97507453$ GH. The new majorant meets $A$ at $0.99004258784\ldots$ and $B_*$ at $0.99004346621\ldots$. Its larger range does not give an allowance for the rest if the entire budget is spent at either crossing.

## The exact candidate count already exceeds one in the upper band

**Proposition 3.** On every history with $g<203.888$,
$$
 \mathbb E[\#\{v\in W_U:k(v)>0,\quad 1.004g<\|v\|<1.097g\}\mid S]>74.85,
 \tag{4}
$$
where $k(v)$ in this display denotes the signed height. This lower bound concerns multiplicities before choosing a winner. Thus even exact evaluation of the unselected ball count cannot by itself give the requested probability bound.

*Proof.* Use the deterministic positive-height counting measure $\mu$ on $K\times\mathbb Z_{>0}$ with mass $1/|H|$ per point. Its mass in the indicated shell is exactly the expectation by the height permutation argument. Put $r=1.05g$, $z=r\sqrt{2\pi/b}$, $z_*=1.05g_0\sqrt{2\pi/b}$, $a=b/2$, $l=1.004/1.05$, $u=1.097/1.05$. For $\theta_L(v)=\sum_{y\in L}e^{-\pi v^2\|y\|^2}$, real Poisson summation separately on the old coordinates and the height gives the exact mass of the tilted measure
$$
 Z(z)=\int e^{-\pi\|y\|^2/z^2}\,d\mu(y)
 =\frac{z^b}{2D}\theta_{K^*}(z)\big(\theta_{\mathbb Z}(z)-1/z\big).
$$
The subtraction removes the zero-height layer. For $\eta=l$ use the tail $\|y\|\le\eta r$, and for $\eta=u$ use $\|y\|\ge\eta r$. On the respective tail, the tilting weight is at most $e^{a(1-\eta^2)}e^{-\pi\|y\|^2/(\eta z)^2}$. Its fraction of $Z(z)$ is at most
$$
 E_\eta=e^{a(1-\eta^2+\log\eta^2)}\Theta(\eta z_*)^d
 \left(1+\frac{(1-1/\eta)_+}{z_*-1}+
 \frac{\Theta(\eta z_*)-1}{1-1/z_*}\right).
$$
Indeed, bound $\theta_{K^*}(\eta z)$ by the coordinate product and both denominator theta functions below by one. The positive-height factor ratio is at most $(\Theta(\eta z)-1/(\eta z))/(1-1/z)$, which gives the parenthesis after using $z\ge z_*>1$. Interval evaluation gives $E_l<0.373135$ and $E_u<0.373878$. On the remaining open shell the weight is at most $e^{-al^2}$. Consequently its untilted mass is bounded below by
$$
 (1-E_l-E_u)(1-1/z_*)\,\frac{J_b}{2}(1.05)^b e^{a(l^2-1)}.
$$
Evaluating before rounding the tail terms encloses this last expression between 74.85561 and 74.85562. No tilted law is asserted for the random mark. ∎

## Keeping shortestness in the joint count

**Proposition 4 (fixed and moving voids).** Fix a good history. For $L=0.97g$ set $A_L=\{\lambda_1(M)>L\}$ and $V_L=\{\lambda_1(W_U)>L\}$. For every event $F$ of the draw, including a relaxed plane-witness test,
$$
 0\le\Pr(A_L\cap F\mid S)-\Pr(V_L\cap F\mid S)
 \le\mathbf1_{A_L}\,C(0.97)^{506}<2.882\cdot10^{-7}.
 \tag{5}
$$
In particular the fresh void has probability above $0.9999997118$ whenever the old lattice clears the cutoff. This is an additive statement before conditioning on a witness; a rare witness can be concentrated entirely on void marks. This extends the analogous comparison at $0.954g$. [Part 153 and Audit](wall1_neargh_vertical.md)

For a fixed $l_0,w$ in the band, let $\mathcal F$ be the vertical candidates $v=(y,k)$, oriented to $k>0$, with $l_0g<\|v\|\le wg$, $y\in K$. Each determines one label
$$
 u_v=k^{-1}[y]\in H.
$$
Retain $v$ in $\mathcal F$ only if it is primitive in $W_{u_v}$ and **forcing** the first projection along $v$ passes the two gates, selecting $x$ by the usual signed rule in that quotient. In this test $h$ is evaluated at $s=\|v\|$. Give every window sign pair the key $(\|v\|^2,\min_{\rm lex}(v,-v))$. Let $n_S(v)$ count horizontal sign pairs of smaller key in $M$, plus the positive-height potential competitors $(y',k')\in K\times\mathbb Z_{>0}$ of smaller key with $u_{(y',k')}=u_v$. Then the conditional probability of the selected plane hit in this subband equals
$$
 \frac1{|H|}\sum_{v\in\mathcal F}\mathbf1_{\{n_S(v)=0\}}.
 \tag{6}
$$
In particular a joint *upper* bound retaining some shortestness is available from any count $0\le n'_S(v)\le n_S(v)$ of actual competitors. With $m_i=\sum_{v\in\mathcal F} n'_S(v)^i$ for $i=1,2$, it is
$$
 \Pr(\text{selected hit in subband}\mid S)
 \le \frac{|\mathcal F|-m_1^2/m_2}{|H|},\qquad 0/0:=0.
 \tag{7}
$$
One can take the smaller-key competitors at the candidate's own radius, including old ties, or just those within $0.97g$. Both use the same mark as the plane witness. The bound can always be capped at one.

*Proof.* Every old vector belongs to the window; on $A_L\setminus V_L$ a positive-height vector of length at most $L$ exists. Apply (1) at $w=0.97$. For (6), $qH=0$ and all candidates and their positive-height competitors have $0<k\le wg<q$. The equation $[y]=kU$ therefore has exactly one solution in $H$. All possible smaller keys in that window are accounted for by the horizontal test or by that same label. Every successful mark has exactly one designated sign pair, and its positive-height orientation appears exactly once. Conversely each surviving candidate gives such a mark. Finally $(\sum n')^2\le\#\{n'>0\}\sum(n')^2$ by Cauchy–Schwarz, proving (7). ∎

This identifies the dependence issue for a Janson-type argument. Conditional on a specified positive-height point, even in a flag with a fixed extra plane witness, all the window competitors have deterministic presence indicators given $S$. With no fixed point, two candidate-presence indicators with the same label coincide and those with different labels are disjoint. A large mean number of competitors can thus reflect repeated coverage of the same marks. A quantitative void bound at the *moving* radius would require counts of distinct covered labels, or mixed moments such as (7), on the relevant histories. Part 139's unconditional second moment on a fixed history does not provide these plane-weighted moments. [Part 139, Theorem 5](wall1_lyapunov.md) · [Finite-group fibers, Part 120](wall1_plane_count.md)

### Exact small graph checks

Each row enumerates every graph matrix with $j$ initial columns and one append. The band for both rows is $(0.97,1.097193]$. “Forced” counts candidate incidences passing both gates before checking shortestness. “Old key” removes a forced candidate if an old sign pair has a smaller key, including a length tie settled by the ambient rule.

| $(m,j,q)$ | Designs | Vertical candidates | Forced | Forced and fixed void | Forced after old key | Selected hits |
|---|---:|---:|---:|---:|---:|---:|
| $(1,2,17)$ | 4913 | 1734 | 24 | 24 | 2 | 2 |
| $(2,2,5)$ | 15625 | 5000 | 48 | 48 | 4 | 4 |

After deduplicating by design, the fixed void, existence of a forced hit, and their intersection have numerators $(4096,8,8)$ and $(13824,16,16)$ respectively. In each row every forced hit has the void, although the void probability is strictly below one. The strict product inequality also occurs conditional on a prefix, in four of the $17^2$ prefixes and eight of the $5^4$ prefixes respectively. The old-key test alone removed all losing forced incidences in these examples. These are graph restarts at the new lower cutoff; they provide no frequency estimate for the width-506 history law.

**Enumeration certificate.** For each $m\times(j+1)$ matrix over $\mathbb F_q$, enumerate all signed integer vectors of squared length at most three satisfying the graph congruences. For every positive-height candidate in the band, evaluate $P_{v^\perp}$ rationally on the list, select by squared length and signed ambient coordinates, and test the positive squared lengths after the second projection. Use the same raw list for all smaller-key competitors. To certify completeness, put $s_*^2=(1.097193g)^2$, $h_*=(q^m/(0.97gV_d))^{1/d}$, $t_*^2=1+c^2h_*^2$. A first projected minimum capable of passing the gate lifts with squared length at most $t_*^2+s_*^2/4$. When $t>1$, a plane witness below cutoff lifts with squared length less than $c^2h_*^2+t_*^2/4+s_*^2/4$. These follow by subtracting nearest multiples, first along the second direction in the first quotient, then along $v$ in the window. The maxima of these bounds and $s_*^2$ are below 3.482 and 3.342 respectively. Thus the raw integer ball through three suffices even for a forced candidate. Every candidate has raw entries in $\{-1,0,1\}$ and is primitive. Squared projections and keys were compared exactly, and all nonrational gate comparisons were separated by outward intervals. As a separate check, the void here excludes only unit vectors. A unit occurs exactly when a graph column vanishes, giving $(q^m-1)^{j+1}=4096,13824$ void designs directly.

## Remaining interval and reproducibility

There is a small deterministic exclusion at the upper endpoint. Rounding a lift of $x$ along the shortest $v$ gives $t^2\ge3s^2/4$. Together with the length gate this implies
$$
 \frac34\rho^2\le g^{-2}+c^2\left(\frac{V_b}{\rho V_d}\right)^{2/d}.
$$
Replacing $g$ by $g_0$ raises the right side. The left side increases and the right side decreases in $\rho$; their unique equality is in $(1.097192284143629678,1.097192284143629680)$. Hence $\rho\ge1.097192284143629680$ is excluded. The second rounding comparison in Part 159 does not exclude any draw passing the length gate at width 506. [Part 159, Propositions 1–2 and Audit](wall1_plane_hit_rounding.md)

For example, using the $0.975$ row leaves the sufficient condition
$$
 P_{>0.975}+\Pr(H_{\rm old})\le 0.00899488647.
$$
The mass from $0.975$ up to the deterministic upper cutoff, subject to both gates, still needs a history-averaged estimate. Equation (6) computes its conditional summand exactly; (7) gives a relaxation that keeps label collisions. Neither has been numerically bounded at width 506 tightly enough to close the budget. The rank-504 gated half-ball comparison up to $e^{o(d)}$ is **conjectural**. Its asymptotic notation alone gives no finite-width constant. Residual (a) is also open. [Part 158 and Audit](wall1_selected_scaling.md) · [Inherited witness, Part 155](wall1_inherited_witness.md)

All numerical enclosures above used 65-decimal-digit outward interval arithmetic. To reproduce the scales, initialize $V_0=1,V_1=2$ and use $V_n=2\pi V_{n-2}/n$. Initialize $L_0=400\log 3329$ and iterate $L_{i+1}=\max(L_i-\log3329,505L_i/506-\tfrac12\log56.2142)$ through $i+1=405$. Then $g_0=\exp((L_{405}-\log V_{506})/506)$. Evaluate the explicit finite sum (3) and the two real tail bounds in (4); the integral itself needs no floating-point quadrature. The roots in Proposition 1 and the upper gate were bracketed by interval sign tests with rational bisection endpoints. The parameters of the restart were fixed throughout.

## Audit

**Verdict — MINOR CAVEATS.** The four propositions and both toy rows check out. Two bookkeeping clarifications concern the $0.985$ row and the distinction between the $A$ and $B_*$ crossings. All stated sufficient allowances remain valid.

**Lower strip and crossings.** An independent 80-decimal-digit outward interval calculation used the factorial formulas for $V_{505}$ and $V_{506}$ and all 405 determinant updates. Substitution gave opposite signs at the endpoints of each of Proposition 1’s three brackets and at the two endpoints of the upper rounding cutoff. The correction to the logarithmic derivative is below $2.36\cdot10^{-12}$ at $w=0.97$ and decreases across the interval. Thus the Part 159 majorant crosses $A$ at $0.98489015562503466\ldots$. The factor $w^{506}$ comes from scaling the candidate ball in 506 dimensions. The calculation precedes shortest-vector selection and both gates.

In (3), the factor of two from integrating over positive and negative frequencies cancels the half used for positive heights. The interval upper sum gives $C\in(1.42274374393705,1.42274374393706)$. At $w=0.97507453$ the charge is $0.00000403886866748\ldots$, strictly below $0.000004038879$. At $w=0.990$ the charge is $0.00880106342945507\ldots$. Subtracting it from $B_*=0.00899877210980392156\ldots$ leaves $0.00019770868034885\ldots$ for the upper band and residual (a). This last decimal uses the unrounded charge. The old $0.00899473323$ allowance already deducts the earlier lower strip, which the new cumulative count includes.

Two details qualify the prose after the table. At $w=0.985$ the remainder is $0.00831978846002882\ldots$, so rounding down to the displayed precision gives $0.00831978846$. The printed $0.00831978845$ is conservative by one last-place unit. Also, under cumulative replacement the $A$ crossing still leaves $B_*-A=0.00000403887980392\ldots$. Only the $B_*$ crossing exhausts the shared allowance under that convention.

**Upper shell.** The auxiliary positive-height measure agrees with the exact conditional candidate count throughout the shell because every height there permutes the mark group. Its full tilted mass subtracts the horizontal layer via the term $1/z$. Bounding the two closed tails leaves the open shell, with tail-fraction bounds $0.3731339990903\ldots$ and $0.3738773437946\ldots$ (rounded here). The resulting lower bound lies in $(74.8556147604,74.8556147605)$ on every history with $g<203.888$. This rules out a useful direct Markov bound from the unselected candidate count. A first moment that retains selection or either gate concerns a different count.

**Joint count and toys.** In (6) a positive-height candidate fixes its mark. Comparing nonzero sign pairs by squared norm and then their signed ambient tuple covers shorter competitors and equal-length ties on that same mark. Exactly one candidate survives per successful mark. Cauchy–Schwarz in (7) counts how many forced candidates have a witnessed competitor, and the bound also holds when $m_2=0$.

An independent scratch enumeration used integer dot products for both projections, exact signed projected coordinates for ties, and outward intervals for the gates. The reverse-rounding bounds on raw squared length were below $3.481505$ and $3.341102$, respectively. Among 4,913 designs the 24 forced incidences occurred on eight designs, all eight satisfying the fixed void. Among 15,625 designs the 48 forced incidences occurred on sixteen designs, all sixteen satisfying the void. The void counts were 4,096 and 13,824, so the product strictly underestimates each intersection. The same strict inequality held on four and eight prefixes, respectively. The old-key test and full selection both left two and four incidences, respectively. These finite checks establish the claimed examples of dependence. The width-506 selected upper-band probability and residual (a) remain open.
