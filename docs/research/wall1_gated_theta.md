# Gated theta ratios at draw 406

For the width-506 marginal restart, the probability that the incoming dual minimum is below $0.2018$ is **less than $1.539\cdot10^{-11}$**. The same good state works for every mark. The difficulty occurs after this exit has been paid. If the full dual theta sum at inverse temperature $1/(2t)$ is at most $2^{134}$, the **exact** capped ratio gives weight one to every gated upper-band candidate in that window. In particular, proving that the dual Gaussian is close to its zero-frequency term cannot suppress any such candidate.

A separate count of marks admitting a shorter vector gives $P<1-1.5325\cdot10^{-85}$. A finite state-dependent temperature certifies $P<1-1.52\cdot10^{-85}$ even with the original sum over gated candidates. Combining the first count with the audited horizontal-residual estimate gives $P+p_a<1-2^{-4435.956}$. These near-one bounds leave the shared allowance $0.00019770868$ open.

## 1. The mark and the normalization

Use the plain LWE $(511,512,3329)$, CBD(3) marginal design from Parts 108 and 169. Fix the physical state $S$ after 405 suffix appends, including its ordered ambient frame. Write $M\subset E$ for the retained rank-$d=505$ lattice, $D=\det M$, $K=P_E\mathbb Z^{910}$, and $H=K/M$. The fresh mark $u$ is uniform in $H$. The rank-$b=506$ window is $W_u=(M,0)+\mathbb Z(\tilde u,1)$ and has determinant $D$. Put $V_i=\pi^{i/2}/\Gamma(1+i/2)$, $g=(D/V_b)^{1/b}$, $a=0.990$, $\beta=1.097193$, and $c=477/500$. The two events here depend on the prefix and draw 406. [Finite chain, Propositions 1 and 5 and audit](wall1_finite_chain.md)

On $32.18553<g<203.888$, let $A_u$ contain the primitive sign pairs of positive absolute height and length $ag<s\le \beta g$ passing both forced tests. After projecting off the candidate, let $x$ be the designated shortest pair, $l=\|x\|$, and $h=(D/(sV_d))^{1/d}$. Require $1<l\le\sqrt{1+c^2 h^2}$ and a nonzero vector strictly shorter than $ch l^{-1/d}$ after projecting off $x$. Take $A_u$ empty off the $g$ range and $A_0=\varnothing$, as the vertical unit precludes an upper-band win there. Let $P$ be the probability that the designated first pair belongs to $A_u$. The separate event of probability $p_a$ requires both designated pairs and a passing witness to have old lifts, without the upper band restriction. [Selected-hit definition and audit](wall1_selected_hit_direct.md) · [Upper-band quotient and audit](wall1_upper_band_quotient.md)

Write $\Theta_t(L)=\sum_{y\in L}\exp(-\pi t\|y\|^2)$ and $Z_t=(\Theta_t-1)/2$. The latter counts all nonzero sign pairs, including multiples. Set $r_u(t)=Z_t(W_u)/Z_{2t}(W_u)$, $w_t(v)=\exp(-\pi t\|v\|^2)$. The pointwise inequality follows by summing $w_t(v)^2\le e^{-\pi t\lambda_1(W_u)^2}w_t(v)$. Thus each shortest pair has $r_u w_t(v)\ge1$. If a single candidate per mark is desired, take $c_u$ to be the least signed key in $A_u$, with key ordered by squared length and then signed ambient lexicographic order. Whenever the designated pair passes, it equals $c_u$. Therefore both expressions in
$$
 P\le \mathbb E_S\frac1{|H|}\sum_{u:A_u\ne\varnothing}
    \min(1,r_u(t)w_t(c_u))
 \le \mathbb E_S\frac1{|H|}\sum_{u\in H}\min\left(1,r_u(t)\sum_{v\in A_u}w_t(v)\right)
 \tag{1}
$$
are valid for any $t=t(S)>0$. An arbitrary preassigned candidate need not cover all possible winners. Both forms allow deletion of candidates beaten by a tie of smaller signed key in the whole window. [Soft minimum, Propositions 1–2 and audit](wall1_softmin.md)

## 2. A uniform ratio bound and the range in which the cap saturates

Put $p=b/2=253$, $A=t^{-p}/D$, $T=\Theta_{1/(2t)}(W_u^*)$, and $U=\Theta_{1/t}(W_u^*)$. Poisson summation gives the exact identity
$$
 r_u(t)=\frac{A U-1}{2^{-p} A T-1}.
 \tag{2}
$$
The subtractions remove the primal origin. In particular the zero-frequency lower bound $2^{-p}A-1$ on the denominator becomes nonpositive at $t\ge1/(2D^{1/p})$. The true denominator stays strictly positive. [Gaussian Poisson summation](https://cseweb.ucsd.edu/classes/wi24/cse206A-a/LecGaussian.pdf)

**Proposition 1.** Suppose $0<R\le1$ and $\lambda_1(M^*)\ge R$. For $s>0$ put
$$
 B_b(s,R)=\sum_{j\ge1}(2j+3)^b e^{-\pi s j^2R^2},\qquad
 L=\max\{2 Z_{2t}(M),\ 2^{-p}A-1\}.
$$
Every mark satisfies
$$
 r_u(t)\le C_S(t):=\min\left\{
 \frac{A(1+B_b(1/t,R))-1}{L},
 \;2^p+\frac{2^p-1}{L}\right\}.
 \tag{3}
$$
Furthermore $T\le1+B_b(1/(2t),R)$. The bound is finite for every $t>0$.

*Proof.* Pairing with the horizontal sublattice and the appended generator gives
$$
 W_u^*=\{(\xi,j-\langle\xi,\tilde u\rangle):\xi\in M^*,\ j\in\mathbb Z\}.
$$
A nonzero horizontal component already has norm at least $R$. With horizontal component zero, a nonzero integral vertical component has norm at least one. For any rank-$b$ lattice with this floor, the open balls of radius $R/2$ about its points are disjoint. Those centered in the shell $jR\le\|y\|<(j+1)R$ fit in the ball of radius $(j+3/2)R$, proving the shell estimate. The denominator in (2) is at least $L>0$ by the horizontal inclusion and $T\ge1$. Finally $U\le T$ yields $A U-1\le2^p(2^{-p}A T-1)+(2^p-1)$. This proves (3). Projection in the preceding steps takes the intrinsic dual section, as in the two Lean files. [AppendDual.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/AppendDual.lean) · [ProjectionDual.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/ProjectionDual.lean)

For a bound uniform also **across states**, let $D_R=(2/R)^b/V_b$ and $s_R=2(D_R/V_b)^{1/b}$. The open ball of radius $\lambda_1(L)/2$ embeds modulo any lattice $L$, so $V_b(\lambda_1(L)/2)^b\le\det L$. Applying this first to $W_u^*$ gives $D\le D_R$, then to $W_u$ gives $\lambda_1(W_u)\le s_R$. The denominator of (2) is therefore at least
$$
 L_R(t)=\max\left\{(2t)^{-p}/D_R-1,\;2\exp(-2\pi t s_R^2)\right\}>0.
$$
It follows that $r_u(t)\le 2^p+(2^p-1)/L_R(t)$ simultaneously on all states with the dual floor. On band histories one may further use $\lambda_1(W_u)\le2g<407.776$. Keeping the state data in (3) avoids this worst-case replacement.

The common old dual gives a second version of (3) which keeps the kick information. For $s>0$ set $\vartheta_s(x)=\sum_{j\in\mathbb Z}e^{-\pi s(j-x)^2}$. The exact expansion is
$$
 \Theta_s(W_u^*)=\sum_{\xi\in M^*}e^{-\pi s\|\xi\|^2}
           \vartheta_s(\langle\xi,\tilde u\rangle).
$$
In raw coordinates the argument modulo one is $\langle\ell(\xi),a_{\rm raw}\rangle/q$ for the fresh column and the horizontal label of Part 142. Poisson summation in one dimension gives $\vartheta_s(x)\le\vartheta_s(0)$ by taking absolute values of the Fourier series. A nearest integer gives $\vartheta_s(x)\ge e^{-\pi s/4}$. The zero horizontal frequency has argument zero for every mark. Thus one may replace the upper bound $1+B_b(1/t,R)$ used for $U$ by its minimum with $\vartheta_{1/t}(0)\Theta_{1/t}(M^*)$, and increase $L$ to the maximum of its old value and
$$
 2^{-p} A\left[\vartheta_s(0)+e^{-\pi s/4}(\Theta_s(M^*)-1)\right]-1,
 \qquad s=1/(2t).
$$
These estimates apply before averaging and require only the common state. The same shift inequality in rank $d$ on each primal height layer gives $Z_1(W_u)\le Z_1(W_0)$, used below. [Dual cusp, Theorem A](wall1_dual_cusp.md)

**Proposition 2.** At every mark with $T\le 2^{134}$, every candidate of length at most $\beta g$ has $r_u(t)w_t(v)>1$. This holds for the individual ratio itself.

*Proof.* Since $\Theta_t\ge\Theta_{2t}>1$, subtracting one from both entries increases their ratio. Thus $r_u\ge 2^p U/T\ge2^p/T$. Also $2^{-p}A T=\Theta_{2t}>1$, giving $t<T^{1/p}/(2D^{1/p})$. Using $D=V_b g^b$ yields
$$
 \log(r_u w_t(v))>p\log2-\log T-J T^{1/p},
 \qquad J=\frac{\pi\beta^2}{2V_b^{1/p}}.
 \tag{4}
$$
The right side decreases in $T$. At $T=2^{134}$ it lies in $(0.42514,0.42516)$. This proves the claim. In particular, on a state of Proposition 1, every $t\le\pi R^2/[2(b\log5+\log2)]$ gives $T\le2$ for all marks. Indeed $2j+3\le5^j$, $j^2\ge j$, and the shell bound is at most $\sum_{j\ge1}2^{-j}=1$. At $R=0.2018$ this sufficient temperature threshold lies in $(0.00007848162,0.00007848163)$. A dual sum larger than $2^{134}$ is a necessary condition for discounting a band candidate by this weight. It gives no sufficient condition.

There is also an obstruction to using a common upper bound even at colder temperatures. Write $m_{\max}=\max_u\lambda_1(W_u)^2$. Every common upper bound on $r_u(t)$ is at least $e^{\pi t m_{\max}}$, by applying the shortest-pair inequality at a maximizing mark. Consequently it assigns capped weight one to **every** candidate of squared length at most $m_{\max}$, including strict losers in other windows. The order-seven example below tests this loss separately from (4).

## 3. The dual exit at the correct time

**Proposition 3.** For $R=0.2018$, the exit probability at the incoming state after draw 405 satisfies
$$
 \Pr\{\lambda_1(M^*)<R\}\le
 \delta_R= q^{-510} V_{910}\big((qR)^2+910/4\big)^{455}
 <1.539\cdot10^{-11}.
 \tag{5}
$$

*Proof.* Part 142 identifies $M^*$ with a section of the raw graph dual for the $400\times510$ prefix. A raw dual vector has the form $(u,w)/q$, $w\equiv-A_{\rm raw}^{\mathsf T}u\pmod q$. A nonzero vector of norm below $R<1$ must have $u\not\equiv0$. For fixed such $u,w$ the probability of the congruence is $q^{-510}$, by independence and prime-field uniformity. An exit requires at least one unordered sign pair. For each eligible integer point $v=(u,w)$ with $0<\|v\|<qR$, take the half of its centered unit cube with $\langle v,y-v\rangle\le0$. Its volume is $1/2$, its squared radius about the origin is bounded by $(qR)^2+910/4$, and the half-cubes have disjoint interiors. Each sign pair consumes volume one, proving (5) by the first moment. The unrounded bound lies in $(1.53879,1.53880)\cdot10^{-11}$. This argument holds even though the retained section is chosen using the graph. The all-times $10^{-3}$ in Part 142 concerns varying radii, with $0.2018$ quoted at 407. Directly inserting the same radius at 405 into its full-cube bound gives $(0.00728912,0.00728913)$ before sign pairing. [Dual cusp, Theorem C and audit](wall1_dual_cusp.md) · [Inward half-cubes at the first selection](wall1_finite_chain.md)

## 4. The Gaussian count left by finite-group uniformity

For each upward candidate $v=(y,k)$, $y\in K$, $0<k\le \beta g<224<q$. Its only possible mark is $u_v=k^{-1}[y]\in H$, since $qH=0$. Let $I_S(y,k)$ test membership in $A_{u_v}$, including the band, primitivity, the two quotient gates, and any tie deletion being used. Set the test to zero outside the band. The linear mean left after a uniform estimate for the ratio is exactly
$$
 Q_S(t)=\frac1{|H|}\sum_{1\le k\le \beta g}\ \sum_{y\in K}
 I_S(y,k)e^{-\pi t(\|y\|^2+k^2)} .
 \tag{6}
$$
Restrict $I_S$ further to $v=c_{u_v}$ for the first expression in (1). Indeed the contribution of each incidence in the original average appears at precisely $u_v$. On the good state, (3), (6), and concavity of $x\mapsto\min(1,x)$ bound the conditional mean in (1) by $\min(1,C_S(t)Q_S(t))$. One may retain the per-mark caps for a sharper estimate.

For example, an explicit sufficient inequality for the target is
$$
 \mathbb E_S\!\left[\mathbf1_{\lambda_1(M^*)\ge R}
       \min(1,C_S(t)Q_S(t))\right]+p_a
 \le 0.00019770868-\delta_R .
 \tag{7}
$$
The right side exceeds $0.00019770866461$. Charging only $P$ on the exit makes (7) valid even if $p_a$ is bounded on the full law. Dropping $I_S$ and extending each horizontal sum to all of $K$ gives an explicit upper bound by Poisson summation,
$$
 Q_S(t)\le\frac{t^{-d/2}}{D}\Theta_{1/t}(K^*)\sum_{1\le k\le \beta g}e^{-\pi t k^2}.
$$
Even restricting to the interior shell $1.004g<\|v\|<1.097g$, the unweighted positive-height count with the gates and selection removed has conditional mean above $74.85$. This is a count with multiplicity. [Band plane hits, Proposition 3 and audit](wall1_band_plane_hits.md)

Neither this identity nor uniformity evaluates the retained $I_S$. At incidence $u_v$ the same window fixes both quotient tests. In the small-dual-mass regime Proposition 2 leaves exactly the fraction of marks having any gated candidate, regardless of the individual normalizers. Part 152 encounters a corresponding acceptance factor for a different draw. [Cylinder average and audit](wall1_cylinder_average.md) · [Selected-hit identity and audit](wall1_selected_hit_direct.md)

The selected **Haar upper bound** at matched determinant is $4.36018\cdot10^{-11}$. It combines a low-strip flag count with a high-strip void probability in the unconditioned Haar window. Equation (6) is a prefix-dependent weighted incidence count, with a different distribution. Using the rounded Haar upper bound merely as a scale, the allowance after (5) is between $4{,}534{,}415$ and $4{,}534{,}416$ times that scale before allocating anything to $p_a$. No comparison factor of this size has been established. [Haar comparison and audit](wall1_restart_haar_ratio.md) · [Haar numerical certificate](wall1_selected_hit_direct.md)

## 5. A finite-temperature numerical bound from shorter marks

**Proposition 4.** For $j=0,1$, put $L_j^2=(ag)^2-j$. On every band history a fraction at least
$$
 \eta_j(g)=\left(\frac2{d+2}\right)^2
 \frac{V_d}{V_b g}
 \left[\frac d{2(d+2)}\left(a^2-\frac{j+1}{g^2}\right)\right]^{d/2}
 \tag{8}
$$
of marks have $\lambda_1(W_u)\le L_j$. If $\lambda_1(M)>L_j$, the exhibited marks have a positive-height vector of length strictly less than $L_j$ and their first winner has positive height.

*Proof.* If $\lambda_1(M)\le L_j$, every mark has the required competitor. Otherwise put $\rho^2=L_j^2-1$, $r^2=\rho^2d/[2(d+2)]$, and $f=2/(d+2)$. Integrating a translated ball count over a fundamental domain of $K$ gives a translate of the radius-$r$ ball containing $n\ge V_d r^d/\det K$ points of $K$. For independent uniform points $X,Y$ in any nonempty subset of these points, $\mathbb E\|X-Y\|^2=2\mathbb E\|X-\mathbb E X\|^2\le2r^2$, by comparison to the ball center. If the subset consists of the $m$ points of one residue class modulo $M$, distinct points are at distance exceeding $L_j>\rho$. Thus $(1-1/m)\rho^2\le2r^2$ and $m\le1/f$. For the whole set the same variance identity and Markov give at least a fraction $f$ of ordered pairs at distance strictly below $\rho$. Fixing one first point with at least $fn$ such neighbors gives at least $f^2 n$ distinct difference classes. Each class has a representative $y$ with $\|(y,1)\|<L_j$. Dividing by $|H|$ and using $|H|\det K=D$ proves (8). Throughout the band $\eta_j\le f^2 (V_d/V_b)(d/(2(d+2)))^{d/2}/32<1$, as required in the first case.

For fixed $j$, the $g$-dependent factor is $g^{-1}(a^2-(j+1)/g^2)^{d/2}$. Its logarithmic derivative has the sign of $(d+1)(j+1)-a^2g^2$. The minimum on the closed interval occurs at one of the endpoints. Outward enclosures there are

| $j$ | $g=32.18553$ | $g=203.888$ |
|---:|---:|---:|
| 0 | $(7.6170,7.6171)\cdot10^{-85}$ | $(1.53258,1.53259)\cdot10^{-85}$ |
| 1 | $(5.9376,5.9378)\cdot10^{-85}$ | $(1.52310,1.52312)\cdot10^{-85}$ |

For $j=0$ each such mark rules out $P$. For $j=1$ it leaves a squared-length gap of at least one. Here is a finite $t=t(S)$ certificate for the full sum in (1). Write $m_u=\lambda_1(W_u)^2$, $N_u=|A_u|$, and $C=\max(1,Z_1(W_0)^2\exp(\pi[(\beta g)^2+(ag)^2]))$. Indeed $N_u\le e^{\pi(\beta g)^2}Z_1(W_u)$ by summing over the band, and $Z_1(W_u)\le Z_1(W_0)$ by the shift bound in Section 2. Hence $N_uZ_1(W_u)e^{\pi m_u}\le C$ on the exhibited marks. Take $t=1+\log(1000C)/\pi$ on band histories, and $t=1$ otherwise. Since $Z_t\le e^{-\pi(t-1)m_u} Z_1$ and $Z_{2t}\ge e^{-2\pi t m_u}$, the uncapped weight on the gap-one marks is at most $C e^{-\pi t}<0.001$. All other marks contribute at most one. Hence the rightmost expression in (1) is less than $1-1.52\cdot10^{-85}$. The $j=0$ probability bound is slightly sharper. These certificates use the original mark law without charging a dual exit.

**Corollary for the joint allowance.** The same argument gives $P+p_a<1-2^{-4435.956}$ when combined with Part 155. To see why the two near-one bounds can be combined, partition prefixes. On a band prefix with $\lambda_1(M)>ag$, the fraction $\eta_0(g)$ from (8) has a vertical first win below the band, excluding both events. Call this class of prefixes $B$. Everywhere outside $B$, $P$ is impossible.

Use the audited Part 155 good forced state $G_a$. Its old forced second length exceeds $\tau=1.19806583315$ and its forced $h\le h_*=204.219$. Set $n=504$, $r_a^2=(\tau^2-1)n/[2(n+2)]$, $p_*=2 V_n r_a^n/[(n+2)V_d h_*^d]$, and $\delta_a=0.009+10^{-3}/408$. Part 155 proves statewise that at least $p_*$ of the marks preclude the horizontal event on $G_a$, and unconditionally that its mass on $G_a^c$ is at most $\delta_a$. On $B\cup G_a$ the conditional joint probability is therefore at most $1-p_*$, since $\inf_g\eta_0(g)>p_*$. Off that union only the horizontal event can occur. If its mass there is $x\le\delta_a$, the union has mass at most $1-x$. This gives $P+p_a\le(1-p_*)(1-x)+x\le1-(1-\delta_a)p_*$. The base-two log of the subtracted term lies in $(-4435.955148,-4435.955147)$. [Inherited witness, Section 4 and audit](wall1_inherited_witness.md)

## 6. Enumeration and interval checks

* **Raw dual count.** For $q=5$, two horizontal coordinates and two columns, enumerate all 625 matrices and all integer $(u,w)$ of squared norm strictly between zero and four with $u\not\equiv0$. There are 56 eligible vectors. Testing $w=-A^{\mathsf T}u\bmod5$ gives respectively $136,344,88,48,9$ matrices with $0,2,4,6,8$ vectors. The mean is exactly $56/25$, verifying both the congruence weight and the sign-pair factor used in (5).
* **A strict loser at a different mark.** Take $M=7\mathbb Z^2$, $K=\mathbb Z^2$, $H=\mathbb F_7^2$. Enumerate $(X,Y,k)\ne0$ in $[-7,7]^3$ with $(X,Y)\equiv ku\pmod7$. Every window contains a vector of length seven, so this box suffices for its minimum. The numbers of marks at squared minima $1,2,3,5,6,9,14$ are $1,4,4,8,12,12,8$. At $u=(0,2)$, the primitive candidate $(0,-3,2)$ has squared length 13 and the minimum squared is five. Every common ratio majorant caps this candidate at one for all $t$. At $e^{-\pi t}=1/2$ its **individual** weight is in $(0.00404064601192,0.00404064601193)$. To reproduce the enclosure, sum $B^{-\|v\|^2}$ over lex-negative representatives in the box, for $B=2,4$. The omitted mass is bounded above by $2(24\cdot8^2+2)B^{-64}$ since a cube shell of index $j$ has $24j^2+2$ points and consecutive shell bounds decrease by a factor below $1/2$ from $j=8$. Divide the positive rational intervals and multiply by $2^{-13}$. This example tests uniformizing the ratio, independently of the distinct pooling failure in Part 170.
* **Both geometric gates.** In the Part 164 order-17 graph, re-enumerating the $17^3$ designs gave 1,734 upward band candidates, 816 first-gate passes and 24 both-gate passes on eight designs. All eight had a shortest gated pair, and exactly two had the signed winner. Thus the **unfiltered** markwise capped expression in (1) is exactly $8/4913$ at every $t>0$, whereas the signed probability is $2/4913$. With the whole-window equal-length tie deletion both bounds equal $2/4913$ at every temperature in this toy. For reproduction enumerate lex-negative representatives through squared norm three, using the graph congruence. Only squared norm two is in the band. Apply the two rational orthogonal projections in order, minimizing by squared norm and signed coordinates after the first, then testing the strict witness cutoff. Rounding lifts along the two axes bounds the raw squared norm needed by $3.04741<4$. The first length test alone needs squared norm below four as well. [Exact cutoff proof and audit](wall1_selected_hit_direct.md)
* **Numerical enclosures.** Scratch computations used exact integers and rational numbers for the graph tests, sign keys, projections and cubical sums. Real cutoffs and the displayed numerical bounds used outward intervals with at least 75 decimal digits, using $V_{2m}=\pi^m/m!$ and $V_{2m-1}=4^m m!\pi^{m-1}/(2m)!$. In particular (4) uses $J\in(56.84461716,56.84461718)$. Equation (5) uses the single integer power 455. No numerical comparison close to a gate boundary was decided by rounding to a displayed decimal.

**Remaining conjecture.** Under the marginal restart law, $P+p_a\le0.00019770868$. A proof by the individual ratios still needs a bound for the gated mark fractions on the adapted prefix law. More precisely it must control the marks with any gated candidate wherever (4) saturates, and the weighted gated candidates with their own denominators elsewhere, while leaving an allowance for the horizontal event. The fixed-time dual exit meets the required scale. None of the estimates here evaluates that terminal joint mass on the Haar scale.

## Audit

**Verdict — SOUND.** The fixed-radius exit, the pointwise saturation claim, both shorter-vector bounds and the order-17 masses hold. The shared target $P+p_a\le 0.00019770868$ remains open.

**Incoming state and draw 406.** At index 405 the raw graph has 510 columns and ambient dimension 910. Each eligible sign pair costs $q^{-510}$ in the first moment and occupies one unit of volume across its two inward half-cubes. Inclusion of the retained dual in the raw dual holds for each prefix, including when that prefix determines the retained section. At $R=0.2018$, a 288-bit outward interval calculation gives $1.53879922659\cdot10^{-11}<\delta_R<1.53879922660\cdot10^{-11}$. This one prefix event gives the floor simultaneously for every possible next mark. Part 172 applies the same count **after** appending draw 406, with 511 columns, dimension 911 and its own unrounded $R_0(406)=0.2009091560256\ldots$. Re-evaluation gives $4.59193101731\cdot10^{-15}<e_{406}(R_0(406))<4.59193101732\cdot10^{-15}$. That exit concerns a graph containing the realized fresh column. [Part 142, Theorem C](wall1_dual_cusp.md) · [Part 172, raw-exit audit](wall1_transference.md)

**Pointwise cap.** Removing the primal origin in both theta sums gives $r_u\ge 2^{253}U/T\ge 2^{253}/T$. Positivity of the denominator gives $t<T^{1/253}/(2D^{1/253})$. At the largest permitted $T=2^{134}$ and length $\beta g$, the decreasing lower bound in (4) is between $0.42514835$ and $0.42514837$. Thus every eligible candidate on that mark has uncapped weight strictly above one. In a mixed state, the contribution from marks satisfying the theta condition is precisely the fraction of **all** marks satisfying the condition and carrying at least one gated candidate. Other marks retain their individual caps. The proof uses each window's own ratio throughout. The $74.85$ comparison in Section 4 counts all positive-height shell vectors, including imprimitive vectors and repeated incidences at a mark. [Part 170, pointwise bound and audit](wall1_softmin.md) · [Part 161, Proposition 3](wall1_band_plane_hits.md)

**Shorter marks and the joint probability.** The two factors $2/(d+2)$ in (8) have separate roles. The ordered-pair second moment supplies that fraction of short neighbors for one center. The bound on occupancy in a single residue class supplies the second factor when counting distinct marks. At the smaller of the two endpoint values for each $j$, the 288-bit calculation gives $\eta_0>1.53258085\cdot10^{-85}$ and $\eta_1>1.52311189\cdot10^{-85}$. The derivative sign in Section 5 puts the minimum at an endpoint. This proves the stated bound on $P$, and the gap of one on the $j=1$ marks gives the stated finite-temperature bound since $0.999\eta_1>1.52\cdot10^{-85}$ there.

On $B$ the exhibited fresh winners exclude both events. On $G_a\setminus B$, $P$ is impossible and Part 155 excludes the horizontal event on at least $p_*$ of marks. With $U=B\cup G_a$ and $x=\Pr(\text{horizontal event},S\notin U)$, one has $\Pr(S\in U)\le1-x$ and $x\le\delta_a$. The events have disjoint first-winner heights, so their total mass is at most $(1-p_*)(1-x)+x$. Direct interval evaluation of the **deficit** gives $-4435.955148<\log_2((1-\delta_a)p_*)<-4435.955147$, which proves the strict joint bound without subtracting a tiny number from one numerically. [Part 155, whole-case audit](wall1_inherited_witness.md)

**Exact enumeration.** An independent scratch run over all 4,913 designs used integer and rational projections through raw squared norm four, signed ambient lexicographic ties, and 288-bit outward intervals for the real gate cutoffs. It found 1,734 band candidates, 816 first-gate passes and exactly three both-gate passes on each of eight designs. Every one of the 24 was shortest. The signed winner passed only at $(A,B,j)=(16,16,1)$ and $(16,16,16)$. On each of the eight designs a shortest candidate saturates the cap for every $t>0$. On every other design the gated sum vanishes. This proves the unfiltered capped mass $8/4913$ for all positive temperatures and the signed mass $2/4913$. Whole-window tie deletion gives $2/4913$ for both expressions in (1). Independent checks also reproduced the order-five histogram and the order-seven minima and rational weight enclosure. [Part 164, exact tests and audit](wall1_selected_hit_direct.md)
