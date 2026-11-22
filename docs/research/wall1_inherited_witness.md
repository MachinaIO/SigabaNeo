# Inherited witnesses at selection 406

Under the unconditioned width-506 restart, write $P_a=\Pr(H_{\rm old})$ for case (a) of Part 151. The inherited minimum is a minimum **after** projection off the horizontal winner. Three successive old directions enter its plane test. Equation (1) gives the exact conditional probability from the state before selection 406, including two comparisons against the same fresh column.

A non-horizontal projection preserves every nonzero old vector already below a fixed physical cutoff, with probability one conditional on such a projection. Except on an event of probability at most $10^{-3}/408+2^{-53.8086}$, every raw lift of the inherited minimum in the 510-column graph has length **greater than $6/5$ times its final length**. This leaves vectors shortened by selection, including projections of design-independent vectors. The unconditional bounds obtained here are
$$
  2^{-1909214.864}<P_a<1-2^{-4435.956}.
$$
The upper bound does not give a percent-level allocation for case (a). All probabilities concern the uniform design. The independent CBD(3) plant and draw 407 are outside this event. [Part 117 restart](wall1_idea_round2.md) · [Part 151, definitions and audit](wall1_penultimate_tail.md)

## 1. Exact conditional probability and backward recursion

Put $q=3329, Q=q^{400}, d=505, c=0.954, G_d=V_d^{-1/d}$, where $V_j$ is unit-ball volume in dimension $j$. Fix the state $S$ after 405 suffix selections, including the ambient frame for signed lexicographic ties. Its retained lattice is $M$, its finite mark is $H$, and $U$ is uniform on $H$. In the old lattice alone, successively select a signed shortest vector $v$ of $M$, a signed shortest vector $x$ of $N=P_{v^\perp}M$, and a shortest vector of $P_{x^\perp}N$. Denote their lengths by $s,t,z$. Define
$$
 D=\det N=\det M/s,\qquad h=G_dD^{1/d},\qquad
 r(h)=\sqrt{1+c^2h^2},\qquad
 J(S)=\mathbf1_{\{1<t\le r(h),\ z<ch\,t^{-1/d}\}}.
$$
On a horizontal win the actual quotient has rank $d$ and determinant $D$, because the new coordinate has height one. The lattice $N$ itself has rank $d-1$. The length cutoff is history dependent. Part 151 proves $30.5692<r(h)<3221.644$ on actual histories. Using 30.57 as an upper cutoff would omit part of the event.

For a lattice $K$, a marked class $a$, and a fresh unit axis, let $b_K(a)$ indicate that the signed winner of $K+\mathbb Z(\tilde a,1)$ has fresh coordinate zero. Use the inherited frame for this test. Write $f:H\to H'$ for the map induced by forcing the projection along $v$, with $H'\subset\operatorname{span}(N)/N$ its image. Then
$$
 F(S):=\Pr(H_{\rm old}\mid S)
  =\frac{J(S)}{|H|}\sum_{u\in H} b_M(u)b_N(fu).
 \tag{1}
$$

**Proof.** If the first comparison selects horizontally, it selects $v$. The full quotient is then $N+\mathbb Z(\widetilde{fu},1)$. Its designated minimum has fresh coordinate zero exactly on the second comparison, in which case it equals $x$. Projecting off $x$ again leaves fresh height unchanged. Thus the possible witnesses of height zero are precisely the nonzero vectors of $P_{x^\perp}N$. Existence of one strictly below the required threshold is exactly the test on $z$, including when a fresh witness also exists. Conversely these two comparisons and $J=1$ furnish all defining conditions. Uniformity of $u$ gives (1). Both comparisons use one draw, and signed equal-length competitors enter both. The old saturated rank-three lattice obtained by lifting the first two lines and a primitive shortest witness has covolume $stz$, by successive primitive basis extension. Rounding a lift of $x$ along $v$ gives only $s^2\le t^2+s^2/4$, hence $s\le 2t/\sqrt3$. Replacing $t$ in $J$ by $\lambda_1(M)=s$ changes the test. [Part 108](wall1_first_tour.md) · [Part 120](wall1_plane_count.md) · [Part 144](wall1_horizontal_core.md) · [Part 146](wall1_subspace_void.md)

There is a small one-sided error if one keeps just the first comparison. With $w_M=|H|^{-1}\sum b_M$,
$$
 0\le \mathbb E[Jw_M]-P_a<1.226519\cdot10^{-9}.
 \tag{2}
$$
On the difference event, $v$ actually wins, the old candidate has $t\le r(h)$, and a fresh vector beats or ties it in the quotient. The unconditioned projected-mark count at radius $r(h)$ is exactly the majorant of Part 151 (6). States whose forced determinant is outside the actual range have $w_M=0$. No independence between the comparisons is used. [Part 151, §2 and audit](wall1_penultimate_tail.md)

For $i=404,\ldots,0$, set $F_{405}=F$ and recursively
$$
 F_i(S)=|H_S|^{-1}\sum_{u\in H_S} F_{i+1}(\Phi(S,u)),
 \qquad P_a=\mathbb E_{A_0} F_0(S(A_0)),
 \tag{3}
$$
where $A_0$ is the uniform $400\times105$ restart graph and $\Phi$ is the actual signed window selection followed by projection and mark update. The tower property proves (3) by backward induction, since each unread raw column maps uniformly onto the current mark. The observable at the end of this recursion is the joint test (1).

## 2. What survives a step

**Fixed-vector survival.** Fix a state, a nonzero $y\in M$ of length at most $u_0$, and its designated old winner $v_0$. For the actual window winner $w=(a,k)$,
$$
 \Pr(0<\|P_{w^\perp}(y,0)\|\le u_0\mid S)
   =1-\mathbf1_{\{y\parallel v_0\}}w_M.
 \tag{4}
$$
Indeed its projected squared norm is $\|y\|^2-\langle y,a\rangle^2/\|w\|^2$. It can vanish only if $k=0$ and $y\parallel v_0$. Exact length preservation requires orthogonality. Remaining below $u_0$ allows arbitrary shortening. For an old span $T$, the same formula for preservation of dimension has indicator $\mathbf1_{\{v_0\in T\}}$. When dimension survives, projection contracts all lengths and all sublattice covolumes, by the Gram determinant or the singular values of an orthogonal projection.

The same survival law applies to an old witness with two fixed upper cutoffs. For independent $y,z$ in the old lattice, prescribe upper bounds on $\|y\|$ and $\operatorname{dist}(z,\mathbb R y)$. If the pair meets both, its image meets both whenever it stays independent. Indeed, writing $P=P_{w^\perp}$, one has
$$
 \operatorname{dist}(Pz,\mathbb R Py)
 \le \|P(z-\alpha y)\|\le \|z-\alpha y\|
$$
for every real $\alpha$. Minimize at the old orthogonal projection coefficient. The probability that the two independent images still meet the bounds is exactly $1-w_M\mathbf1_{\{v_0\in\operatorname{span}(y,z)\}}$. This statement concerns existence of the pair. A different line can become the designated minimum.

For a prescribed old vector, track its successive images $y_i$ until the first zero. If $C_i$ denotes survival up to time $i$, then
$$
 \Pr(C_{i+1})=\Pr(C_i)-
 \mathbb E[\mathbf1_{C_i}\mathbf1_{\{y_i\parallel v_{0,i}\}}w_{M_i}].
$$
This follows by conditioning (4) on the actual history. The fixed physical upper cutoff persists on $C_i$. A lower threshold such as $t>1$, primitivity, or winning the next shortest-vector comparison requires further tests. On a non-horizontal step, the image of the old lattice has index $|k|$ in the quotient. Indeed the window modulo the old lattice is $\mathbb Z$ via height, and adding the primitive winner to the old lattice kills exactly $k\mathbb Z$. For $|k|=1$ every output has an old lift. For $|k|>1$ new cosets can contain the designated shortest vector. For example, in $x\equiv3k\pmod7$ the signed winner is $(-1,2)$. Heights zero and one have minima 7 and $\sqrt{10}$, and heights of magnitude at least three have length at least three. The output spacing is $7/\sqrt5$, while the image of $7\mathbb Z\times\{0\}$ has spacing $14/\sqrt5$. [Part 139, Theorem 4](wall1_lyapunov.md)

For an old vector longer than $u_0$, entry below cutoff on a vertical win is equivalent to
$$
  |\langle y,a\rangle|^2\ge\|w\|^2(\|y\|^2-u_0^2).
$$
For a varying cutoff, substitute $u_0=r(G_d(\det M/\|w\|)^{1/d})$ into this squared inequality separately for each draw. The inequality also holds automatically when its right-hand side is nonpositive. Its joint probability on vertical wins is obtained by counting precisely those $u\in H$ whose selected $w(u)$ passes this inequality and has $k\ne0$, divided by $|H|$. Part 142 gives uniformity of the chosen Voronoi representative for a uniform **class**. Conditional on $|k|=1$, only representatives passing the winner test occur. Equation (4) already attains one for every old vector on every vertical draw. Neither that uniformity nor Part 105's Haar-parent estimate supplies a per-step factor smaller than one for fixed-cutoff survival. Along a string of horizontal pullbacks each complete preimage of a witness flag also gains the kernel line and hence one rank. [Part 142, Theorem B and audit](wall1_dual_cusp.md) · [Part 105](wall1_selection_law.md) · [Horizontal depth and its audit](wall1_depth_truncation.md)

## 3. Which raw vectors can be ancestors?

On a horizontal 406th win, all 406 removed directions lie in the **old** 910-dimensional raw space (400 output coordinates and 510 inputs). Let $T$ be their span, $P=P_{T^\perp}$ within this space, and
$$
  \mathcal M=\{(b,y)\in\mathbb Z^{400}\oplus\mathbb Z^{510}:b\equiv Ay\pmod q\},
  \qquad K=\mathcal M\cap T .
$$
The old quotient is $N=P\mathcal M$. A point $x=Pz$ has exactly the raw lifts $z+K$, by the kernel of $P$. Consequently it has a lift in the initial graph exactly when the last 405 input coordinates of $z$ belong to the corresponding coordinate projection of $K$. Subtracting that kernel vector gives the required lift. This distinguishes membership in the pre-406 graph from membership at restart.

**Design-independent lifts.** The intersection of all raw graph lattices of this size equals $q\mathbb Z^{910}$. The zero design first forces $b=0\bmod q$. Varying a single column then forces each $y_j=0\bmod q$. Conversely all such multiples belong to every graph. A specific $x=Pz$ has a design-independent raw lift exactly when $z\in q\mathbb Z^{910}+K$. More precisely, if $e$ is the dimension of the span of the input residues of $K$, then
$$
  N/P(q\mathbb Z^{910})\simeq\mathbb F_q^{510-e},\qquad e\le406.
 \tag{5}
$$
Reduction of the input tuple identifies $\mathcal M/q\mathbb Z^{910}$ with $\mathbb F_q^{510}$. Taking the quotient by the image of $K$ proves (5). The rational kernel has rank 406 because the frozen directions have independent integral lifts. Thus every retained vector has a multiple by $q$ with a design-independent lift, while a given primitive vector requires the displayed residue test. The index alone gives no sampling law for the designated minimum.

**Raw length bound.** For the graph on $n$ input and output coordinates in total, at any fixed $0<R<q$,
$$
 \Pr(\exists z\ne0\text{ in the raw graph with }\|z\|\le R)
 \le C_n(R):=\frac{V_n(R+\sqrt n/2)^n}{2Q}.
 \tag{6}
$$
A candidate with zero input residue cannot belong at this radius. Every other fixed candidate has membership probability $1/Q$, by a nonzero coefficient of an independent uniform input column. The disjoint unit cubes of integer candidates fit in the ball of radius $R+\sqrt n/2$. Counting sign pairs and using the union bound proves (6), before any history is selected.

* At restart $h_0=G_d Q^{1/d}$ bounds every actual $h$. The probability that **any** initial raw vector is already as short as the full final cutoff $r(h_0)$ is at most $C_{505}(r(h_0))<1.3630\cdot10^{-10}$. Initial $q$-axes and their nonzero integer combinations are longer than this cutoff.
* At time 406, Part 151 §4 gives $h<204.219$ outside probability $10^{-3}/408$. On this event $H_{\rm old}$ implies $t<194.827493$. If even one of its old raw lifts has norm at most $6t/5$, the *unconditioned* 910-dimensional graph has a vector of length at most $6r(204.219)/5$. By (6) the joint event costs less than $2^{-53.8086}$. Thus the total contribution of such lifts to $P_a$ is at most $10^{-3}/408+2^{-53.8086}$, without conditioning the raw graph on the dual estimate.
* Outside that union of events, every old lift $z$ of the selected $x$ satisfies $\|P_Tz\|^2/\|z\|^2>11/36$ by Pythagoras. For any nonzero raw $q$-multiple projecting to $x$, already on $h<204.219$ the lost fraction exceeds $1-(r(204.219)/q)^2>0.9965749$. In particular, among all 910 coordinate axes at most 407 can have projected $q$-axis length at most $r(204.219)$, including zero images. Sum $\|P_T e_j\|^2$ over the axes to obtain $\operatorname{tr}P_T=406$, and divide by the required lost fraction. These are length and incidence tests on a selected span. Its orientation is design dependent. [Part 147, last-used-coordinate count](wall1_uncovered_lines.md) · [Part 151, determinant and dual bounds](wall1_penultimate_tail.md)

## 4. Bounds on the whole horizontal residual

Equation (1) gives $F(S)\le1-|H|^{-1}\le1-Q^{-1}$ on every history. At zero displacement either the fresh unit preempts the old winner or it remains in the quotient, making the minimum at most one.

**A design-averaged upper bound.** Put $n=504, \tau=1.19806583315, h_*=204.219, \rho=\sqrt{\tau^2-1}$, and define
$$
  a=\rho\sqrt{\frac{n}{2(n+2)}},\qquad
  p=\frac{2}{n+2}\frac{V_n a^n}{V_d h_*^d},\qquad
  \delta=0.009+10^{-3}/408 .
$$
Then $P_a\le 1-(1-\delta)p<1-2^{-4435.956}$.

**Proof.** Call a pre-draw state good here if its forced $t>\tau$ and $h\le h_*$. On a good state, let $L'\supset N$ be the inverse image of the projected mark $H'$ in the span of $N$. It has determinant $D/|H'|$. Some translate of the ball of radius $a$ contains $m\ge |H'|V_n a^n/D$ points of $L'$, by integrating the count over a fundamental domain. Those points represent distinct classes modulo $N$, since $2a<\tau<t$. For independent uniform $X,Y$ among the $m$ points, $\mathbb E\|X-Y\|^2=2\mathbb E\|X-\mathbb EX\|^2\le2a^2$, by taking the ball center as a candidate mean. At least the fraction $1-2a^2/\rho^2=2/(n+2)$ of ordered pairs have distance strictly less than $\rho$. Fix a first point attaining at least this fraction. Its short differences represent distinct marked classes. A proportion at least $p$ of $H'$ therefore have representatives shorter than $\rho$, since $D=V_d h^d\le V_d h_*^d$. This uses the fundamental-domain form of Blichfeldt's argument. [Fukshansky, *Geometric Number Theory*, §1.4](https://www1.cmc.edu/pages/faculty/lenny/papers/GNT_lecture_notes.pdf)

The forced image $fU$ is uniform before any winner comparison. Each such short class supplies a fresh height-one vector of length less than $\tau<t$ in the forced quotient. Hence it precludes case (a), regardless of the first comparison. On $H_{\rm old}$ the forced values are the actual values. Part 151 (4) and its crossing interval give $\Pr(t_{\rm actual}\le\tau)\le0.009$, and its time-406 dual bound pays $10^{-3}/408$ for $h_{\rm actual}>h_*$. Writing $g$ for the good-state probability and $e=\Pr(H_{\rm old},S\text{ outside good})\le\delta$, we have $P_a\le(1-p)g+e\le(1-p)(1-e)+e$. This proves the assertion. [Part 151, §§1 and 4](wall1_penultimate_tail.md)

**A reachable obstruction.** Among the first 510 columns let exactly 104 be nonzero. At every one of the 405 selections at least one active column is zero, since the window has 106 active columns. All unit vectors of the integral graph are signed zero-column axes. Deleting one preserves every nonzero column, in order. Immediately before draw 406 there is exactly one old zero axis. It wins against every fresh draw, including a zero draw, by the signed tie rule. Its quotient is the ordinary coordinate graph on the 104 surviving columns plus the fresh one.

Conditional on their positions the surviving columns are independent uniform nonzero. Require the first three to coincide, at cost $(Q-1)^{-2}$. Their differences give two independent old vectors of length $\sqrt2$. The old quotient contains no unit, and its chosen old minimum has length $\sqrt2$. At least one of the two differences has a nonzero projection off that minimum, of length at most $\sqrt2$. Here $s=1, D=Q$ and both cutoffs exceed $\sqrt2$ since $G_d\ge1/2$ and $Q/\sqrt2>4^d$. A fresh vector of norm at most $\sqrt2$ can only have unit height and old part zero or a signed coordinate unit. This excludes at most $1+800+2\cdot104=1009$ raw draws, namely zero, the signed output units and the signed surviving columns. All other draws give case (a), for any tie between old roots. Consequently
$$
 P_a\ge\binom{510}{104}\frac{(Q-1)^{104}}{Q^{510}}(Q-1)^{-2}
            (1-1009/Q)>2^{-1909214.864}.
$$
On the subfamily where all 104 nonzero columns equal a common $v$ of support at least two, the conditional probability is exactly $1-803/Q$. The old signed root is minus the first graph unit plus the last old graph unit. At a draw $\pm v$, a fresh root with negative first graph coordinate and zero last old coordinate precedes it. At $\pm e_i$, a negative output coordinate precedes every old root. Zero supplies a strictly shorter fresh unit. These are all exceptions by the same height-one list. This gives nearly certain conditional failure of the desired lower-tail guarantee on a rare history even with $t>1$. [Zero-column audit](wall1_horizontal_core.md) · [Signed root comparisons in Part 146](wall1_subspace_void.md) · [Related terminal families in Part 149](wall1_long_lines.md)

## 5. Verification and remaining gap

One scratch enumeration used one output coordinate over $\mathbb F_3$, three initial graph inputs and one append. For each of the 81 graphs it compared signed squared-length/ambient-lexicographic minimizers before and after exact rational projections. Replace the two scale tests in $J$ by $1<t^2\le4$ and $z^2<3$. The direct quotient test agreed with (1) on every graph. There were 71 horizontal first wins, 47 with both designated lines horizontal, 60 draws whose pre-state passed $J$, and 26 inherited events. Eight of the 26 had $s>t$. Equation (4) agreed on all 2,268 pairs of draws and nonzero old vectors with squared length at most four, with 2,012 surviving. To reproduce the enumeration, list the integer vectors of squared norm at most 14 satisfying each graph congruence. Each projected minimum is at most three from the spanning projected 3-axes. Rounding successive lifts in reverse order bounds the squared norm needed for the third minimizer by $9+9/4+9/4<14$.

A second exact check used two output coordinates over $\mathbb F_5$, three copies of a common nonzero column of support two, and one old zero. Enumerating signed vectors of squared length at most two suffices for both comparisons. The old zero won all 400 draws over the 16 choices of common column. Exactly 288 second comparisons chose the old minimum, as $16(25-7)=288$. A rank-one graph check gave old-image index two for the example modulo seven in §2.

The numerical bounds used 50-decimal-digit outward-rounded interval operations in scratch storage. Generate $V_0=1, V_1=2, V_j=2\pi V_{j-2}/j$. Substitution gave $r(h_0)\in(3221.64340609,3221.64340610)$, $6r(h_*)/5\in(233.79299086,233.79299088)$, and $\log_2 C_{910}(6r(h_*)/5)\in(-53.808697,-53.808696)$. The logarithms of $p$ and $(1-\delta)p$ are in $(-4435.942101,-4435.942100)$ and $(-4435.955148,-4435.955147)$, respectively, in base two. The logarithm of the displayed lower bound belongs to $(-1909214.863455,-1909214.863454)$.

**Conjecture (open).** Under the marginal restart, $P_a+\Pr(V_{\rm mid})\le0.0089999976$. For case (a) the missing quantity is the expectation of (1), or to within (2), the probability-weighted old flag test $\mathbb E[Jw_M]$. The raw-length estimate bounds the part with a near-length raw lift. The remaining part permits substantial shortening of every raw lift and requires both the designated minimum and a witness in the old quotient. Equation (4) does not suppress it as a product of survival probabilities. No split of the joint allowance between the two residual cases follows from these results.

## Audit

**Verdict — SOUND.** The recursion, fixed-cutoff survival claim, raw-lift estimate, and unconditional bounds hold under Part 117’s marginal restart law with Part 108’s signed ambient tie rule. No correction is required.

**Recursion.** On a horizontal first win the selected line is the forced old line, so the second comparison uses exactly the projected class of the same draw. When both wins are horizontal, both projections preserve fresh height. The smallest nonzero height-zero witness then has length $z$, even if a fresh witness is shorter. This proves the indicator in (1) draw by draw, including ties and the strict witness cutoff. Averaging over the uniform mark at each of the preceding 405 transitions and then over the initial graph gives (3). On a first horizontal win with $J=1$, failure of the second comparison requires a fresh competitor of length at most $r(h)$, so Part 151 (6) also gives (2).

**Witness geometry.** For a vertical winner the projection kernel meets the entire old space only at zero. Thus all old independent pairs retain rank simultaneously. For $P=P_{w^\perp}$, minimizing $\|P(z-\alpha y)\|\le\|z-\alpha y\|$ over $\alpha$ bounds the projected witness distance by the old one. Multiplying by $\|Py\|\le\|y\|$ shows that the parallelogram area also cannot increase. Saturating the image pair in the output lattice can only decrease its covolume further. This proves survival with probability one on vertical draws for fixed upper cutoffs, including strict ones. The designated-line comparison, the lower cutoff $t>1$, and the history-dependent thresholds in $J$ still require their own tests.

**Raw lifts.** On $H_{\rm old}$ with $h\le204.219$, any qualifying lift gives a nonzero vector in the 910-dimensional pre-draw graph of norm at most $6r(204.219)/5<233.792991<q$. The graph is uniform marginally, so (6) applies before either the history or the dual test is imposed. Independent 65-decimal-digit outward-rounded arithmetic gave $-53.808697<\log_2 C_{910}(6r(204.219)/5)<-53.808696$. Adding Part 142’s single-time exit probability as in Part 151 gives
$$
 \Pr\!\left(H_{\rm old}\ \text{and}\ \exists\,\text{old raw lift of }x\text{ of norm }\le6t/5\right)
 \le 10^{-3}/408+2^{-53.8086}<2.450981\cdot10^{-6}.
$$
This bounds the contribution to $P_a$. Conditioning on $H_{\rm old}$ would require dividing the joint bound by $P_a$.

**Whole case.** On a good forced state, $2a<\tau<t$ makes the points in the translated ball distinct modulo $N$. From one point, at least the fraction $2/(n+2)$ of differences have norm strictly below $\rho$, by the ordered-pair second moment. The uniform image mark therefore gives a fresh competitor strictly shorter than $\tau$ with probability at least $p$. On $H_{\rm old}$ the forced and actual values agree, so Part 151 bounds the mass $e$ of inherited events outside the good states by $\delta$. Good states have mass at most $1-e$, yielding $1-P_a\ge(1-e)p\ge(1-\delta)p$. The interval calculation gave $\log_2((1-\delta)p)\in(-4435.955148,-4435.955147)$ and placed the log of the reachable-family lower bound in $(-1909214.863455,-1909214.863454)$. Both endpoints round in the stated directions. The resulting upper bound leaves the shared $0.0089999976$ allowance for the horizontal and vertical cases open.

**Finite checks.** A separate scratch enumeration over $\mathbb F_3$ compared exact rational projections in the full window against the two forced comparisons for every draw. The event indicators agreed on all 81 graphs. Of the 27 initial graphs, 14 had conditional probability zero and 13 had conditional probability $2/3$, giving $26/81$ overall. The counts were 71 horizontal first wins, 47 joint horizontal wins, 60 draws passing $J$, and eight inherited events with $s>t$. The fixed-vector test agreed on all 2,268 instances, with 2,012 survivors. Over $\mathbb F_5$ the old zero axis won all 400 draws. For each common column $v$, the second comparison chose fresh precisely on $0,\pm v,\pm e_1,\pm e_2$, leaving 288 old second wins.
