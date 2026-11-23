# The small-area tail in the selected rank-505 lattice

Let $a=1352/\sqrt3=780.577563944\ldots$, the exact cutoff corresponding to radius 26. Write $N_a(L)$ for the number of unoriented saturated rank-two sublattices of Euclidean area at most $a$, and $p(D)$ for the probability $N_a\ge1$ in a rank-505 Haar lattice of determinant $D$. At the determinant floor $D_*=\exp L_{406}$,
$$
 2.00059\cdot10^{-58}<p(D_*)<2.07179\cdot10^{-58}.
$$
The rank-two mean is $7.64066\cdot10^{-58}$ to six significant figures. Planes sharing a short line cluster. The upper bound makes the requested $3329^{13.6133}$ comparison worth **at most $1.84782\cdot10^{-10}$**, even before averaging over determinants.

For the finite law, a hit forces the window winner immediately preceding it to have length at most $33.22505$. The probability of **any** hit through selection 154 is below $5.284\cdot10^{-15}$. The probability of a hit at a positive-height selection anywhere through draw 394 is below $2.067\cdot10^{-12}$. The estimates below leave two contributions unbounded at the required scale. They are horizontal wins with an inherited short direction and positive-height wins late in the tour. The determinant-matched comparison remains open. All probability statements here concern the unconditioned Part 108 marginal restart before draw 407. [Part 108](wall1_first_tour.md) · [Part 190](wall1_rank2_transverse.md) · [R59 and audit](wall1_plane_comparison.md#audit)

## Haar probability and multiplicities

Use $n=505, m=n-2, V_j=\pi^{j/2}/\Gamma(1+j/2)$. Put $c=3/\pi$. For a marked plane write $A$ for its area, $s_P$ for its shortest length, and $y=A/s_P^2$. Kim's one-sublattice formula gives exactly
$$
 U(D)=\mathbb E N_a=\frac{(n-1)\pi V_nV_{n-1}}{24\zeta(n)\zeta(n-1)}\frac{a^n}{D^2}.
$$
The general constant for rank two is $\binom n2 V_n V_{n-1}\zeta(2)/(n V_1V_2\zeta(n)\zeta(n-1))$. The area density divided by $U(D)$ on $0<A\le a$ is $n A^{n-1}/a^n$. Unfolding in a basis extending the plane gives independent unimodular Haar shapes for the plane and outer quotient, and uniform lift shear conditional on those shapes. Integer changes of basis in either block preserve the shear-torus measure. The physical outer lattice $Q_P$ has determinant $D/A$. The plane shape has density $c\,du\,dy/y^2$ on $|u|\le1/2, y\ge\sqrt{1-u^2}$. In particular the marginal density of $y$ is at most $c/y^2$ everywhere and equals $c/y^2$ for $y\ge1$. [Kim, Theorem 3 and Lemma 10](https://arxiv.org/pdf/2005.10874) · [Part 190, plane incidence](wall1_rank2_transverse.md#plane-incidence)

An **exact probability expression** uses the unique least-area plane. Given $A$, draw unimodular bases $g,h$ with independent Haar lattice laws in ranks $2,m$, and a uniform shear $B\bmod \mathbb Z^{2\times m}$. Set
$$
 F_A=\begin{pmatrix}\sqrt A\,g&\sqrt A\,gB\\0&(D/A)^{1/m}h\end{pmatrix}.
$$
Enumerate primitive integer two-column matrices $X$ once modulo right $GL_2(\mathbb Z)$, omitting the marked coordinate plane. Then
$$
 p(D)=U(D)\int_0^a \frac{nA^{n-1}}{a^n}\,
 \mathbb E_{g,h,B}\prod_X
 \mathbf1\{\det(X^\top F_A^\top F_A X)>A^2\}\,dA.                 \tag{1}
$$
The count below any fixed area is finite by discreteness of the exterior lattice. Equal areas for distinct rational planes give a countable union of proper algebraic hypersurfaces in the parent metric. To see properness, contract one plane relative to its complement. A distinct plane has at least one transverse direction. Consequently the selected marked count in (1) is the event indicator almost surely. Truncating the product along an exhaustion gives decreasing integrals converging to (1). The single-plane mean formula alone does not evaluate this void integral.

**Lower bound.** Any distinct competing plane of area at most $A$ meeting the marked plane in a line has area at least $s_P\lambda_1(Q_P)$. In fact a primitive intersection generator extends to a basis of the competitor, and orthogonally projecting its other basis vector off the entire marked plane can only shorten the perpendicular height. Thus discarding all marks with $\lambda_1(Q_P)\le A/s_P=\sqrt{Ay}$ eliminates every intersecting smaller competitor. By primitive-line incidence their conditional discarded fraction is bounded by
$$
 \min(1,b(A)y^{m/2}),\qquad b(A)=\frac{V_m A^{1+m/2}}{2\zeta(m)D}.
$$
Integration against $c/y^2$ on $0<y<\infty$, split at $b(A)^{-2/m}$, costs at most $cm b(A)^{2/m}/(m-2)$. Two planes meeting only at zero are independent in Kim's Theorem 3, so the expected number of unordered such pairs below $a$ is exactly $U(D)^2/2$. A retained mark with a smaller disjoint competitor can be charged to one such pair, with the larger member marked. Integrating in $A$ gives
$$
 \frac{p(D)}{U(D)}\ge
 1-\frac{cm}{m-2}\left(\frac{V_m}{2\zeta(m)D}\right)^{2/m}
 a^{1+2/m}\frac{n}{n+1+2/m}-\frac{U(D)}2.                         \tag{2}
$$
Counting *all* pairs by the independent-pair formula would omit the intersections responsible for most of the loss.

**Upper bound.** Fix $0<\ell\le\sqrt a$. A marked plane with $s_P<\ell$ implies a parent line shorter than $\ell$. Charge those parents once by primitive-line incidence. For $A\ge\ell^2$ the fraction of marks with $s_P<\ell$ is exactly $c\ell^2/A$, by the cusp density above $y=1$. Keeping only this much of the saving gives
$$
 \frac{p(D)}{U(D)}
 \le 1-\frac{c n\ell^2}{(n-1)a}\left[1-(\ell^2/a)^{n-1}\right]
     +\frac{V_n\ell^n}{2\zeta(n)D U(D)}.                            \tag{3}
$$
At the floor take $\ell^{n-2}=V_{n-1}a^{n-1}/(2\zeta(n-1)D)$, which balances the derivatives of the leading two corrections. This gives $24.43272<\ell<24.43273$. Equations (2)–(3) give $0.26183489<p(D_*)/U(D_*)<0.27115261$. They give a strict numerical separation between the probability and the mean at these parameters.

For $D\ge D_*$, $p(D)\le p(D_*)$ by dilation of a common unimodular sample. At exponent 13.6 the floor comparison is below $1.65887\cdot10^{-10}$. At exponent 13.6133 its floor value lies between $1.78431\cdot10^{-10}$ and $1.84782\cdot10^{-10}$. A chain-to-Haar proof must use the actual determinant average on its right. R59's sufficient criterion allows the *larger* right side $q^{13.61330}\mathbb E_D U(D)$, worth at most $6.81468\cdot10^{-10}$. The count and probability versions are distinct sufficient conditions. [R59, scalar implication](wall1_plane_comparison.md#audit)

## The conditional first moment and the origin of a plane

Write $S=(\Lambda,H,\text{frame})$ for the state before a draw. The raw uniform column maps by a homomorphism onto $H$, so $u\in H$ is uniform conditional on $S$. The window is $W_u=\Lambda+\mathbb Z(\tilde u,1)$, its designated primitive shortest vector is $v=v(u)$, of length $s$, and the output is $W_u/\mathbb Zv$ with the orthogonal metric. Every saturated output plane has a unique saturated rank-three preimage $J\subset W_u$ containing $v$, of covolume $s\det P$, by extending $v$ to a basis of $J$. The **exact conditional first moment** is
$$
 \frac1{|H|}\sum_{u\in H}\left(
 \sum_{J\subset\Lambda}^{\rm sat,\,rk\,3}
       \mathbf1_{v\in J,\ \det J\le as}
 +\sum_{\Delta\subset\Lambda}^{\rm sat,\,rk\,2}\;
   \sum_{j\ge1,\ \mu\in\Lambda/\Delta}
       \mathbf1_{\rm prim}\mathbf1_{v\in J}
       \mathbf1_{d\sqrt{j^2+\|\pi(\mu+j\tilde u)\|^2}\le as}
 \right).                                                           \tag{4}
$$
Here $d=\det\Delta$, $\pi$ projects off its span, and in the second sum $J=\Delta+\mathbb Z(\mu+j\tilde u,j)$. A choice of representatives for $\mu$ gives the same subgroups. The primitivity test says that the generator modulo $\Delta$ is primitive in $W_u/\Delta$. Each positive-height subgroup has a unique positive generator $j$ of its height image and one generating coset at that height. Taking the indicator that the total inside the parentheses is positive gives the exact conditional event probability. This keeps the mark that created the plane in the winner test. [Part 120 and audit](wall1_plane_count.md#audit-note-nov-2026) · [Part 155](wall1_inherited_witness.md) · [Part 161](wall1_band_plane_hits.md)

For a positive-height winner, choose its sign to have height $k>0$, and write $v_h$ for its horizontal component. In a triple through $v$, $j\mid k$. The projected old plane $\Delta$ has index $k/j$ in $P$, by taking heights modulo $k$. Thus (4) has the equivalent compression test
$$
 \det P=\frac{j}{k}\,d\sqrt{1-\|\operatorname{proj}_{\Delta}v_h\|^2/s^2}.              \tag{5}
$$
Indeed the projected Gram form on the old space is the identity minus $v_hv_h^\top/s^2$. For a horizontal winner, force its designated old line before the draw. On the branch where it wins, the output is the old quotient extended by the projected mark at height one. Both statements use the original uniform mark prior to the winner comparison. [Part 139 and corrections](wall1_lyapunov.md#audit) · [ProjectedCovolume.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/ProjectedCovolume.lean)

To split **both fresh, mixed, and both inherited** over the last two draws without depending on a chosen plane basis, freeze the state just before draw 405. Form the unprojected two-column extension $B_2$ of this old lattice. Its two displacement classes in the old torus are independent uniform marks given this state, since both raw columns are still unread. Run the first comparison in the first extension only. Let $F\subset B_2$ be the saturated rank-two kernel of the two actual selections. Its covolume is $s_1s_2$, and $h:B_2\to\mathbb Z^2$ records the two last input coordinates. Each terminal $P$ corresponds to a saturated rank-four $J\supset F$ with $P=J/F$. The image $P_{\rm old}$ of its old representatives and the quotient by them are
$$
 P_{\rm old}=((J\cap\ker h)+F)/F,\qquad
 P/P_{\rm old}\simeq h(J)/h(F).
$$
In a Smith basis for $P_{\rm old}\subset P$, the number $e\in\{0,1,2\}$ of nonunit factors (including missing generators as zero factors) is the minimum number of basis directions requiring fresh coordinates. Restrict $J$ to $\det J\le a s_1s_2$, partition by $e$, and average the three counts over the $|H|^2$ equally likely mark pairs and then the pre-405 state. Their sum is exactly $\mathbb E N_a(M)$. Free rank alone would lose finite-index cases such as (5). Counting two fresh directions by two independent single-vector tests would also drop the shared flag $F$.

## First creation under the Rankin recursion

Let $A_i=\{a_2(\Lambda_i)\le a\}$, with $i=0$ the initial $400\times105$ graph and $i=406$ the requested output. If $i\ge1$ and $A_i$ occurs, a winning triple in (4) has minimum $s$ and determinant at most $as$. Using $\gamma_3=2^{1/3}$, the ternary Hermite inequality gives $s^3\le\sqrt2\,as$. Binary reduction also bounds a shortest vector of the output plane. In physical units,
$$
 s\le R=2^{1/4}\sqrt a<33.22505,\qquad
 s_P\le T=\sqrt{2a/\sqrt3}<30.02222.                               \tag{6}
$$
These bounds include anisotropic planes. Area alone supplies no comparable upper bound on their second basis length.

Pathwise $a_3(W)=\min(a_3(\Lambda),\min_\Delta d\rho_\Delta(u))$ and $a_2(\Lambda_i)\ge a_3(W)/s$. The latter inequality follows by lifting through the actual winner. Equality would require a least-volume triple through that winner. In particular, on $A_{i-1}^c\cap A_i$, (4) implies either an old triple of determinant at most $aR$, or an old plane with
$$
 a<d\le aR,\qquad 1\le j\le as/d<s\le R,\qquad
 \|\pi(\mu+j\tilde u)\|^2\le(aR/d)^2-j^2.                         \tag{7}
$$
Hence **every layer of the new-triple sum at first creation is invertible modulo $3329$**. For a fixed state with $a_2(\Lambda)>a$, an explicit upper bound on the conditional creation probability is the minimum of one and
$$
 w_0\!\sum_{J\subset\Lambda}^{\rm sat,\,rk\,3}
 \mathbf1_{x_0\in J,\,\det J\le a\|x_0\|,\,\|x_0\|\le R}
 +\sum_{a<\det\Delta\le aR}\;
 \sum_{1\le j\le aR/d}
 \frac{\#\{z\in K_\Delta:\|z\|^2\le(aR/d)^2-j^2\}}{|H_\Delta|}.    \tag{8}
$$
Here the outer plane sum uses saturated planes, $x_0$ is the forced signed old shortest, and $w_0$ is its probability of winning. The projected mark $H_\Delta$ lives modulo $\pi\Lambda$, and $K_\Delta$ is its full preimage in the projected space. Multiplication by $j$ permutes $H_\Delta$, giving exactly the indicated average of the unfiltered disk count. Equation (8) drops primitivity and incidence only in the second term. The first term still involves the selected old flag. This identifies the history-dependent plane counts that a uniform one-step estimate would have to control. [RankinWindow.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/RankinWindow.lean) · [RankinSaturation.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/RankinSaturation.lean)

## Summing charges along the tour

Put $L_0=400\log q$ and $L_i=\max(L_{i-1}-\log q,505L_{i-1}/506-\tfrac12\log56.2142)$. Each window has the old determinant, contains the fresh period of length $q$, and satisfies the certified Hermite bound $\gamma_{506}\le56.2142$. Division by the selected length thus gives $\log D_i\ge L_i$. For a fixed projected old lattice of rank $b-1$ and determinant at least $e^l$, a positive-height vector of length at most $r<q$ has probability at most
$$
 B_b(r,l)=\frac{e^{b/2-l}}2 z^b\Theta(z)^{b-1},
 \quad z=r\sqrt{2\pi/b},\quad
 \Theta(z)=1+2e^{-\pi z^2}/(1-e^{-3\pi z^2}).
$$
The fresh-mark average over each allowed height is a sum on the projected integer lattice divided by the mark order. Its Poisson dual embeds by coordinate restriction into $\mathbb Z^{b-1}$, shortening lengths. Sum the Gaussian over positive integer heights by the integral $z/2$, and use its value at the ball boundary. All forced old projections used below are chosen before the corresponding draw. [Parts 147 and 151](wall1_penultimate_tail.md#1-where-the-last-used-coordinate-count-exhausts-its-budget)

**All origins in an initial segment.** For horizon $t$, use the last-used-coordinate flag count with terminal radius $T$. A hit at any $h\le t$ supplies the $h$ selected winners followed by a retained shortest vector of length at most $T$. If $i$ is the last new coordinate used by that flag, its suffix from $i$ lifts into the window at $i$. Every later coordinate is zero on these lifts because it is zero on the projected vectors and on the frozen directions before that coordinate arrived. Each tail of length $l$ has first vector shortest in its lifted tail lattice. Applying Hermite to that tail and peeling off its first length bounds the first length by $T b_l$, where
$$
 b_l=\max_{1\le v\le l}\sqrt{g_v}\prod_{m=2}^v g_m^{1/(2(m-1))},
 \qquad p_l=\sum_{v=1}^l\log b_v,\quad p_0=0 .
$$
Here $g_l$ are the Part 147 caps and $b_1=1$. The maximum makes the envelope monotone. Before the first flag vector that uses coordinate $i$, the omitted-coordinate winners are the forced old-only choices, by the signed tie rule. If $j$ such choices occur, their lengths are bounded by the first $j$ caps in a tail of length $k=t-i+2$. The remaining old determinant is at least $e^{L_{i-1}-p_k+p_{k-j}}T^{-j}$. The first vector that uses the column has length at most $Tw, w=b_{k-j}$. These bounds cover all horizons $h\le t$ in the *same* test for $(i,j)$, since the actual tail length is at most $k$. No extra factor of $t$ is necessary.

If $Tb_{t+1}<q$, an upper bound on $\Pr(\bigcup_{i=0}^t A_i)$ is
$$
 \frac{V_{505}(Tb_{t+1}+\sqrt{505}/2)^{505}}{2q^{400}}+
 \sum_{i=1}^t\sum_{j=0}^{k-1}
 \frac{T^{506}}2 e^{\pi w^2/z^2-L_{i-1}+p_k-p_{k-j}}
 z^{p+1}\Theta(Tz)^p,
 \quad p=505-j,\quad z=\max(1,w\sqrt{2\pi/(p+1)}).
$$
The first term covers an entirely old flag by the initial graph membership probability and disjoint integer unit cubes. The double sum uses the preceding Gaussian argument at scale $Tz$. For $t=154,155,156$ the three caps $Tb_{t+1}$ are below 2885, 2921, 2958, respectively. The corresponding upper sums are below $5.284\cdot10^{-15},1.349\cdot10^{-11},3.402\cdot10^{-8}$. By $t=160$ the evaluated upper sum exceeds $1.224\cdot10^6$, still with all tested heights below $q$. This is a loss of the relaxed first moment. [Part 147, flag bounds and caps](wall1_uncovered_lines.md#3-a-separate-bound-at-the-unit-threshold) · [Part 151 audit](wall1_penultimate_tail.md#audit)

**Positive-height winner.** At draw $i$ its joint probability with $A_i$ is at most $B_{506}(R,L_{i-1})$ by (6). Summing through 394 costs less than $2.067\cdot10^{-12}$. Through 395 the sum is below $9.965\cdot10^{-11}$, and through 396 it exceeds $4.767\cdot10^{-9}$. At draw 406 alone the uncapped bound exceeds $1.9274\cdot10^8$. Replacing $R$ by 30 and summing over all 406 draws costs less than $7.190\cdot10^{-15}$. The remaining late positive-height stratum has $30<s\le R$. The size of the unselected ball majorant gives no lower bound on this selected stratum.

**Horizontal winner and a fresh shortest plane vector.** Force projection along the old shortest $x_0$. Discard the state if $\|x_0\|>R$. The projected old determinant is at least $e^{L_{i-1}}/R$, and the fresh height is unchanged. If any hit plane has a shortest vector using the new coordinate, its length is at most $T$. Therefore the sum of the joint probabilities of these horizontal cases over *all* draws is at most $\sum_i B_{505}(T,L_{i-1}-\log R)<1.038\cdot10^{-13}$. A horizontal winner can also leave a wholly old plane or a mixed plane whose short generator is old and whose other generator uses the fresh column. In the latter case $a/s_P$ can be large. Counting its long generator with the radius $T$ would undercount.

**Residual.** Let $G$ be the Part 184 raw radius-250 and dual-floor good event. Partition on the first $A_i$, restricting each unresolved summand to $G$ and to $A_{406}$. After draw 154 retain the horizontal cases where no hit plane has a shortest vector of positive height. After draw 394 also retain positive-height wins with $30<s\le R$. Let $Z$ be the sum of these disjoint residual masses. The preceding bounds and a union bound give
$$
 \Pr(G,A_{406})\le Z+2.184\cdot10^{-12},\qquad
 \Pr(A_{406})\le Z+6.515\cdot10^{-12}.
$$
The unconditional bound charges the two exits once, using $4.249\cdot10^{-12}+8.147\cdot10^{-14}$. On $G$ an initial hit is impossible by (6)'s plane-vector bound and the raw cutoff. For an explicit determinant-matched target, put $\omega=\mathbb E[(D_*/D_{406})^2]$. Both loss terms in (2) decrease with $D$, so $p(D)\ge0.26183489\,U(D)$ uniformly for $D\ge D_*$. For exponent 13.6133 it suffices to prove $Z+2.184\cdot10^{-12}\le1.78431\cdot10^{-10}\omega$ on the good-event formulation, or to use $6.515\cdot10^{-12}$ as the charge for the unconditional formulation. The determinant floor alone gives only $\omega\le1$ as an upper bound. The first moment in (4), or its nonempty indicator, with the history weights on these residual strata has no budget-sized estimate here. Capping the evaluated total at one leaves a factor greater than $5.4117\cdot10^9$ over even the *largest* requested $q^{13.6133}p(D)$ allowance. This quantifies the gap in the upper bound. **Conjecture.** $\Pr(A_{406})\le q^{13.6133}\mathbb E[p(D_{406})]$. [Part 184 exit audit](wall1_penultimate_projection.md#audit) · [Parts 183–190](../PROOF_GAP.md)

## Verification

The numerical bounds used 83-decimal-digit outward interval arithmetic in scratch. Start the ball-volume recurrence at $V_0=1,V_1=2$, use $V_j=2\pi V_{j-2}/j$, and bracket $\zeta(j)$ between 1 and $1+2^{-j}(1+2/(j-1))$. The alternatives in every determinant update have disjoint intervals. For the prefix sum use the exact Hermite constants in ranks 1 through 8 and 24 and $g_l=(2/\pi)\Gamma(2+l/2)^{2/l}$ elsewhere. Evaluate each positive summand before adding. The bound at $t=154$ lies in $(5.28383,5.28385)\cdot10^{-15}$.

An exact small check used one horizontal coordinate over $\mathbb F_3$, two old inputs and one new input, with squared area cutoff 5. All 27 graphs had a hit. The 87 saturated output planes pulled back to 6 horizontal triples and 81 positive-height triples. Two independent integer counts agreed separately on every graph. For the first, take the signed shortest $v$, enumerate triples $v,x,y$, and retain primitive triples using the gcd of their three-row minors in graph-basis coordinates. Deduplicate by the signed primitive normal. For the second, enumerate primitive dual normals $z/3\in W^*$ with $z\cdot v=0, |z|^2\le5|v|^2$. The primitive triple has covolume $3\|z/3\|$. For the search through squared raw length 9, observe that $1\le |v|^2\le2$, the retained minimum is at least $\sqrt3|v|/2$, and a reduced plane basis lifts by rounding along $v$. Its longer projected generator has squared length at most $5/(3/4)+(2\sqrt5/\sqrt3)/4$, to which lifting adds at most $2/4$.

For a two-fresh example take one horizontal coordinate modulo 7, two initial zero inputs, then append columns 1 and 2. Both removals consume old unit axes. In the surviving coordinates the vectors $(-1,1,0),(-2,0,1)$ span a saturated plane of squared area 6. Their two last input columns form the identity, so $h(J)/h(F)=\mathbb Z^2$. This illustrates the origin split without imposing any distributional approximation. The toy graphs serve only to check the finite identities.

## Audit

**Verdict — SOUND.** The Haar enclosure, the finite-chain upper bounds and the exact graph counts check out. One wording clarification applies to the introduction. The unconditioned restart specifies the law of the **finite-chain** probabilities. The function $p(D)$ uses independently sampled Haar shape at fixed $D$. The finite–Haar comparison remains conjectural.

**Haar probability and multiplicity.** Kim's Theorem 3 applies both to one saturated plane and to an ordered pair with direct-sum span, since $2+2<505$. An unordered disjoint pair therefore costs $U(D)^2/2$. Off the null set of area ties, only the larger plane can be charged to that pair for having a smaller competitor. For intersecting planes, the primitive common line and an independent projected vector give the area lower bound $s_P\lambda_1(Q_P)$. Integrating the capped outer-line mean gives the loss in (2). For (3), parents with a line shorter than $\ell$ are charged once by line incidence, and the remaining plane incidence excludes the cusp $y>A/\ell^2$. Its mass is exactly $3\ell^2/(\pi A)$ on $A\ge\ell^2$. These arguments account for shared-line multiplicity without assuming that plane occurrences are probabilistically independent. [Kim, Theorem 3](https://arxiv.org/pdf/2005.10874)

I recomputed the bounds in scratch with 90-decimal-digit outward interval arithmetic, factorial formulas for the ball volumes and the stated zeta brackets. The determinant maximum selected the period bound 20 times and the Hermite bound 386 times. At $D_*$ the mean lies in $(7.6406558128,7.6406558130)\cdot10^{-58}$. Equations (2) and (3) enclose the event probability between $2.0005903166\cdot10^{-58}$ and $2.0717836951\cdot10^{-58}$. Equivalently, $3.68796<\mathbb E[N_a\mid N_a\ge1]=U(D_*)/p(D_*)<3.81921$. Multiplying the probability bounds by $3329^{13.6133}$ gives the outward enclosure $(1.7843192052,1.8478163199)\cdot10^{-10}$. Dilation makes the upper endpoint valid above the floor. The sufficient lower comparison still contains the actual determinant weight $\omega$.

**First creation and the terminal charge.** Projection through the primitive winner gives a bijection between output planes and saturated triples containing it. For a positive-height winner the image of the old plane has index $k/j$, since the quotient by this image is $j\mathbb Z/k\mathbb Z$. This verifies the direction of the factor in (5). At first creation $d>a$ implies $j<s\le R<q$ in the positive-height triple sum, so the uniform-mark average in (8) uses only invertible heights. The two-draw Smith factors likewise retain finite-index old images.

For the prefix test one may append the designated shortest vector of the hit lattice, whose length is at most $T$. The monotone caps for horizon 154 contain every shorter suffix, so each pair $(i,j)$ requires only one test over all those horizons. Summing the positive interval terms gave $(5.28383826,5.28383828)\cdot10^{-15}$, including the initial-graph term, with largest tested radius below $2884.088<3329$. The other three charges were below $2.066877\cdot10^{-12}$ for positive-height wins through 394, $7.189181\cdot10^{-15}$ for positive-height wins of length at most 30 through 406, and $1.037845\cdot10^{-13}$ for horizontal wins with a fresh shortest plane vector through 406. Their sum with the prefix charge is below $2.183135\cdot10^{-12}$. Adding the two Part 184 exits once gives less than $6.513605\cdot10^{-12}$, within the stated $6.515\cdot10^{-12}$.

More precisely, on $G\cap A_{406}$ let $\tau=\min\{i:A_i\}$. The two contributions to $Z$ are disjoint:

- $155\le\tau\le406$, the winner is horizontal, and **every** shortest vector of **every** hit plane at $\tau$ has zero fresh height. A mixed plane with an inherited shortest vector can contribute. A tie with a fresh shortest vector in any hit plane puts that history in the controlled charge.
- $395\le\tau\le406$, the winner has positive absolute height, and $30<s\le 2^{1/4}\sqrt a<33.22505$. The lower endpoint belongs to the controlled charge.

The definition requires a hit at draw 406 and permits intervening misses. Both charges are joint masses with $G$. This gives $\Pr(A_{406})\le Z+6.515\cdot10^{-12}$ before draw 407. Neither $Z$ nor the determinant average has been evaluated at the scale required for the conjecture.

**Small graphs.** Independent integer enumeration gave the same set of primitive normals by both methods on each of the 27 graphs. The pairs of counts (horizontal triples, positive-height triples) were $(0,1)$ on 13 graphs, $(0,3)$ on six, $(1,6)$ on six and $(0,7)$ on two. Thus every graph had a hit, with 6 horizontal and 81 positive-height triples in total. The signed selector also removes the two old unit axes in the modulo-seven example. The surviving plane has squared area 6 and its last two coordinates project onto $\mathbb Z^2$.
