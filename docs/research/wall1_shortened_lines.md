# Shortened primitive lines on a nonhorizontal terminal win

In the marginal width-506 restart, the small-radius positive-height plane moment satisfies
$F_< < 2^{219.843}$. The bound holds conditionally on **every** penultimate history. The part with winning length $s\le R/8$ contributes less than $4.21822\cdot10^{-8}$, including every witness on those draws. The contribution of exactly aligned nonzero horizontal parts is below $2^{-909.45}$. The remaining bound is far above the required allowance. The unresolved term is a discrete cylinder count on $R/8<s<2R/\sqrt3$, averaged over the selected histories.

## Law and cutoff

The old rank is $d=505$, the window rank is $b=506$, $q=3329$, and $c=0.954$. Condition on the complete history $S$ after the 406 selections following the independent $400\times105$ restart graph. Write $L\subset E$ for the old lattice, $D=\det L$, $H\subset E/L$ for its mark, and $K$ for the preimage of $H$ in $E$. The last column gives $U$ uniform on $H$. The window is $W=(L,0)+\mathbb Z(\tilde U,1)$. Use the inherited signed tie rule and orient a nonhorizontal winner to positive height, writing $v=(y,k)$ and $s=\|v\|$. All expectations use the design law. The independent CBD(3) plant does not enter. [First-tour law](wall1_first_tour.md) · [Restart coupling](wall1_idea_round2.md)

Write $G_n=V_n^{-1/n}$ for unit-ball volume $V_n$, $g=G_bD^{1/b}$, $R=cG_d(D/s)^{1/d}$, and $R_*=q^{400/912}\sqrt{d/(2\pi)}$. Let $Z$ count the primitive unoriented lines of the projected window below $R$ on a nonhorizontal win, and set $Z=0$ on a horizontal win. Each line gives one saturated positive-height plane through $v$. We use Part 148's precise definition $F_<=\mathbb E[Z\mathbf1_{R<R_*}]$. Every contributing draw then has $1\le k\le362$. If the cutoff is instead imposed only on $k$, the additional moment is less than $1.871946\cdot10^{-9}$ by Part 148. [Plane convention](wall1_plane_count.md) · [Height and radius cutoffs, including audit](wall1_vertical_multiplicity.md)

## 1. The conditional cylinder and its transverse lattice

Fix a primitive $x\in L$ up to sign, put $B=\|x\|$, and let $P_x$ project $E$ onto $x^\perp\cap E$. At height $k$ the winning $y$ is a shortest representative of $kU$ in the closed Voronoi cell of $L$. Denote the collection of representatives selected at that height by $Y_k(S)$. Each point has joint mass $1/|H|$ because $k$ is invertible modulo $q$. The selection of $Y_k(S)$ includes all competing heights and signed ties. Part 105 estimates a projected shape under Haar input. Part 142 gives a uniform law on a **finite set** of representatives before height selection. Neither supplies a spherical direction density for $Y_k(S)$. [Haar selection law](wall1_selection_law.md) · [Voronoi law and audit](wall1_dual_cusp.md) · [Signed projective-line tests](wall1_subspace_void.md)

**Proposition 1.** Complete $x$ to an integral basis of $L$ and write $qy=(n_1,\ldots,n_d)$ in this basis. Set $e=\gcd(k,n_2,\ldots,n_d)$. With $s^2=\|y\|^2+k^2$, the exact conditional moment on $R<R_*$ is
$$
\frac1{|H|}\sum_{k=1}^{362}\sum_{x\in L_{\rm prim}/\{\pm1\}}
\sum_{y\in Y_k(S)}
\mathbf1_{R<R_*}\,
\mathbf1\!\left\{\frac{\|P_xy\|^2}{e^2}
 < \frac{s^2R^2}{B^2}-\frac{k^2}{e^2}\right\}.                 \tag{1}
$$
The transverse point $P_xy/e$ belongs to $P_xK$. Only $B<sR$ can contribute.

*Proof.* Write $y=\lambda+k\tilde U$. The projection off $v$ identifies the quotient with the image of $L+\mathbb Z\lambda/k$ under its restriction to $E$. This restriction is injective since $k>0$. The vector $v$ is primitive, so $k$ and the content of $\lambda$ are coprime. For $j\mid k$, the primitive generator $x/j$ belongs to the extension exactly when $x\equiv a\lambda\pmod{jL}$ for a unit $a$ modulo $j$. In the basis beginning with $x$, this requires divisibility by $j$ of all transverse coordinates of $\lambda$. When that holds, its first coordinate is a unit modulo $j$ by primitivity. Since $qy\equiv q\lambda\pmod{kL}$ and $q$ is a unit modulo $k$, the largest such $j$ is $e$. Thus $x/e$ generates the extended lattice on this line. Direct projection gives
$$
 \|\pi_{v^\perp}(x/e,0)\|^2
   =\frac{B^2}{e^2s^2}\big(k^2+\|P_xy\|^2\big).
$$
This proves the indicator and the truncation since $e\le k$. Also $qP_xy\in eP_xL$ and $P_xy\in P_xK$. Bézout for $q,e$ gives $P_xy\in eP_xK$. Summing over the selected representatives proves (1). [One-step isometry](wall1_lyapunov.md) · [Primitive extensions and audit](wall1_vertical_multiplicity.md)

For an explicit conditional upper count, restrict $s$ to a bin with upper endpoint $t$. For fixed $x,k,e\mid k$, put
$$
 m_x=\min(B/2,\sqrt{t^2-k^2}),\qquad
 a_x^2=(tR(t)/B)^2-(k/e)^2,\qquad R(t)=cG_d(D/t)^{1/d}.
$$
Skip $t<k$ or $a_x^2\le0$. Write $K\cap\mathbb Rx=\mathbb Zx/o$, with $o=1$ or $q$ because $qK\subseteq L$. The number of representatives in this bin with $P_xy\ne0$ that can qualify is at most
$$
 \left(1+\left\lfloor 2m_x o/B\right\rfloor\right)
 \#\{z\in P_xK:0<\|z\|<a_x\}.                                    \tag{2}
$$
Indeed $sR(s)$ is increasing, and $z=P_xy/e$. The Voronoi comparisons with $\pm x$ put the axial coordinate in $[-B/2,B/2]$, and the length test bounds it by $\sqrt{t^2-k^2}$. For fixed $z$, the lifts of $ez$ in $K$ have axial spacing $B/o$. This proves (2) without any assumption on directions. A specified angular restriction $\sin\angle(x,y)\le\epsilon$ for $y\ne0$ further imposes $\|z\|\le\epsilon\sqrt{t^2-k^2}/e$. The strict cutoff in (2) still applies. Summing the bounds over the bins, divisors, lines and heights, dividing by $|H|$, and taking $\mathbb E_S$ is a first-moment bound.

There is an exact gap next to the aligned atom. In (1), either $P_xy=0$ or $B\|P_xy\|/e\ge D/q^{400}$. To see this, let $C$ be the intersection of the old raw graph lattice with the frozen subspace. It is primitive and has covolume $q^{400}/D$, by extending a basis in the raw graph and projecting its complement. Lift $x$ and a preimage in $K$ of $P_xy/e$ to integer raw vectors using $K=P_E\mathbb Z^{911}$. Adjoining both vectors to a basis of $C$ gives a nonzero integer exterior product if $P_xy\ne0$. Its norm is $(\det C)B\|P_xy\|/e$ by orthogonal projection. This proves the claim. The bound can be very small over the restart law. [Projected mark identity](wall1_dual_cusp.md)

## 2. Counting planes by nonzero-height lifts

**Lemma 2.** Put $\alpha=\sqrt3/2$ and $\rho=R/s$. If a line contributes, $\rho>\alpha$. For each contributing line one can choose a lift $w\in W$ of a primitive generator, with positive height, satisfying
$$
 \|w\|^2 <
 \begin{cases}
  2R^2 & \rho\le1,\\
  R^2+s^2 & \rho\ge1.
 \end{cases}                                                       \tag{3}
$$
If $e>1$ or $2|\langle x,y\rangle|\ge s^2$, one can use $\|w\|^2<R^2+s^2/4$. Choices for different lines are distinct.

*Proof.* Round any primitive lift along $\mathbb Zv$ so its signed component $a$ along the **unit** winner lies in $[-s/2,s/2]$. Its perpendicular length $p$ is below $R$. Minimality gives $p^2+a^2\ge s^2$, hence $p\ge\alpha s$. If a rounded lift has nonzero height, orient it upwards. Otherwise add or subtract $v$, choosing the sign that gives parallel length $s-|a|$. The resulting lift has nonzero height and squared norm $p^2+(s-|a|)^2<R^2+s^2$. When $R\le s$, the horizontal rounded vector has length at least $s$, so $|a|\ge\sqrt{s^2-p^2}$. The shifted squared length is at most
$$
 2s^2(1-\sqrt{1-p^2/s^2})=\frac{2p^2}{1+\sqrt{1-p^2/s^2}}<2R^2.
$$
A nonhorizontal rounded lift itself satisfies $p^2+s^2/4<2R^2$ since $R>\alpha s$.

A primitive quotient generator with a horizontal lift must have $e=1$, by injectivity on $E$. Its only horizontal lifts, allowing either orientation, are $\pm x$. Their absolute parallel component is $|\langle x,y\rangle|/s$. Above $s/2$ they cannot be rounded lifts, and at equality a neighboring nonhorizontal lift is also rounded. Finally each chosen vector projects onto its own quotient line. ∎

**Theorem 3.** The conditional first moments on $R<R_*$ satisfy the following bounds for every $S$. The last row counts only lines satisfying the indicated test.

| Count on nonhorizontal wins | Upper bound |
| --- | ---: |
| All witness planes | $2^{219.843}$ |
| All witness planes on $s\le R/8$ | $4.21822\cdot10^{-8}$ |
| Witnesses with $e>1$ or $2\lvert\langle x,y\rangle\rvert\ge s^2$ | $2^{71.640}$ |

*Proof.* Define $\eta=(cG_d)^{d/b}/G_b$. Eliminating $D$ gives $R/g=\eta\rho^{1/b}$. On a contributing draw $\alpha<\rho<R_*$ since $s\ge k\ge1$. For $\rho\le1$, (3) uses radius at most $\sqrt2\eta g$. For $\rho\ge1$ its radius divided by $g$ is
$$
 B_1(\rho)=\eta\rho^{1/b}\sqrt{1+\rho^{-2}} .
$$
For rounded nonhorizontal lifts use $B_{1/4}(\rho)=\eta\rho^{1/b}\sqrt{1+1/(4\rho^2)}$ over the whole interval. For $B_h(r)=\eta r^{1/b}\sqrt{1+h/r^2}$, the logarithmic derivative with respect to $\log r$ is $1/b-h/(r^2+h)$, increasing in $r$. Thus the maximum on each closed interval occurs at an endpoint. The respective radius factors for the three rows are $B_1(1)$, $B_1(8)$ and $B_{1/4}(\alpha)$, using the endpoint comparisons below. Every chosen lift has height less than $q$ since $\|w\|<R_*\sqrt{1+\alpha^{-2}}<481$.

For a history-dependent radius $A$ fixed before the draw, count all window vectors of norm below $A$ at heights $1\le j<q$. By Lemma 2 this count majorizes the appropriate multiplicity when $A$ is the corresponding radius factor times $g$. For each $j$, $jU$ is uniform on $H$. Averaging the horizontal Gaussian at scale $z$ gives $|H|^{-1}\sum_{y\in K}\exp(-\pi\|y\|^2/z^2)$. Poisson summation and $\det K=D/|H|$ turn this into $z^d/D$ times the dual Gaussian sum at scale $z$. Since $K^*=E\cap\mathbb Z^{911}$, projection onto a suitable set of $d$ coordinate axes injects this dual into $\mathbb Z^d$ and shortens norms. Its theta sum is at most $\theta(z)^d$, where $\theta(z)=\sum_{n\in\mathbb Z}\exp(-\pi z^2n^2)$. Using $\sum_{j\ge1}\exp(-\pi j^2/z^2)\le z/2$ and majorizing the ball indicator gives the conditional expectation bound
$$
 \frac{e^{\pi A^2/z^2}z^b\theta(z)^d}{2D}.
$$
Uniformity was used only for $j<q$. Several witness planes on the same draw are charged individually. [Conditional Gaussian count](wall1_uncovered_lines.md) · [Poisson summation](https://dlmf.nist.gov/1.8.iv)

Write $A=Bg$, choose $z=A\sqrt{2\pi/b}$ and let $J_n=\Gamma(1+n/2)(2\mathrm e/n)^{n/2}$. The bound is at most
$$
 M(B)=\tfrac12 J_b B^b\theta\!\left(BG_bD_*^{1/b}\sqrt{2\pi/b}\right)^d,\qquad
 \log D_* = a^{406}400\log q-\tfrac b2(1-a^{406})\log(56.2142),\quad a=d/b.       \tag{4}
$$
Here $D\ge D_*$ follows by iterating the Hermite cap $D_i\ge D_{i-1}^{d/b}/\sqrt{56.2142}$ from $D_0=q^{400}$, and $\theta$ is decreasing. Evaluation of (4) proves the table. Taking $\mathbb E_S$ proves the same bounds for the marginal restart. More precisely, the first row has log-majorant below $219.84216$. Adding Part 148’s large-radius charge therefore gives $F_{\rm nh}<2^{219.843}$ for the full restart moment as well. In particular any set of penultimate histories of probability $p$ contributes at most $2^{219.843}p$ to $F_<$. [Hermite cap](wall1_hermite_caps.md) · [Restart determinant floor](wall1_vertical_multiplicity.md)

In particular, on $k=1$ and $s>R/8$, every old witness making an unoriented angle of at most $\pi/4$ with $y$ satisfies the rounded-lift test. Indeed $s\le\sqrt2$ would imply $R\ge cG_d(D_*/\sqrt2)^{1/d}>8\sqrt2$, contradicting $s>R/8$. Thus $\|y\|=\sqrt{s^2-1}>s/\sqrt2$, and $\|x\|\ge s$ by minimality. The angle condition gives $2|\langle x,y\rangle|\ge s^2$. This bounds the full discrete count on a finite angular sector by the third row. Its size still exceeds the allowance.

## 3. The exactly aligned contribution

**Theorem 4.** On $R<R_*$, the conditional mean count of witnesses with $x/q\in K$ and $0\ne U\in\langle x/q+L\rangle$ is below $2^{-909.45}$ for every history. This includes every witness with $y\ne0$ parallel to $x$.

*Proof.* For alignment, $qy=nx$ for an integer $n$, since $qy\in L$ and $x$ is primitive. If $q\mid n$, then $kU=0$, hence $U=0$. At that draw the shortest representative at every height is zero. Otherwise $q\nmid n$, and an inverse of $n$ modulo $q$ gives $x/q\in K$ and $U$ on its marked line. For each fixed eligible $x$, at most $q-1$ draws have the indicated class, with total conditional mass $(q-1)/|H|$.

On every contributing draw, $B<sR$, $s<R_*/\alpha$, and $R\le cG_dD^{1/d}$. Thus $x/q\in K$ has length below $u=\tau G_dD^{1/d}$, where $\tau=cR_*/(q\alpha)$. Different old primitive lines give different sign pairs. Sum the preceding mass over them, and majorize the ball in $K$ by the same Gaussian calculation as in Theorem 3, now in rank $d$ without a height sum. At $z=u\sqrt{2\pi/d}$ the result is at most
$$
 \tfrac12(q-1)J_d\big(\tau\theta(z_*)\big)^d,
 \qquad z_*=\tau G_dD_*^{1/d}\sqrt{2\pi/d}.                         \tag{5}
$$
This retains multiplicity even when several $x$ map to the same marked line. The verification below bounds (5). The remaining possibility $y=0$ on a nonhorizontal win forces $U=0$, $k=s=1$. Then $R=cG_dD^{1/d}>30$ by the determinant floor, so Theorem 3 already charges the entire draw on $R<R_*$. ∎

## 4. Exact and interval checks

For $L=q\mathbb Z^2$ use either the full mark or the first coordinate axis in $(\mathbb Z/q)^2$. At each draw $u$, choose the shortest signed vector by squared norm and ambient lexicographic order. The following counts use fixed toy cutoffs and integer or rational comparisons throughout.

| $q$ | Mark | $R^2$ | Draws | Witnesses | With nonhorizontal rounded lift | Exactly aligned, $y\ne0$ |
| ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 5 | full | $25/2$ | 25 | 16 | 16 | 8 |
| 17 | full | $289/2$ | 289 | 712 | 712 | 136 |
| 17 | full | $289/8$ | 289 | 116 | 116 | 44 |
| 17 | axis | $289/2$ | 17 | 14 | 14 | 14 |
| 5 | full | $50$ | 25 | 126 | 116 | 24 |

One enumeration uses $x=q p$ with primitive signed-normalized $p$ and $\|x\|<sR$. It checks $e=\gcd(k,\det(p,y))$ against the unit-congruence definition and applies (1). The independent enumeration tests each positive-height $w$ of squared norm below $R^2+s^2$. In window-basis coordinates, the three minors of $(v,w)$ must be coprime for $w$ to give a primitive quotient generator. The area test is $s^2\|w\|^2-\langle v,w\rangle^2<s^2R^2$. The old line has direction $kw_h-w_{\rm height}y$. The sets of old lines agreed on every draw, as did the rounded-lift test and direct rounding. All accepted lines had a lift within (3). The third row includes 24 incidences with $R<s$. The last row includes ten planes requiring translation of a horizontal rounded lift.

For the numerical checks, 70-decimal-digit outward interval arithmetic used $G_n=\Gamma(1+n/2)^{1/n}/\sqrt\pi$ and the displayed $D_*$. Upper-bound $\theta(z)$ by $1+2v/(1-v^3)$ with $v=\exp(-\pi z^2)$, since successive gaps between positive squares are at least three. For (5), use $\theta(z_*)=\theta(1/z_*)/z_*$ first. Intervals for moments below enclose the evaluated **upper majorants**.

| Quantity | Open interval |
| --- | --- |
| $B_1(1),\ B_1(8),\ B_1(R_*)$ | $(1.343445,1.343446)$, $(0.961294,0.961295)$, $(0.960821,0.960822)$ |
| $B_{1/4}(\alpha),\ B_{1/4}(R_*)$ | $(1.096606,1.096607)$, $(0.960818,0.960819)$ |
| $\log_2 M(B_1(1))$ | $(219.84214,219.84216)$ |
| $M(B_1(8))$ | $(4.21821,4.21822)\cdot10^{-8}$ |
| $\log_2 M(B_{1/4}(\alpha))$ | $(71.63911,71.63913)$ |
| $z_*$ and $\log_2$ of (5) | $(0.370515,0.370516)$ and $(-909.45395,-909.45393)$ |

## Remaining gap

Let $F_{\rm rem}$ be (1) averaged over $S$ on $\alpha<R/s<8$, omitting the marked incidences of Theorem 4. Then
$$
  F_{\rm rem}\le F_< < F_{\rm rem}+4.21822\cdot10^{-8}+2^{-909.45}.
$$
Consequently $h_{\rm long}+F_{\rm rem}\le0.0097738000$ would suffice. **Conjecture (open).** The Part 147 combined allowance holds for the marginal restart. The stronger sufficient inequality just displayed has no budget-sized proof here.

At $k=1$, the divisor in (1) is one. The remaining terms include old lines already shorter than $R$ and lines shortened across $R$ by a winning representative with nonzero transverse coordinate. Formula (2) retains the transverse spacing, but evaluating its sum needs control of the old line lengths and projected lattices on the selected histories. Theorem 3 avoids that history law by counting all short positive-height lifts, at the cost quantified in (4). The Part 117 coupling cost applies to the final failure event after the two terminal charges have been bounded. [Remaining allowance and audit](wall1_vertical_multiplicity.md)

## Audit

**Verdict — SOUND.** All five toy cases and every printed numerical interval reproduce. The per-history bounds in Theorems 3 and 4 apply on $R<R_*$. The full $F_{\rm nh}<2^{219.843}$ uses Part 148 after averaging over restart histories. The sufficient condition on $h_{\rm long}+F_{\rm rem}$ remains open.

**Exact count.** After the signed winner is fixed and oriented upwards, $k$ and $y+L$ determine $U$ uniquely by Part 108. Thus each term of the joint count has mass $1/|H|$. In Part 139's cyclic extension, primitivity of $(\lambda,k)$ makes the first coordinate of $\lambda$ coprime to $j$ whenever $j\mid k$ divides every transverse coordinate. Multiplication by $q$ preserves this test. Hence the gcd in (1) gives the primitive generator $x/e$ on each old line, including composite $k$. Part 120's line–plane bijection counts each saturated plane once. Bézout applied to $P_xy\in P_xK$ and $qP_xy\in eP_xL$ gives $P_xy/e\in P_xK$. At fixed $e$ and transverse point the lifts have spacing $B/o$, which gives (2) even when both axial endpoints occur. For the exterior-product gap, choose a preimage of the transverse point in $K=P_E\mathbb Z^{911}$ and lift that preimage to an integer raw vector. Orthogonalizing the two integer lifts after a basis of $C$ gives the product $\det(C)B\|P_xy\|/e$. A nonzero integer minor gives the claimed lower bound.

**Multiplicity and alignment.** Rounding gives $p\ge\alpha s$. Equality cannot contribute at $R=\alpha s$ because the cutoff is strict. Translating a horizontal rounded lift changes its absolute parallel component from $|a|$ to $s-|a|$. At $|a|=s/2$ a nonhorizontal rounded lift exists as well. Chosen lifts of different quotient lines are distinct and have positive height below $481<q$. Part 108 therefore gives the uniform layer average for every height used in the Gaussian bound, even when several planes occur on a draw. Part 142 gives the determinant and integral dual used in that bound. For alignment with $y\ne0$, writing $qy=nx$ forces $q\nmid n$, because the zero class has the unique shortest representative zero. For each eligible old line there are at most $q-1$ nonzero marked classes. Summing their masses over old lines preserves multiplicity when marked lines coincide. The draw with $y=0$ has $k=s=1$ and belongs to the short-length charge whenever $R<R_*$.

**Independent checks.** Scratch computations compared two exact integer enumerations on all 645 case–draw pairs. One used centered residues, primitive old directions and the gcd test, checking each divisor against the unit congruence. The other enumerated signed window vectors to select the winner, then tested positive-height lifts by primitive minors and squared area. The winner, witness set, rounded-lift flags and alignment flags agreed on each draw. The five witness totals were $16,712,116,14,126$ in table order. The third case had 24 incidences with $R<s$. The last had ten planes requiring translation.

Independent 90-decimal-digit outward interval checks used $V_0=1$, $V_1=2$, $V_j=2\pi V_{j-2}/j$ and iterated the log-determinant floor 406 times. The log-majorants for all witnesses, rounded lifts and marked incidences were in $(219.8421500601,219.8421500602)$, $(71.6391186280,71.6391186281)$ and $(-909.4539403750,-909.4539403748)$, respectively. The short-length majorant lay in $(4.2182117401,4.2182117402)\cdot10^{-8}$. The full marginal log-majorant stayed in the first interval after adding Part 148's large-radius charge.

**Budget.** Within $R<R_*$, first remove all incidences with $R/s\ge8$, including equality. On $\alpha<R/s<8$, remove only the incidences in Theorem 4. What remains is exactly the restricted sum (1) defining $F_{\rm rem}$. Theorem 4's bound over the larger set dominates its charge on this second stratum. Part 148 covers the complementary $R\ge R_*$ once. With the proposed sufficient condition the rounded charges give
$$
 h_{\rm long}+F_{\rm nh}
 <0.0097738000+4.21822\cdot10^{-8}+2^{-909.45}+1.871946\cdot10^{-9}
 <0.0097738441 .
$$
Part 149's horizontal long-line term is already present as $h_{\rm long}$. Adding Part 147's three other charges gives restart failure below $0.00977696$. Part 117 then adds less than $0.00022304$ once to that event probability, yielding original failure below $0.01$ if the sufficient inequality holds.
