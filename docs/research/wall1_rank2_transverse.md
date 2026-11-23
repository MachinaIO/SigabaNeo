# Primitive planes, the shortest-line void, and the radius-26 quotient

A primitive plane of area $A$ in a Haar lattice of determinant $D$ has two independent unimodular lattices under plane-counting measure. They are the rescaled plane lattice and the rescaled projection of the parent. This gives a two-sided estimate for the Part 186 event. At the rank-505 determinant floor its Haar probability lies in $(9.97119357603,9.97119357604)\cdot10^{-63}$. The event uses the spacing **inside** the witness plane modulo the shortest line. If instead one asks for **any** plane through the shortest line with a short vector in the quotient **by the plane**, the probability is one. Selecting the second line or imposing an area gate changes this latter event.

## Plane incidence

Let $n\ge3$, $m=n-2$, $X_j=SL_j(\mathbb R)/SL_j(\mathbb Z)$, with invariant probability $\mu_j$. Take $X_1$ to be a singleton. Write $V_j=\pi^{j/2}/\Gamma(1+j/2)$. All lengths are Euclidean. Draw $L=D^{1/n}L_0$ with $L_0\sim\mu_n$ and fixed $D>0$. Sum once over each unoriented saturated subgroup $P=L\cap U$ of rank two, where $U=\operatorname{span}_{\mathbb R}P$. Set $A=\det P$, $Q=\pi_{U^\perp}L$. Saturation lets a basis of $P$ extend to one of $L$, so $Q\cong L/P$ is a lattice and $\det Q=D/A$. Fix measurable orthonormal frames on $U,U^\perp$ depending only on $U$, with the combined frame positively oriented. In these coordinates put
$$
 S=A^{-1/2}P,\qquad Z=(A/D)^{1/m}Q.
$$

**Theorem 1.** For every nonnegative Borel test on $(U,A,S,Z)$, its expected sum over planes is its integral against
$$
 d\nu_{\rm Gr}(U)\;
 \frac{n C_n}{D^2} A^{n-1}\,dA\;
 d\mu_2(S)\;d\mu_m(Z),\qquad
 C_n=\frac{1}{n}{n\choose2}
 \frac{V_n V_{n-1}\zeta(2)}{V_1 V_2\zeta(n)\zeta(n-1)}
 =\frac{(n-1)\pi V_n V_{n-1}}{24\zeta(n)\zeta(n-1)}.                 \tag{1}
$$
Here $\nu_{\rm Gr}$ is invariant probability on the unoriented Grassmannian. This is a sigma-finite incidence measure. Restriction to $0<A\le a<\infty$ has mass $C_n a^n/D^2$. A regular conditional law for $Z$ given the plane data equals $\mu_m$ almost everywhere for that marginal. The exceptional set can be shared by all Borel tests since $X_m$ is standard Borel.

*Proof.* First take $D=1$. The integral stabilizer of the coordinate plane lattice is the block upper triangular subgroup of $SL_n(\mathbb Z)$ with diagonal blocks in $GL_2(\mathbb Z),GL_m(\mathbb Z)$. Every saturated plane is in its orbit by basis extension. Unfolding a nonnegative sum therefore integrates invariant measure on the quotient by this stabilizer. To describe the fibers, temporarily give the plane both orientations, so that the integral diagonal blocks have determinant $+1$. At fixed oriented $U,A$ the real determinant-one block group with diagonal blocks in $SL_2(\mathbb R),SL_m(\mathbb R)$ acts transitively in adapted, scaled coordinates. A representative there has the form
$$
 \begin{pmatrix} A^{1/2}g&A^{1/2}gB\\0&A^{-1/m}h\end{pmatrix},
 \qquad g\in SL_2(\mathbb R),\ h\in SL_m(\mathbb R).
$$
Integer shear on the right reduces $B$ modulo $\mathbb Z^{2\times m}$. Integer basis changes in the blocks act by $B\mapsto\gamma_2^{-1} B\gamma_m$ and preserve torus volume. Haar measure of this block group is the product of the two group Haar measures and Lebesgue measure of the shear in these coordinates because the actions of the diagonal factors on the additive block have determinant one. Equivalently, disintegrate the unfolded quotient by the closed stabilizer of the oriented area element. The invariant fiber measure in the quotient integral formula thus normalizes to $d\mu_2\,d\mu_m\,dB$, with probability Haar on each torus. Rotation invariance gives uniform direction at each area. Forgetting orientation counts each plane once after dividing by two. Opposite frame orientations transport the block laws by reflections, which preserve these lattice laws after composing with an integral reflection on the right.

The remaining scalar marginal is fixed by the primitive-sublattice mean value $\mathbb E\#\{P:A\le a\}=C_na^n$, the single-sublattice case of Kim's Theorem 3. Its normalization counts subgroups, without an ordered basis or orientation. Dilating the parent multiplies areas by $D^{2/n}$, giving the $D^{-2}$ factor. This proves (1), including the fiber over the shapes. [Kim, *Mean value formulas on sublattices and flags of the random lattice*, Theorem 3 and Lemma 10](https://arxiv.org/pdf/2005.10874)

The rank-one formal precedents are `primitive_frame_unfolding`, `transverseShape_product`, and `transverseShape_kernel_ae_haar`. The declaration `part105` applies the short-minimum inequality to the oriented rank-one count. Equation (1) is a paper proof. [PrimitiveUnfolding](../../SigabaNeo/Lib/Lattices/Research/Wall1/PrimitiveUnfolding.lean) · [TransverseProduct](../../SigabaNeo/Lib/Lattices/Research/Wall1/TransverseProduct.lean) · [TransverseKernelLaw](../../SigabaNeo/Lib/Lattices/Research/Wall1/TransverseKernelLaw.lean) · [TransverseMinimumBound](../../SigabaNeo/Lib/Lattices/Research/Wall1/TransverseMinimumBound.lean)

## A bounded plane with a short vector and a short outer quotient

Modulo rotation, use the modular fundamental region $\mathcal F=\{|u|\le1/2,\ y\ge\sqrt{1-u^2}\}$, with the boundary identified up to null sets. Its Haar shape probability is $3\,du\,dy/(\pi y^2)$, the normalized hyperbolic area. The physical Gram matrix in a reduced basis is
$$
 \frac{A}{y}\begin{pmatrix}1&u\\u&u^2+y^2\end{pmatrix}.
$$
Thus a shortest generator has length $s=\sqrt{A/y}$, and the spacing of $P$ modulo this generator is $h=A/s=\sqrt{Ay}$. Indeed a reduced basis is proportional to $1,u+iy$. For a coefficient of the second generator of magnitude one the shortest possible modulus is at least one, and for magnitude at least two the imaginary part alone exceeds one. For shape modulo all isometries, fold $u$ to $|u|$ and double the interior density.

For $a,\ell,c>0$, let $N$ count planes with $A\le a$, a **nonzero** point of length at most $\ell$, and $\lambda_1(Q)<c$. Define $F_m(t)=\mu_m\{\lambda_1<t\}$. Equation (1) gives
$$
 \mathbb E N=\frac{n C_n}{D^2}\int_0^a A^{n-1} H(A,\ell)
 F_m\big(c(A/D)^{1/m}\big)\,dA,\qquad
 H(A,\ell)=\frac{3}{\pi}\int_{-1/2}^{1/2}
 \frac{du}{\max(\sqrt{1-u^2},A/\ell^2)}.                         \tag{2}
$$
The primitive sign-pair mean gives $F_m(t)\le\min(1,V_mt^m/(2\zeta(m)))$ for $m\ge2$. For $m=1$ use $F_1(t)=\mathbf1_{1<t}$. In particular an explicit bound for $m\ge2$ is
$$
 \mathbb E N\le\frac{n C_n}{D^2}\int_0^a
 A^{n-1}\min\!\left(1,\frac{3\ell^2}{\pi A}\right)
 \min\!\left(1,\frac{V_m c^m A}{2\zeta(m)D}\right)dA .
$$
A closed expression follows by replacing $H$ by this same bound and dropping the cap on the final factor. With $b=\min(a,3\ell^2/\pi)$, it is
$$
 \frac{n C_n V_m c^m}{2\zeta(m)D^3}
 \left(\frac{b^{n+1}}{n+1}+\frac{3\ell^2}{\pi}\frac{a^n-b^n}{n}\right).
$$
For the **normalized** outer minimum use $F_m(c)$ independent of area in (2). With $m\ge2$, strict and weak outer cutoffs have the same incidence mass by the zero-volume sphere in the primitive mean formula.

## Shortestness given the plane

Given $P,Q$ under incidence, the shear is a uniform homomorphism $T:Q\to U/P$. In bases it sends each quotient basis vector to an independent uniform torus point. Every lift of $z\in Q$ has squared norm $|z|^2+|v|^2$ with $v\bmod P=T(z)$. Write $d_P(t,0)$ for the distance to zero in $U/P$. For a candidate $x\in P\setminus\{0\}$ of length $s$, the exact indicator of being shortest in the parent is
$$
 I_x=\mathbf1_{\lambda_1(P)\ge s}
 \prod_{z\in Q,\ 0<|z|<s}
 \mathbf1_{\,d_P(T(z),0)^2\ge s^2-|z|^2}.                      \tag{3}
$$
The first factor checks the zero fiber and the finite product checks every remaining fiber that can meet the open ball. For $s=\lambda_1(P)$, denote the torus average of (3) by $w(P,Q)$. The conditional void given $P$ is its average over the scaled Haar $Q$. For some shears every lift of a quotient vector shorter than $s$ has length at least $s$. Evaluations at multiples obey $T(kz)=kT(z)$. Thus multiplying a marginal parent void by a quotient-hit probability can give the wrong integral. A transverse void $\lambda_1(Q)\ge s$ suffices for $w=1$. Haar parents have a unique shortest sign pair almost surely by the countable union of equal-length hypersurfaces for independent integer vectors. Equation (3) itself permits ties. [Part 105, marked calculation](wall1_selection_law.md)

There is also a bound conditional on the plane alone. For $m\ge2$ and fixed $P$ with $s=\lambda_1(P)$, the conditional mean number of **outside** sign pairs in the open parent $s$-ball is exactly $V_n s^n/(2D)$. Indeed evaluation of Haar $T$ at any nonzero $z\in Q$ is uniform in $U/P$, even for a multiple, since multiplication by any nonzero integer is surjective on a torus. Averaging all lifts in its coset gives the area of the planar ball slice at $z$ divided by $A$. Ordinary Siegel in $Q$ integrates the slices against Lebesgue measure times $A/D$. Slicing recovers the parent ball volume, and opposite points form pairs. Hence
$$
 \left(1-\frac{V_n s^n}{2D}\right)_+
 \le \mathbb E[w(P,Q)\mid P]\le1 .
$$
Conditioning further on a short outer minimum restricts the $Q$ integral in this argument. Equation (3) still applies under that restriction.

In particular the probability that some plane satisfies the gates in (2) **and** contains a shortest vector is at most the incidence integral (1) of
$\mathbf1_{A\le a,\,s\le\ell,\,\lambda_1(Q)<c}\,w(P,Q)$, with $s=\lambda_1(P)$. This integral is the exact expected number with the void. Dropping its weight gives (2).

**Unrestricted outer-quotient event.** Fix any full lattice of rank $n\ge3$, any shortest vector $x$, and any $r>0$. In $L/\mathbb Zx$, realized by projection, choose the first two vectors $b_1,b_2$ of a lattice basis. The primitive vector $kb_1+b_2$ spans a line whose inverse image is a saturated plane $P_k$ through $x$. The image of $b_1$ modulo this line has length
$$
 \frac{|b_1\wedge b_2|}{|kb_1+b_2|}\longrightarrow0 .
$$
Successive orthogonal projections realize $L/P_k$, so eventually $\lambda_1(L/P_k)<r$. These planes have unbounded area $s|kb_1+b_2|$. Even with the normalized outer quotient the displayed length after scaling is $O(k^{1/m-1})$ for $m>1$. In ranks 505 and 506 the unrestricted event has probability one with either convention and $x$ genuinely shortest.

## The spacing event at radius 26

For a designated shortest line $\mathbb Zx\subset L$, define $E_r=\{\lambda_1(\pi_{x^\perp}L)\le r\}$. A primitive witness line in this projection pulls back to precisely one saturated plane through $x$ with internal spacing $h\le r$. Conversely such a plane supplies a witness. Part 186 uses this event at rank 505. For a plane counted through its own shortest line, reduction gives $y\ge\sqrt3/2$, hence on $h\le r$
$$
 s=h/y\le T_r:=2r/\sqrt3,\qquad A=sh\le r T_r .
$$

**Theorem 2.** For $n\ge4$, write
$$
 K_n(D,r)=\frac{C_n r^{2n}}{D^2}\frac{3}{\pi(n+1)}
 \int_{-1/2}^{1/2}(1-u^2)^{-(n+1)/2}\,du,\qquad
 \delta_n(D,r)=\frac{V_{n-2}T_r^{n-2}\,rT_r}{2\zeta(n-2)D}.
$$
Then
$$
 (1-\delta_n)_+ K_n\ \le\ \Pr_{\rm Haar,D}(E_r)\ \le\ \min(1,K_n). \tag{4}
$$

*Proof.* The mean count of all planes with $h\le r$ is exactly $K_n$. Integrate (1) first over $A\le r^2/y$, then integrate $y^{-n-2}$ from $\sqrt{1-u^2}$ to infinity. Every selected witness is in this count. Retaining the exact weight $w(P,Q)$ would count only planes through a parent shortest line.

For the lower bound keep planes with $h\le r$ and $\lambda_1(Q)>T_r$. Given such plane data before drawing $Q$, the excluded Haar mass is at most $V_{n-2}T_r^{n-2}A/(2\zeta(n-2)D)\le\delta_n$ by (1). On retained planes, every vector outside $P$ already has an outer projection longer than $T_r\ge s$. Thus the plane shortest line wins in the parent for every shear. Projecting off this line still preserves that outer component. Every quotient witness of length at most $r$ therefore belongs to the one-dimensional image of $P$. Its primitive line uniquely determines $P$, so each parent contributes at most one retained plane outside the Haar-null tie set. Its mean is a lower bound on the event probability. This proves (4).

One can check the normalization of $K_n$ independently by counting a primitive line of length $s$ followed by a primitive line of length $h$ in its projection. Two applications of the rank-one formula, each with its sign-pair divisor, give the flag density
$$
 \frac{n(n-1)V_n V_{n-1}}{4\zeta(n)\zeta(n-1)D^2}s^n h^{n-2}\,ds\,dh .
$$
The centered longitudinal lift coefficient $u$ of the second generator is uniform on $[-1/2,1/2]$. The first line is shortest inside the resulting plane precisely when $h\ge s\sqrt{1-u^2}$, the binary reduction condition above. Integrating over $0<h\le r$ and $0<s\le h/\sqrt{1-u^2}$ gives exactly $K_n$. The shortest line then counts each plane once off the shape boundary.

| Haar parent | Assumed determinant | Enclosure for $\Pr(E_{26})$ at this determinant | Upper bound on $\delta_n$ |
|---|---|---:|---:|
| Rank 505 | $D=\exp L_{406}$ | $(9.97119357603,9.97119357604)\cdot10^{-63}$ | $2.348\cdot10^{-13}$ |
| Rank 506 | $D=\exp L_{405}$ | $(4.97926985101,4.97926985102)\cdot10^{-65}$ | $1.788\cdot10^{-14}$ |

The second row takes one shortest-line quotient of a fresh rank-506 Haar parent. The upper endpoints also hold uniformly above the respective determinant floors by $K_n\propto D^{-2}$. For an actual **unimodular** parent, 26 is a different scale. Minkowski's first theorem in dimension $n-1$ implies that $E_r$ holds whenever $s\ge s_0=D(2/r)^{n-1}/V_{n-1}$. Primitive Siegel in the parent gives $\Pr(E_r^c)\le V_n s_0^n/(2\zeta(n)D)$. At $D=1,r=26$ this is below $10^{-96019}$ and $10^{-96291}$ respectively.

**Two successive shortest selections.** If $P$ is specified by the shortest line in the parent followed by the shortest line in its quotient, its internal spacing $h$ is that second minimum. On $\lambda_1(Q)\le r$, a shortest outer vector lifts in the first quotient to length at most $\sqrt{r^2+h^2/4}$ by rounding along the second line. Thus $h\le T_r$ and $A\le T_r T_{T_r}$. Count planes with $h\le T_r$ and the physical outer hit by (1), using primitive Siegel at the largest allowed area. This gives
$$
 \Pr(\lambda_1(L/P)\le r)\le
 K_n(D,T_r)\,\frac{V_{n-2}r^{n-2}T_rT_{T_r}}{2\zeta(n-2)D}.
$$
At the rank-505 and rank-506 floors above this is below $1.467\cdot10^{-43}$ and $6.438\cdot10^{-47}$, respectively. Part 162 uses a band and length-dependent gates in the rank-506 window. Its audited $4.361\cdot10^{-11}$ bounds that particular joint event. [Part 162 and audit](wall1_upper_band_quotient.md#audit)

## What comparison to the finite law requires

Take the rank-505 state $M$ after draw 406, with its designated signed shortest-vector rule. Let $D=\det M$ and let the comparison draw have the same marginal $D$ and independent Haar shape conditional on $D$. The finite law is supported on finitely many shapes of Haar mass zero. The two shortest selections in the final window also use the same mark. Neither averaging histories nor the fiber identity (1) gives a density bound for these selected shapes. Ties can have positive mass in this law. [Part 163](wall1_restart_haar_ratio.md) · [Parts 183–188](../PROOF_GAP.md)

For precision, let $G$ be the raw-minimum and dual good event of Part 184. Let $Z_0$ be the canonical raw pair chosen from the designated frame on $E_{26}\cap G$, with the prescribed signed tie and lift rules. Write $I_z$ for raw membership of both points of a fixed pair. One sufficient **comparison conjecture** (with an additive allowance $\eta\ge0$) is
$$
 \sum_z \Pr(I_z)\Pr(E_{26}\cap G\cap\{Z_0=z\}\mid I_z)
 \ \le\ 3329^{15}\,\mathbb E_D[\Pr_{\rm Haar,D}(E_{26})]+\eta,       \tag{5}
$$
omitting zero-mass terms. The left side equals the finite good-event probability by disjointness. A direct upper bound by $3.9999566953\cdot10^{-7}$ would also suffice with the exits charged there. To use (5), its right side must fit this good-event budget. Part 186's coarser Haar majorant at the floor, $B(D_*)<3.33666\cdot10^{-60}$, gives $3329^{15}B(D_*)<2.28045\cdot10^{-7}$. With (4), $3329^{15}K_{505}(D_*,26)<6.815\cdot10^{-10}$. Before charging exits, the sufficient multiplicative budget from $K_{505}$ has base-3329 logarithm in $(15.78601,15.78603)$. Inequality (5) remains open for the selected finite law.

For a fixed raw pair, congruences can determine both last columns given the prefix. Its conditional chance of winning must then count compatible prefixes with the required earlier selections, lift rules and ties. Retaining only membership discards these weights. Part 188 gives a family where membership events alone cover the design space. The missing inequality is on this history-weighted selected event or an upper envelope with a proved finite-law cost. The discrepancy for replacing the penultimate event by the terminal event is a separate charge in Part 183. [Canonical-pair calculation](wall1_canonical_pair.md) · [Part 184](wall1_penultimate_projection.md) · [Part 186](wall1_quotient_slack.md) · [Part 187](wall1_local_comparison.md) · [Part 188](wall1_state_counting.md)

## Reproducing the numerical enclosures

Scratch calculations used 85-decimal-digit outward interval arithmetic. Start with $V_0=1,V_1=2,V_j=2\pi V_{j-2}/j$ and bound $1\le\zeta(j)\le1+2^{-j}(1+2/(j-1))$ for the large indices. Use $L_0=400\log3329$ and $L_i=\max(L_{i-1}-\log3329,505L_{i-1}/506-\tfrac12\log56.2142)$. The interval alternatives were disjoint at all 406 steps. This uses the determinant floors of Part 186. [Determinant recurrence](wall1_restart_passes_test.md)

For the integral in $K_n$, set $b=1/\sqrt3$ and $J_p=\int_0^b(1+t^2)^pdt$. The substitution $t=u/\sqrt{1-u^2}$ on the positive half gives $2J_{(n-2)/2}$ for the full integral. Use $J_0=b$, $J_{-1/2}=\log\sqrt3$, and $(2p+1)J_p=b(4/3)^p+2pJ_{p-1}$, obtained by differentiating $t(1+t^2)^p$. Applying the lower endpoint to $(1-\delta_n)K_n$ and the upper endpoint to $K_n$ gives the probability brackets above. As an independent interval check, substituting $t=\sinh v$ gives $2\int_0^{\log\sqrt3}\cosh^{n-1}v\,dv$. Expanding the integer power into a finite binomial sum of exponentials and using the rank-one flag prefactor reproduced both brackets.

## Audit

**Verdict — SOUND.** Equations (1)–(4) give the stated Haar incidence and probability bounds. Part 186's earlier bound applies to the same physical event. Equation (5) is a sufficient comparison conjecture for the finite restart law.

**Incidence normalization.** Kim's Theorem 3 with one rank-two subgroup counts each saturated subgroup once. Substituting $V_1=2$, $V_2=\pi$, Kim's convention $\zeta(1)=1$, and $\zeta(2)=\pi^2/6$ gives $a(n,2)=(n-1)\pi V_nV_{n-1}/(24\zeta(n)\zeta(n-1))$. Differentiating $a(n,2)(a/D^{2/n})^n$ gives exactly the area density in (1). In the oriented cover the shear torus has unit mass, and its integer basis changes preserve that mass. The two determinant-one diagonal blocks therefore have independent Haar probability laws on the lattice spaces. Forgetting orientation divides the oriented mass by two, already accounted for in $a(n,2)$. As a low-rank check, $C_3=V_3/(2\zeta(3))$, also obtained by counting primitive normal lines in the unimodular dual. The four cited Lean declarations give the rank-one unfolding, almost-everywhere kernel, product measure and oriented count bound. The rank-two disintegration uses the block argument in this note. [Kim, Theorem 3 and Lemma 10](https://arxiv.org/pdf/2005.10874)

**Bounded count and shortestness.** At fixed $A$, integrating $3/(\pi y^2)$ above both $\sqrt{1-u^2}$ and $A/\ell^2$ gives exactly $H$. The two elementary upper bounds on $H$ cross at $A=3\ell^2/\pi$. Multiplying by the primitive-line mean of the physical outer ball introduces $A/D$ because $\det Q=D/A$. Integrating the two resulting powers of $A$ gives the displayed closed upper bound. For (3), the least squared length in a nonzero quotient fiber is $|z|^2+d_P(T(z),0)^2$. Thus only $0<|z|<s$ can defeat the candidate, and equality allows a tie. The indicators must be averaged over a single shared shear. For the outside-point mean, the factors $1/A$ from the torus average and $A/D$ from ordinary Siegel leave $1/D$ before the sign-pair divisor.

**Which event is rare.** Part 183 calls the pre-draw-407 event $J$ and the terminal event $F$. Parts 184–186 use $E$ for $J$. In the rank-505 parent $M=H_{406}$ the test is $\lambda_1(\pi_{x^\perp}M)\le26$ for its designated shortest line. A primitive witness pulls back to a saturated plane $P$ with spacing $\det(P)/|x|\le26$ **inside** $P$ modulo $x$. The outer quotient $M/P$ has rank 503. With unrestricted choice of $P$ through $x$, the primitive directions $kb_1+b_2$ make its outer minimum arbitrarily small while the internal spacing tends to infinity. This proves the probability-one assertion for every lattice in both stated ranks. In (4) the outer minimum instead serves to discard planes with possible outside competitors. On the retained set every short witness projects onto the same primitive line modulo $x$, so the retained count is at most one almost surely. This last step justifies the probability lower bound. Part 162 has a preceding rank-506 selection and additional band and length gates. Part 183 charges the discrepancy between $F$ and $J$ separately. [Part 162](wall1_upper_band_quotient.md) · [Part 183](wall1_terminal_tail_047.md) · [Part 186](wall1_quotient_slack.md)

**Independent numerical enclosure.** Rescaling $v=2u$ on the positive half of the shape integral gives $\int_0^1(1-v^2/4)^{-(n+1)/2}\,dv$. Its binomial-series terms satisfy $t_0=1$ and $t_{k+1}/t_k=(n+1+2k)(2k+1)/(8(k+1)(2k+3))$. I summed through $k=600$ in exact rational arithmetic. All subsequent ratios are below $1/2$ for both ranks, so the omitted tail is bounded by $t_{600}$. Using the two primitive sign-pair factors, factorial formulas for ball volumes and 100-decimal-digit outward interval arithmetic for the determinant recurrence and remaining operations gave
$$
 9.97119357603428\cdot10^{-63} < (1-\delta_{505})K_{505}
 \le \Pr_{\mathrm{Haar},D_*}(E_{26})
 \le K_{505} < 9.97119357603664\cdot10^{-63}.
$$
The same calculation reproduced the rank-506 bracket and gave $3.3366580972102\cdot10^{-60}<B(D_*)<3.3366580972103\cdot10^{-60}$ in rank 505. The latter was a valid upper bound for $J$ obtained by counting extra flags. Only the upper probability bound extends uniformly to all determinants above the floor.

**Finite comparison.** Each canonical-pair event in (5) implies its membership event $I_z$, and the signed tie and lift rules partition $E_{26}\cap G$. The left side is therefore exactly $\Pr_{\rm finite}(E_{26}\cap G)$. At the floor, $3329^{15}K_{505}<6.814815066272\cdot10^{-10}$. If (5) holds, an additive allowance $\eta\le3.99314188023\cdot10^{-7}$ still fits Part 184's good-event budget, using the uniform Haar upper bound. The comparison itself requires control of the conditional selection probabilities with their history weights. The Haar fiber law and the raw membership counts alone give no such control. [Part 184](wall1_penultimate_projection.md) · [Part 187](wall1_local_comparison.md) · [Part 188](wall1_state_counting.md) · [Part 189](wall1_canonical_pair.md)
