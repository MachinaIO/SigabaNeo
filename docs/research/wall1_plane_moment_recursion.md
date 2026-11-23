# Can the plane count be propagated from draw 154?

The proposed recursion gives a one-step inequality for a positive-height win. Its first term needs the incoming plane count **above** the first-hit threshold. Its second term needs the joint law of the incoming planes and the mark subgroup. The draw-154 bound supplies neither input. In fact, two marked lattices can have identical incoming counts at **every** area cutoff and different outgoing first moments, even when every mark gives a unique height-one winning line. The example below concerns the transition law. It gives no lower bound on the residual of the finite chain.

## One vertical step

Write $N_X(M)$ for the number of unoriented saturated rank-two sublattices of $M$ of area at most $X$. Take the unconditioned restart law and put $a=1352/\sqrt3$. Write $G_t$ for survival of the good-event tests through draw $t$, and $\tau$ for the first area hit at cutoff $a$, including time zero. For a first-hit upper bound the appropriate incoming weight is $B_t=G_t\cap\{\tau>t\}$. Define
$$
 m_t(X)=\mathbb E[\mathbf1_{G_t}N_X(M_t)],\qquad
 \mu_t(X)=\mathbb E[\mathbf1_{B_t}N_X(M_t)].
$$
These are unnormalized expectations. In particular $\mu_t(a)=0$. Both weights are measurable before the next mark. Imposing the terminal event $G_{406}\cap\{N_a(M_{406})>0\}$ on the incoming law would change the mark average. Dropping the terminal requirement bounds the joint residual from above. [First-tour law](wall1_first_tour.md) · [First-hit partition and audit](wall1_rank2_tail.md#audit)

Fix an incoming framed state $S=(M,H,\mathrm{frame})$. For a uniform mark $u\in H$, write a positive-height winner as $v=(y,k)$, $s=\|v\|$, and $l=y-k\tilde u\in M$. The retained lattice is isometric to the image of $M'=M+\mathbb Zl/k$ under the horizontal compression. The primitive window vector $v$ has coprime coordinates in a window basis, so $M'/M$ has order $k$. The old and refined lattices have the same rational two-spaces. For each such space $F$ write $d_F=\det(M\cap F)$ and $e_F=[M'\cap F:M\cap F]$. This quotient embeds in $M'/M$, so $e_F\mid k$. Restricting the compression's Gram form to an orthonormal basis of $F$ gives determinant $1-\|P_Fy\|^2/s^2$. The corresponding saturated output plane therefore has area
$$
 d'_F=\frac{d_F}{e_F}
       \sqrt{1-\frac{\|P_Fy\|^2}{s^2}}
     =\frac{d_F}{e_Fs}\sqrt{k^2+\|P_{F^\perp}y\|^2}
     \ \ge\ \frac{d_F}{s}.
 \tag{1}
$$
The compression is invertible for $k>0$, so this indexes each output plane once. For $d_F>e_F X$, a hit requires $\|P_F y\|^2/s^2\ge1-(e_F X/d_F)^2$. For $X<d_F\le e_F X$, refinement already puts the area at or below $X$ for every compression angle compatible with that index. Thus a first hit need not incur an angular probability factor. [Vertical-winner isometry and norm formula](../../SigabaNeo/Lib/Lattices/Research/Wall1/VerticalWinnerIsometry.lean) · [Vertical plane calculation](wall1_z2_vertical.md)

Let $V$ select a vertical band on the next draw with $s\le R$. For an old plane define the conditional probability
$$
 K_X(S,F)=|H|^{-1}\sum_{u\in H}
          \mathbf1_{\{V,\ d'_F\le X\}}.
$$
Evaluate $d'_F$ only on $V$, using the winner at that mark. For every $1\le c\le R$, summing (1) and splitting at $cX$ yields
$$
 \mathbb E[\mathbf1_{B_t}\mathbf1_V N_X(M_{t+1})]
 \ \le\ \mu_t(cX)+
 \mathbb E\!\left[\mathbf1_{B_t}
       \sum_{cX<d_F\le RX} K_X(S_t,F)\right].
 \tag{2}
$$
Indeed each plane in the first sum has conditional weight at most one, and the planes above $RX$ have weight zero. With $G_t$ in place of $B_t$ the same calculation gives the corresponding inequality with $m_t$. For the full no-exit moment one must also account for wins outside $V$.

At $X=a$, use the specified remaining band on each draw $t+1=396,\ldots,406$. A first hit in this band contributes at least one plane on the left of (2). Their sum therefore bounds the residual from above. At $c=1$ the first term vanishes, but the sum then extends over **all** qualifying old areas above $a$. At $c=R$ only $\mu_t(Ra)$ remains. The ternary preimage of a hit has minimum $s$ and determinant at most $sa$, whence $s^3\le\sqrt2\,sa$ by ternary Hermite. Thus one can take $R=2^{1/4}\sqrt a$. Outward interval arithmetic gives $33.22504<R<33.22505$ and $25934.72189<aR<25934.72190$. There is some genuine slack in this split. A winner with $s>30.5$ forces $\lambda_1(M_t)>30.5$ since the entire old lattice is a competitor. This old-minimum test is prefix measurable, so it may be included in $B_t$ on the right of (2). Binary reduction gives $d_F\ge(\sqrt3/2)\lambda_1(M_t)^2$ for every old plane. Indeed a shortest plane basis vector has length $\lambda$ and the perpendicular component of a reduced second vector has length at least $\sqrt3\,\lambda/2$. On eligible parents this yields $d_F>805.62013$ and in exact terms $d_F/a>c_0=11163/10816$. Thus the first term vanishes on those parents for $1\le c\le c_0$. At $c=c_0$ the second term still covers every area that could contribute. Taking $c>c_0$ requires accounting for the near-threshold term or proving a further exclusion.

## Why the estimate does not iterate from the stated inputs

1. **Initial condition.** The draw-154 flag argument bounds $\Pr(\tau\le154)$ by $5.284\cdot10^{-15}$. It charges a short-vector witness for a history with a hit. Several saturated planes can share that witness. Even an upper bound on $\mathbb E N_a$ would not bound $\mu_{154}(ca)$ for $c>1$. On a surviving history every plane in $(a,ca]$ is compatible with the absence of an earlier hit. At time zero the random graph is explicit given its initial columns, so its count can be defined directly. Even exact knowledge of its entire mean area distribution would still require a transition estimate at each later step. [Draw-154 estimate and audit](wall1_rank2_tail.md#audit)
2. **The mark and the plane.** The Voronoi theorem assigns equal weights to the image of a fixed shortest section on a finite set of marks. That image depends on the embedded subgroup. Selection among different heights also uses the same mark. The projected-ball theorem bounds a radial candidate count in rank 506. Applied to all candidates it can overcount the marks for a *fixed* plane. Summing that bound repeats the charge for every eligible plane. The transverse-grid relaxation in the vertical note retains precisely this outer sum. A uniform envelope $K_X(S,F)\le f_X(d_F)$ would turn it into an integral against the incoming area-count measure $d\mu_t$. Its size and the needed incoming moments must both be controlled. The transverse Haar incidence formula concerns a different parent law, and a fixed void on fresh candidates supplies no such finite-chain comparison. [Voronoi mark law](../../SigabaNeo/Lib/Lattices/Research/Wall1/VoronoiMarkLaw.lean) · [Projected ball count](../../SigabaNeo/Lib/Lattices/Research/Wall1/ProjectedBallCount.lean) · [Parts 142 and 153](../PROOF_GAP.md) · [Haar incidence audit](wall1_rank2_transverse.md#audit) · [Finite comparison audit](wall1_plane_comparison.md#audit)
3. **Horizontal wins between the restart and the last eleven draws.** An output plane lifts to a unique saturated triple containing the designated line. For a horizontal winner $x$, a triple can be entirely in the old lattice. Such a triple $J$ contributes when $x\in J$ and $\det J\le X\|x\|$. This part of the transition counts old rank-three sublattices through the selected line. A triple using the fresh coordinate has a rank-two old intersection and a separate height and coset condition. The Rankin projection inequality bounds a minimum, and the saturation theorem restricts an infimum to primitive old sublattices. Neither supplies these incidence multiplicities. Horizontal wins can occur *before* a first hit at a vertical win, so the incoming moments for that last win include these histories. [Rankin projection and append](../../SigabaNeo/Lib/Lattices/Research/Wall1/RankinWindow.lean) · [Rankin saturation](../../SigabaNeo/Lib/Lattices/Research/Wall1/RankinSaturation.lean) · [Conditional first moment](wall1_rank2_tail.md#the-conditional-first-moment-and-the-origin-of-a-plane)

## Exact check with identical incoming plane counts

Take $M=\operatorname{diag}(4,5,7)\mathbb Z^3$, cutoff $X=23/2$, and height-one appends. Compare uniform order-three mark groups generated by $(4/3,0,0)$ and $(0,0,7/3)$ modulo $M$. The incoming lattice, determinant, entire function $Y\mapsto N_Y(M)$, and mark order agree. Its least plane area is $20>X$.

For a nonzero mark on an axis of spacing $b$, the shortest possible horizontal components at heights one and two both have length $b/3$. Height three has length at least three, and the horizontal minimum is four. In both groups $s=\sqrt{1+b^2/9}<3$, so height one wins uniquely up to sign. The output is rectangular with the marked spacing divided by $s$. At the zero mark all spacings are unchanged. In a rectangular lattice a plane's squared area is a sum of squared coordinate-pair areas times squared integral minors. Its least area is therefore the least pair product.

| Mark generator | Least squared output area at either nonzero mark | $\mathbb E N_{23/2}(M_{\rm out})$ |
|---|---:|---:|
| $(4/3,0,0)$ | $144$ | $0$ |
| $(0,0,7/3)$ | $3528/29$ | $2/3$ |

Here the table counts saturated output planes. In the second row only the plane of the first and third axes qualifies. Its squared area is below $529/4$, the other coordinate-pair squares exceed $529/4$, and saturation fixes the subgroup in its span. Both means also equal their respective first-hit probabilities. Exact rational enumeration in scratch checked all three marks in each group, the height comparisons, and the coordinate-pair squares. The intervals above used 35-decimal-digit outward arithmetic.

The example rules out recovering the vertical transition exactly from the incoming area-count function and mark order in general. It leaves room for upper bounds specific to the reachable framed states. For the stated chain, the missing estimate is the sum in (2) averaged on surviving prefixes, together with any enlarged-cutoff moments left after the old-minimum exclusion. **The proposed $6.485\cdot10^{-11}$ allocation remains conjectural.**

## Audit

**Verdict — sound.** Equation (2) gives a one-step upper bound. Parts 190–194 leave the surviving-prefix plane counts and their joint distribution with the next winning mark open.

**One vertical step.** Fix the prefix and average over its uniform mark. Each winning mark contributes one indicator per rational two-space because refinement preserves the rational spaces and compression is invertible. In (1), $e_F\mid k$ gives $d'_F\ge d_F k/(e_Fs)\ge d_F/s$. Thus $d_F>RX$ contributes zero, $cX<d_F\le RX$ contributes exactly $K_X(S,F)$, and each $d_F\le cX$ contributes at most one. Averaging with the prefix indicator gives (2), including the endpoint $d_F=cX$. A history in the remaining vertical residual contributes at its unique first hit. Dropping the terminal test and counting all qualifying planes can only increase that charge. [Part 193, conditional plane count](wall1_z2_vertical.md#audit)

**Strict endpoint.** Even if the selected line ties an old line, $\lambda_1(M)\ge s$. On the specified band every old plane therefore satisfies
$$
  \frac{d_F}{a}\ \ge\ \frac{3\lambda_1(M)^2}{2704}
  \ >\ \frac{3(61/2)^2}{2704}=\frac{11163}{10816}.
$$
Consequently the small-area term vanishes at $c=c_0$ **after** intersecting $B_t$ with $\{\lambda_1(M_t)>30.5\}$. The unfiltered $\mu_t(c_0a)$ may include other parents. Exact rational comparisons of fourth powers confirm both printed intervals for $R$ and $aR$.

**Horizontal incidence.** Projection along a primitive horizontal winner $x$ identifies the output group with $W/\mathbb Zx$. Taking the full inverse image and passing to the quotient are inverse operations on saturated output planes and saturated triples through $x$. Extending $x$ to a basis of such a triple gives $\det J=\|x\|\det P$. The kernel of the integer height map is $M$, so a wholly old triple is saturated in $W$ exactly when it is saturated in $M$. Each qualifying old triple through $x$ therefore contributes once. A triple of nonzero height image instead has a rank-two kernel in $M$. The Lean statements `rankin_project` and `rankin_append` concern infima of volumes. A count through the selected line requires the incidence condition in Part 192, equation (4). [Part 192](wall1_rank2_tail.md#the-conditional-first-moment-and-the-origin-of-a-plane) · [RankinWindow.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/RankinWindow.lean)

**Rank-three example.** I checked all six marks with rational squared lengths. At a nonzero mark, height two has squared minimum $s^2+3$, heights of absolute value at least three have squared minimum at least $9$, and the horizontal minimum squared is $16$. The nearest representative at height one is unique on either marked axis. At the zero mark the vertical unit wins and the least squared plane area is $400$. At either nonzero mark the coordinate-pair squares, in order $12,13,23$, are $(144,7056/25,1225)$ for the first axis and $(400,3528/29,11025/58)$ for the third. A saturated plane corresponds to a primitive triple of integral minors up to sign. At cutoff squared $529/4$, only the second group admits a triple, $(0,1,0)$ up to sign. This gives the stated means $0$ and $2/3$ and establishes the distinction between the two abstract transition laws. The finite-chain allocation remains open.
