# First small-area planes on late vertical wins

Let $a=1352/\sqrt3$, $A_i=\{a_2(\Lambda_i)\le a\}$, and let $\tau$ be the first $i$ with $A_i$. Use the unconditioned Part 108 restart and the good event $G$ of Part 184. R60's vertical residual $Z_2$ is the joint mass of $G,A_{406},395\le\tau\le406$, and a vertical win of length $s>30$ at $\tau$. There are **12** eligible draws. A hit at draw 406 permits intervening misses after the first hit. [R60, audit](wall1_rank2_tail.md#audit) · [First-tour law](wall1_first_tour.md)

**Partial bound.** Write $k$ for the positive height of the oriented winner, $g=(\det\Lambda_{\tau-1}/V_{506})^{1/506}$ for the incoming Gaussian-heuristic length (GH), and $R=2^{1/4}\sqrt a$. Let $Z_{\rm rem}$ be the portion of $Z_2$ with
$$
396\le\tau\le406,\qquad 1\le k\le12,\qquad
\max(30.5,0.945g)<s\le R.
$$
Then
$$
0\le Z_2-Z_{\rm rem}<2.515\cdot10^{-11}.
\tag{1}
$$
Throughout the remainder $s/g<1.032298$. A sufficient outstanding inequality for the proposed allocation is $Z_{\rm rem}\le6.485\cdot10^{-11}$. The mark law gives the exact conditional plane count below. The outstanding quantity depends on which old planes occur in the selected histories and which marks win there. The absolute allocation $9\cdot10^{-11}$ is itself a target. R60's determinant-matched comparison also uses the other first-hit stratum, the exit charges, and the actual determinant average.

## One draw, with its plane and winner selected by the same mark

Fix the incoming framed state, write $M=\Lambda_{i-1}\subset K=P_E\mathbb Z^N$, $D=\det M$, $H=K/M$, and $q=3329$. Conditional on the prefix, the fresh mark $U$ is uniform on $H$, and $qK\subset M$. The window is $W_U=(M,0)+\mathbb Z(\tilde U,1)$. Select its shortest sign pair by the original tie rule, then orient a vertical winner as $v=(y,k)$ with $k>0$. If its quotient contains a saturated plane of area at most $a$, the preimage is a rank-three lattice of determinant at most $as$ and minimum $s$. The ternary Hermite inequality $s^3\le\sqrt2\,as$ gives $k\le s\le R<33.22505$. Thus every candidate height is invertible modulo $q$.

For $1\le k\le33$ and $y\in K$ with $s^2=k^2+\|y\|^2\le R^2$, put $u=k^{-1}[y]\in H$, choose a lift $\tilde u\in K$, and write $l=y-k\tilde u\in M$. Let $I(y,k)$ indicate that this candidate's sign pair wins in $W_u$. This includes every smaller-key competitor at the same label, with ties resolved before orienting. A prescribed shortest section is uniform on its finite image for uniform marks. Within a specified winning-height subset the image is restricted to that subset. Fixing $y,k$ already determines the mark. [VoronoiMarkLaw.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/VoronoiMarkLaw.lean) · [Part 161, fixed and moving voids](wall1_band_plane_hits.md#keeping-shortestness-in-the-joint-count)

For a winning candidate set $M'=M+\mathbb Zl/k$. Each saturated old plane $\Delta=M\cap F$, with rational two-space $F$, indexes exactly one saturated output plane $P=A_v(M'\cap F)$. Indeed $M'$ and $M$ are commensurable and $A_v$ is an isomorphism on the horizontal real space. Put $d=\det\Delta$, $\pi=P_{F^\perp}$, and
$$
e=[M'\cap F:\Delta]
 =\gcd\big(k,\operatorname{content}_{\pi M}(\pi l)\big).
$$
Content is the gcd of lattice coordinates, with content zero for the zero vector. Primitivity of $v$ gives $M'/M$ order $k$, since the coordinates of $l$ in $M$ together with $k$ are coprime. The residues $m\bmod k$ with $m\pi l\in k\pi M$ are precisely the cosets admitting a representative in $F$. Counting them gives the gcd formula, unchanged by changing the lift of $u$. The compression has Gram form $1-yy^\top/s^2$. Its area factor on $F$ is $\sqrt{1-\|P_F y\|^2/s^2}$. Hence
$$
\det P=\frac{d}{es}\sqrt{k^2+\|\pi y\|^2}.
\tag{2}
$$
In particular $k=1$ allows creation by compression of a plane generated entirely by old vectors. [VerticalWinnerIsometry.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/VerticalWinnerIsometry.lean) · [Part 139, one-step geometry](wall1_lyapunov.md)

On a prefix with no earlier hit, the conditional expected number of newly qualifying saturated planes on the vertical band is exactly
$$
\frac1{|H|}\sum_{(y,k):\,30<s\le R} I(y,k)
 \sum_{\Delta}^{\rm sat,\,rk\,2}
 \mathbf1\!\left\{d^2(k^2+\|\pi y\|^2)\le a^2s^2 e^2\right\}.
\tag{3}
$$
In (3), $y\in K$ and $k>0$. Evaluate the inner sum only for winners. All contributing terms have $a<d\le as\le aR$. Replacing the inner count by its nonempty indicator gives the exact conditional first-hit probability in this band. One may impose the remaining length and height restrictions in the outer sum. To recover the exact residual mass, average on surviving prefixes and weight each successful mark by the conditional probability of $G\cap A_{406}$ given the extended prefix. Dropping this last weight gives an upper bound. In particular, conditioning the mark to be uniform *after* imposing $G\cap A_{406}$ would require a separate argument.

### A projected-grid bound for the plane count

On a surviving prefix put $t=\min(R,\lambda_1(M))$ and restrict to $k\le12$. For a hit through $v$, its saturated preimage $J\subset W_u$ intersects the old space in $\Delta$ and its heights are $j\mathbb Z$, where $j=k/e$. This follows by taking heights in $J/(\Delta+\mathbb Zv)$, of order $e$. The vectors of $J$ at height $j>0$ form one coset modulo $\Delta$. Their common transverse horizontal part is $z\in j\pi\tilde u+\pi M$. Its triple has determinant $d\sqrt{j^2+\|z\|^2}\le as\le at$. For fixed $u,\Delta,j$, distinct triples give distinct $z$, because the kernel of $\pi$ on $M$ is $\Delta$. Thus dropping shortestness, incidence through $v$, and primitivity bounds the expectation in (3), restricted to these heights, by
$$
\sum_{a<d\le at}\ \sum_{1\le j\le\min(12,at/d)}
 \frac{\#\{z\in\pi K:\|z\|^2\le(at/d)^2-j^2\}}{|\pi K/\pi M|}.
\tag{4}
$$
The first sum runs over saturated planes. The projected mark multiplied by $j$ is uniform, so each normalized ball count in (4) is an exact unfiltered coset average. Both $D$ and $t$ can be evaluated at the incoming state. On the remainder, old planes also satisfy $d\ge\sqrt3\,s^2/2>805.6201$, by binary reduction.

For any $h>0$ and transverse radius $b\ge0$, the individual ratio in (4) is at most
$$
\frac dD\exp(\pi b^2/h^2)h^{503}
 \left(1+\frac{2e^{-\pi h^2}}{1-e^{-3\pi h^2}}\right)^{503}.
\tag{5}
$$
Indeed $\det\pi M=D/d$ by basis extension. The lattice $\pi K$ is the projection of the ambient integer grid onto $E\cap F^\perp$, with intrinsic rank 503. Its dual there is the integer section. Restriction to 503 independent coordinate rows injects that section into $\mathbb Z^{503}$ and decreases norms. Gaussian majorization of the ball followed by Poisson summation gives (5), using $n^2\ge1+3(n-1)$ for $n\ge1$. The history fixes $F$ before this average. Applying (5) still leaves the sum over the old planes. Applying a radial theorem directly to a pair of output vectors would also require the joint law of their common compression and cyclic refinement. Parts 148 and 150 count shortened *lines* for a different terminal observable. [Positive-height multiplicity](wall1_vertical_multiplicity.md#audit) · [Shortened lines](wall1_shortened_lines.md#audit)

## Charging the parts removed in (1)

Let $g_i^0=(e^{L_{i-1}}/V_{506})^{1/506}$, where $L_0=400\log q$ and
$$
L_i=\max\big(L_{i-1}-\log q,\ (505/506)L_{i-1}-\tfrac12\log(56.2142)\big).
$$
The window contains the height-$q$ period and has determinant $D$. Its shortest length is at most $\min(q,\sqrt{56.2142}\,D^{1/506})$ by the paper's rank-506 Hermite certificate. Dividing $D$ by the winner length gives the recurrence and $g\ge g_i^0$. [Hermite certificate](wall1_hermite_caps.md)

For a physical radius $52/\sqrt3\le r<q$, the expected number of positive-height candidates through $r$ is at most $C(r/g)^{506}$, $C=1.422743743939$. Each positive-height grid point of $K\times\mathbb Z$ in the ball occurs for one mark. The grid is the projected cubic grid onto $E\times\mathbb R$, and its determinant times $|H|$ is $D$. The positive-height subset is disjoint from its negative. Each term of the binned radial constant decreases weakly with $r$ by monotonicity of the theta bound. One can therefore use the certified constant at $52/\sqrt3$ for all the radii below. [ProjectedBallCount.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/ProjectedBallCount.lean) · [TerminalMajorant506.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/TerminalMajorant506.lean)

For the tall part, inject **candidate grid points** of height $k\ge13$ in the radius-$R$ ball by $(y,k)\mapsto(y,k-12)$. The image has positive height and squared norm at most $R^2-24k+144\le R^2-168$. Thus the same count applies at $r_H=\sqrt{R^2-168}>30.59253$. This translation counts the source points with weight $1/|H|$ each, without requiring the translated point to win or to have the original label.

| Part covered | Upper expression | Strict upper bound |
|---|---|---:|
| Draw 395, all winning heights | $C(R/g_{395}^0)^{506}$ | $6.96163\cdot10^{-12}$ |
| Draws 396–406, $s\le30.5$ | $\sum_i C(30.5/g_i^0)^{506}$ | $2.19992\cdot10^{-12}$ |
| Same draws, $30.5<s\le0.945g$ | $11 C(0.945)^{506}$ | $5.79449\cdot10^{-12}$ |
| Same draws, $k\ge13$ | $\sum_i C(r_H/g_i^0)^{506}$ | $1.01891\cdot10^{-11}$ |

In the third row use $r=\min(R,0.945g)$ and skip the empty interval when $r\le30.5$. Summing the four bounds covers the union in (1). For comparison, the same unrestricted radius-$R$ majorant is greater than $3.3300\cdot10^{-10}$ at the draw-396 determinant floor and $1.3751\cdot10^7$ at the draw-406 floor. These values quantify the loss of discarding the plane and selection in that upper bound. They give no lower bound on the selected probability.

The fixed void of Part 153 has the following implication here. For $V=\{s>30.5\}$, $B=\{\lambda_1(M)>30.5\}$ and any mark event $C_1$,
$$
0\le\Pr(B\cap C_1\mid S)-\Pr(V\cap C_1\mid S)
 \le\mathbf1_B C(30.5/g)^{506}.
$$
Indeed $V\subset B$, and on $B\setminus V$ a positive-height point wins. Thus on an eligible old history the fixed fresh void has probability close to one. A void at the *candidate's own key* instead gives the exact selector $I(y,k)$. After $S,y,k$ are specified its truth value is deterministic. Inverting a framed branch retains the mass of its parent prefix. Both arguments leave the history-weighted counts in (3) or (4). [Part 153, audit](wall1_neargh_vertical.md#audit) · [Part 176, audit](wall1_inverse_branch.md#audit) · [InverseBranch.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/InverseBranch.lean)

## A finite check of creation at height one

Take $M_0=155\mathbb Z^2$ and the uniform cyclic mark generated by $155(1,19)/3329\bmod M_0$. Its only saturated plane has area $155^2>a$. Write $[n]_q\in[-1664,1664]$ for the centered residue. For mark $m$, the least squared window length at positive height $k$, multiplied by $q^2$, is
$$
T_m(k)=(qk)^2+155^2\big([km]_q^2+[19km]_q^2\big).
$$
The horizontal minimum is 155. Testing all 3329 marks and $1\le k\le33$ suffices for the band. The quotient plane is the whole rank-two output and has area $155^2/s$. Exact integer comparisons give exactly two marks with $30.5<s\le R$ and area at most $a$, namely 141 and 3188. Both have unique positive winning height one, $q^2s^2=10639285766$. The runner-up is height 21 with value 10820962781. Their retained area lies in $(775.3913,775.3914)$. At $k=1$, $e=1$ and $\pi y=0$ on this plane, giving the same area from (2).

The example also admits the physical GH and rank of the remaining interval. Pad orthogonally by a rank-503 lattice $B_0$ of determinant $V_{506}(32.2)^{506}/155^2$ and minimum above 31, keeping the mark on the first summand. Such a lattice exists by the mean-value formula. At that determinant the Haar expected number of nonzero points through 31 is $V_{503}31^{503}/\det B_0<2.624\cdot10^{-6}$. The padded old minimum exceeds 31, so binary reduction excludes every incoming area hit. The two displayed winners have $s<31$, hence are still shortest. Their output planar summand is saturated and unchanged in area. They pass both the $0.954g$ void and the remaining band, with $0.96224<s/g<0.96225$. Thus even at rank 506 the one-step area, length, old minimum and a uniform prime-order mark permit hit mass at least $2/3329$. This is an example for abstract marked lattices. Its old dual contains a vector of length $1/155$. Applying it to the restart would require the projected-grid hypotheses, a reachable prefix satisfying the good-event constraints, and its probability. [Haar mean and line incidence](../../SigabaNeo/Lib/Lattices/Research/Wall1/HaarMinimumTails.lean)

**Verification.** Scratch evaluation used 65-decimal-digit outward interval arithmetic, $V_{506}=\pi^{253}/253!$, and $V_j=2\pi V_{j-2}/j$ from $V_1=2$ for the odd volume. The alternatives in each logarithmic determinant update were disjoint. The sum of the four unrounded upper expressions was in $(2.5145099725,2.5145099726)\cdot10^{-11}$, and $R/g_{406}^0\in(1.03229725,1.03229727)$. The mark enumeration used integer residues and the exact area test $3\cdot155^4 q^2\le1352^2\min_k T_m(k)$.

**Open estimate.** Neither the distribution of the transverse plane counts on surviving prefixes nor their same-mark shortestness weights have been bounded here at the remaining $6.485\cdot10^{-11}$ scale. The asserted allocation $Z_2\le9\cdot10^{-11}$ remains conjectural. The example bounds a conditional mass in another model and gives no lower bound on $Z_2$.

## Audit

**Verdict — SOUND.** No correction to (1)–(5), the residual allocation, or the height-one example is needed.

**Numerical charges.** An independent 85-decimal-digit outward interval calculation used $V_{506}=\pi^{253}/253!$. The 4096-bin sum at physical radius $52/\sqrt3$ lies in $(1.42274374393791,1.42274374393793)$. Its theta factors decrease with radius, so the printed $C$ covers all four charges. The determinant updates had disjoint branch intervals, choosing the period bound 20 times and the Hermite bound 386 times. Using the incoming $L_{i-1}$ for draw $i$ gave the following enclosures.

| Charge | Enclosure in units of $10^{-12}$ |
|---|---:|
| Draw 395 | $(6.96162850,6.96162852)$ |
| Draws 396–406, $s\le30.5$ | $(2.19991891,2.19991893)$ |
| Draws 396–406, $30.5<s\le0.945g$ | $(5.79448009,5.79448011)$ |
| Draws 396–406, $k\ge13$ | $(10.18907220,10.18907221)$ |

For the last row, subtracting 12 from the height keeps it positive and reduces squared length by at least 168. Each source point has mark weight $1/|H|$. Injectivity therefore suffices even when translation changes the mark. The tall and short charges can overlap. Their use in a union bound gives a total upper expression in $(2.51450997256,2.51450997258)\cdot10^{-11}$.

**Conditional plane count.** Primitivity of $(l,k)$ in window coordinates gives the cyclic refinement $M'/M$ order $k$. Its map to $(\pi M+\mathbb Z\pi l/k)/\pi M$ has kernel of order $e=\gcd(k,\operatorname{content}_{\pi M}(\pi l))$, including $e=k$ when $\pi l=0$. This kernel identifies with $(M'\cap F)/\Delta$. The area before compression is consequently $d/e$. Restricting the compression Gram form to $F$ gives the remaining factor $\sqrt{k^2+\|\pi y\|^2}/s$ in (2). Commensurability gives one old rational plane per output rational plane. At these heights the candidate determines $U=k^{-1}[y]$, the projection and every same-mark tie. Thus (3) counts each qualifying saturated plane once for each winning mark, and its inner nonempty indicator counts that mark once.

In (4) the height image of the lifted triple is $j\mathbb Z$ with $ej=k$. For fixed mark, old plane and $j$, two generators at height $j$ with the same transverse projection differ by an element of $\Delta$ and generate the same triple with $\Delta$. Multiplication by $j$ permutes the projected mark group. These facts justify the unfiltered coset average, and $\det(\pi M)=D/d$ gives the normalization in (5). On eligible surviving prefixes the fixed-radius void inequality bounds the additive error for any mark event. The selector at the candidate's own key is deterministic once the prefix and candidate are fixed. Part 176's inverse retains the prefix multiplicity. Equations (3)–(5) still require the distribution of old planes on surviving prefixes. The exact first-hit mass uses the original probability of each such prefix and the continuation weight for $G\cap A_{406}$. [Part 142](../PROOF_GAP.md) · [Part 153 audit](wall1_neargh_vertical.md#audit) · [Part 161 audit](wall1_band_plane_hits.md#audit) · [Part 176 audit](wall1_inverse_branch.md#audit)

**Residual.** Removing draw 395 leaves eleven draws, $396\le\tau\le406$, with $1\le k\le12$ and $\max(30.5,0.945g)<s\le R$. The determinant floors decrease over these draws, and $1.03229725<R/g_{406}^0<1.03229727$, giving $0.945<s/g<1.032298$. Equality at either lower length cutoff has already been charged. The proposed $6.485\cdot10^{-11}$ for this residual suffices for the absolute $9\cdot10^{-11}$ allocation. That residual estimate is open. The determinant-matched comparison in Parts 190–192 also retains the horizontal residual, the applicable exit charges and the actual determinant average. [Rank-two tail audit](wall1_rank2_tail.md#audit)

**Height-one example.** Exact integer enumeration used the horizontal competitor of length 155 and all positive heights through 155 for each of the 3329 marks. With $T=q^2s^2$, the upper band test is $3T^2\le2\cdot1352^2q^4$. Exactly marks 141 and 3188 passed the length band, and both also passed $3\cdot155^4q^2\le1352^2T$. Each has a unique positive shortest representative at height 1 with $T=10639285766$. The next sign pair has height 21 and value $10820962781$. The area lies in $(775.39135,775.39136)$. For the orthogonal padding, the mean nonzero count through 31 lies in $(2.62322,2.62324)\cdot10^{-6}$, while the two winners have $s<31$ and $0.96224700<s/32.2<0.96224702$. This verifies a conditional hit mass of at least $2/3329$ for the abstract marked example. Its occurrence and weight under the finite restart remain unproved.
