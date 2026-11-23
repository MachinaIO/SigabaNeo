# Raw section area and the terminal plane index

Two obstructions prevent the proposed deduction from Part 205. The terminal area ratio is one factor of the index bounded below by 1,893. At the proposed raw cutoff there is also a deterministic obstruction to a small first moment. **Every** draw-406 raw graph has a saturated plane of area below $266{,}710$, whereas $1893a>1{,}477{,}633$. This holds on every history passing both gates. The guaranteed plane need not lie in the retained space, so the result concerns the proposed raw-plane count and leaves the probability of a terminal hit open.

## Which index measures the area ratio?

Let $L$ be the draw-406 raw lattice, $F$ the frozen span, $E=F^\perp$, and $T\subset E$ the rational span of a terminal hit. Write $A_P=\det P$ and
$$
 B=L\cap T,\qquad P=(\pi_E L)\cap T,\qquad C=\pi_T L .
$$
The inclusions $B\subseteq P\subseteq C$ give
$$
 \frac{\det B}{A_P}=[P:B]
    =\frac{[C:B]}{[C:P]}.
$$
Part 205 gives $[C:B]\ge1893$. Deducing the same lower bound on $[P:B]$ from it alone would require controlling the denominator. The dual gate gives a **lower** bound $[C:P]\ge A_PR^2/\gamma_2$. The raw minimum gives $\det B>250^2/\gamma_2$, hence $[P:B]>250^2/(\gamma_2 A_P)$. At $A_P\le a=1352/\sqrt3$ this yields $[P:B]\ge70$. For an illustration of the gap using only plane data, take $B=270\mathbb Z^2$, $P=27\mathbb Z^2$, $C=(9/2)\mathbb Z^2$. Then $\lambda_1(B)=270$, $\lambda_1(C^*)=2/9>R_0(406)$, and $A_P=729<a$. The two factors are 100 and 36, with product 3,600. This example tests the inference from the plane inequalities alone. Its reachability under the selector is unspecified. [Part 205 and audit](wall1_doubly_gated.md#audit)

The quotient has a direct interpretation. Projection $\pi_E$ maps $L\cap(F\oplus T)$ onto $P$, with kernel $L\cap F$. The preimage of $B$ is $(L\cap F)\oplus B$, by subtracting the raw representative in $B$. Consequently
$$
 P/B \simeq
 \frac{L\cap(F\oplus T)}{(L\cap F)\oplus (L\cap T)} .
$$
Projection fixes every vector of $B$. The extra points in $P$ come from raw lifts with a frozen component. In particular the area ratio counts cosets, and a bound on it assigns no probability to the choice of $F$. The Lean covolume update divides the *whole* retained covolume by the winning length at a vertical step. A plane-specific update by that factor does not follow. [ProjectedCovolume.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/ProjectedCovolume.lean)

## A moderate raw plane exists for every matrix

For a rank-$d$ Euclidean lattice of covolume $D$, $d\ge2$, let $\lambda_i$ be its successive minima and $V_d$ the Euclidean unit ball volume. Take independent vectors realizing $\lambda_1,\lambda_2$. Their parallelogram has area at most $\lambda_1\lambda_2$, and saturation in their span can only reduce the area. Ordering the minima and applying Minkowski's second theorem gives
$$
 \min_{\dim S=2,\;S\ {\rm rational}}\det(L\cap S)
 \ \le\ \lambda_1\lambda_2
 \ \le\ \left(\prod_{i=1}^d\lambda_i\right)^{2/d}
 \ \le\ 4(D/V_d)^{2/d}.
$$
The middle inequality holds because every $\lambda_i$ for $i\ge3$ is at least $\sqrt{\lambda_1\lambda_2}$. [Minkowski's second theorem, Theorem 7.9.4](https://ocw.mit.edu/courses/18-225-graph-theory-and-additive-combinatorics-fall-2023/mit18_225_f23_lec22-25.pdf)

Here $d=400+511=911$ and $D=3329^{400}$ for every $A$, since the parity map $(x,y)\mapsto x-Ay\bmod q$ is onto. The resulting upper bound $M$ satisfies
$$
 266709.8799<M<266709.8800,\qquad
 M/(1893a)<0.181 .
$$
Thus for **every multiplier $c\ge0.181$** the raw count at $X=c\,1893a$ is at least one pointwise. Its expectation is at least one under any law on these matrices, including conditioning on a positive-probability pair of gates. This rules out paying for all moderate raw sections by a small probability at $c=1$, even with a perfect raw counting formula. It gives no lower bound on the count of planes that also satisfy the winner and terminal tests.

For reproducibility, let $V(p)=2^{456}p^{455}/911!!$, $p_-=31415926535/10^{10}$, $p_+=31415926536/10^{10}$. The two bounds on $M$ follow from the exact rational comparisons
$$
 (266709.8799)^{911} V(p_+)^2
 <4^{911}3329^{800}<
 (266709.8800)^{911} V(p_-)^2 .
$$
Squaring gives $1477633<1893a<1477634$.

## The raw first moment above the modulus

There is an exact extension of Part 197's raw count, even though it cannot give the proposed small upper bound. For a primitive integer two-space $S$, write $h=\det(S\cap\mathbb Z^{911})$, and reduce a basis of its integer section modulo $q$ in blocks $(B_0;Y)$. Set $s=\operatorname{rank}Y$. The graph section has area $h q^r$, where $r=\operatorname{rank}(B_0-AY)$. For $0<X<q^2$ the expected raw count is
$$
 \sum_{S:\,h\le X}\Pr_S(r=0)
 \;+\;\sum_{S:\,qh\le X}\Pr_S(r=1).
$$
Each sum counts rational spans once. The restriction excludes rank two because $h\ge1$ by the integer minors. For a *fixed* $S$ the probabilities under uniform $A$ are

| Input rank $s$ | $\Pr_S(r=0)$ | $\Pr_S(r=1)$ |
|---:|---:|---:|
| 0 | 0 | 0 |
| 1 | 0 | $q^{-399}$ |
| 2 | $q^{-800}$ | $(q^{400}-1)(q+1)q^{-800}$ |

Indeed the stacked basis has rank two modulo $q$ by primitivity. At $s=0$ the horizontal images are independent. At $s=1$ the kernel direction has a fixed nonzero horizontal image, and the complementary column is uniform in $\mathbb F_q^{400}$. It lies on the fixed line with probability $q/q^{400}$. At $s=2$ both columns are independent uniform draws. There are $(q^{400}-1)(q+1)$ rank-one matrices, obtained by choosing an image line and a nonzero pair of coefficients. These fixed-space probabilities are taken before selection. At Part 197's $X=676\sqrt2<q$, the second sum is empty. At $X=1893a$, it includes integer sections through $h\le X/q\approx443.87$. As a finite check, enumeration with three horizontal rows modulo three gives rank-$(0,1,2)$ counts $(0,0,1)$, $(0,3,24)$, and $(1,104,624)$ for the three rows of the table after fixing the kernel columns. [Part 197, raw configurations](wall1_enlarged_cutoff.md#raw-configurations-and-membership-conditioning)

## What remains in the two residuals

For an actual hit, a split at any $X>0$ is valid. If its corresponding $B$ has $\det B>X$, then $[P:B]>X/a$. In particular the threshold 1,893 is valid **on the branch $\det B>1893a$**. On the other branch, dropping the requirement that $B$ belongs to a terminal hit leaves an event of probability one. On the large-index branch the numerical size of the index gives no bound on the mass of histories selecting its frozen span. The Haar plane mean integrates over Haar shape, and Part 202's survival fraction counts fresh mark tuples for a prescribed old flag. Neither is a law for this section index conditional on the winners. [RankTwoPlaneMean.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/RankTwoPlaneMean.lean) · [Part 202](wall1_joint_exclusion_scale.md)

The vertical residual retains the first-hit, height, length and terminal tests on draws 396–406. Its $6.485\cdot10^{-11}$ ceiling remains open. For the horizontal bound, $p_{\rm old}$ includes draws 155–171. Charging those draws by the audited original-cutoff prefix bound $5.055\cdot10^{-12}$ leaves a sufficient budget of $7.1275\cdot10^{-11}$ for wholly old first hits on 172–406 together with the mixed remainder on 403–406. The index and raw count above give no new charge on either late class. [Vertical residual](wall1_z2_vertical.md#audit) · [Horizontal residual](wall1_z1_horizontal.md#audit) · [Wholly old hits](wall1_z1_old_planes.md#audit) · [Prefix bound](wall1_flag_horizon.md#audit)

## Audit

**Verdict — SOUND.** The factorization, deterministic obstruction, fixed-space first moment and residual accounting all check.

**Indices.** For a lift of a vector in $P$, projecting onto $T$ gives that vector again. This proves $P\subseteq C$, while projection fixes $B$. Multiplicativity gives $[C:B]=[C:P][P:B]$. The draw-406 Hermite product threshold $3(250R_0(406))^2/4$ lies in $(1892.08542070,1892.08542071)$. For the area ratio alone the raw gate gives $[P:B]>250^2/(\gamma_2 a)=46875/676$, strictly between 69 and 70. Thus 1,893 bounds the product and 70 bounds the area ratio from below. In the displayed square-lattice example $[C:P]=36$ and $[P:B]=100$. On the branch $\det B>1893a$ the strict inequality actually gives $[P:B]\ge1894$. [Part 205 audit](wall1_doubly_gated.md#audit)

**Universal raw plane.** Surjectivity of the parity map fixes $D=q^{400}$ for every matrix. Saturating the two independent minimum vectors divides their area by a positive integer. Applying the upper half of Minkowski's second theorem to the Euclidean unit ball therefore gives the stated $M$. An independent 85-decimal-digit outward interval calculation, using $V_1=2$ and $V_j=2\pi V_{j-2}/j$, gave
$$
266709.87998686<M<266709.87998688,\qquad
1477633.32854669<1893a<1477633.32854671.
$$
Both displayed rational power comparisons in the note also passed exactly. The ratio $M/(1893a)$ lies in $(0.18049801,0.18049802)$. The probability-one conclusion applies at $X=1893a$, and more generally at $X\ge M$. The guaranteed plane can depend on the matrix and has no prescribed incidence with $E$. [Minkowski's second theorem, Theorem 7.9.4](https://ocw.mit.edu/courses/18-225-graph-theory-and-additive-combinatorics-fall-2023/mit18_225_f23_lec22-25.pdf#page=21)

**First moment.** On each primitive integer section the parity map has image of size $q^r$, so the section contributes exactly when $hq^r\le X$. For input rank one the fixed image of the kernel direction is nonzero and exactly $q$ of the $q^{400}$ possible complementary images lie on its line. For input rank two, counting a nonzero coefficient pair on each image line gives $(q^{400}-1)(q+1)$ rank-one maps. These checks reproduce the table under the unconditional matrix law, including the extra term with $h\le X/q$ and $443.86702569<(1893a)/q<443.86702571$. Enumeration over $\mathbb F_3$ reproduced all three stated rank histograms. A separate check compared the summed first moment against direct section areas in the nine graphs $x=b y_1+c y_2\pmod3$. For each primitive normal $(u,v,w)$ up to sign with length $h\le X$, the raw section area is $3h/\gcd(3u,bu+v,cu+w)$. At $X=2,3,5,8$ the totals over the nine graphs agreed exactly at $9,67,213,905$, respectively. This also checks the inclusive threshold at $X=q$. Part 197's $10^{-604}$ bound uses the smaller cutoff $676\sqrt2$. [Part 197 raw configurations](wall1_enlarged_cutoff.md#raw-configurations-and-membership-conditioning)

**Residuals.** The wholly old events with first hit on draws 155–171 are disjoint by first-hit time and their union lies in the audited prefix event. Charging that event once leaves $7.6330\cdot10^{-11}-5.055\cdot10^{-12}=7.1275\cdot10^{-11}$ for the wholly old events on 172–406 and the remaining mixed events on 403–406 together. The horizontal terms retain the good event, terminal hit and fresh-shortest exclusion. The vertical remainder retains the good event and terminal hit, a first hit on 396–406, height $1\le k\le12$ and winning length $\max(30.5,0.945g)<s\le2^{1/4}\sqrt a$. Its $6.485\cdot10^{-11}$ allowance is separate. Both late estimates still require the probability of the selected histories. [Prefix audit](wall1_flag_horizon.md#audit) · [Horizontal residual](wall1_z1_horizontal.md) · [Vertical audit](wall1_z2_vertical.md#audit)
