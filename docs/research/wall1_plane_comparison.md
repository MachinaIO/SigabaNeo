# What a two-vector comparison must count at radius 26

In the width-506 marginal restart, two reachable histories give the **same embedded candidate plane, the same reduced Gram matrix and opposite answers to the radius-26 event**. This occurs even when membership of the two raw vectors pins the final two columns. The missing probability is the frequency with which the compatible prefixes select that plane and its first line. A rank-two Haar incidence formula supplies a reference count for the planes. It supplies no measure on those prefixes.

There is a simpler sufficient comparison. One can discard the shape and shortest-line tests and count saturated planes up to one area cutoff in the selected rank-505 lattice. On the Haar side this costs a factor between 76,627 and 76,628. It leaves a multiplicative budget of about $3329^{14.39932}$ for a direct good-event bound. The finite area count is open, as is R58's equation (5). [R58](wall1_rank2_transverse.md) · [Parts 183–189](../PROOF_GAP.md)

## The distinction between a plane test and a selected-plane test

Put $r=26$, $q=3329$, $V=\mathbb F_q^{400}$ and $Q=|V|$. The restart has 105 initial graph columns and 406 appends. In its retained rank-505 lattice $M$, let $x$ be the designated signed shortest vector and $E=\{\lambda_1(\pi_{x^\perp}M)\le r\}$. For a saturated plane lattice $P\subset M$ put $s=\lambda_1(P)$, $a=\det P$ and $h=a/s$. The image of $P$ modulo any one of its shortest lines has spacing $h$. If $P$ contains $x$, then $h\le r$ witnesses $E$. Conversely a shortest quotient point on $E$ is primitive and its line lifts to a saturated plane containing $x$. Reducing a second generator along the first gives $s^2\le h^2+s^2/4$. Thus every witness has $s\le T=2r/\sqrt3$ and $a\le a_*=rT$.

A useful partial converse holds for every parent, including ties. If a plane has both $s\le r$ and $h\le r$, then $E$ holds regardless of which shortest line is designated. If $x$ lies outside the plane, any shortest vector of the plane survives projection at length at most $s$. If $x$ lies inside, the spacing is $h$. Consequently a parent with a qualifying plane but no hit must have $s>r$ on **every** plane with $h\le r$. The following example realizes this distinction in the chain. [Part 108](wall1_first_tour.md) · [Part 184](wall1_penultimate_projection.md)

## Same projected pair, opposite outcomes

Use the graph sign $b+Ac=0\bmod q$. Take two of the 105 initial columns to be zero. Put the other 103 on separate horizontal axes $e_3,\ldots,e_{105}$, with coefficient 40 on each except that the coefficient on $e_3$ is $d$. Compare $d=40$ and $d=25$. Take the first 404 appends to be zero and the last two columns to be $27e_1$ and $13e_1+24e_2$, in that order. The fixed raw vectors $z_1,z_2$ are the negative of these horizontal columns paired with input units 510 and 511 respectively. Their membership fixes exactly those two columns and leaves all 509 earlier columns free.

Every one of the 406 projections removes a zero-column input axis. Indeed each zero column splits off an orthogonal unit direction. The remaining integral graph has no unit vector because its columns are nonzero and horizontal periods have length $q$. During the 404 zero appends two unit axes remain after each selection. The final two appends consume them. The prescribed signed tie order can change which unit goes first without changing the resulting projection. Both outputs have $D=Q$ by the index of the remaining graph, and their mark groups have order $Q$ since the horizontal intersection is $q\mathbb Z^{400}$.

The embedded pair survives unchanged in both outputs. It generates a saturated plane, since its last two input coordinates form the identity and determine its real coefficients. Its Gram data are
$$
 \begin{pmatrix}730&351\\351&746\end{pmatrix},\qquad
 s^2=730,\qquad h^2=746-351^2/730=421379/730<26^2 .
$$
To check the minimum even in the whole four-coordinate factor, any vector of squared norm at most 760 has input coefficients $|i|,|j|\le27$. The horizontal coordinates must be the centered residues of $-27i-13j,-24j$. These expressions already have magnitude below $q/2$. Enumeration of $(i,j)$ gives just $\pm(1,0)$ and $\pm(0,1)$ besides zero. Their squared norms are 730 and 746. Equivalently the binary form completes the square to $730(i+351j/730)^2+(421379/730)j^2$.

| Coefficient on $e_3$ | Designated shortest line | Result after projecting it off |
|---|---|---|
| $d=40$ | $\mathbb Z z_1$ | The image of $z_2$ has squared length $421379/730<676$. |
| $d=25$ | Line of the $(-25,1)$ vector on the third factor | The quotient minimum has squared length $730>676$. |

For the second row the third factor has area $q$, hence its quotient has squared spacing $q^2/626>730$. The unaffected four-coordinate factor has minimum squared 730. Each other graph factor has minimum squared 1601 and the unused axes have spacing $q$. In a single-column factor with $d=25$ or 40, any input coefficient in the closed ball of radius $\sqrt{1+d^2}$ has magnitude at most $d$, so $|di|\le1600<q/2$. This verifies the factor minima and also shows that $z_1$ wins uniquely up to sign in the first row. There the image of $z_2$ is the unique shortest quotient line. A competitor as short has a centered lift of squared length at most $421379/730+730/4<760$, covered by the enumeration.

Each design has unconditional mass $Q^{-511}$ and conditional mass $Q^{-509}$ given this pair's membership. Both have short raw vectors and are removed by Part 184's raw exit. The example distinguishes the two tests on reachable histories. It gives no lower bound on their discrepancy after that exit.

## The remaining finite probability

Let $G$ impose Part 184's raw and dual good conditions. On $E\cap G$ select the signed shortest $x$, the signed shortest point modulo its line, the centered shortest lift of that point in $M$, and the shortest raw representatives of the resulting two vectors, with the prescribed ambient tie order throughout. Denote the ordered raw pair by $Z$. For a fixed pair $z$, let $I_z$ be joint membership and $t_z$ the rank of the two input residue columns over $\mathbb F_q$. Each horizontal row of the design satisfies $t_z$ independent equations if consistent, so $\Pr(I_z)=Q^{-t_z}$ on consistent pairs. The candidate sum is finite. Reverse rounding along 406 winner directions of lengths at most $q$ gives a representative of each vector of squared norm at most $T^2+406q^2/4$. Disjointness gives
$$
 \Pr(E\cap G)=\sum_{z\ {\rm consistent}}Q^{-t_z}
                \Pr(E,G,Z=z\mid I_z).
$$
For independent final two input rows, the conditional factor is the fraction of the $Q^{509}$ unrestricted prefixes whose unique completion passes all tests. For general pivots, at each row where the suffix rank drops there is a unique column given the earlier prefix. Every other column is uniform, by equal-size fibers for the remaining linear system. With $\Pi$ the final projection off all frozen lines, the candidate Gram entries are $z_i^{\mathsf T}\Pi z_j$. The projection depends on that completed design. Even specifying these entries leaves open the competition with vectors outside the plane, as the example shows. [Part 189 and audit](wall1_canonical_pair.md#audit)

One can quantify the loss in treating reach and membership independently. A fixed framed parent with mark order $m$ imposes one coset of a kernel of size $c=Q/m$ on each of the 510 prefix columns by projecting its graph generators. Fixing the final mark imposes one more such coset. Their product has $c^{511}$ designs. Intersect it with a consistent pair's membership equations. When compatible, exactly $c^{511-t_z}$ designs remain, by extending the required linear map on the $t_z$-dimensional input span to the whole input space with values in the kernel. Hence the ratio of the intersection probability to the product of the two probabilities is $m^{t_z}$. This concerns the coset constraints. At maximal mark order they identify a single design, so for a reachable compatible branch the ratio is attained for actual reach as well. In the hit row above this factor is $Q^2=q^{800}$, far above $q^{15.78602}$. This is a branch ratio. Its size does not imply a loss of that size on the sum.

On a coprime positive-height branch Part 176 recovers the parent and mark from the full embedded quotient and oriented winner. A reachable output there has $N(S)Q/m$ raw preimages, where $N(S)$ counts prefixes reaching the recovered parent. This follows by completing each such prefix with any representative of the recovered mark. Part 188 gives $N(S)\le c^{510}$. Counting the completions that produce $Z=z$ still requires summing over compatible parents and marks. Coarsening the output to a local Gram matrix can combine branches. Neither the reach cap nor the Haar density bounds their total selected weight. The forward coset count also covers horizontal winners. [Part 176 and audit](wall1_inverse_branch.md#audit) · [Part 188 and audit](wall1_state_counting.md#audit) · [Finite-chain audit](wall1_finite_chain.md#audit)

## How much does it cost to discard the plane shape?

Let $n=505$, $V_j$ be unit ball volume, $H(D)=\Pr_{\rm Haar,D}(E)$, and $N_a(M)$ count unoriented saturated rank-two sublattices of area at most $a$. The following calculation uses a Haar **parent** at fixed determinant $D$. Count primitive unoriented lines of length $s$, then primitive unoriented lines of length $h$ in the first quotient of determinant $D/s$. Rank-one incidence twice gives the flag measure
$$
 \frac{n(n-1)V_nV_{n-1}}{4\zeta(n)\zeta(n-1)D^2}
 s^n h^{n-2}\,ds\,dh\,du,
$$
where $u\in[-1/2,1/2]$ is the centered shear. Its uniformity follows by evaluating Haar measure on the lift torus at the primitive quotient generator. Write $a=sh$ and $y=h/s$. Then $ds\,dh=da\,dy/(2y)$. Restricting to $y\ge\sqrt{1-u^2}$ makes the first line shortest in the plane by binary reduction, counting each plane once off a Haar-null boundary. Integration of $du\,dy/y^2$ on this region gives $\pi/3$. With $C_n=(n-1)\pi V_nV_{n-1}/(24\zeta(n)\zeta(n-1))$ we obtain
$$
 U(D):=\mathbb E_{\rm Haar,D}N_{a_*}=C_n a_*^n/D^2 .
$$
Imposing $h^2=ay\le r^2$ before integration gives the mean count $K(D)$ of qualifying planes,
$$
 K(D)=\frac{C_n r^{2n}}{D^2}\frac{3}{\pi(n+1)}
          \int_{-1/2}^{1/2}(1-u^2)^{-(n+1)/2}\,du .
$$
This recovers R58's upper bound $H(D)\le K(D)$ independently from flags. [Part 105 marked law](wall1_selection_law.md) · [Kim, mean value formula for primitive sublattices](https://arxiv.org/pdf/2005.10874)

For the lower bound, after the second primitive incidence the outer quotient has Haar shape at determinant $D/a$, independently of the two lengths and the first lift shear. This follows by applying the rank-one transverse product law in the first quotient, with the first shear still independent. Its chance of a primitive line of length at most $T$ is bounded by $\delta(D)=V_{n-2}T^{n-2}a_*/(2\zeta(n-2)D)$ by first moment. When the outer minimum exceeds $T$, every outside vector has length greater than $T$ even after projecting off the shortest line in the plane. The first line then wins, and all quotient witnesses of length at most $r$ lift into that same plane. Such planes are counted at most once per parent outside the null tie set. Therefore $(1-\delta(D))K(D)\le H(D)$ on the determinant range used here. [R58, Theorem 2](wall1_rank2_transverse.md)

With $D_*=\exp L_{406}$ from Part 186, outward interval calculations give the following bounds. Put $b_G=3.9999566953\cdot10^{-7}$, the sufficient good-event budget after the two exits. [Part 186 audit](wall1_quotient_slack.md#audit) · [Part 187 audit](wall1_local_comparison.md#audit)

| Quantity | Enclosure |
|---|---:|
| $H(D_*)$ | $(9.97119357603,9.97119357604)\,10^{-63}$ |
| $U(D_*)$ | $(7.64065581288,7.64065581290)\,10^{-58}$ |
| $U(D)/K(D)$, independent of $D$ | $(76627.29395,76627.29397)$ |
| $\log_q(b_G/K(D_*))$ | $(15.78601776,15.78601777)$ |
| $\log_q(b_G/U(D_*))$ | $(14.39932033,14.39932034)$ |

In particular $q^{15.8}K(D_*)>4.48027\cdot10^{-7}$, so rounding the exponent to 15.8 spends more than the budget. At exponent 15 the floor charge is below $6.81482\cdot10^{-10}$. The remaining sufficient additive allowance in R58 (5) after both exits exceeds $3.99314\cdot10^{-7}$ at that exponent. The floor bounds the determinant-matched reference from above. Replacing its average by the floor upper bound on the right would weaken the comparison.

**A sufficient scalar estimate.** Pathwise, $\mathbf1_{E\cap G}\le\mathbf1_G N_{a_*}(M)$. For a direct bound it suffices to show $\mathbb E_{\rm chain}[\mathbf1_G N_{a_*}(M)]\le q^{14.39932}U(D_*)$. For R58 (5) itself with exponent 15 and zero additive allowance, the stronger determinant-matched condition
$$
 \mathbb E_{\rm chain}[\mathbf1_G N_{a_*}(M)]
           \le q^{13.61330}\,\mathbb E_D U(D)
$$
suffices. Indeed $U(D)/H(D)\le (U/K)/(1-\delta(D_*))$ uniformly for $D\ge D_*$, with $\delta(D_*)<2.348\cdot10^{-13}$. The base-$q$ logarithm of this factor is below $1.386698$. In either sufficient condition the finite left side can be decreased to $\Pr_{\rm chain}(G, N_{a_*}\ge1)$, since each good hit has at least one qualifying plane. This avoids charging a rare parent once for every small plane it contains. The probability of that single area event under the selected finite law is also unknown. **Open conjecture.** R58 (5) holds at exponent 15 with an additive allowance small enough to meet $b_G$. Neither a pointwise Gram test nor the exact membership factor establishes this average. The draw-407 transfer has a separate error and is outside this comparison.

The numerical check used 85-decimal-digit interval arithmetic in scratch. It iterated $L_0=400\log q$, $L_i=\max(L_{i-1}-\log q,505L_{i-1}/506-\tfrac12\log56.2142)$ with disjoint alternatives on all 406 steps, used $V_j=2\pi V_{j-2}/j$ with $V_0=1,V_1=2$, and enclosed $\zeta(j)$ between 1 and $1+2^{-j}(1+2/(j-1))$. Substituting $u=\tanh v$ expressed the integral in $K$ as $2\int_0^{(\log3)/2}\cosh^{504}v\,dv$, evaluated by the finite binomial expansion. The four-coordinate disk and the two single-column minima in the example were checked separately with integer arithmetic and rational squared spacings.

## Audit

**Verdict — SOUND.** The two histories give opposite answers for the same embedded plane. The scalar area comparison would imply R58 (5) with $\eta=0$. The finite probability estimate remains open.

**Exact check of the histories.** At each draw the only unit lines are the active zero-column input axes. Removing the signed lexicographic winner leaves two such lines after draw 404, one after draw 405 and none after draw 406. The remaining graph has index $q^{400}$ in its coordinate lattice in both histories. Its horizontal kernel modulo $q$ is zero, so the mark order is also $q^{400}$. The final two input coordinates restrict to the identity on the candidate generators, proving saturation and pinning both final columns under raw membership. Each of the $Q^{509}$ prefixes has exactly one completion. Both raw graphs already contain a unit vector and hence fail the radius-250 good condition.

I enumerated every input pair with $i^2+j^2\le760$ and every horizontal representative of the two required residues within the remaining squared-norm budget. The only nonzero points were $\pm z_1,\pm z_2$, of squared lengths 730 and 746, with $\langle z_1,z_2\rangle=351$. Separate exact enumerations through $d^2+1$ gave only $\pm(-d,1)$ in each single-column factor. For $d=40$ the shortest line is $\mathbb Zz_1$. Every quotient competitor at squared length at most $421379/730$ has a centered lift of squared length below 760, so the image of $z_2$ attains the quotient minimum. For $d=25$ the outside line of squared length 626 wins. Its factor then has squared spacing $3329^2/626>730$, leaving the unchanged pair factor to attain the quotient minimum of 730. Thus the squared cutoff 676 separates the two histories. This example measures no discrepancy on $G$. The factor $Q^2$ is the joint-to-product ratio for one compatible maximal-order branch under Part 188's coset count.

**Scalar implication.** On $E$ the primitive quotient witness pulls back to a saturated plane containing the designated shortest vector. A centered lift gives $s^2\le h^2+s^2/4$ even at a tie, so $sh\le2r^2/\sqrt3$. Thus $\Pr(E\cap G)\le\Pr(G,N_{a_*}\ge1)$. On the Haar side $U/K$ compares two mean counts. The lower bound $H(D)\ge(1-\delta(D_*))K(D)$ converts that ratio to a uniform bound for $U(D)/H(D)$ before averaging over the actual determinant marginal. This uses the pre-draw-407 event of Parts 183–190.

**Independent arithmetic and rounding.** Using 105-decimal-digit outward intervals and factorial ball volumes, I obtained 20 period and 386 Hermite steps in the determinant recurrence. For the shape integral, substituting $v=2u$ on the positive half gives $\int_0^1(1-v^2/4)^{-253}\,dv$. I summed its positive binomial series through index 700. Every subsequent term ratio is below $1/2$, so the last included term bounds the omitted tail. This reproduced all five table enclosures and gave
$$
76627.29396059625<U/K<76627.29396059626,\qquad
\log_q\!\frac{U/K}{1-\delta(D_*)}<1.38669743046100.
$$
Adding $13.61330$ gives an exponent strictly below 15. The exact cutoff in both calculations is $a_*=1352/\sqrt3=780.577563944374\ldots$. Use $780.578$ only as a rounded display value. Substituting that decimal into the Haar count multiplies it by $(780.578/a_*)^{505}$ and reduces the sufficient exponent from $13.613302569539\ldots$ to $13.613267786033\ldots$ under the same bound.
