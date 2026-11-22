# Integer aliases and the width-506 terminal block

At oracle rank 506 the horizontal rank is 505. The recorded GSA determinant and terminal GS lengths alone cannot certify 1% failure. There is a physical graph lattice of exactly the recorded ambient determinant with **every terminal length within 0.75% of GSA**, on which height zero fails with probability greater than 99.60%. At the recorded Gaussian test scale, even the height-two majorant exceeds $10^7$ on this block. Its exact integer aliases have negligible weight.

There is a stronger conclusion if the terminal head is independently known to be shortest. At the GSA head length this settles heights zero and one on the usual norm cap. The cap costs less than $0.000479$, and the additional height-one charge is less than $6.5\cdot10^{-14}$. The remaining question on such a block is the mass of **nonintegral** dual classes at heights 2 through 30, or the corresponding finite-group ball probabilities. No 1% conclusion for a reducer-selected GSA block follows here.

## Fixed block and exact aliases

Use secret-first coordinates, $N=1023$, $r=511$, $n=512$, and $q=3329$. Write $F=[A\ I_r]$ over $\mathbb F_q$ and $L=\{z\in\mathbb Z^N:Fz=0\bmod q\}$. The identity block makes $F$ onto, so $\det L=q^r$. Fix an ordered basis of $L$ chosen independently of the CBD plant conditional on the design. Let $W$ be its prefix span, $E=W^\perp$, $P$ orthogonal projection onto $E$, $d=\dim E$, $H=PL$, $J=P\mathbb Z^N$, and $T=E\cap\mathbb Z^N$. In this note $\det$ denotes Euclidean covolume in the span. Write $y=PX$, $Z=\|y\|^2$ for the plant image and its energy. The projected vectors are $(h+ky,k)$. This follows by subtracting $k(X,1)$ before projecting. A tie with the origin excluded and outside the signed plant pair counts as failure. [Physical graph and projection](../../SigabaNeo/Lib/Lattices/Research/Wall1/AttackLattice.lean) · [All-heights criterion](../../SigabaNeo/Lib/Lattices/Research/Wall1/UniquenessCriterion.lean)

**Proposition 1.** Put $\overline T=T\bmod q$ and $\mathcal C=\overline T\cap\operatorname{row}(F)$, with row vectors identified with coordinate columns. Then
$$
 J^*=T,\qquad H^*=\{u/q:u\in T,\ u\bmod q\in\mathcal C\},\qquad
 H^*/T\simeq\mathcal C .
$$
At every tested height, including all heights up to the support limit $\lfloor\sqrt{1+9N}\rfloor=95$, the exact aliases $\{w\in H^*:kw\in\mathbb Z^N\}$ are precisely $T$ for $1\le k\le95$.

*Proof.* The prefix is integral, hence $P$ is rational (use its Gram matrix) and $J$ is discrete and spans $E$. We have $qJ\subset H\subset J$. For $w\in E$, pairing against a projected vector equals pairing against its original vector. This gives $J^*=T$ and $H^*=E\cap L^*$. As $q\mathbb Z^N\subset L$, write $w=u/q$ with $u$ integral. Pairing integrally with $L$ now says exactly that $u\bmod q$ annihilates $\ker F$, i.e. belongs to $\operatorname{row}(F)$. The map $w\mapsto qw\bmod q$ is onto $\mathcal C$ by its definition and has kernel $T$. Since $q$ is prime, $ku=0\bmod q$ implies $u=0\bmod q$ for every indicated $k$. Finally $T\subset H^*$ consists entirely of aliases. ∎

Set $a=1.9d$, $B=1+a$, $t=d/(2B)$, $\alpha=\pi^2/t$, $K=\lfloor\sqrt B\rfloor$. With $d=505$ we have $B=960.5$ and $K=30$. Define
$$
 b_k=\frac{e^{t(B-k^2)}(\pi/t)^{d/2}}{\det H},\qquad
 F_k=\sum_{w\in H^*} e^{-\alpha\|w\|^2}\prod_j\cos^6(\pi k w_j).
$$
Each CBD(3) entry is a sum of six fair independent half-signs, so the product is the characteristic function at $kw$. On $Z\le a$ a collision at height $k\ge2$ puts a point of $H+ky$ in the closed ball of squared radius $B-k^2$. Its indicator is majorized by the sum of $e^{t(B-k^2-\|h+ky\|^2)}$ over $h\in H$. Periodizing the Gaussian gives Fourier coefficient $(\pi/t)^{d/2} e^{-\alpha\|w\|^2}/\det H$ by integration over $E$. Taking expectation over the original CBD law in the absolutely convergent series gives the upper charge $b_kF_k$. This calculation allows dependence between $Z$ and $ky$. [Gaussian Fourier transform and Poisson formula, Lemma 2.8](https://cims.nyu.edu/~regev/papers/average.pdf) · [Earlier cap and Poisson bound](wall1_smoothing_uniqueness.md)

Choose $d$ ambient coordinate positions whose restriction to $E$ is injective, using a nonsingular row minor of a basis. Dropping other coordinates decreases squared length and injects $T$ into $\mathbb Z^d$. With $z=e^{-\alpha}$ this proves
$$
 0\le \sum_{0\ne w\in T}e^{-\alpha\|w\|^2}
 \le \left(1+\frac{2z}{1-z}\right)^d-1 < 5.005\cdot10^{-14}.
$$
Here the geometric bound uses $m^2\ge m$ for $m\ge1$. At the model determinant the sum of the $b_k$ is below $4.463\cdot10^{-125}$, so **all nonzero exact aliases combined** cost less than $2.24\cdot10^{-138}$ across all higher heights. This sharpens the ambient-dimension estimate in the earlier finite near-alias test. [Finite near-alias test](wall1_theta_heights.md)

## Which finite data are missing?

For each $c\in\mathcal C$ choose $u_c\in T$ lifting $c$. If $[c]$ denotes the coordinatewise centered residue, put $D(c)=\|[c]/q\|^2$. Grouping the positive Gaussian series by Proposition 1 gives the identity
$$
 F_k=\sum_{c\in\mathcal C}
 \prod_j\cos^6(\pi k[c]_j/q)
 \sum_{v\in T}e^{-\alpha\|v+u_c/q\|^2}.
 \tag{1}
$$
In particular a single finite sum gives an upper bound. For $0<\beta<\alpha$ let $\theta(\beta)=\sum_{m\in\mathbb Z}e^{-\beta m^2}$. Then
$$
 F_k\le \theta(\beta)^d\sum_{c\in\mathcal C}
 e^{-(\alpha-\beta)D(c)-3\pi^2 D(kc)}.                 \tag{2}
$$
Indeed every lift in the inner sum of (1) has squared length at least $D(c)$. On the remaining Gaussian with coefficient $\beta$ use the same coordinate injection into a translate of $\mathbb Z^d$. Its shifted Gaussian sum is at most the centered one, since its Fourier coefficients are nonnegative and each phase has modulus one. Finally $\log\cos(\pi x)\le-\pi^2 x^2/2$ for $|x|<1/2$ by integrating $\tan u\ge u$ for positive $u$ and using evenness. Applying this after centering $kc$ proves (2). Centering can move a lift outside $E$. The centered integer vector still satisfies the ambient row-code congruence. Thus an ambient dual floor can exclude a ball of residues, while a floor on the retained section alone need not survive centering. Either use requires a multiplicity estimate to control the sum.

A primal version also retains the dependence on plant energy. Set $S=W\cap\mathbb Z^N$ and $G=\mathbb F_q^r/F(S)$, using residues for $F(S)$. The map $Pz\mapsto Fz+F(S)$ is well defined and onto, with kernel $H$. Indeed, two lifts of $Pz$ differ by a vector in $S$, and a zero class means that one can subtract a vector in $S$ to obtain a lift in $L$. Thus $J/H\simeq G$. For a class $g$, let $\delta(g)$ be the least squared length of its points in $J$. For $k\ge2$ the **actual** height-$k$ failure probability equals
$$
 \sum_{g\in G}\Pr\big(FX+F(S)=g,\ Z\ge k^2-1+\delta(kg)\big).
 \tag{3}
$$
Every point of class $kg$ equals $h+ky$ for one $h\in H$. Minimizing proves (3), including ties. For a first-moment bound at fixed radius one can instead weight the number of points in class $kg$ by the marginal probability of $g$. In either formula each projected point has a whole fiber of lifts differing by $S$ and must be counted once.

All these data are determined by the actual graph matrix and integer prefix. An integer kernel basis for the transpose of the prefix gives $T$; reduction modulo $q$ and finite-field intersection give $\mathcal C$. A basis of the saturated prefix span gives $S$ (a Smith normal form suffices). The projection matrix has rational entries, so energy and squared-distance comparisons in (3) have exact rational meaning. To check a distance up to any required radius, enumerate $J$ in that closed ball using a rational basis obtained from the projected standard generators. The positive definite Gram form bounds each basis coefficient, making the enumeration finite. The plant probabilities are finite sums of the integer weights $\prod_j\binom6{3+X_j}$ divided by $64^N$. This establishes checkability without assuming feasibility at rank 505.

## If the GSA head is shortest

With $b=506$, index the terminal GS lengths by $j=0,\ldots,d-1$. The full-row model gives
$$
 s=\frac{\log(b/(2\pi e))+\log(\pi b)/b}{2(b-1)},\qquad
 g_j=q^{511/N}\exp((2d-N-1-2j)s).
$$
Their geometric mean is $G_0=q^{511/N}\exp((d-N)s)\in(10.03252,10.03253)$ and $g_0\in(54.82115,54.82116)$. The full sequence has product $q^{511}$. An arbitrary terminal head gives an **upper** bound on $\lambda_1(H)$ because it is itself a lattice vector. The next estimate requires a **lower** bound $L=54.82$; an exact shortest head of the model length would supply it. [Recorded GSA convention](wall1_null_terminal.md)

**Proposition 2.** For any physical block of rank 505 with $\lambda_1(H)\ge54.82$, on $Z\le a$ there is no height-zero failure, and the unconditional probability of a height-one failure *and* $Z\le a$ is less than $6.5\cdot10^{-14}$.

*Proof.* We have $L^2>B$. A height-one collision implies $-\langle h,X\rangle\ge\|h\|^2/2$ for some nonzero $h\in H$ of length at most $2\sqrt a$. Since $\cosh(u/2)^6\le e^{3u^2/4}$, exponential Markov (at multiplier $1/3$) bounds this one-vector probability by $e^{-\|h\|^2/12}$. It remains to count vectors in two shells. [CBDTail, half-energy bound](../../SigabaNeo/Lib/Lattices/Research/Wall1/CBDTail.lean)

Any $L$-separated set in a closed $d$-ball of radius $r\ge L$ has size at most
$$
 N(r)=2(d+1)^2(\sqrt2\,r/L)^d .
$$
Lift a point $v$ to $(v,\sqrt{r^2-\|v\|^2})/r$ on $S^d$. Lifted distances are at least $L/r$. Put $s_0=L/(\sqrt2\,r)$. In an open cap of angular radius $\arcsin s_0$ the components perpendicular to the cap axis have pairwise strictly negative inner products: the full inner products are at most $1-s_0^2$, and the axial products exceed $1-s_0^2$. There are at most $d+1$ such components in $\mathbb R^d$. Otherwise an affine dependence gives two disjoint nonempty positive sums equal to one another (move negative coefficients across), with strictly negative inner product, a contradiction. A cap occupies at least $s_0^d/(2(d+1))$ of the sphere: project it onto its equatorial $d$-ball of radius $s_0$, whose volume is at most the cap area, and bound the sphere area $(d+1)V_{d+1}\le 2(d+1)V_d$ by slicing the unit ball. Here $V_i$ is unit $i$-ball volume. Averaging the cap occupancy over its axis proves the count. Applying it first at radius 58 and then at $2\sqrt a$ bounds the charge by
$$
 N(58)e^{-L^2/12}+N(2\sqrt a)e^{-58^2/12}<6.5\cdot10^{-14}.
$$
∎

The cap exception is $p_a\le e^{-d(v-1-\log v)/2}<0.000479$, $v=2a/(3d)$. For $0<u<1/3$, average the linear CBD moment bound against an independent standard Gaussian in $E$ at multiplier $\sqrt{2u}$. This gives $\mathbb Ee^{uZ}\le(1-3u)^{-d/2}$. Use exponential Markov at $u=(1-1/v)/3$. With $\det H=G_0^d$, $\sum_{k=2}^{30}b_k\in(4.4627,4.4628)\cdot10^{-125}$. For instance, **if** the lower bound on $\lambda_1(H)$ and $F_k\le 2.13\cdot10^{122}$ at all 29 heights both hold at this determinant, the total charge is below $0.01$. The ceiling is a sufficient numerical comparison. For an actual terminal determinant use its own $b_k$.

## A physical obstruction with a near-GSA terminal profile

Here is a fixed plant-independent basis at the exact dimensions and ambient determinant. For each of the first 505 disjoint secret/error pairs $(x_i,e_i)$ put $m_i=\lfloor q/g_i+1/2\rfloor$ (index the pairs from zero). Take $e_i-m_i x_i=0\bmod q$. On the six remaining rows use $e_i=0\bmod q$. There are seven remaining free secret coordinates. Take the 505 vectors $(1,m_i)$ in their own pairs and all 13 unused coordinate basis vectors of $L$ (seven units and six $q$-scaled units) as prefix. Complete by $(0,q)$ in each pair in model order. Each pair basis has determinant $q$ and generates precisely its congruence kernel. The prefix has size 518 and the full determinant is exactly $q^{511}$.

In pair $i$ the surviving line has unit direction $(-m_i,1)/\sqrt{1+m_i^2}$, and the projected spacing is $\ell_i=q/\sqrt{1+m_i^2}$. The lines are orthogonal, so these spacings are also the ordered terminal GS lengths. Interval evaluation gives
$$
 0.99252 < \ell_i/g_i < 1.00695,\qquad
 10.03263 < (\det H)^{1/505} < 10.03264 .
$$
The last spacing, with $m_{504}=1813$, is below $1.837$. On this independent pair, $|X_{\rm sec}|\ge1$ forces $2|-m_{504}X_{\rm sec}+X_{\rm err}|\ge 2(1813-3)>q$, a strict height-one collision along that axis. Its probability is $44/64$. Height zero alone fails with probability greater than $0.99603$. Indeed, $\mathbb EZ=3d/2$ and $\operatorname{Var}(Z)=(9/2)d-(3/4)\sum_j P_{jj}^2\le(9/2)d$. This follows by expanding the quadratic form: each coordinate has second moment $3/2$, fourth moment $6$ and fourth cumulant $-3/4$, and $\operatorname{tr}P^2=d$. Cantelli bounds $\Pr(Z<\ell_{504}^2-1)$ by $V/(V+(3d/2+1-\ell_{504}^2)^2)$ with $V=9d/2$. [CBDQuadratic, projection variance](../../SigabaNeo/Lib/Lattices/Research/Wall1/CBDQuadratic.lean)

At height two the Gaussian charge $b_2 F_2$ already exceeds one at the specified cap and test scale. The embedded dual generators on the separate pairs are $(-m_i,1)/q$. Restrict their integer coefficients to $-4,\ldots,4$. Nonnegativity and orthogonality give the lower bound
$$
 F_2\ \ge\ \prod_i\left[1+2\sum_{j=1}^4
 e^{-\alpha j^2(1+m_i^2)/q^2}
 \cos^6(2\pi j m_i/q)\cos^6(2\pi j/q)\right].
$$
The base-ten log of this product lies in $(131.8889,131.8890)$, while $\log_{10} b_2\in(-124.47190,-124.47189)$ at the **constructed** determinant. Every term of this finite box except the origin belongs to a nonzero residue class because $4<q$. This proves $b_2F_2>10^{7.41}$ without a tail estimate. The large upper charge alone gives no lower bound on actual height-two failure. The lower bounds at heights zero and one concern actual events.

The construction tests the implication from **terminal lengths and ambient determinant**. Its head exceeds its minimum, its prefix is prescribed, and its retained dual contains a vector of length below $0.019$. It supplies no counterexample with a shortest terminal head, with the Part 172 dual gate imposed, or with a typical reduced prefix. In particular its failure probability is conditional on its design and prefix.

## Exact small check

For a check where even the intrinsic primal and dual lattices, the projected integer spacing, and the finite index agree, take $q=13$ in a single pair. Use prefixes $(a,b)=(1,8)$ and $(4,7)$ in the respective graph kernels $ae-bx=0\bmod13$. Each prefix is primitive in $\mathbb Z^2$ and in its kernel. Both have $a^2+b^2=65$, $J=(1/\sqrt{65})\mathbb Z$, and $H=(13/\sqrt{65})\mathbb Z$ in the unit line coordinate. Bézout gives every integer value of $l=-bx+ae$, so the kernel gives precisely the multiples of 13. Write $z=[2l]\bmod13$ centered in $[-6,6]$. Enumerating the 49 CBD pairs gives the following numerators over the common denominator 4096.

| Prefix | Class zero | Fixed ball $\lvert z\rvert\le1$ | Actual height two, $z^2+4\cdot65\le l^2+65$ |
|---|---:|---:|---:|
| $(1,8)$ | 424 | 1066 | 812 |
| $(4,7)$ | 424 | 1128 | 588 |

Thus even an exact intrinsic dual theta series and index leave different actual height-two probabilities. The last column keeps the radius coupled to the same plant, as in (3).

**Numerical verification.** The displayed decimal enclosures were checked with 80-decimal `mpmath.iv` intervals, taking $a=19d/10$ exactly. For each of the 505 pairs, the interval for $q/g_i+1/2$ lay strictly between the candidate integer $m_i$ and $m_i+1$. The physical determinant was evaluated by summing $\log\ell_i$, and the box estimate by summing the logs of its 505 positive finite factors. The interval for the combined conditional charge used $p_a$ plus the two shell bounds plus $2.13\cdot10^{122}\sum b_k$. The small check used integer arithmetic: for each pair $x,e=-3,\ldots,3$ take weight $\binom6{3+x}\binom6{3+e}$, center $2(-bx+ae)$ modulo 13, and sum the weights passing each column's test.

## Scope of the conclusion

Part 39 averages a prescribed coordinate projection over designs. Part 101 gives design-probability bounds for minimum certificates, and Part 103 distinguishes a necessary height-zero floor from a sufficient conditional guarantee. Part 147 concerns selected-line and plane multiplicities in a restart. Part 171 and the Lean profile obstruction rule out a particular coordinatewise theta-product acceptance test. Parts 172–174 address dual exits, gated theta weights and selection laws; none supplies the distribution of the joint residues in (1) on this final CBD block. A dual floor restricts the admissible classes but does not supply their Gaussian weights or multiplicities. [Part summaries](../PROOF_GAP.md) · [Lean profile bound](../../SigabaNeo/Lib/Lattices/Research/Wall1/UniquenessProfile.lean) · [Lean profile obstruction](../../SigabaNeo/Lib/Lattices/Research/Wall1/ProfileObstruction.lean)

A physical GSA-like block with verified per-block error at most 1% remains open. On a block with a verified $54.82$ minimum, the unresolved conditional estimate in this test is the higher-height sum. Establishing how often a particular reducer supplies such blocks would additionally require its design and prefix law. The results above concern one fixed block at a time.

## Audit

**Verdict — MINOR CAVEATS.** The prescribed-prefix counterexample and the conditional bounds are sound. Two qualifications matter for the headline. The counterexample rules out a uniform 1% guarantee over the stated 0.75% profile tolerance. The minimum hypothesis in Proposition 2 is close to one horizontal Gaussian-heuristic radius at the full-row model determinant. Its frequency under a width-506 reducer remains unknown.

**Physical block and quantifier.** In each active pair every null vector has the unique expansion $(x,e)=x(1,m_i)+((e-m_i x)/q)(0,q)$. Together with the seven free units and six scaled units, these pairs form an integer basis of the plain-LWE null lattice with index $q^{505+6}$. Its first 518 prescribed vectors therefore give a genuine prefix. Projecting the other 505 vectors gives the stated mutually orthogonal spacings. An independent 80-decimal interval calculation placed the extreme spacing-to-model ratios in $(0.9925251,0.9925252)$ and $(1.0069448,1.0069449)$. On the last axis Part 94 counts a height-zero failure whenever $Z+1\ge\ell_{504}^2$, including a tie. Cantelli gives probability greater than $0.99603050$ over the plant for this fixed design. This refutes a certificate that accepts every physical block in that tolerance band solely on its terminal lengths and ambient determinant. Exact equality to all model lengths, exact terminal covolume, and occurrence under a reduced-prefix law are stronger hypotheses. Part 138 treats block-reduction inequalities, and Part 171 treats a particular acceptance test. The construction needs neither result. [Parts 94, 138 and 171](../PROOF_GAP.md)

**Scale of the minimum.** In Euclidean length units the Gaussian-heuristic radius of the rank-505 horizontal lattice is $\mathrm{GH}(H)=(\det H/V_{505})^{1/505}$, where $V_d$ is unit-ball volume. At $\det H=G_0^{505}$ this gives $54.95252664$ rounded, so $54.82/\mathrm{GH}(H)=0.99758834$ rounded. The projected horizontal plant has RMS length $\sqrt{757.5}=27.52272$ rounded, and including height one gives $\sqrt{758.5}=27.54088$ rounded. Thus the floor is about $1.9905$ times the projected plant's RMS length and exceeds the capped radius $\sqrt{960.5}$. It is a plausible shortest-vector *scale* under the Gaussian heuristic at this determinant. Neither the GSA head nor this scale comparison proves the lower bound for an individual BKZ output or a success frequency over outputs. The $28.8095$ in the earlier first-pass analysis is a lower bound on that pass's GH radius. Part 103's $27.4538$ is a necessary height-zero minimum for its 99% target. [Part 103](wall1_width_scan.md) · [First-pass normalization](wall1_idea_drift.md) · [Part 175 audit](wall1_smoothing_uniqueness.md)

**Conditional charges.** The cap costs less than $0.000478351$ once. On the cap, $54.82^2>960.5$ excludes height zero. At height one the two shell counts at $58$ and $2\sqrt a$, weighted by their respective one-vector tails, sum to less than $6.44043\cdot10^{-14}$. This bounds the joint event of a height-one failure and the cap holding. At the model determinant the sum of $b_k$ for $2\le k\le30$ is less than $4.46272\cdot10^{-125}$. The nonzero exact-alias factor is less than $5.00438\cdot10^{-14}$, giving a charge below $2.23332\cdot10^{-138}$. The zero mode is accounted for separately. Using the proposed ceiling on each full $F_k$ gives total failure below $0.009983941$, conditional on that ceiling and the minimum. On the constructed block the finite-box and $b_2$ logarithms give $\log_{10}(b_2F_2)>7.41704$. This last inequality concerns the Gaussian majorant alone.

**Remaining evidence.** At the recorded determinant and with the minimum certified, the unresolved contribution is the weighted sum of the nonzero residue classes in (1) over heights 2–30. The actual design matrix and integer prefix determine $T$ and $\mathcal C$. The finite upper test (2) then uses each class's centered squared lengths $D(c),D(kc)$ with their joint multiplicities. The exact primal test (3) instead needs the class distances and the joint class/energy probabilities, with rational projected distances and ties retained. Independent enumeration of all 4096 equally likely sign assignments in each small example gave $(424,1066,812)$ and $(424,1128,588)$ in table order. All displayed numerical enclosures and the 505 rounding decisions were checked in scratch space. Parts 172–174 supply no such class count, and Part 176's inverse description still needs the prefix multiplicities to obtain a reducer probability. [Parts 172–176](../PROOF_GAP.md)
