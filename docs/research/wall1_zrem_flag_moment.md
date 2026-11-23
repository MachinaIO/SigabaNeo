# Conditioning the late vertical hit on a primitive line

**Result.** Counting a line and one quotient line removes the intersecting-pair divergence. There are two different choices of first line. Using a shortest line **of each witness plane** gives an exact hit test and an eleven-draw Haar flag mean below $1.908268\cdot10^{-58}$. Using the **single designated shortest line of the retained lattice** gives a test that requires no estimate of its length distribution beyond its total mass. At the proposed radius $a/r$ this second test misses some planes. A larger ball covers them. A sharper repair uses a line test and a plane test in the same rank-504 quotient. Their combined reference sum is below $9.334050\cdot10^{-18}$, allowing a common comparison factor of $6{,}947{,}681$. These are reference means. The required comparison under the doubly gated restart is open.

Let $L=\Lambda_i$ be the retained rank-505 lattice, $D=\det L$ its **outgoing** covolume, $s$ the rank-506 window winner length, and $g$ the **incoming** window GH length. Set
$$
 a=1352/\sqrt3,\qquad \alpha=\sqrt3/2,\qquad B=\sqrt{a/\alpha}=52/\sqrt3,
 \qquad R=2^{1/4}\sqrt a.
$$
For $396\le i\le406$, write $D_i^*=\exp L_i$ for the Part 193 floor, $g_i^*=(D_{i-1}^*/V_{506})^{1/506}$, and $b_i=\alpha\max(30.5,0.945g_i^*)$. Here $V_j$ denotes unit ball volume. A residual first hit requires no earlier hit, both good gates, a vertical win with $1\le k\le12$ and $\max(30.5,0.945g)<s\le R$, and a hit at draw 406. On the specified band, rounding any nonzero quotient point's lift along the window winner gives $\lambda_1(L)\ge\alpha s>b_i$. Throughout these draws $a/b_i<B$. The notation $N_Q(t)$ counts unoriented primitive lines of length at most $t$ in $Q$. [Part 193 and audit](wall1_z2_vertical.md) · [Terminal second-moment calculation](wall1_z2_terminal_law.md)

## Two choices of first line

**Lemma 1 (exact incidence test).** On the specified band let
$$
 T_i(L)=\sum_{\ell\ {
m primitive\ line\ in}\ L,\ b_i<r=|\ell|\le B}
               N_{\pi_\ell L}(a/r).
$$
Then $A_i=\{a_2(L)\le a\}=\{T_i(L)>0\}$. Here and below $\pi_\ell$ projects off the line and $|\ell|$ denotes the primitive generator length.

*Proof.* A shortest primitive line of any qualifying plane $P$ has $r^2\le\det P/\alpha\le B^2$ by binary reduction. Saturation identifies $P/\ell$ with a primitive line in $\pi_\ell L$ of length $\det P/r$. Conversely the full preimage of a primitive quotient line within this ball is a saturated qualifying plane. This proof allows ties and multiple incidences. One may assign one shortest line per plane by a tie rule if a plane count is wanted.

**Lemma 2 (one selected line).** Let $\ell_0$ be the designated shortest line of $L$, let $r=|\ell_0|$, and put $Q=\pi_{\ell_0} L$. A hit implies $b_i<r\le B$ on the band. It also implies
$$
 N_Q(a/r)>0\quad\text{or}\quad a_2(Q)\le a. \tag{1}
$$
In particular it implies $N_Q(B)>0$.

*Proof.* For a witness containing $\ell_0$ use its quotient line. Otherwise its projection to $Q$ has rank two and area at most $a$, since orthogonal projection contracts area. Saturation can only decrease this area. Its binary minimum is at most $B$. The incident case also gives a quotient point within $B$ since $a/r<a/b_i<B$.

The first disjunct alone fails geometrically. Take an orthogonal sum of a length-27 line and a hexagonal plane of minimum $B$ and area $\alpha B^2=a$. The line is the unique global shortest line, and its projection quotient has minimum exactly $B>a/27$. Orthogonal padding by longer periods preserves this example. It even has $27>\alpha\cdot30.5$. This tests the geometric implication only. Whether a given example occurs on a gated first hit is a separate reachability question.

## Reference measures and the size of the missing comparison

Write $c_j=V_j/(2\zeta(j))$, $n=505$, and $m=504$. Under Haar at determinant $D$, primitive lines of length $r$ have intensity $n c_n r^{n-1}dr/D$. Under this line-counting measure the orthogonal quotient has Haar shape at determinant $D/r$. A fixed quotient ball then has mean $c_m t^m r/D$. This is the unfolded law of a marked line. [Kim, Theorem 3, Lemma 10 and §5](https://arxiv.org/pdf/2005.10874)

**Lemma 3 (flag integral).** At fixed $D$ the exact Haar mean of the displayed sum in Lemma 1 is
$$
 F_i(D)=\frac{n c_n c_m a^m}{2D^2}(B^2-b_i^2).
$$
Indeed the radial powers in the two line factors leave $r\,dr$. The finite first moment involves no pair of distinct planes. The formula computes incidence, including multiplicities. Summing at $D_i^*$ gives $1.9082676\cdot10^{-58}<\sum_iF_i(D_i^*)<1.9082677\cdot10^{-58}$. Domination of the **joint line intensity and quotient ball mean** by a common factor $3.3983702\cdot10^{47}$ would suffice. Comparison of quotient shapes alone does not control how many first lines the finite chain places in the integration window.

**Lemma 4 (conditioning on the shortest line in a Haar parent).** For a marked Haar line of length $r\in(b_i,B]$, the probability, over the quotient and lift shear, that the line fails to be shortest is at most $\epsilon=c_m r^{m+1}/D$. Indeed a shorter competitor projects to a nonzero point of length at most $r$ and hence to a primitive-line witness within that radius. Ties have Haar measure zero. Disintegrating the shortest-line selection at fixed $r,D$ therefore gives, for almost every such $r$, a quotient law with density bounded above by $1/(1-\epsilon)$ relative to the unfolded Haar quotient. For a nonnegative test, restrict its integral to winning shears and divide by their total probability. The TV change is at most $\epsilon$ by conditioning and projection. Here $\epsilon<3.02519\cdot10^{-14}$ at all eleven determinant floors. This estimate quantifies the selection bias **within Haar**.

For the finite restart one can dispense with a comparison of first-line intensities by using Lemma 2. Take the subprobability law at draw $i$ restricted to both gates $G$, no prior hit, a vertical win in the specified band and $b_i<r\le B$. Leave the current plane outcome and the terminal hit out of this restriction. Disintegrate by $(r,D)$, using the actual subprobability mass on those data. Write $M_{2,Q}(a)$ for the number of saturated quotient planes through area $a$. Consider the following sufficient assumption on the resulting conditional expectations: each test in a chosen row of the table has mean at most $K$ times its mean under the **unfolded** Haar quotient at determinant $D/r$. An integrated comparison with the same upper sum suffices as well. Lemma 4 explains the choice of reference and is not an assumption about the restart.

| Quotient tests | Sum of reference upper bounds over draws 396–406 | Budget divided by the sum |
|---|---:|---:|
| $N_Q(B)$ | $(3.0955018,3.0955020)\cdot10^{-14}$ | $(2094.9753,2094.9754)$ |
| $N_Q(a/r)+M_{2,Q}(a)$ | $(9.3340497,9.3340500)\cdot10^{-18}$ | $(6947681.00,6947681.01)$ |

For the first row bound each mean by $c_m B^{m+1}/D_i^*$. In the second row use
$$
 \frac{c_m a^m}{b_i^{m-1}D_i^*}
 \quad\text{and}\quad
 \frac{(m-1)\pi c_m c_{m-1}a^m B^2}{6(D_i^*)^2},
$$
respectively. The second expression uses the primitive plane mean at determinant $D/r$, with $r\le B$. Their separate sums lie in $(9.3340497,9.3340498)\cdot10^{-18}$ and $(7.0806513,7.0806514)\cdot10^{-56}$. Each draw's subprobability mass is at most one. The first-moment inequality, Lemma 2, and dropping the terminal condition thus bound $Z_{\rm rem}$ by $K$ times the chosen row's sum, **if that comparison holds**. Using a Haar parent conditioned to have shortest length $r$ instead increases the reference upper bounds by at most $(1-3.02519\cdot10^{-14})^{-1}$. [Primitive plane mean in physical units](wall1_rank2_tail.md#haar-probability-and-multiplicities)

## What restriction of the fresh-mark law gives

**Lemma 5 (finite conditional law).** Fix a raw prefix $S$ before the draw, with fresh group $H$. For every mark $u$, form its window $W_u$, select its winner $v_u$ and form $L_u=\pi_{v_u}W_u$. Given a primitive output line $\ell$, lift its generator to $x\in W_u$. Its orthogonal quotient is exactly the projection of $W_u$ onto $\operatorname{span}(v_u,x)^\perp$ inside the window. This follows by composing the two orthogonal projections and is independent of the lift. Once $(S,y,k)$ for a vertical winner is known, $u=k^{-1}[y]$ is fixed in $H$, so this calculation has no second independent mark.

For a test $f(Q_u)$ of the designated-line quotient, a conditioning cell $C$ (e.g. a length window), and any gate event $J$, put $w_J(S,u)=\Pr(J\mid S,U=u)$. Then
$$
 \mathbb E[f(Q)\mid S,C,J]=
 \frac{\sum_{u\in H}\mathbf1_C(u)w_J(S,u)f(Q_u)}
      {\sum_{u\in H}\mathbf1_C(u)w_J(S,u)}
$$
when the denominator is positive and $C$ is determined by $(S,u)$. Uniformity before selection gives the identity. For an exact expression for the entire residual, take the expectation over the original prefix law of
$$
 \sum_{i=396}^{406}\mathbf1_{\tau\ge i}\,
 \frac1{|H_i|}\sum_{u\in H_i}
 \mathbf1_{\rm vertical\ band}(S_i,u)\,
 \mathbf1_{T_i(L_u)>0}\, w_{G\cap A_{406}}(S_i,u),
$$
where $S_i,H_i$ are the prefix and group before draw $i$. Each eligible first hit is charged once, including a hit followed by loss of the first plane and creation of a different terminal plane. The weights for $i=406$ can include the current hit again without changing its indicator. [Part 108, filtration and transition](wall1_first_tour.md) · [Part 193, exact winning-mark count](wall1_z2_vertical.md)

On every positive-mass conditioning cell the concrete normalized quotient shape has finite support. Haar in rank 504 gives this support measure zero, including after the positive-probability shortest-line conditioning of Lemma 4. Thus total variation is exactly one, and no finite constant dominates all measurable tests. Even the normalized quotient minimum has finite support on the chain side and a nonatomic Haar law: every possible Haar level requires some nonzero integer vector to lie on a fixed norm level, a countable union of null hypersurfaces. The unit probability bound from this uniform comparison exceeds the budget by a factor in $(1.5420,1.5421)\cdot10^{10}$. This argument gives no lower bound on the error of the particular ball test.

There is also a quantitative failure for the **same ball test** if only the one-step marked law, the length band and the incoming GH scale are assumed. In Part 193's padded example $g=32.2$ and at least two of 3329 marks win on the band and yield a small plane. The mass of eligible marks with $N_Q(B)>0$ is at least $2/3329$ by Lemma 2. For every eligible mark with $r\le B$ the Haar mean is at most $c_m B^{505}R/(V_{506}32.2^{506})$, since $D=D_{\rm in}/s$. Even using total eligible mass one, comparison at this threshold would require $K>3.3022456\cdot10^{10}$, while the single-ball allocation allows about 2095. This is an abstract one-step example. It has no established reach probability under the two restart gates. It rules out deducing the desired factor from these one-step hypotheses. [Part 193, example and independent audit](wall1_z2_vertical.md#audit)

**Status for the actual chain.** The flag identity and the two quotient covers hold on the stated residual. The evaluated Haar reference integrals give explicit sufficient distortion factors. The finite weighted conditional ball and plane means in Lemma 5 remain unevaluated on reachable doubly gated prefixes. Bounding their probabilities by one and using disjointness of first-hit draws gives only $Z_{\rm rem}\le1$ from this comparison. No numerical ceiling of $6.485\cdot10^{-11}$ follows here.

**Reproduction.** Run `python docs/research/scripts/wall1_zrem_flag_moment.py` from the repository root. It uses 80-decimal-digit outward interval arithmetic, encloses the zeta tails by the integral test, and checks the determinant branches before summing. All reported reference constants use the Part 193 recurrence with $L_0=400\log 3329$ and coefficient 56.2142. [Verification script](scripts/wall1_zrem_flag_moment.py)

## Audit

**Verdict — CONFIRMED for the hit tests, all three reference sums and the abstract example's distortion bound.** The reachability statement can be strengthened to probability zero for the specific padded example. The residual bound $Z_{\rm rem}\le 6.485\cdot10^{-11}$ remains open.

On the band, rounding a lift gives $\lambda_1(L)\ge\alpha s>b_i$. A shortest line in each saturated witness plane has $r\le B$ by binary reduction. The primitive quotient line has length $\det P/r$, and its full preimage recovers $P$. Thus $T_i>0$ is exact. The summation index in Lemma 1 has a stray “m” and should read $\ell\text{ primitive in }L,\ b_i<r=|\ell|\le B$. The integral counts every eligible incidence, including ties and other eligible lines in the same plane. One quotient-line factor leaves $r\,dr$ in the radial integral. Part 207's unrestricted plane second moment uses two such factors and still diverges as $\int_0^1 r^{-502}\,dr$. [Kim, Theorems 3–4 and Lemma 10](https://arxiv.org/pdf/2005.10874)

For the global shortest line, incidence gives a quotient line through radius $a/r$. A transverse witness projects to a rank-two lattice whose saturation has area at most $a$ and minimum at most $B$. These implications justify both quotient covers. The orthogonal length-27 example verifies that the smaller ball alone can miss a witness.

The interval script passed. An independent 200-digit computation updated physical covolumes by dividing by the winner cap, evaluated the ball volumes and zeta factors directly, and integrated the flag intensity over each of the eleven radial intervals. The period cap was active on 20 draws and the Hermite cap on 386.

| Test | Eleven-draw reference sum, rounded | Budget divided by sum, rounded |
|---|---:|---:|
| All line incidences | $1.908267663103\cdot10^{-58}$ | $3.3983702210\cdot10^{47}$ |
| Global shortest line, single ball | $3.095501881069\cdot10^{-14}$ | $2094.97530583$ |
| Global shortest line, line plus plane | $9.334049729579\cdot10^{-18}$ | $6947681.00436573$ |

The transverse summand contributes $7.08065136772\cdot10^{-56}$ to the last row. The downward choices $2094.97$ and $6{,}947{,}681$ both fit the budget. For the optional shortest-line-conditioned Haar reference at the chain's discrete radii, use the version obtained by sampling the unfolded quotient and shear at each specified $(r,D)$ and retaining winning marks. This fixes the conditional law even at individual radii of Haar measure zero. Its acceptance probability is at least $1-c_m r^{m+1}/D$ throughout the band.

**Part 193 example.** Independent integer enumeration recovered marks 141 and 3188, both at height one with $q^2s^2=10639285766$. The eligible ball-hit mass is at least $2/3329$. Dividing this by the upper bound $c_{504}B^{505}R/D_{\rm in}$ gives $3.30224564331\ldots\cdot10^{10}$. The example itself is unreachable even before either gate. Every restart prefix satisfies $qP_E\mathbb Z^N\subseteq M$, hence $qM^*\subseteq (P_E\mathbb Z^N)^*=E\cap\mathbb Z^N$. The padded $155\mathbb Z^2$ summand supplies $z\in M^*$ with $\|qz\|^2=3329^2/155^2\notin\mathbb Z$. This proves the obstruction for every orthogonal padding in the construction. [Part 193, marked law and example](wall1_z2_vertical.md)

On a reachable prefix the fresh mark is uniform before selection. Its contribution to the exact first-hit mass carries the continuation weight $\Pr(G\cap A_{406}\mid S_i,U_i)$, which includes a terminal hit after loss of the original witness. Dropping the terminal hit leaves a sufficient first-moment estimate with both gates and the surviving-prefix weights. The missing estimate can be integrated over those weights. The quotient covers require control of the indicated test means, and the all-incidences version also requires control of the first-line intensity. The Haar computations alone leave those chain quantities unevaluated. [Part 193, residual event](wall1_z2_vertical.md) · [Part 208, terminal replacement](wall1_z1_terminal_law.md#audit)
