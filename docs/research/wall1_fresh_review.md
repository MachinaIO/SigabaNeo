# A coordinate-section bound for selected width-506 lattices

The prescribed codimension-400 family from Parts 226 and 242 has selected probability below **$10^{-1111.57}$**. Its first 405 proposed winners avoid three specified input coordinates. Deleting those columns determines the same frozen span whenever the proposals win. The three old anchors must then pass independent tests against that span. This resolves the selection question for the particular family whose chronological membership sum exceeds $10^{356}$. The same comparison bounds an entire class of terminal planes without prescribing their anchors, deficiency or first-hit history.

## The statement worth proving

Use the **unconditioned 400-row marginal restart**. Draw $A$ uniformly in $\mathbb F_{3329}^{400\times512}$, initialize with 105 input columns, and append the other 407 in order. Use the Part 108 signed shortest-vector rule, including its ambient tie order. Let $P$ be the final projector, $H=P L(A)$, $s_i$ the 407 selected lengths and $X$ an independent product of 912 CBD(3) variables. Put $Z=\|PX\|^2$ and define

$$
 C(A)=\mathbb E_X\!\left[\mathbf1_{Z\le959.5}
 \sum_{k=0}^{30}\sum_{v\in H\setminus\{0\}}
 \mathbf1_{\|v+kPX\|^2+k^2\le1+Z}\right],\qquad
 S^+(A)=\sum_i2e^{-s_i^2/12}+222e^{-3329^2/12}.
$$

Let $U(A)$ be the conditional contribution left after assigning the three paid Part 241 classes **on each realized summand before averaging over $X$**. Set $\tau=0.00012938,\ \ell=0.000623$. The joint distributional statement that would close the score and lift arguments is

$$
 \boxed{
 \forall a,b\ge0,\quad
 \mathbb E_A\!\left[a\,U(A)+b\,\mathbf1_{C(A)\le\tau,\ S^+(A)>\ell}\right]
 \le (5.2408\times10^{-7})a+0.003546229\,b .}                        \tag{1}
$$

Both coordinates concern the **same returned basis**. The first accounts for signed multiplicities at all plant heights and the orientation of the embedding. The second counts additional rejections on score-accepted designs. Equation (1) is equivalent to its two coordinate inequalities. It includes the 111-axis increment for the 511-row transfer. [Marginal law and score](wall1_score_rejection.md) · [Height-by-height assignment](wall1_height_split.md)

The two paid means sum to less than $5.283493\times10^{-8}+6.998082\times10^{-8}$. With (1), Markov gives score rejection below 0.005. The additional prefix rejection, accepted terminal charge $0.000607731$, accepted prefix charge $\ell$ and single coupling charge $0.00022304$ then fit the 0.01 budget. For this last conclusion alone it would suffice to prove $\Pr(C>\tau\ \text{or}\ S^+>\ell)\le0.008546229$. This direct probability would leave the proposed mean-score certificate open. To settle the historical plane targets in the same theorem, add $c\mathbf1_{Z_1}+d\mathbf1_{Z_2}$ on the left of (1) and $9\times10^{-11}(c+d)$ on the right, for every $c,d\ge0$. Here $Z_1,Z_2$ retain the Part 192 first-hit and terminal conditions. This extension gives the Part 184 spacing probability $\Pr(E)<1.84652\times10^{-10}$ by Part 224. The converse inference from spacing to (1) fails. [Plane ledger](wall1_budget_ledger.md) · [Dependency correction](wall1_detect_repair.md)

## 1. An entropy budget for the whole sequence of comparisons

Put $I_i=\mathbf1_{s_i>1.10g_i}$ and $p_i=\mathbb E[I_i\mid\mathcal F_{i-1}]$, where $g_i$ is the incoming window GH length and $\mathcal F_{i-1}$ is the actual past. Part 216 implies that the small-scale crossing on draws 396–406 forces $N=\sum_{i=1}^{405}I_i\ge100$.

**Lemma 1.** For $0<p<r=100/405$, writing $\bar p=405^{-1}\sum p_i$ and $d$ for binary relative entropy in nats,

$$
 \Pr(N\ge100)\le\Pr(\bar p>p)+\exp[-405\,d(r\|p)].
$$

The product of $e^{tI_i}/(1+(e^t-1)p_i)$ has expectation one by successive conditioning. On the indicated upper tail with $\bar p\le p$, concavity of the logarithm bounds the denominator by $(1+(e^t-1)p)^{405}$. Optimize at $e^t=r(1-p)/(p(1-r))$.

At $p=.12$ the exponential term is below $1.9642\times10^{-11}$. It would suffice that $\Pr(\sum p_i>48.6)\le7.6\times10^{-12}$. Even 48 unit conditional probabilities and 357 zeros fit the deterministic budget. The open input is the distribution of the *sum of conditional void fractions on the realized histories*. Accounting only for the number of available marks at each draw provides no such estimate. This route addresses the vertical branch. [Crossing criterion and paid large-scale charge](wall1_small_g_frequency.md)

## 2. Three independent probes with a two-draw delay

Fix the past before draw $i-2$. View the three unread columns as independent uniform marks $U_1,U_2,V$ in its current mark group $G$. Let $p_F(b)$ be the fraction of those marks whose distance to the old lattice exceeds $b$. Write $h=\sqrt{56.2142}\,V_{506}^{1/506}$, with $V_n=\pi^{n/2}/\Gamma(1+n/2)$. Starting at the current $\log g$, apply $x\mapsto(505x-\log h)/506$ twice to obtain $x_2$. The deterministic winner cap and determinant recurrence give $g_i\ge e^{x_2}$. Put $b=\sqrt{1.10^2e^{2x_2}-2}$ when real.

**Lemma 2.** The delayed conditional probability of a long winner at $i$ is at most $p_F(b)^3$. Use the three old-frame coefficient vectors $(0,0,1),(1,0,1),(0,1,1)$. Their displacements $V,V+U_1,V+U_2$ are jointly uniform on $G^3$ by an invertible change of variables. Any one horizontal representative through $b$ has full length at most $1.10e^{x_2}$. The intermediate projections can only shorten it. Its last coefficient is one, so it survives both projections as a nonzero candidate. With $k$ intermediate columns, the same proof gives $k+1$ independent tests with squared coefficient norm at most two and the corresponding $k$-fold lower scale update. [Two-mark update and deferred-column law](wall1_inductive_typicality.md)

The delay matters numerically. On a path with 100 long wins, one congruence class modulo three contains at least 34. If the delayed probabilities are at most .06, each class is dominated for this tail by $\mathrm{Bin}(135,.06)$ using successive conditioning within that class. The first two draws have zero long probability. The union bound is below $1.9640\times10^{-12}$. Thus $p_F(b)\le.3914$ on each required starting entry would suffice. At $g=35$, $b=37.89001\ldots$, and its 505-ball volume is only $0.0003726682$ times the volume at $\sqrt{(1.10g)^2-1}$, rounded up. That ratio quantifies the loss of this sufficient test. A lower bound on the fraction of distinct covered marks at the smaller radius remains open. A delayed estimate cannot be inserted into a one-draw conditional-moment recursion. [Limits of a radial initialization](wall1_drift_recursion.md)

## 3. Delete input columns on which the frozen span vanishes

The following comparison gives unconditional bounds for parts of the horizontal, score and small-prefix events. The deletion takes place only in the proof. The reported probabilities refer to the original reducer.

**Lemma 3 (agreement with a coordinate section).** Fix a cut and a set $J$ of $r$ input coordinates available by that cut. Run the signed comparisons on the coordinate section $y_J=0$ at the **original draw times**. When a column in $J$ is scheduled, freeze on the current section without appending it. Use the original ambient tie order with zero padding. Assume the section has enough dimensions for these freezes, as it does below for $r\le3$. If the full frozen space at the cut lies in $y_J=0$, every earlier freeze agrees with this forced sequence.

Indeed every earlier winner then has zero $J$-coordinates. Before each comparison the projector fixes those axes. A projected vector has zero such coordinates exactly when its raw representative does. Thus the zero-coordinate candidates are precisely the projected section, and the designated full winner minimizes the restricted signed order as well. Induction proves agreement. Revealing the other columns first determines the forced projector $P_0$. Agreement can depend on all columns. It is dropped below only after majorizing a nonnegative count on the forced path.

At the cut write $M=P_0 L_{\rm section}$, $K=P_0\mathbb Z^{N-r}$ in the reduced ambient space, and $G=K/M$. The section still has its 400 sample periods and graph columns for every undeleted input, hence raw covolume $q^{400}$. The conditional marks of the held-out columns are independent uniform in $G$. Indeed one can subtract graph columns from any integer vector to eliminate its input part, leaving only sample coordinates. Each sample $q$-period is in the graph. On agreement $\det M=D$, the full retained covolume, since the same frozen lengths divide the same raw covolume. Any required lower bound on $D$ may therefore be imposed on the forced path **before** averaging the held-out columns. The argument applies to a pre-freeze window as well.

**Lemma 4 (incidences with independent hidden heights).** Suppose the full dimension at the cut is $n$. Count ordered tuples of $r$ points whose $r\times r$ matrix of coordinates in $J$ is invertible modulo $q$. Impose triangular constraints

$$
 \left\|v_j-\sum_{k<j}c_{jk}v_k\right\|\le R_j,\qquad 1\le j\le r,
$$

with specified real coefficients and positive radii. The **unconditional mean count with indicators of agreement in $y_J=0$ and $D\ge D_*$** is at most

$$
 \prod_{j=1}^r B_n(R_j,D_*),\qquad
 B_n(R,D_*)=\frac{e^{n/2}}{D_*}\,[z\Theta(z)]^n,\qquad
 z=R\sqrt{2\pi/n},\quad
 \Theta(z)=1+\frac{2e^{-\pi z^2}}{1-e^{-3\pi z^2}} .                 \tag{2}
$$

For fixed integer heights of full residue rank, the $r$ cosets in $K/M$ are jointly uniform by a field-linear bijection. Average their point sums, paying $|G|^{-r}$, and then enlarge the height sum to **all** integer matrices. Only at this last step do singular height matrices enter the upper estimate. The deterministic sum is over $(K\times\mathbb Z^r)^r$. Majorize each ball by $e^{n/2}\exp(-\pi\|\cdot\|^2/z^2)$. Sum from $j=r$ downwards, allowing an arbitrary translate at each summation. By Poisson summation the translated Gaussian sum on this grid is bounded by its centered dual theta factor times $z^n/\det K$. The dual grid embeds isometrically in ambient integer coordinates because a vector in the image of $P_0$ pairs integrally with the projected grid precisely when it pairs integrally with the integer grid. Some $n$ coordinate rows restrict injectively to its span, decreasing norms. The theta factor is consequently bounded by $\Theta(z)^n$. Finally $|G|\det K=\det M$. The proof counts tuples after the forced selections without summing over frozen flags.

### The explicit family from Parts 226 and 242

Take the cut after draw 405 and $J=\{103,104,105\}$ in one-based input numbering. Every proposed private pivot has zeros there. The three projected anchors have height matrix the identity and visible components within $1/2$ of their respective centers $29e_1,14e_1+28e_2,14e_1+27e_3$. Use the forced projections of those centers, which agree on the family. Here the heights are fixed, so count only in $K$ of rank 502. At Gaussian width one the mean number of compatible ordered triples, with agreement, is at most

$$
 \left(\frac{e^{\pi/4}\Theta(1)^{502}}{e^{L_{405}}}\right)^3
 <10^{-1111.57}.
$$

Here $L_0=400\log q$ and $L_{i+1}=\max(L_i-\log q,505L_i/506-\tfrac12\log56.2142)$. This covers the original and modified families together. The mean includes all allowable perturbations. The two signed height-zero points used for the Part 242 incidence lower bound contribute at most twice this mean *along the prescribed selected flags*. A visit to the same rational space via another flag is covered only if it has the required vanishing coordinates and anchors at the specified cut. [Three anchor patterns and private pivots](wall1_wholly_old_mass.md) · [Modified family](wall1_high_codim_sections.md) · [Chronological score incidence](wall1_score_first_moment.md)

### Wholly old first hits without prescribed centers

Call an input coordinate **untouched at a cut** if it vanishes identically on the real frozen span. For a wholly old first hit at draw $i$, take the saturated old ternary lattice through the winner over a hit plane. Consider the event that such a ternary lattice has rank three modulo $q$ on **some three untouched input coordinates**. Coordinates of its projected points on these axes are integers and independent of the raw lift. Across draws 155–406 the probability of this event is below **$1.13\times10^{-20}$**, at all deficiencies combined.

Take the winner $v$ of length $s$, and lift a Gauss-reduced basis of the hit plane to $x,y$. Let $s,t,u$ be the three successive GS lengths and $a=1352/\sqrt3$. Then $tu\le a,\ st>a,\ u\ge\sqrt3\,t/2$. The second inequality follows because before the first hit even the saturation of the old plane spanned by $v,x$ has area greater than $a$. Also $t\le T=52/\sqrt3$ and $s\le R=(\sqrt2 a)^{1/2}$, the latter by the rank-three Hermite bound applied to the ternary lattice of determinant $stu$ and minimum $s$. In particular $s>a/T,\ t>a/R,\ u>\sqrt3\,a/(2R)>20,\ u<s$. [First-hit geometry](wall1_z1_horizontal.md)

Size-reduce the lifts so all three GS coefficients have magnitude at most $1/2$. For the form $x-c_{21}v$ the ideal coefficient lies in $[-1/2,1/2]$. For $y-c_{32}x-c_{31}v$ the two ideal coefficients lie in $[-1/2,1/2]$ and $[-3/4,3/4]$, since the latter is $\mu_{31}-\mu_{32}\mu_{21}$. Round to multiples of $1/100$. The extra norm is at most $e_x=R/200$ and $e_y=(R+\sqrt{T^2+R^2/4})/200$, respectively. Round $s,t+e_x,u+e_y$ upwards to multiples of $\eta=1/8$. The resulting radii are between 20 and 36. Their product is at most

$$
 Ra(1+\eta/(a/T))(1+(\eta+e_x)/(a/R))
       (1+(\eta+e_y)/(\sqrt3\,a/(2R))).
$$

Every integral basis of the ternary lattice has the required mod-$q$ rank if one does. Apply (2) with $n=505,\ D_*=\exp L_{405}$, using this product for the factors $z^{505}$ and radius 20 for the decreasing theta factors. The union costs at most $252\binom{510}{3}289^3\,101^2\,151$ for the draws, masks, radii and shears. The base-ten logarithm of the resulting bound lies in $(-19.97,-19.95)$. This includes choosing the three untouched coordinates after observing the flag.

### Terminal planes, small prefix winners and score

* **Terminal area, including a replacement.** After draw 406, the probability of an area-$\le a$ plane with rank two on some pair of untouched inputs is below **$2.39\times10^{-41}$**. Work directly at this cut with $D_*=\exp L_{406}$. For a Gauss-reduced basis with GS lengths $t,u$, if $t\le24$ its first vector is primitive in the plane and nonzero modulo $q$ on at least one of the two coordinates. Charge $511 B_{505}(24,D_*)$ by the one-coordinate lemma. Otherwise $24<t\le T,\ 12\sqrt3<u\le a/24$. Round the size-reduction coefficient to the $1/100$ mesh and the two radii up in eighths. Their product is at most $a(1+\eta/24)(1+(\eta+T/200)/(12\sqrt3))$. The remaining union costs $\binom{511}{2}289^2\,101$. This uses only the plane present at the terminal cut.
* **A small winner first using an input.** Across all 407 draws, the probability of $s_i\le13$ with a nonzero coordinate on any input untouched just before that freeze is below **$10^{-190.05}$**. In the pre-freeze window $n=506$ and $D\ge\exp L_{406}$. Every nonzero height of such a point is invertible modulo $q$. Sum $B_{506}(13,\exp L_{406})$ over at most $407\cdot512$ choices. This includes old tiny winners that first use a previously available input. Small winners supported entirely on previously used inputs remain possible.
* **Shifted score.** At cut 407, sum over signed points having a nonzero coordinate on an untouched input. For plant heights 6 through 30 their joint mean score is below **$2.1625\times10^{-9}$**. For each fixed coordinate Lemma 3 gives a forced rank-504 visible lattice. On agreement the forced projector, extended by the identity on that axis, gives the actual $PX$. For fixed plant the nonzero input coefficient $j$ satisfies $|j|\le3k+\sqrt{960.5}<122$, so its coset is uniform before the agreement test. Part 239's translated Gaussian sum with the identical determinant floor, cap and rank-505 plant moment applies even when the coordinate was present from initialization. The bound is $512(5.26586\times10^{-8})\sum_{k=6}^{30}\exp(-505k^2/1921)$. The class can overlap earlier paid ones. At $k=0$ summing the single-coordinate upper estimate over 512 already exceeds the entire residual allowance. [Translated Gaussian and plant cap](wall1_score_rejection.md)

The historical plane targets concern all hit planes. A high rank for the raw lift, or a private pivot when an earlier winner was selected, does not imply rank on coordinates untouched by **every** preceding winner. Even a one-dimensional frozen span can have nonzero entries on every input axis. The actual probabilities of hits supported on previously used coordinates, the rest of the score and (1) remain undetermined. These are paper bounds with outward-rounded arithmetic.

Run the [interval checker](scripts/wall1_fresh_review.py) from the repository root with **python -B docs/research/scripts/wall1_fresh_review.py**.

## Audit

**Verdict.** The three stated selection and plane bounds hold for the unconditioned marginal restart. The entropy and delayed-probe implications also hold. One qualification concerns the proposed void ceiling. Requiring it at every starting history already fails on a reachable initial graph.

**Selection of the prescribed family.** Fix all columns outside $J=\{103,104,105\}$ and call this information $\mathcal H$. The forced sequence, including its ties, is $\mathcal H$-measurable. If the full frozen span vanishes on $J$, then all earlier winner directions vanish there. At the first purported disagreement the projectors still coincide on the section and fix the held-out axes in the full space. Thus a full candidate has zero held-out heights exactly when its representative does. Restricting the ambient signed order retains the full winner, contradicting disagreement. This gives agreement on the event without conditioning the marks on that event.

Given $\mathcal H$, the projected sample-coordinate map $\mathbb F_q^{400}\to K/M$ is onto. The graph generators eliminate all visible input coordinates and the sample $q$-periods kill the choice of lift. The three columns therefore give independent uniform cosets. Write $N_j$ for the number of eligible points in the $j$th coset within $1/2$ of its forced center. The selected-family indicator is bounded pointwise by $\mathbf1_{\det M\ge e^{L_{405}}}\prod_jN_j$. On selection, primitivity and the common frozen lengths give the required determinant floor. On other outcomes the right side is nonnegative. The three counts factor **given $\mathcal H$**. The identity height matrix and the fixed centers cover all perturbations in both families with this one product. The base-ten logarithm of its mean majorant is $-1111.5796246445\ldots$. This bounds joint occurrence of the selected prefix and the three required anchors. The prefix selection event by itself has fewer requirements.

**Plane counts.** For each fixed mask, invertibility of the height matrix permutes tuples of marks in $(K/M)^r$. Enlarging the height sum after this average permits successive translated Gaussian bounds even with nonintegral shears. A change of integral basis multiplies the height minor by $\pm1$, so reduction and lift rounding preserve its rank. For a wholly old hit the cut is *before* the append. There are at most 510 available inputs on draw 406, and the incoming log determinant throughout draws 155–406 is at least $L_{405}$. The inequalities $tu\le a<st$ give $u<s$, justifying the third radius cap. Direct evaluation with the stated meshes and mask count gives a majorant below $1.097258\times10^{-20}$. At the terminal cut the 511 inputs and floor $L_{406}$ apply. An invertible two-row height minor makes the first reduced vector nonzero on at least one of its columns. The short-line contribution is below $1.087\times10^{-59}$ and the combined majorant is below $2.377830\times10^{-41}$. This terminal argument includes replacement planes satisfying the rank test at that cut.

**Budget and conditional tails.** Evaluating (1) on the two coordinate axes recovers both proposed inequalities, and linearity gives the converse. The paid means plus the proposed residual give a Markov charge below $0.004999968$. The event $C\le\tau,\ S^+>\ell$ is disjoint from score rejection on the same design. The five rounded charges sum to $0.01$, including the coupling charge once. Both estimates in (1) remain hypotheses. For the entropy argument the compensator controls the denominator of the mean-one product on $\sum p_i\le48.6$. The resulting crossing charge, including the proposed exceptional mass, is below $2.72415\times10^{-11}$. For the delayed argument the three marks are independent in the frame *before* draw $i-2$. The last height of each candidate remains one after both freezes. Within each residue class the preceding indicator is already measurable at that conditioning time, which justifies binomial domination under the stated delayed probability ceiling. The three-class tail is below $1.96394\times10^{-12}$.

**Qualification on the void hypothesis.** For example, the first 105 columns can all be zero, an event of positive probability. The initial lattice is then $q\mathbb Z^{400}\times\mathbb Z^{105}$. The uniform mark has 400 independent balanced sample residues, and their Euclidean norm is its distance to the lattice. For the delayed test on draw 3, the stated recurrence gives $b<4000$ from $D_0=q^{400}$. A covered mark can have at most 64 coordinates of magnitude at least 500. The expected number of coordinates of magnitude below 500 is $400\cdot999/3329$. Markov's inequality therefore gives
\[
 p_F(b)\ \ge\ 1-\frac{400\cdot999}{3329\cdot336}\ >\ 0.6427.
\]
Thus $0.3914$ cannot serve as a uniform void bound over all entries. The draw-3 long-winner probability on this history is zero because the two freezes leave unit input directions available and the incoming threshold exceeds one. Histories discharged directly may be omitted from the void test. Applying the binomial bound still requires control of the delayed long-winner probabilities on the remaining histories. The checker rerun passed every interval assertion.
