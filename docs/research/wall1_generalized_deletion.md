# Congruence sections of the selected graph lattice

A frozen flag can touch every input coordinate and still leave independent tests for short points. The appropriate section is the preimage of a subspace **modulo** $q$. It has full real dimension. The rank test is on raw integral graph lifts, including the lattice of frozen lifts. Replacing it by reduction of an orthogonal projector modulo $q$ can give an undefined operation.

For the unconditioned Part 243 restart, a wholly old first hit detected on a four-input block has probability below $4.67\times10^{-20}$. A terminal small-area plane detected on a five-input block has probability below $3.46\times10^{-19}$, including replacement planes. Detection means that the witnesses add respectively three or two dimensions to the frozen input residues on that block. Both estimates allow the block and the relation to be chosen after seeing the flag. The late full-support frequency and the unrestricted width-506 targets remain open. [Audited coordinate-section result](wall1_fresh_review.md) · [Parts 212–243](../PROOF_GAP.md)

## How many inputs does the actual flag touch?

Set $q=3329$ and draw the $400\\times512$ matrix uniformly over $\\mathbb F_q$. Use the ambient lexicographic signed tie rule of Part 108, with sample coordinates first. Write $F_f$ for the real frozen span after $f$ freezes. There are $105+f$ available inputs. The old cut at draw $i$ is $f=i-1$. Between the append and its freeze the newest axis is always untouched. The question about all-coordinate coverage concerns the old cut or the post-freeze cut. [Forward-pass convention](wall1_first_tour.md)

**Proposition 1.** The following bounds hold simultaneously at all old cuts on draws 155–406 and at their post-freeze cuts. The population counted is the **first 106 inputs**, including the first append.

| Number of these 106 left untouched | Upper probability |
|---|---:|
| At least 6 | 0.00505 |
| At least 10 | $3.20\times10^{-6}$ |
| At least 14 | $1.44\times10^{-9}$ |
| At least 17 | $1.21\times10^{-11}$ |

In particular the probability of touching at least 101 of the first 106 is greater than 0.99495. Consequently there are at most $f+4$ untouched among all $105+f$ on this event. The concentration is about the initial block. The arrival order precludes extending it by permutation to a late input.

*Proof.* Call a winner a period here if, in the still-unfrozen coordinate frame, it has zero input residue and is a signed $q$-axis. Until the first winner with nonzero input residue, the winners must be the first available sample axes. The minimum is at most $q$, a zero-input-residue graph member has all coordinates divisible by $q$, and the signed order among such axes picks the first sample axis. Thus, up to and including the first other winner, draw $i$ agrees with the comparison that projects away the first $i-1$ sample axes. The latter graph has 506 coordinates, $401-i$ independent uniform rows and $105+i$ inputs before imposing agreement. The argument only uses $i\le5$.

Put $R_0=\sqrt{q^2-1}$, and write $V_n$ for the unit-ball volume. At draw $t$ in that forced comparison the probability of having no vector through $R_0$ is at most $4q^{401-t}/(V_{506}R_0^{506})$. Indeed the Part 222 projective candidate list in dimension 506 is independent of the row count. Every candidate has nonzero last input. The mean is at least $V_{506}R_0^{506}/(4q^{401-t})$, and the variance is at most the mean by the same independent-or-incompatible pair calculation. This proves the bound also for the event that only period axes win through draw $t$.

For a nonperiod winner at draw $i\le t$ vanishing on $z$ of the original 106 inputs, some signed pair in a $(506-z)$-dimensional coordinate ball of radius $q$ meets the graph, with nonzero input residue. For fixed residues the incidence costs $q^{-(401-i)}$. The inward half of the unit cube at each integer center in a radius-$q$ ball lies in the ball of squared radius $q^2+(506-z)/4$. Counting one sign cancels the half-cube factor two. Consequently the upper bound for at least $z$ untouched coordinates at any subsequent cut is
\[
 \frac{4q^{401-t}}{V_{506}R_0^{506}}
 +\binom{106}{z}\sum_{i=1}^t
 \frac{V_{506-z}(q^2+(506-z)/4)^{(506-z)/2}}{q^{401-i}} .
\]
Use $(t,z)=(2,6),(3,10),(4,14),(5,17)$. Touching a coordinate persists under extension of the real span. In particular there is no factor 252. [Raw projective list](wall1_long_winner_handle.md) · [Improved raw list](wall1_raw_graph_winner_cap.md)

**Two-sided bounds for touching every available coordinate.** Write $p_f$ for this probability after $f\ge1$ freezes, $f\le407$. Then
\[
 .03694\,q^{-400(f-1)} < p_f
 < 1-.7298\,q^{-399(f-1)}.
\]
At draw one the improved raw list has mean at least $u=V_{506}R_0^{506}/(2.09q^{400})$. Its hit probability is at least $u/(1+u)$. Subtract the preceding signed-pair bound at $i=1,z=1$ with radius $R_0$. The difference exceeds .03694. On this event the first winner touches every input and has length at least $\sqrt{106}$. After removing a primitive shortest vector of length $s$, the old minimum is at least $\sqrt3\,s/2$, by reducing a lift along that vector. Thus subsequent zero columns give unique unit winner lines and preserve full coverage. Their probability gives the lower bound. Conversely, subtract the unoriented first-moment bound at $i=1,z=0$ and radius $q$ from one. With probability greater than .7298 the first winner is a sample period and the old minimum after projection exceeds one. Every later column supported on that same sample row projects to a fresh unit, preserving this old lattice and leaving all first 106 inputs untouched. Each such column costs $q^{-399}$. These bounds establish both possibilities under the specified law. At the late cuts they do not determine which is typical.

There is an exact expression for the missing support statistic. For a set $J$ of available inputs, expose all other columns and perform the Part 243 **real** section comparison at the original draw times. Let $\mathcal V_J$ consist of the tuples of hidden sample columns for which, at some comparison on this forced path, a projected candidate outside the section precedes its forced winner in the signed shortest order. Include ties according to the ambient order. Conditional on the exposed columns, the probability that all of $J$ stay untouched is exactly $1-|\mathcal V_J|/q^{400|J|}$. Indeed the earliest such comparison is precisely the first disagreement. Before disagreement the projector fixes the held-out axes. If too few section dimensions remain for the required freezes, the untouched event is empty. Write $\pi_J$ for the resulting unconditional probability, including $\pi_\varnothing=1$. For the total number $N_f$ of untouched inputs,
\[
 \mathbb E\binom{N_f}{b}=\sum_{|J|=b}\pi_J,\qquad
 p_f=\sum_{J\subseteq[105+f]}(-1)^{|J|}\pi_J .
\]
In particular even the mean needs the one-column *union* of forbidden comparisons along the forced path. Multiplying their separate success fractions would resample the same column. No late-cut evaluation of these union sizes is available here.

**How much modular rank is available?** Let $S=F_f\cap\mathbb Z^N$, $L=L(A)$, $B=L\cap F_f$, and $d=400-\dim\sigma(S)$, where $\sigma(x,y)=x-Ay\bmod q$. On *all* the available inputs the frozen graph lifts have rank exactly $f-400+d$ modulo $q$. Indeed saturation embeds $S/qS$ into the ambient residue space. The image of $B$ in that space is the kernel of the syndrome on $S/qS$, and input projection is injective on the graph residues. The global input quotient therefore has dimension exactly $505-d\ge105$, even on a fully touched flag. The Part 240 simultaneous estimate $d\ge133$ outside probability $10^{-1069}$ gives frozen rank at least $\max(0,f-267)$ and quotient dimension at most 372 there. For example the old draw-406 rank is at least 138 on this event. A large quotient on the full block does not imply a short list of tests fixed independently of the matrix. [Frozen deficiency under the actual law](wall1_high_deficiency.md)

## Deletion modulo a fixed linear map

Fix an old, pre-freeze or terminal cut with $k$ available inputs. Take a surjection $H:\mathbb F_q^k\to\mathbb F_q^r$ fixed before sampling. It may use only a specified coordinate block. Write $h(x,y)=H\bar y$, $W=\ker H$, $E_0=\ker h\subset\mathbb Z^N$, and $L_0=L(A)\cap E_0$. Expose only $A|_W$. Choose a linear splitting $T$ of $H$ and extend the exposed map to $A_0$ by setting $A_0 T=0$. Then $A=A_0+UH$, where the $r$ columns of $U$ are still independent uniform sample vectors.

**Lemma 2 (agreement).** Run the same signed shortest comparisons, in the original metric and times, on the successive coordinate-prefix restrictions of $L_0$. This determines a forced projector $P$ from the exposed data. On the event $h(L(A)\cap F_f)=0$ the full and forced frozen flags agree through the cut.

*Proof.* At every earlier comparison an integral lift of the full winner belongs to $L(A)\cap F_f$, after zero padding. Thus its projection is available in the forced comparison whenever the preceding projections agree. The forced set is a subset of the full set and inherits the signed ambient order. Induction proves the assertion. The test can equally be applied to a basis of integral frozen graph lifts obtained by successive primitive completions. Such lifts generate $L(A)\cap F_f$ by induction, since each shortest winner is primitive in its projected lattice. No modular reduction of projected coordinates or invariance of a real coordinate section is required. Information about $A|_W$ may mix columns from different times. It is used only to define the comparison for this fixed cut.

**Lemma 3 (independent marks and physical density).** Write $M=PL_0$, $K_0=PE_0$, $K=P\mathbb Z^N$ and $G=K_0/M$. For a fixed label $b\in\mathbb F_q^r$, the projected graph points with a lift of label $b$ form a translate of $M$. Within the ambient coset $K_b=P h^{-1}(b)$ its random displacement is the image of $Ub$ in $G$, up to a fixed translate. For any linearly independent list of labels these displacements are independent uniform marks, conditional on $A|_W$.

*Proof.* Choose $y_b$ lifting $Tb$. With $x_b$ lifting $A_0\bar y_b$, a representative is $(x_b+\widetilde{Ub},y_b)$. All other lifts at this label differ by $L_0$. On $E_0$, subtracting a graph element eliminates the input component, and sample periods kill lifts of multiples of $q$. Thus $\mathbb F_q^{400}\to G$, $u\mapsto[P(\tilde u,0)]$, is a surjection. Extending independent labels to a basis proves joint uniformity. This is a statement before imposing agreement.

There is a multiplicity even if different ambient labels project to the same geometric grid. Put $c=|h(\ker P\cap\mathbb Z^N)|$. Then $[K:K_0]=q^r/c$, and the multiset of all $K_b$ covers $K$ exactly $c$ times. On agreement $M$ has determinant $q^r D$, where $D=\det PL(A)$. Indeed the raw graph has every input residue, so $[L(A):L_0]=q^r$, and its entire kernel lattice lies in $L_0$ on agreement. On arbitrary forced paths use $D_0=\det M/q^r$, determined before averaging the marks. The two index identities give
\[
 |G|\det K_0=\det M,\qquad \frac{c}{|G|\det K}=\frac{1}{D_0}.
\]
This cancellation is needed for an oblique or purely modular relation. Merely keeping the $q^r$ labels while assigning each label the full projected grid would lose the index factor.

For example, take one sample and one input, a nonzero scalar graph map over $\mathbb F_q$, the label $h=y\bmod q$, and project off the input axis. Algebraically $K=K_0=\mathbb Z$, $M=q\mathbb Z$, and $c=q$. Although every ambient label projects to the identical grid, the graph lattice in the projected-away axis is $q\mathbb Z$ and has zero label. This illustrates the index calculation independently of the choice of reducer.

**Corollary 4 (short tuples).** Count ordered tuples of $s\le r$ projected graph points whose raw labels are independent. On agreement the label of each projected graph point is well defined. Impose constraints $\|v_j-\sum_{l<j}a_{jl}v_l-w_j\|\le R_j$, with fixed radii and shears, and centers determined by the exposed data or independent plant. The mean count jointly with agreement and $D\ge D_*$ is at most
\[
 \prod_{j=1}^s B_n(R_j,D_*),\qquad
 B_n(R,D_*)=\frac{e^{n/2}}{D_*}\{z\Theta(z)\}^n,\quad
 z=R\sqrt{2\pi/n},\quad
 \Theta(z)=1+\frac{2e^{-\pi z^2}}{1-e^{-3\pi z^2}},
\]
where $n=\operatorname{rank}K$.

*Proof.* Keep the forced determinant gate $D_0\ge D_*$, then drop the agreement indicator on the nonnegative count. For each independent label tuple, averaging gives $|G|^{-s}$ times the sum over its ambient cosets. Enlarge to all label tuples only now. Lemma 3 gives a factor $c^s$ times the sum over $K^s$. Majorize each indicator by $e^{n/2}\exp(-\pi\|\cdot\|^2/z^2)$ with its own width. Sum last variable first. By Poisson summation the translated Gaussian on $K$ is bounded by $z^n\Theta(z)^n/\det K$, since $K^*=\operatorname{im}P\cap\mathbb Z^N$ and some $n$ coordinate rows embed that lattice injectively while decreasing norms. Lemma 3 cancels the remaining determinant factors. The argument gives the translated Gaussian bound itself before introducing ball factors. [Integral-grid Gaussian estimate](wall1_fresh_review.md)

**Choosing a block from the data.** Suppose on a $b$-input block the raw lifts of $s$ witnesses increase the frozen residue rank by $s$. A linear map of rank $s$ kills the frozen residues and sends the witness residues to a basis. Conversely such a map implies the rank increment. One representative per kernel suffices. Allowing every block and kernel costs at most
\[
 M(k,b,s)=\binom{k}{b}{b\brack s}_q,\qquad
 {b\brack s}_q=\prod_{j=0}^{s-1}\frac{q^{b-j}-1}{q^{s-j}-1}.
\]
Smaller supporting blocks are included by padding the map with zero coefficients. This is where selecting an annihilator from the realized flag can be expensive. For example a fixed rank-$t$ residue space in $k$ dimensions lies in only ${k-t\brack s}_q/{k\brack s}_q$ of the codimension-$s$ kernels. The existence of many annihilators by rank-nullity does not give free independent marks on a flag-dependent kernel.

## The width-506 budgets

**Wholly old first hits and terminal planes.** Apply Corollary 4 to the witnesses in Part 243. The frozen objects used in the rank tests are the graph lifts at the *old* cut for the ternary test and the *post-406* cut for the terminal binary test. Let $a=1352/\sqrt3$, $S=(\sqrt2 a)^{1/2}$, $T=52/\sqrt3$, $L_j$ the Part 239 log determinant floors. The following details tighten the numerical union sufficiently to pay for oblique kernels.

* In a wholly old first hit let $s,t,u$ be the three GS lengths. Part 243 gives $s\le S$, $a/S<t\le T$, $tu\le a$, and $s,t,u>20$. Round the three shears to the original 0.01 mesh, costing $101^2\cdot151$ choices. For interval $j/16\le t\le(j+1)/16$, valid radii are $S,(j+1)/16+S/200,16a/j+(S+\sqrt{T^2+S^2/4})/200$. Only $375\le j\le480$ are needed. Sum their products to the power 505, using the common theta upper bound at radius 20. Sum the determinant factors $e^{-3L_{i-1}}$ for $155\le i\le406$. Multiplying by $M(510,4,3)$ gives **less than $4.67\times10^{-20}$**. Increasing four to five costs $1.7390\times10^{-7}$ in this majorant.
* After draw 406, take a Gauss-reduced terminal plane basis with GS lengths $t,u$, $tu\le a$. If $t\le24$, the first point has nonzero quotient label by rank two. Use $B_{505}(24,e^{L_{406}})$ per kernel. Otherwise $24<t\le T$, $u\ge\sqrt3 t/2>20$. Use radii $(j+1)/16,16a/j+T/200$, $384\le j\le480$, and 101 shears. With $M(511,5,2)$ the entire charge is **less than $3.46\times10^{-19}$**. Six instead of five gives a majorant between $3.22\times10^{-10}$ and $3.24\times10^{-10}$.

The ternary bound allows frozen rank one on four inputs, provided the three witnesses add three ranks. The binary bound allows frozen rank three on five inputs if the plane adds two. Integral unimodular changes of witness basis preserve these rank conditions. Every $Z_1$ path with either detection can therefore be charged for less than $3.93\times10^{-19}$ combined. Against the Part 226 unpaid allowance $>4.0203\times10^{-12}$, more than $4.0202996\times10^{-12}$ remains for the complement after this conservative charge. Mixed first hits are covered here only when their terminal plane passes the terminal test. The six- and five-input majorants above measure losses of this union bound. [First-hit geometry](wall1_z1_horizontal.md) · [Residual ranges](wall1_high_codim_sections.md)

**Residual mean score.** On a fixed forced path the projector has the true ambient orientation on agreement. Condition on the independent plant $X$ and apply the Gaussian version of Corollary 4 to the shift $kPX$, with $k$ now denoting plant height. The Part 239 cap moment then bounds the joint mean of all signed summands of nonzero quotient label by $5.26586\times10^{-8}\exp(-505k^2/1921)$ for this kernel. This also bounds the subset left unpaid on each realized summand. Four preassigned linear forms, with arbitrary support, cost less than $4.70\times10^{-7}$ at heights 0–30 together. Across **every** rank-increasing pair of input coordinates at heights 9–30, the charge is below $1.31\times10^{-8}$ after multiplication by $M(512,2,1)$. Including height 8 raises this particular majorant to $1.145\times10^{-6}$, above the entire $5.2408\times10^{-7}$ allowance. Charging the height-9–30 pair class alone leaves $5.1098\times10^{-7}$ for all remaining unpaid summands. Neither coverage by four fixed forms nor the remaining score contribution has been established. [Cap moment and orientation](wall1_score_rejection.md) · [Summand assignment](wall1_height_split.md)

**Additional prefix rejection.** If all 407 lengths exceed 13, then $814e^{-169/12}+222e^{-q^2/12}<0.000623$. At each pre-freeze window take the previous frozen lattice and the raw winner lift. For a fixed test whose value on that lift is nonzero and which kills the previous frozen lattice, use $B_{506}(13,e^{L_{i-1}})$. The sum over the 407 draws is below $4.313\times10^{-196}$ per test. The probability that any length through 13 increases frozen rank on **some block of 38 inputs** is below $3.83\times10^{-8}$. On **39 inputs** it is below 0.0015484, leaving 0.001997829 of the 0.003546229 allowance for score-accepted rejections without such a small winner. On 40 inputs the same majorant exceeds 60.94. A small winner can have its residue in the old span on every small block. This calculation also includes old tiny winners using only physically touched coordinates when their residue increases rank.

A stronger rejection bound allows different lengths on different draws. Take $r_i=\min(16,10.89+0.095(407-i))$. The deterministic sum $\sum_i2e^{-r_i^2/12}+222e^{-q^2/12}$ is below 0.000619. Hence every rejection has some $s_i\le r_i$. Across all draws the probability of such a winner which increases rank on some block of **46 inputs** is below $4.949\times10^{-6}$. This uses $M(512,46,1)\sum_i B_{506}(r_i,e^{L_{i-1}})$. It leaves at least 0.00354128 for the score-accepted rejections having no detectable threshold violation. The same calculation on 47 inputs gives a majorant above 0.163. The varying cutoffs bound the rejection event and allow some earlier lengths above 13. They do not bound the entire class of length-13 winners on 46 inputs.

**Long winners and $Z_{\rm rem}$.** The congruence section supplies an exact product bound for a joint event at one draw. At its old cut fix $H$ on the old inputs, form $M,K_0,G$ as in Lemma 3, and append the original new column. At fresh coefficient one the physical vertical length is one. For each old label $b$ the old part of this layer is a coset of $M$ in $K_b$. Its random translate is the image of $U_{\rm new}+Ub$, up to the fixed offset of Lemma 3. Let $p_b(B)$ be the fraction of the $|G|$ translates in $K_b/M$ missing the closed radius-$B$ ball about the origin. For affinely independent $b_0,\ldots,b_r$, the augmented coefficient vectors $(1,b_j)$ are independent. Conditional on the exposed data these $r+1$ translates are independent. On old agreement every one of their points gives a full candidate. Thus, for an exposed-data threshold $R\ge1$,
\[
 \Pr(\text{old agreement and }s_i>R\mid A|_W)
 \le \prod_{j=0}^r p_{b_j}(\sqrt{R^2-1}).
\]
One may take $R=1.10(D_0/V_{506})^{1/506}$ on the range where it is at least one. This uses the current radius and requires no intervening projections. For $r=2$, three fractions at most .3914 give a product below .06. The fractions refer to the index-$q^r$ section, whose physical determinant on agreement is $q^rD$. Dropping this index would evaluate a different void.

Given the full incoming history the old hidden marks are already determined. Only $U_{\rm new}$ remains random, so the three marginal void bounds do not multiply in that filtration. Even in a finite group with identical miss set of density $p$ and identical fixed offsets, the intersection over one common uniform translate has probability $p$, which can exceed $p^3$. The algebra gives no uniform .3914 bound on the section fractions, and an unconditional joint mean cannot be substituted for a conditional long-winner probability along the path. The Part 243 compensator test still needs $\Pr(\sum_{i=1}^{405}p_i>48.6)\le7.6\times10^{-12}$ for the actual one-draw probabilities $p_i$, or a separate bound of $2.72513\times10^{-11}$ on the unpaid small-scale branch. No new unconditional numerical charge for that branch follows here. [Conditional targets and direct windows](wall1_raw_graph_winner_cap.md) · [Compensator audit](wall1_fresh_review.md)

## Reproduce the numerical bounds

The checker runs in the repository's scripts directory and uses its audited log-floor and theta helpers. It is embedded to keep the worktree change to the requested new file.

```sh
(cd docs/research/scripts && awk '/^```python$/{p=1;next} /^```$/{p=0} p' ../wall1_generalized_deletion.md | python -B -)
```

```python
from math import comb, prod
from mpmath import iv
from wall1_hermite_budget import log_floors, log_theta

iv.dps = 50
I, log, exp, sqrt = iv.mpf, iv.ln, iv.exp, iv.sqrt
q = 3329

def check(name, x, low, high):
    assert I(low) < x < I(high), (name, x)
    print(name, x)

def vol(n):
    half = I(n)/2
    return iv.pi**half / iv.gamma(1+half)

def sparse(i, z, radius_sq):
    n = 506-z
    return (comb(106,z)*vol(n)*(radius_sq+I(n)/4)**(I(n)/2)
            / I(q)**(401-i))

r0 = sqrt(q*q-1)
for t,z,low,high in [(2,6,'.00504','.00505'), (3,10,'3.19e-6','3.20e-6'),
                     (4,14,'1.43e-9','1.44e-9'), (5,17,'1.20e-11','1.21e-11')]:
    missed = 4*I(q)**(401-t)/(vol(506)*r0**506)
    check(f'initial support, t={t}, z={z}', missed+sum(sparse(i,z,q*q)
          for i in range(1,t+1)), low, high)
mu = vol(506)*r0**506/(I('2.09')*I(q)**400)
check('full initial support lower bound',mu/(1+mu)-sparse(1,1,q*q-1),'.03694','.03695')
check('sample period lower bound',1-sparse(1,0,q*q),'.7298','.7299')

def masks(k,b,r):
    # Number of blocks times the Gaussian binomial [b choose r]_q.
    return comb(k,b)*(prod(q**(b-j)-1 for j in range(r))
                      //prod(q**(r-j)-1 for j in range(r)))

L = log_floors()
n = 505
unit = sqrt(2*iv.pi/n)
a = I(1352)/sqrt(3)
S, T = sqrt(sqrt(2)*a), I(52)/sqrt(3)
assert 375 < 16*a/S < 376 and 480 < 16*T < 481
assert sqrt(3)*a/(2*S) > 20
c = I(n)/2 + n*(log(unit)+log_theta(20*unit))
ds = S/200
du = (S+sqrt(T*T+S*S/4))/200
three = I(0)
for j in range(375,481):
    low, high = I(j)/16, I(j+1)/16
    product = S*(high+ds)*(a/low+du)
    three += exp(3*(c-L[405])+n*log(product))
three *= 101**2*151*sum(exp(3*(L[405]-L[i-1])) for i in range(155,407))
check('four inputs, ternary',three*masks(510,4,3),'4.65e-20','4.67e-20')
check('five inputs, ternary majorant',three*masks(510,5,3),'1.73e-7','1.75e-7')

def ball(n, radius, floor):
    z = radius*sqrt(2*iv.pi/n)
    return exp(I(n)/2+n*(log(z)+log_theta(z))-floor)

two = ball(505,I(24),L[406])
for j in range(384,481):
    low, high = I(j)/16, I(j+1)/16
    two += 101*exp(2*(c-L[406])+n*log(high*(a/low+T/200)))
check('five inputs, terminal plane',two*masks(511,5,2),'3.45e-19','3.46e-19')
check('six inputs, terminal majorant',two*masks(511,6,2),'3.22e-10','3.24e-10')

pref = sum(ball(506,I(13),floor) for floor in L[:407])
for b,low,high in [(38,'3.82e-8','3.83e-8'),(39,'.0015482','.0015484'),
                   (40,'60.94','60.96')]:
    check(f'small winner, {b} inputs',pref*masks(512,b,1),low,high)
assert 814*exp(-I(169)/12)+222*exp(-I(q*q)/12)<I('.000623')
radii = [min(I(16), I('10.89')+I('.095')*(407-i)) for i in range(1,408)]
strip_sum = sum(2*exp(-r*r/12) for r in radii)+222*exp(-I(q*q)/12)
check('varying cutoff prefix charge',strip_sum,'.0006187','.000619')
weighted = sum(ball(506,r,floor) for r,floor in zip(radii,L))
check('threshold violation, 46 inputs',weighted*masks(512,46,1),'4.948e-6','4.949e-6')
check('threshold violation, 47 inputs',weighted*masks(512,47,1),'.163','.164')

def score(start):
    return I('5.26586e-8')*sum(exp(-I(505)*k*k/1921) for k in range(start,31))
check('four fixed score tests',4*score(0),'4.69e-7','4.70e-7')
check('pair score at heights 9 to 30',masks(512,2,1)*score(9),'1.30e-8','1.31e-8')
check('pair score at heights 8 to 30',masks(512,2,1)*score(8),'1.14e-6','1.15e-6')
assert I('.3914')**3 < I('.06')
```

## Audit

**Verdict.** The generalized deletion bound, the simultaneous support estimate, and all four numerical charges hold for the unconditioned marginal restart and the stated rank-increase events. The embedded interval checker passed. The conditional ceiling for $Z_{\rm rem}$ remains open.

**Agreement and independence.** In Lemmas 2–3, agreement means agreement of the successive signed winners, including their lengths. On $h(L(A)\cap F_f)=0$, each earlier winner has a zero-label integral lift in its own prefix, so the restricted comparison contains the full winner and inherits its tie order. Conversely, on signed-winner agreement one may take a forced lift at every step. These lifts generate $L(A)\cap F_f$ because at each step the primitive shortest vector generates the projected lattice on its line. This justifies the label of a projected point and $[PL(A):PL_0]=q^r$ on the counting event. Equality of the final real spans alone would leave this index undetermined.

Conditional on $A|_W$, the forced projector is fixed and $U$ is uniform on the space of linear maps. Evaluation on independent labels gives independent uniform sample vectors. Their images are uniform in $K_0/M$ by surjectivity. The count retains the exposed determinant gate and drops the agreement indicator before averaging. The identity $[K:K_0]=q^r/c$ gives $c/(|G|\det K)=q^r/\det M$, including when different labels project to the same grid. On a block, the witnesses are independent modulo the frozen residues exactly when their classes can be sent to a basis by a quotient of rank $s$. Maps with the same kernel differ by an invertible change of labels. Thus $\binom{k}{b}{b\brack s}_q$ covers adaptive choices of both the block and the kernel, including overlapping detections.

**Support and rank.** For the first two draws the signed tie order fixes the sample-axis comparison up to the first nonperiod winner. Six untouched inputs at a late cut require either no early nonperiod winner or one vanishing on some six of the first 106 inputs. In the forced comparison at draw two, independent input residues give independent incidences against the 399 remaining uniform rows, while proportional inputs of distinct projective candidates give incompatible incidences. The miss bound and the two sparse-winner charges together are below $0.005042179$. Persistence under extension of the real span therefore gives probability greater than $0.99495782$ simultaneously at every specified cut. Separately, saturation makes $S/qS$ an $f$-dimensional subspace of the ambient residue space. Its syndrome kernel has dimension $f-(400-d)$ and maps injectively to the inputs because a graph residue is determined by its input. Subtracting from $105+f$ gives the exact quotient dimension $505-d\ge105$ for every flag.

**Numerical checks.** The entries bound the computed majorants, rounded upward.

| Detected contribution | Upper bound |
|---|---:|
| Wholly old first hit, three ranks on four inputs, draws 155–406 | $4.657713\times10^{-20}$ |
| Terminal plane, two ranks on five inputs, after draw 406 | $3.453819\times10^{-19}$ |
| Residual mean score, some input pair, heights 9–30 | $1.305648\times10^{-8}$ |
| Varying length-cutoff violation, some 46-input block, draws 1–407 | $4.948145\times10^{-6}$ |

For the ternary count, evaluating the shear and radius sum separately from $\sum_{i=155}^{406}e^{-3L_{i-1}}$ and using the four-input kernel count $q^3+q^2+q+1$ gives the same $4.6577120464\ldots\times10^{-20}$. The binary count uses $L_{406}$ and the plane present at that cut. A rank-two label map on the plane sends the first reduced basis vector to a nonzero label, so the single-vector charge covers $t\le24$ even for a replacement plane. For the score, the independent plant and forced projector fix the translate before the marks are averaged, and $M(512,2,1)=\binom{512}{2}(q+1)$ pays for the pair and its kernel. For the prefix, the deterministic strip sum is below $0.000618780<0.000623$. Here “every rejection” means every **prefix** rejection $S^+>0.000623$. The 46-input charge covers such rejections with a detectable violation and also bounds their score-accepted subset. The remaining allowances are budgets for the complementary events.

**Long winners.** For fixed $H$ and affinely independent labels fixed given $A|_W$, the full-rank augmented coefficient matrix makes the chosen layer displacements jointly uniform in $G^{r+1}$. Their joint miss probability equals the displayed product. Old agreement and a long winner imply all these misses, giving the stated inequality. Conditional on the full incoming columns, the offsets from $Ub_j$ are fixed and all translates share the one new column. The individual void fractions and the required upper tail for the actual compensator remain unbounded by this calculation.
