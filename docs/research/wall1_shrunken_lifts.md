# Shrunken raw lifts of an inherited minimum

Under the unconditioned width-506 restart, the probability of the shrunken-lift remainder differs from the probability of the **whole inherited event** by less than $2.450981\cdot10^{-6}$. The shrink condition is a lower bound on a distance in a kernel lattice. Counting arbitrary raw vectors that lose this much length counts infinitely many lifts of each qualifying quotient point. Even for an independent uniformly oriented subspace of the same dimension, losing this fraction of squared length is typical for a fixed vector. The selected minimum and its old plane witness are therefore essential to interpreting the proposed count. The $10^{-3}$ bound remains open.

There is also a correction to the reading of the depth-two experiment. The 16 signed-unit prefixes contribute exactly $(16q-38)/q^5$ for every prime $q\ge19$. At $q=1009$ the single prefix $(2,2,2,2)$ adds another $1006/q^5$. More generally, constant prefixes give a lower bound of order $q^{-15/4}$ on the full toy event. The signed-unit share tends to zero along the primes, despite accounting for every hit on the five reported primes. The [Part 158 research note and audit](wall1_selected_scaling.md) already distinguish the subfamily identity from the exhaustive counts.

## 1. The shortest lift and the selected history

Use the marginal restart for plain LWE $(511,512,3329)$ and the ambient signed tie rule. The probability here is over the design. The independent CBD(3) plant and draw 407 do not enter. On a horizontal win at selection 406, let $T$ be the span of the 406 removed directions in the old 910-dimensional raw space, $P$ the orthogonal projection onto its complement, $\mathcal M$ the raw graph lattice on the first 510 input columns, and $K=\mathcal M\cap T$. Write $x$ for the designated inherited minimum and $t=\|x\|$. The event $H_{\rm old}$ includes the two horizontal comparisons, $1<t\le\sqrt{1+c^2h^2}$ and an old nonzero witness of length strictly below $ch\,t^{-1/505}$ after removing $x$. Here $c=0.954$ and $h$ is the Gaussian-heuristic length of the full retained quotient. [Part 151, definitions](wall1_penultimate_tail.md) · [Part 155, §§1 and 3](wall1_inherited_witness.md)

**Proposition 1.** For any $z\in\mathcal M$ with $Pz=x$, put $d_K(x)=\operatorname{dist}((I-P)z,K)$. This distance is independent of $z$, and
$$
\min_{Pz'=x,\ z'\in\mathcal M}\|z'\|^2=t^2+d_K(x)^2.
$$
Consequently the remainder is exactly $A=H_{\rm old}\cap\{d_K(x)^2>11t^2/25\}$. In particular,
$$
0\le\Pr(H_{\rm old})-\Pr(A)
\le 1/408000+2^{-53.8086}<2.450981\cdot10^{-6}.
$$

*Proof.* The lifts form $z+K$. Their components in $T$ form $(I-P)z+K$, so the choice of lift leaves the distance unchanged. This discrete translate attains its minimum distance to the origin. Pythagoras gives the identity, and $(6/5)^2-1=11/25$ gives the strict threshold. Equality belongs to the near-lift event. The probability difference is exactly the joint near-lift probability bounded in Part 155. Its displayed majorant lies in $(2.45098039222024,2.45098039222026)\cdot10^{-6}$ by outward-rounded arithmetic. Rounding it down to $2.45\cdot10^{-6}$ would lose the certified inequality. [Part 155, Audit](wall1_inherited_witness.md)

One can retain this distance in the exact Part 108 law. Fix the complete prefix $S$ before draw 406, force the old signed winner $v$, then force the old signed minimum $x$ in its quotient $N$. This fixes $T,K,x$ and $t$ before the draw. Use $J(S)$ for Part 155's length and old-witness tests, $H$ for the finite mark, $f$ for its forced projection, and $b_M,b_N$ for the respective horizontal-win indicators. Then
$$
\Pr(A\mid S)=
\mathbf1_{\{d_K(x)^2>11t^2/25\}}J(S)
\frac1{|H|}\sum_{u\in H} b_M(u)b_N(fu).
$$
Indeed, on the first horizontal win the forced quotient is the actual quotient and the second comparison uses the same mark $u$. When both comparisons pass, the forced old minimum is the designated one and the old witness test is exact. Averaging over the single uniform mark proves the formula, including signed ties. If only the projected state is stored, the raw kernel need not be available. Here $S$ includes the raw prefix. [Part 108](wall1_first_tour.md) · [Part 155, equation (1)](wall1_inherited_witness.md)

## 2. What total shrinkage says about correlations

Let $e_1,\ldots,e_k$ be unit vectors along the successive orthogonalized winners, embedded in the final old ambient space by zero extension. They are orthonormal. For a fixed raw lift $z$,
$$
\|z\|^2-\|Pz\|^2=\sum_{i=1}^k |\langle z,e_i\rangle|^2.
$$
Thus $\|z\|>6\|Pz\|/5$ is exactly the condition that this sum exceeds $11\|z\|^2/36$. In particular the largest squared correlation with the normalized lift exceeds $11/(36k)$. The identity alone allows the loss to be spread over all $k$ directions.

**Multiplicity obstruction.** Fix any nonzero quotient point $x=Pz$ and any nonzero $w\in K$. All $z+n w$, $n\in\mathbb Z$, project to $x$. Their norms tend to infinity as $|n|$ tends to infinity, and the fraction of squared length lost tends to one. Hence a raw-vector count without a choice of representative or an upper truncation has infinite multiplicity at every such point, even if $x$ also has a lift of length $t$. This follows directly by expanding $\|z+nw\|^2$. A shortest representative removes this multiplicity, but it depends on the realized $K$. Part 108 makes each *new mark* uniform given the past. Conditioning further on which height wins restricts that mark to the winning subset. At height one, the Voronoi representatives on that subset have the corresponding restricted law. There is no independence statement for the correlations of a shortest raw representative chosen from the completed history. [Part 142, Theorem B and audit](wall1_dual_cusp.md) · [Part 154, winner comparison](wall1_winner_exchange.md)

**Independent-subspace check.** For a fixed nonzero $z\in\mathbb R^{910}$ and an independent rotation-invariant 406-dimensional $T$, the probability that $\|z\|\le6\|Pz\|/5$ lies in $(1.57391767055,1.57391767057)\cdot10^{-10}$. This computes only the angular test on one lift. It contains no bound on $t$, no minimum over lifts, and no plane test.

*Proof.* By rotational invariance the squared fraction lost has the law $X/(X+Y)$ for independent sums of squares of 406 and 504 standard normal variables. Indeed normalizing a standard Gaussian gives a uniform unit vector. The two sums are independent gamma variables of shapes 203 and 252 with common scale, so changing variables to their sum and ratio gives a beta density of parameters $(203,252)$. The event is loss at most $11/36$. Integrating the density gives the exact probability
$$
36^{-454}\sum_{j=203}^{454}\binom{454}{j}11^j25^{454-j}.
$$
The binomial tail as a function of its success probability vanishes at zero and differentiates to the beta density, which proves the integration identity. Evaluating the integer numerator first and enclosing the division gives the stated interval. This independent rotation model gives no comparison theorem for the selected restart.

## 3. Exact depth-two examples

Use Part 158's $(m,j,T)=(1,3,2)$ family, with one output, four inputs through the first selection and a fifth input at the second selection. Write $p=(p_1,\ldots,p_4)$ for the prefix and $a$ for the fifth column. The raw congruence in coordinates $(b,y_1,\ldots,y_5)$ is $b\equiv p\cdot y_{1:4}+ay_5\pmod q$. The first selection uses $y_5=0$. The next winner and its quotient minimum must both be horizontal in $y_5$. For each row below the first three forced squared lengths are $2,3/2,4/3$, in order, and the shortest raw lift of the third has squared length two. Thus $\min\|z\|^2/t^2=3/2>36/25$. The quotient determinant is $q/\sqrt3$ after the first two wins, since their lengths have product $\sqrt3$.

| Prefix | Number of prefixes | Fifth columns failing either horizontal comparison | Squared length of an old witness |
|---|---:|---|---:|
| Signed units, at most one negative | 5 | $0$ | $5/4$ |
| Signed units, at least two negative | 11 | $0,\pm1$ | $5/4$ |
| $(2,2,2,2)$ | 1 | $0,\pm2$ | $17/4$ |

**Proposition 2.** The first two rows give exactly $(16q-38)/q^5$ for every prime $q\ge19$. The third gives exactly $(q-3)/q^5$ for every prime $q\ge1009$. In particular the full shrunken event at $q=1009$ has probability at least $17112/1009^5$. This is a lower bound from 17 prefixes.

*Proof and reproducible finite enumeration.* To check the signed ties, let $B$ consist of the 72 signed integer vectors in dimension six of squared norm one or two. They are $\pm e_i$ and $\pm e_i\pm e_j$ for $i<j$. For a list $L$ of orthogonal projected winners, let $Q_L$ project off their span. In the following enumeration, minimum means lexicographic minimum of the pair (squared norm, signed ambient coordinate tuple), excluding zero projections. Arithmetic on the projections is rational.

```text
old  = {z in B : y5 = 0 and b = p · y[1:4] mod q}
full = {z in B : b = p · y[1:4] + a*y5 mod q}
u = signed_min(old)
v = signed_min(Q_[u](old))
x = signed_min(Q_[u,v](old))
accept both comparisons exactly when
    v = signed_min(Q_[u](full)) and x = signed_min(Q_[u,v](full))
```

Here $y[1:4]$ denotes all four prefix inputs. For each of the 16 sign tuples it suffices to check $a=0,\pm1$ and one residue outside this set. For $(2,2,2,2)$ check $a=0,\pm1,\pm2$ and one outside. Indeed every point of $B$ with $y_5\ne0$ has $y_5=\pm1$ and at most one other signed unit entry. Its congruence requires $a\in\{0,\pm1,\pm p_i:1\le i\le4\}$. The old membership test and each of these exceptional-residue tests are unchanged across the indicated primes because the bounded integer differences do not wrap modulo $q$. Enumerating the finite sets above gives the three rejected-residue lists in the table. In every row $x$ has a preimage of squared norm two, and the old graph contains no unit.

To see that the short-vector enumeration is exhaustive for these selections, round a lift by subtracting nearest integer multiples of raw lifts of the preceding winners, in reverse order. Each rounded coefficient contributes at most one quarter of the corresponding projected squared length. There is a first candidate of squared length two. At the next two stages, the displayed candidates of squared lengths $3/2$ and $4/3$ give raw upper bounds $3/2+2/4=2$ and $4/3+(2+3/2)/4<3$ on representatives of every competitor, including ties. All squared raw norms are integers. For a signed-unit prefix, the same enumeration in the old graph at the fourth stage yields squared length $5/4$, with raw bound $5/4+(2+3/2+4/3)/4<3$. On the all-twos prefix the three selected lines span the differences among the four input axes: all old points of squared norm two are signed differences of these axes, and the enumerated three images are independent. The old vector $(2,1,0,0,0,0)$ therefore projects to $(2,1/4,1/4,1/4,1/4,0)$ after those lines are removed. Its squared length $17/4$ suffices for the existence test.

It remains to verify the strict plane gate. Write $h=(2q/(\sqrt3\,\pi^2))^{1/4}$ and $t=\sqrt{4/3}$. Both squared thresholds increase with $q$. Outward interval arithmetic gives the following enclosures.

| $q$ | $1+(0.954h)^2$ | $(0.954h)^2t^{-1/2}$ |
|---:|---:|---:|
| 19 | $(2.35693,2.35694)$ | $(1.26276,1.26277)$ |
| 1009 | $(10.88842,10.88843)$ | $(9.20221,9.20222)$ |

The first row admits $t$ and the witness of squared length $5/4$. The second admits $t$ and $17/4$. Each accepted design has mass $q^{-5}$. The signed-unit numerator is $5(q-1)+11(q-3)=16q-38$ and the all-twos numerator is $q-3$. The prefix sets are disjoint. The rational comparisons were rerun in scratch storage at $q=19,23,1009$ for signed units and at $q=1009$ for the all-twos prefix. Interval calculations used at least 50 decimal digits.

**Corollary 3 (the signed-unit share tends to zero).** Put $L(q)=\lfloor q^{1/4}/2\rfloor$. For primes $q\ge1009$ the full depth-two toy probability satisfies
$$
 \Pr(A_{\rm toy})\ \ge \frac{16q-38+(L(q)-1)(q-3)}{q^5}.
$$
In particular the right side is asymptotic to $\tfrac12 q^{-15/4}$, while the signed-unit contribution is asymptotic to $16q^{-4}$.

*Proof.* Take each constant prefix $(b,b,b,b)$ with $2\le b\le L(q)$. The residues $0,\pm1,\pm b$ are distinct. In the old graph the candidates of squared norm two are exactly the signed differences between the four input axes, as for $b=2$. The finite comparison in Proposition 2 has the same coordinate tuples in each corresponding residue class. In fact a nonzero fresh coordinate in the short ball can occur alone when $a=0$, with the output axis when $a=\pm1$, or with one of the old input axes when $a=\pm b$. In each case the signs in the congruence agree with those for the corresponding residue at $b=2$. Thus the rejected residues are exactly $0,\pm b$ and the shrink test still passes. Projecting $(b,1,0,0,0,0)$ off the same three lines gives an old witness of squared length $b^2+1/4$.

The squared plane cutoff is $K_0\sqrt q$, where
$$
 K_0=(477/500)^2\sqrt{2/(\sqrt3\,\pi^2)}\,(4/3)^{-1/4}
 \in(0.28969892037,0.28969892038).
$$
Since $q\ge1009$, we have $b^2+1/4\le\sqrt q/4+1/4<0.26\sqrt q<K_0\sqrt q$. The length gate already passes at 19. Summing the $q-3$ accepted draws for each distinct constant prefix proves the bound. Dividing the signed-unit mass by this lower bound and taking $q\to\infty$ proves the share tends to zero. This estimates the share without assuming that constant prefixes exhaust the event. As separate scratch checks, all actual fifth residues on the signed-unit prefixes at 19 and 23 gave 266 and 330 hits respectively. At the toy prime 10007 the exceptional-residue comparisons for each $b=2,3,4,5$ rejected exactly $0,\pm b$.

## Remaining gap

**Conjecture (open).** At width 506, $\Pr(A)\le10^{-3}$. The exact expectation in §1 still requires the joint law of the shortest-lift distance, the old witness and the selected comparisons. The toy calculation disproves one extrapolation across moduli already at fixed rank. It gives no upper bound on other prefixes, or on this joint law at width 506. Part 155's upper bound $1-2^{-4435.956}$ for the whole inherited event remains applicable to $A$. No smaller width-506 upper bound is established here.

## Audit

**Verdict — SOUND.** The distance identity gives exactly the shrunken remainder of Part 151(a). The toy counts and the vanishing signed-unit share hold. No correction to this note is required.

**Width 506.** On the two horizontal wins, the old lifts of the designated $x$ form one coset of the rank-406 kernel $K$. Minimizing the squared norm in that coset gives $t^2+d_K(x)^2$. Thus equality at $d_K(x)^2=11t^2/25$ is charged to Part 155's near-lift event. Its bound of $2.450981\cdot10^{-6}$ applies to the joint probability removed from $H_{\rm old}$. Both horizontal comparisons in the conditional expression use the same mark, and the old-plane inequality remains strict, as in Parts 120 and 151. Translating by arbitrary multiples of one nonzero kernel element gives infinitely many long representatives even at a point with a short lift. Minimizing over the coset removes that counting ambiguity while retaining dependence on the selected kernel. A shortest lift can have ties, but its length is unique. The independent-subspace binomial sum and the numerical bound on the near-lift probability both reproduce. The target $\Pr(A)\le10^{-3}$ remains open.

**Independent enumeration.** A scratch implementation traversed all $19^4$ and $23^4$ ordered old prefixes. It computed the signed projected minima by integer Gram updates in the old raw ball of squared radius 14. At every stage used, reverse rounding placed a representative of every potential shorter vector or tie at squared norm strictly below 15. The shrink test compared the least raw squared norm among lifts of the designated signed vector. After the length and strict old-witness tests, precisely the 16 signed-unit prefixes remained at each prime. A separate rational projection calculation resolved both comparisons against the fifth column. Five prefixes rejected only $0$ and eleven rejected $0,\pm1$, giving **266 and 330 hits for the full toy event**. At $q=1009$ the signed-unit count was $16106$ and $(2,2,2,2)$ rejected exactly $0,\pm2$, contributing $1006$ more. The resulting $17112$ is a lower bound on the full numerator there.

**Strict cutoffs and scaling.** Independent 70-decimal-digit interval arithmetic reproduced both columns of the cutoff table and the enclosure for $K_0$. In particular the squared plane thresholds exceed $1.26276>5/4$ at 19 and $9.20221>17/4$ at 1009. For every $2\le b\le L(q)$ the old short vectors are input-axis differences, and a fresh short vector can occur only at $0,\pm1,\pm b$. The signed tuples in those classes agree with the all-twos comparison. Its rejection list therefore transports to $0,\pm b$, while $b^2+1/4<0.26\sqrt q$ certifies the strict old-witness gate. There are $L(q)-1$ disjoint such prefixes, each with $q-3$ hits. Their contribution is asymptotic to $\tfrac12 q^{-15/4}$. Dividing the exact signed-unit mass by this lower bound gives an upper bound asymptotic to $32q^{-1/4}$ on its share of the full event. This also fixes the scope of the Part 158 index entry: the all-prime identity counts the signed-unit subfamily.
