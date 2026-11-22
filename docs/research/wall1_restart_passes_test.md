# Does the width-506 restart pass the shifted-ball test?

**The cited first moments do not prove a rejection probability of 0.005.** For the exact R49 score, Markov's inequality would give this result from a mean at most $6.469\cdot10^{-7}$. Already at height zero, that mean would imply that the *terminal* minimum is at most 26 with probability below $4.318\cdot10^{-7}$. Part 151 controls a *penultimate* minimum through physical radius 1.1981. Part 161 reaches a physical radius above 31 on its good histories, but counts positive-height vectors of the incoming window. A short horizontal vector can survive projection without appearing in that count. The numerical overlap of radii does not supply the missing implication.

## The score and the two probabilities

Use plain LWE $(511,512,3329)$, width $b=506$ and retained rank $d=505$. Let $(E,H)$ be the final embedded horizontal block selected from the design, $P$ the orthogonal projector onto $E$, and $X$ an independent product CBD(3) vector. Write $y=PX$, $Z=\|y\|^2$, $a=959.5$, $B=1+a$, and $\tau=0.00012938$. In physical length units the score is

$$
 C(E,H)=\sum_{k=0}^{30}\sum_{v\in H\setminus\{0\}}
 \Pr_X\!\left[Z\le a,\ \|v+ky\|^2+k^2\le 1+Z\mid E,H\right].
$$

The sum counts both signs at height zero, all integer multiples, and equality at the boundary. On the cap, a competitor can be signed to have height between 0 and 30. With $v=0$ the only nonzero points as short as the plant are its two signs. Thus the conditional probability of a competing line is at most $\Pr_X(Z>a)+C(E,H)$. To check the cap, $\mathbb E e^{\langle t,X\rangle}\le e^{3\|t\|^2/4}$ follows from $\cosh(u)\le e^{u^2/2}$ for each half-sign. Gaussian integration on $E$ gives $\mathbb E e^{sZ}\le(1-3s)^{-d/2}$ for $0<s<1/3$. At $s=(1-3d/(2a))/3$ the cap bound is $\exp[(d/2)(1+\log u-u)]<0.00047835048014$, where $u=2a/(3d)$. Consequently every accepted block has terminal failure below $0.000607731$. [R49, §4](wall1_test_acceptance.md) · [Fixed-block estimates and audit](wall1_nonintegral_classes.md)

For the separate probability over designs, $\delta_{\rm restart}=\Pr_{\rm restart}(C>\tau)\le\min(1,\mathbb E_{\rm restart} C/\tau)$. If a procedure actually tests a majorant $U\ge C$, its rejection event is $U>\tau$, which requires control of $U$ or of the additional rejections. Even an exact mean for $C$ would only control the exact-score test by this argument. The prefix lift in Part 47 is another event. [Restart hypotheses and audit](wall1_restart_certificate.md)

## A necessary terminal count at height zero

Let $N_H(r)=\#\{0\ne v\in H:\|v\|\le r\}$. On $675\le Z\le a$, every vector counted by $N_H(26)$ contributes at height zero because $26^2=676$. Conditional on any output, $\mu=\mathbb E Z=757.5$ and $\operatorname{Var}Z\le 2272.5$. Indeed, a CBD(3) coordinate has variance $3/2$ and fourth cumulant $-3/4$, by adding the cumulants of six half-signs. Expansion of the quadratic form gives $\operatorname{Var}Z=(9/2)\operatorname{tr}(P^2)-(3/4)\sum_j P_{jj}^2$. Cantelli's inequality and the cap estimate give

$$
 \Pr_X(675\le Z\le a\mid E,H)
 \ \ge\ \frac{(757.5-675)^2}{2272.5+(757.5-675)^2}-0.00047835048014
 \ >\ 0.74921186.
$$

Hence $C\ge0.74921186\,N_H(26)$. A nonempty count has at least two points. Such a block necessarily rejects, and the proposed mean bound would require

$$
 \Pr_{\rm restart}[\lambda_1(H)\le26]
 \ \le\ \frac{6.469\cdot10^{-7}}{2(0.74921186)}
 \ <\ 4.318\cdot10^{-7}.
$$

This is a **necessary consequence of the proposed first-moment proof**. A direct proof of $\delta_{\rm restart}\le0.005$ would only imply that this minimum event has probability at most 0.005. Conversely even perfect control of the minimum at 26 would leave the other radii and heights in $C$. [Part 134, Theorem 2 and audit](wall1_breakthrough_r1.md)

## Physical radii and the stage at which they are measured

In the marginal restart, start from the unconditioned uniform $400\times105$ graph. Let $D_i$ denote the covolume after suffix selection $i$. The graph appends have physical height one, so the window at draw $i$ has covolume $D_{i-1}$ and $D_i=D_{i-1}/s_i$ for the selected primitive vector length $s_i$. Use $V_j$ for the Euclidean unit-ball volume. [Part 108](wall1_first_tour.md) · [Part 117](wall1_idea_round2.md)

| Quantity | Lattice and units | Published estimate or derived scale |
|---|---|---|
| Part 147/151, $t$ | $\lambda_1$ after draw 406, rank 505, physical length | The flag majorant for $\Pr(t\le u)$ crosses $0.009$ at $u=1.19806583\ldots$ and 1 at $1.20927112\ldots$. |
| Part 161, $wg$ | Before selection 406, rank 506, $g=(D_{405}/V_{506})^{1/506}$ | At $w=0.990$, the conditional expected positive-height candidate count is below $0.008801064$ when $g<203.888$. The physical cutoff is at least $31.86368$. |
| R49, $r_0=\sqrt B$ | After draw 407, rank 505, $h=(D_{407}/V_{505})^{1/505}$ | $r_0=30.99193443\ldots$. The restart determinant floor gives $r_0/h<0.974974$. At the full-row model $h=54.95252664\ldots$ this ratio is $0.563977$ rounded. |

The determinant floors in the table can be checked without a shape assumption. Since $s_i\le\min(q,\sqrt{56.2142}\,D_{i-1}^{1/506})$, start at $L_0=400\log q$ and iterate $L_i=\max(L_{i-1}-\log q,(505/506)L_{i-1}-\tfrac12\log 56.2142)$. Then $\log D_i\ge L_i$. The rank-506 GH floor from $L_{405}$ is in $(32.18553678,32.18553679)$. The rank-505 floors from $L_{406}$ and $L_{407}$ are in $(32.02610188,32.02610189)$ and $(31.78746500,31.78746501)$, respectively. Thus 1.1981 amounts to less than 0.03742 penultimate GH, and the maximum terminal ball radius is about 25.87 times the Part 151 physical crossing. The degree-506 envelope $u^{506}S_-$ in Part 151, with $\log_2 S_-\simeq-138.7137$, already reaches one at $u\simeq 2^{138.7137/506}$. Extrapolating the flag sum also loses its hypothesis $u\max_l B_l<q$. The crossing is a property of the upper bound. [Parts 147 and 151, including audits](wall1_penultimate_tail.md) · [Unit-cutoff proof](wall1_uncovered_lines.md)

Part 161 counts vectors of $W=(M,0)+\mathbb Z(\widetilde U,1)$ with *positive fresh-coordinate height*. At each eligible height multiplication permutes the finite group of possible marks $U$; this is what permits the conditional average. An old vector of $(M,0)$ has height zero for every mark. If the selected line is perpendicular to it, the vector survives at its full length in the quotient. Moreover a quotient vector is a coset modulo the selected line, and a reduced representative can still have a nonzero component along that line. Its window length can exceed its quotient length. Neither the inherited vectors nor the shortened representatives are covered by substituting the terminal radius in Part 161. The height $k$ in R49 is the **plant height**, independent of the label “positive height” for an incoming graph column. Parts 120 and 147 do count some quotient witnesses, but use primitive unoriented lines, winner gates and their own cutoffs. R49 counts points with multiplicity. [Part 161, Theorem 2 and audit](wall1_band_plane_hits.md) · [Terminal plane count](wall1_plane_count.md)

## What shifts change

For $k>0$ the capped ball has center $-ky$ and radius at most $\sqrt{B-k^2}$. A point it counts need only satisfy $\|v\|\le k\sqrt a+\sqrt{B-k^2}$. This enclosing radius is $61.95159\ldots$ at height one and $937.05208\ldots$ at height 30. A small ball about its own center therefore does not justify truncating a centered count at $30.992$. The larger radii describe a geometric enclosure, with no claim about the probability mass near their endpoints.

An exact check illustrates why even the entire centered counting function leaves information out. In rank one take $H=2\mathbb Z u$ in the plane, $a=1.9$, and $X$ with two independent CBD(3) entries. For the unit directions $u=(1,0)$ and $u=(3,4)/5$, every $N_H(r)$ is identical. Their scores are respectively $1920/4096$ and $462/4096$. Indeed only height one contributes: on the cap, exactly one of $\pm2u$ qualifies when $1\le|\langle u,X\rangle|\le\sqrt{1.9}$. Summing $\binom6{i+3}\binom6{j+3}$ over the 49 pairs $(i,j)\in[-3,3]^2\cap\mathbb Z^2$ gives those numerators. This example tests determination of the score by intrinsic lengths. A uniform upper bound using additional estimates is logically possible. [Physical orientation and class data](wall1_aliasing.md)

For fixed $E$ and independent intrinsic Haar $H$ of covolume $\Delta$, Siegel integration averages each translated nonzero count to its ball volume divided by $\Delta$. With $h=(\Delta/V_d)^{1/d}$ this gives the cap-enlarged mean bound $S(h)=\sum_{k=0}^{30}(\sqrt{B-k^2}/h)^{505}$. At the full-row model determinant $S(h)<5.425\cdot10^{-126}$, giving the reported Haar rejection bound. If only the marginal restart's determinant floor is inserted into this *same Haar comparison*, $S(h_{\rm floor})/\tau\in(0.04753348,0.04753350)$. This checks the sensitivity of the cap-enlarged bound. Smaller realized radii can lower it. The restart itself samples finitely many selected embedded lattices; even exact knowledge of their determinants supplies no Siegel identity for their shapes. [Siegel mean-value formula, Theorem 1](https://arxiv.org/pdf/1410.2005) · [Part 163, Proposition 1](wall1_restart_haar_ratio.md)

## Transfer to the first pass and proof status

Under Part 117's coupling, agreement through the first 105 graph appends deletes prescribed coordinate axes. Both processes then use the same surviving coordinates and signed selector. The original product CBD plant restricts to product CBD on those coordinates, so the *embedded* scores agree on the coupling event. This verifies the orientation requirement for R49. It gives $|\delta_{\rm first}-\delta_{\rm restart}|<0.00022304$. The argument transfers a rejection indicator. Transferring the expectation of a count with the same additive error would require a bound on the count on disagreement. [Part 117, coordinate prefix theorem](wall1_idea_round2.md) · [Part 147 audit](wall1_uncovered_lines.md)

The exact missing estimate is the expectation, over the **selected embedded output after draw 407**, of the CBD-weighted nonzero point count in the displayed score. The height-zero consequence above is already beyond the cited minimum-tail estimates. At positive plant heights the translation involves the same embedding as the lattice. Parts 176–180 give branch identities and conditional tests for fixed outputs, while the frequencies of those outputs remain open. Thus the Markov reduction, the scale comparisons, and the coupling are rigorous on paper. The proposed mean and the 0.005 reducer rejection bound remain unproved. [Parts 176–180](../PROOF_GAP.md)

Numerical checks used 55-decimal outward interval arithmetic for the radius, cap, covolume recurrence and Haar sums, with $V_0=1$, $V_1=2$, $V_j=2\pi V_{j-2}/j$. The rank-one enumeration used rational arithmetic. The Part 151 flag-sum enclosures and Part 161 Fourier constant are taken from their cited audits.

## Audit

**Verdict — MINOR CAVEATS.** The probability implications, the distinction between the three lattices, the coupling and the CBD enumeration hold. Two wording corrections matter. Read “through physical radius 1.1981” as “up to the crossing at approximately 1.1981.” At the literal endpoint $1.1981$ the Part 151 majorant already exceeds $0.00913$. Read “the exact missing estimate” as “the missing estimate for the proposed Markov proof.” The exact rejection target is $\Pr(C>\tau)\le0.005$, which could also follow from a direct tail bound.

**Markov and height zero.** The identity $0.005\tau=6.469\cdot10^{-7}$ is exact. On $675\le Z\le959.5$, both signs of any shortest vector of length at most 26 are counted, including equality. Substituting the stated variance upper bound in Cantelli and subtracting the cap charge gives a conditional mass greater than $0.74921186017$ for every block. Using the note’s conservative $0.74921186$ yields an upper bound in $(4.31720341,4.31720342)\cdot10^{-7}$ on the terminal minimum event under the proposed mean hypothesis. Under the rejection target alone, the same event is contained in rejection and has upper bound $0.005$.

**Physical radii and counted vectors.** I used 70-decimal outward intervals, $V_j=\pi^{j/2}/\Gamma(1+j/2)$, and all 407 updates of the determinant recurrence. The lower bounds on the GH scales before draw 406, after draw 406 and after draw 407 are respectively $32.1855367820$, $32.0261018832$ and $31.7874650011$, rounded down. Using Part 151’s audited logarithmic enclosure in its two envelopes places the $0.009$ crossing in $(1.19806583316013,1.19806583316015)$. Part 161’s physical cutoff on the stated histories is at least $31.8636814142$, while $\sqrt{960.5}\in(30.9919344346,30.9919344347)$. The latter is at most $0.974973451$ times terminal GH. The table’s model value $54.95252664$ is rounded to eight decimal places.

The overlap is numerical. Part 161 averages points with strictly positive fresh height in the window before draw 406. An old horizontal vector perpendicular to the selected line keeps its length under projection. For a quotient point with reduced lift $z$, the identity $\|z\|^2=\|\pi z\|^2+\|z-\pi z\|^2$ also permits every lift to exceed a cutoff met by the projected point. Thus the window count alone supplies no terminal point-count bound. The terminal score is evaluated after one further draw and uses plant height. [Part 151 and audit](wall1_penultimate_tail.md) · [Part 161 and audit](wall1_band_plane_hits.md)

**Coupling and orientation.** Re-evaluating Part 117’s prefix bound gives $B(105)\in(0.0002230399378194,0.0002230399378196)$. On agreement, coordinate deletion preserves the order of all surviving coordinates and the suffix uses the same marks and signed selector. Inserting zeros in the deleted coordinates identifies the embedded outputs, and restricting an independent product CBD vector gives the restart’s plant law. Hence both exact scores agree there, and the rejection indicators differ with probability at most $B(105)$ under the unconditioned coupling. In the rank-one example, $1+a<4$ excludes heights at least two and height zero contributes nothing. Enumerating the 49 weighted pairs with rational squared lengths gives height-one numerators $1920$ and $462$ over $4096$. [Part 117 and audit](wall1_idea_round2.md)

**Scope.** The cap-enlarged Haar calculation at the determinant floor gives $S(h_{\rm floor})/\tau\in(0.04753348,0.04753350)$. The cited Haar identity averages over intrinsic shapes. The physical reducer’s exact-score rejection probability, any additional rejections from a majorant verifier, and the lift charge on the same prefix remain separate obligations. [Part 181, §4 and audit](wall1_test_acceptance.md)
