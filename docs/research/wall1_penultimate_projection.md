# Fixed raw lifts and the penultimate projection

Let $M=H_{406}$ in the unconditioned width-506 restart, let $x$ be its designated signed shortest vector, and write $E=\{\lambda_1(P_{x^\perp}M)\le 26\}$. There is an obstruction to multiplying raw membership probabilities by angular probabilities from the fresh-mark law. **If a fixed candidate has a nonzero input coefficient modulo $q$, membership and the earlier columns determine the column of its last such coefficient.** If this happens at an append with mark group $H$, the conditional mark law differs from the fresh law by exactly $1-1/|H|$ in total variation. A finite example below attains a factor of seven between the joint probability and the product, at the physical cutoffs 250 and 26. A second example exhibits the dependence for a unique shortest lift. The width-506 target $\Pr(E)\le 4\cdot10^{-7}$ remains open. [Part 108](wall1_first_tour.md) · [Part 183 and audit](wall1_terminal_tail_047.md)

## Counting each design once

Use $q=3329$, $Q=q^{400}$, and the raw graph $\mathcal M_A=\{(b,c)\in\mathbb Z^{400}\oplus\mathbb Z^{511}:b+Ac=0\bmod q\}$. Embed each frozen direction by zero extension in the raw space. Let $T_A$ be the span of the 406 frozen directions together with $x$, let $P_A$ project off $T_A$, and let $K_A=\mathcal M_A\cap T_A$. Successive projections remove orthogonal directions. Thus $P_A\mathcal M_A=P_{x^\perp}M$ has rank 504 and $K_A$ has rank 407. Every lift of a point $y=P_Az$ lies in $z+K_A$. For $y\ne0$, adding multiples of a nonzero kernel vector gives infinitely many lifts with the same projected length and fractional squared loss tending to one. In particular the raw-vector first moment with only the lower cutoff 250 is infinite. It counts infinitely many vectors on $E$, and the all-zero design has positive probability. On that design at least two independent unit axes remain in $M$, so $E$ holds. Even choosing a primitive quotient point retains the entire fiber. [Part 155](wall1_inherited_witness.md) · [Part 160 and audit](wall1_shrunken_lifts.md)

A deterministic upper cutoff is available for the **shortest** lift. Take any nonzero $y\in P_A\mathcal M_A$ of length at most 26. Write $s_1,\ldots,s_{406}$ for the window winner lengths. Choose a raw lift of each winner at its step and a lift of $x$ after step 406. Their Gram–Schmidt lengths, in that order, are $s_1,\ldots,s_{406},\|x\|$. Starting from any lift of $y$, subtract integer multiples of these kernel vectors in reverse order. Rounding its coefficient in each orthogonal direction leaves absolute component at most half the corresponding Gram–Schmidt length and preserves all components already reduced. Consequently the shortest raw lift has squared length at most
$$
 \|y\|^2+\tfrac14\Big(\sum_{i=1}^{406}s_i^2+\|x\|^2\Big).
$$
Each incoming window contains $q$ times its fresh unit axis, so $s_i\le q$. Rounding a lift of $y$ in $M$ along $x$ gives a nonzero old vector of squared length at most $26^2+\|x\|^2/4$. Shortestness of $x$ gives $\|x\|^2\le4\cdot26^2/3$. Thus one may use the deterministic upper radius
$$
 B=\sqrt{26^2+406q^2/4+26^2/3}\in(33538.75911,33538.75912).
$$
Only the availability of a finite set is claimed for this radius. [Nearest-plane bound, proof of Lemma 4.3](https://cims.nyu.edu/~regev/papers/crp.pdf) · [Winner exchange](wall1_winner_exchange.md)

For an exact probability identity, let $G$ require absence of a nonzero raw graph vector of length at most 250 and validity of the Part 172 dual floors through draw 406. On $E$, choose the lexicographically first signed shortest point in $P_A\mathcal M_A$, then its lexicographically first shortest raw lift. Let $D_z$ say that $E\cap G$ occurs and this choice is $z$. Both minimum sets are finite. With $I_z=\{z\in\mathcal M_A\}$, disjointness gives
$$
 \Pr(E\cap G)=
 \sum_{\substack{z\in\mathbb Z^{911},\ 250<\|z\|\le B\\ \Pr(I_z)>0}}
       \Pr(I_z)\Pr(D_z\mid I_z).                                      \tag{1}
$$
The two audited exits give $0\le\Pr(E)-\Pr(E\cap G)<4.249\cdot10^{-12}+8.147\cdot10^{-14}$. Hence a bound of $3.9999566953\cdot10^{-7}$ on (1) would suffice. For unit vectors $e_i$ along the 407 removed directions, the cutoffs imply $\sum_i|\langle z/\|z\|,e_i\rangle|^2>1-(26/250)^2=0.989184$. This only forces the largest summand above $0.989184/407$. The sum includes the designated $x$ and all horizontal winners. [Part 172](wall1_transference.md) · [Part 183](wall1_terminal_tail_047.md)

## Conditional law for one summand

For fixed $z=(b,c)$, first suppose $\bar c\ne0$ over $\mathbb F_q$. Put $j=\max\{i:\bar c_i\ne0\}$ and write $a_i$ for column $i$. For every assignment of the other 510 columns there is exactly one completing column,
$$
 a_j^*=-\bar c_j^{-1}\Big(\bar b+\sum_{i<j}\bar c_i a_i\Big).
$$
Thus $\Pr(I_z)=Q^{-1}$. Given $I_z$, the other columns are jointly independent and uniform, and $a_j=a_j^*$. This includes later coefficients divisible by $q$ even when their integer values are nonzero. When $j\le105$ the constraint lies in the initial graph. When $j>105$ the prefix before append $j-105$ has exactly its original law. For a pre-append raw history $S$, write $\phi_S$ for the mark map, absorbing the sign convention of the graph column. For every set $C(S)$ of marks,
$$
 \Pr(I_z,\ U\in C(S)\mid S)
   =Q^{-1}\mathbf1_{\{\phi_S(a_j^*)\in C(S)\}}.                       \tag{2}
$$
Before imposing membership the corresponding mark fraction at this prefix is $|C(S)|/|H(S)|$. The singleton containing $\phi_S(a_j^*)$ attains the stated total variation distance. Later raw columns remain fresh given membership and the history before their reveal. Finally, when $\bar c=0$, membership has probability one if $\bar b=0$ and zero otherwise. The candidate radius $B>q$ therefore requires accounting for the deterministic members $q\mathbb Z^{911}$.

The pinned **mark** can also be recovered from the embedded geometric state, even when that state merges raw prefixes. At an append pivot let $P$ denote the old projection, $L$ the old retained lattice, and use the convention $\phi_S(a)=[P(-a,0)]$ in the torus modulo $L$. The old graph contains $(-A_{<j}c_{<j},c_{<j})$, so
$$
 [P(b,c_{<j})]=[P(b+A_{<j}c_{<j},0)]
              =c_j\,\phi_S(a_j^*).
$$
The class belongs to the mark group, which is killed by $q$. Since $c_j$ is a unit modulo $q$, this identity determines the pinned mark from $P,L,z$ alone.

For a vertical win, the Voronoi section gives the uniform image of a uniform set of marks for a prescribed shortest section. Selecting a winning height restricts that set by the global shortest-vector comparison. Equation (2) acts even before that comparison. The character transport identity evaluates the resulting label pairing along the selected projection. The subsequent projection off $x$ uses the same history and has no additional mark. [VoronoiMarkLaw](../../SigabaNeo/Lib/Lattices/Research/Wall1/VoronoiMarkLaw.lean) · [CharacterTransport](../../SigabaNeo/Lib/Lattices/Research/Wall1/CharacterTransport.lean) · [Part 155, fixed-vector survival](wall1_inherited_witness.md)

On the reachable positive-height branches covered by Part 176, the embedded output and oriented winner recover the parent state $S$ and its mark. The unconditioned mass there is $N(S)/(Q^{510}|H(S)|)$, where $N(S)$ counts prefixes giving $S$. For example, if the pivot above is the 511th column, each of those raw prefixes has **one** completion satisfying $I_z$. Its mass contribution to a specified final branch is $Q^{-511}$ if its pinned mark equals the recovered mark, and zero otherwise. The preceding class identity makes the mark test identical for all prefixes of $S$. Consequently the exact joint mass of membership and this inverse branch is either $N(S)/Q^{511}$ or zero. Multiplying its unconditioned branch mass by $1/Q$ would undercount a matching branch by the factor $|H(S)|$. Inversion evaluates compatibility at a specified branch. Summing over compatible outputs still requires the parent masses $N(S)/Q^{510}$, and (1) also imposes the raw-lift and exit tests. Equation (1) includes horizontal branches as well. [Part 176, Proposition 2 and audit](wall1_inverse_branch.md)

## Exact checks on the dependence

Use the one-append graph $W_a=\{(d,h):d\equiv ah\pmod q\}$, with $a$ uniform. Negating the uniform column gives the sign convention of (1). Choose the shortest vector $v=(v_1,v_2)$ by minimizing $(\|v\|^2,v_1,v_2)$ in lexicographic order. For each fixed $z=(c,j)$, test membership $I_z$ and the geometric event $C_z=\{0<\|P_{v^\perp}z\|^2\le r^2\}$. The latter is defined for every mark, including those for which $z\notin W_a$.

| $q$ | $z$ | $r^2$ | Marks in $I_z$ | Marks in $C_z$ | Joint probability | Product of marginals |
|---:|---|---:|---|---|---:|---:|
| 7 | $(239,123)$ | 676 | 2 | 2 | $1/7$ | $1/49$ |
| 11 | $(-3,2)$ | $121/10$ | 4 | 0, 2, 3, 4, 5, 7, 8, 9, 10 | $1/11$ | $9/121$ |

In the first row $\|z\|^2=72250>250^2$. At $a=2$ the winner is $(-2,-1)$ and the projected squared length is $49/5$. This long representative has a shorter lift in its fiber. The second row checks what happens after imposing shortest-lift selection. At $a=4$, $v=(-1,-3)$, $|\det(v,z)|=11=\det W_4$, and $2|\langle z,v\rangle|=6<10=\|v\|^2$. Hence $z$ generates the quotient up to sign after projection and is the unique shortest lift of its projected point. The strict discrepancy in the second row therefore persists for a shortest lift. The examples test the multiplication of probabilities at one append and make no estimate of the mass of $E\cap G$ in rank 911.

For reproduction, enumerate both coordinates of $v$ from $-q$ through $q$, discard zero and failed congruences, and minimize the signed tuple above. The candidate $(q,0)$ proves the box is exhaustive. For each mark compare the exact rational $(v_1j-v_2c)^2/\|v\|^2$ with the tabulated threshold. A separate check of the pinned-mark identity used $q=7$, an old graph $d+ah=0\bmod 7$ and its signed winner $v=(u,k)$. The projected class in this rank-one quotient is represented by $\det(v,\cdot)\bmod 7$, since $v$ is primitive in the old graph of covolume seven. For each $a,b,c\bmod7$ and $t=1,\ldots,6$, set $d=-(b+ac)/t\bmod7$. All $7^3\cdot6=2058$ tests gave $uc-kb=tkd\bmod7$, as predicted for the next pivot of coefficient $t$. Scratch calculations used exact integers and rationals for the finite checks and 60-decimal-digit outward interval arithmetic for $B$ and the remaining probability budget.

**Open estimate.** The canonical choice in (1) removes the infinite multiplicity and permits exact conditioning. The missing estimate is the sum of its conditional selection probabilities weighted by raw membership. Part 151's one-vector majorant already reaches one near physical radius 1.20927. Part 172 controls the dual-floor exits, while its rank-503 section on the remaining histories still depends on the selected plane. Neither yields the required estimate for (1). The obstruction rules out a factorization of the proposed first moment and leaves the conjectured probability bound undecided. [Part 151 and audit](wall1_penultimate_tail.md) · [Part 172 and audit](wall1_transference.md)

## Audit

**Verdict — SOUND.** The factor $|H(S)|$ is exact when the final column is the pivot and the specified reachable inverse branch is compatible. Equation (1) counts every design in $E\cap G$ once. The width-506 bound $\Pr(E)\le 4\cdot10^{-7}$ remains open.

**Compatibility and mass.** Fix a raw prefix and let $u$ be the recovered final mark. Membership fixes one raw column $a_j^*$ because $\bar c_j$ is invertible. The old graph relation identifies $[P(b,c_{<j})]$ with $c_j\phi_S(a_j^*)$, so the compatibility test is exactly $c_j u=[P(b,c_{<j})]$. Both sides are determined by the framed parent, the candidate and the recovered mark. Different prefixes of that parent may require different raw columns, but they all give the same answer to the test. Part 108 gives the fresh uniform mark law, and Part 176 gives $N(S)Q/|H(S)|$ designs on this branch. Exactly $N(S)$ of them satisfy membership on a match and zero do on a mismatch. Dividing by $Q^{511}$ proves the joint mass and the claimed factor. The total variation distance at the pivot is $1-1/|H(S)|$, including zero for a trivial mark group. A fresh typecheck of `InverseBranch.lean` reported only the standard axioms for `recover`, `framed_injective` and `raw_fiber_card`. These declarations supply the inverse and the unconditional fiber count. The fixed-candidate compatibility argument is proved in the note.

**Exact examples.** Independent enumeration over the closed ball of squared radius $q^2$ reproduced both rows and all 2,058 projected-class checks. At $q=7$ only mark 2 passes either test, giving joint mass $1/7$ and product $1/49$. At $q=11$ the nine listed marks pass the projection cutoff, with equality at mark 4. There $|\det(v,z)|=11$ makes $(v,z)$ a basis of the graph lattice, and $2|\langle v,z\rangle|=6<10$ gives strict uniqueness among the lifts $z+\mathbb Z v$. One can also impose this strict strip inequality directly in the geometric event for every mark. Then only mark 4 passes the combined test, giving joint mass $1/11$ and product $1/121$. The table's $9/121$ is correct for its stated projection event.

**Finite sum and budget.** Reverse rounding only needs the chosen kernel vectors to span the removed real space. Their integer span suffices to produce a lift within the claimed radius, even if that span is a proper sublattice of the kernel. Exact squaring confirms $B^2=6749090177/6$ and the displayed interval. On $E\cap G$ the two tie rules select one raw member in the finite annulus. Thus the events $D_z$ partition $E\cap G$, and $D_z\subseteq I_z$ justifies each conditional summand, including deterministic members. Subtracting the two audited exit bounds from $4\cdot10^{-7}$ gives $3.9999566953\cdot10^{-7}$ exactly. Part 183's separate last-draw discrepancy concerns the terminal event and does not enter this budget for $E$. The remaining quantity is the sum of the conditional selection probabilities in (1), with their membership weights. [Nearest-plane inequality, proof of Lemma 4.3](https://cims.nyu.edu/~regev/papers/crp.pdf) · [Part 183 audit](wall1_terminal_tail_047.md#audit)
