# Counting draw-406 prefixes before shortest-vector selection

**Result.** The membership-only union bound exceeds one even after deduplicating by the final pair of rational subspaces, enforcing the reveal order and the width-506 Gram–Schmidt upper caps, and requiring a positive-height last direction of length between 31 and 33.2. One full-input-rank family alone contributes more than $10^{14220.3962}$ to the first moment. Its terminal planes have area at most $729<1352/\sqrt3$. Thus clipping this bound at one costs exactly $1/(6.485\cdot10^{-11})$ or $1/(7.1275\cdot10^{-11})$ relative to the two allowances. This is a lower bound on a configuration sum. The frequency of selected flags passing the raw and dual gates and the first-hit tests remains open.

## The flag and its probability

Use the horizontal marginal restart of Part 108. At draw $i$ its raw lattice is
$$
 L_i(A)=\{(x,y)\in\mathbb Z^{400+105+i}: x= A_{[:,1:105+i]}y\pmod q\},
 \qquad q=3329 .
$$
The terminal ranks are 911 raw, 406 frozen, and 505 retained. The height-one planted summand of Part 47 plays no role in this marginal. Let $F_i$ be the raw span of the first $i$ lifted winners, and put $F_0=0$. Earlier coordinates embed by zero extension. Projection through the winners identifies the final lattice with $\pi_{F_{406}^\perp}L_{406}$. Each selected line is primitive in its current window. By induction the lifted winners generate the full section of their span, since the kernel at the next step is the preceding section. A saturated terminal plane corresponds to a rational $408$-space $T\supset F_{406}$, with area
$$
 \frac{\det(L_{406}\cap T)}{\det(L_{406}\cap F_{406})}.
$$
The successive section-determinant ratios for $F_i/F_{i-1}$ likewise equal the GS lengths $s_i$. Shortness applies in the quotient. A size-reduced raw lift has squared norm at most $s_i^2+\tfrac14\sum_{k<i}s_k^2$ by backward rounding. Using $s_i$ as its raw radius could omit actual paths. [First tour](wall1_first_tour.md) · [Part 47](wall1_decoupled.md) · [Terminal section identity](wall1_raw_section_compression.md)

**Lemma 1 (fixed configuration).** Write columns of proposed lifts as $(B;Y)$, reduced modulo $q$. For uniform $A$ the simultaneous membership probability is zero unless $\ker Y\subseteq\ker B$. In the compatible case it is $q^{-400r}$, where $r=\operatorname{rank}Y$. Indeed the equations prescribe each of the 400 independent row functionals on an $r$-space. A period vector divisible by $q$ adds no equation. A relation on inputs whose output residue is nonzero makes membership impossible. Real rank alone gives neither conclusion.

One can count saturated graph sections without assuming their bases are primitive in the ambient integer grid. For a fixed rational flag extend an integer basis successively along $Z(F_i)=F_i\cap\mathbb Z^{911}$ and then to $Z(T)$. These extensions exist by saturation. Use the resulting $(B;Y)$ for the basis of $Z(T)$. For every $C$ with $\ker Y\subseteq\ker(B-C)$ the event $B-AY=C$ has probability $q^{-400r}$. With $C_S$ the columns for a flag member $S$,
$$
 H_C(S)=\det Z(S)\,q^{\operatorname{rank} C_S}=\det(L_{406}\cap S)
$$
on that event. This follows from the index of the kernel of the restricted parity map. Summing $q^{-400r}$ over the compatible $C$ for which the ratios $H_C(F_i)/H_C(F_{i-1})$ pass the GS tests and $H_C(T)/H_C(F_{406})\le a$ gives the exact fixed-flag probability for those tests. The sum over geometric flags is finite when $s_i\le q$ since $\det Z(F_i)\le q^i$ and $\det Z(T)\le aq^{406}$ bound their primitive exterior coordinates. Distinct flags may occur for the same matrix. To include the raw/dual gates or the actual winner tests one must also weight by their fraction among the $q^{400(511-r)}$ completions for that $C$. [Part 197 membership formula](wall1_enlarged_cutoff.md#raw-configurations-and-membership-conditioning) · [Part 206 rank-deficient example](wall1_raw_section_compression.md#the-raw-first-moment-above-the-modulus)

## A lower bound for distinct prefix–plane pairs

We count a subfamily for which the fixed-configuration probability is exactly $q^{-163200}$ throughout. All input coordinates below are one-based. Start with the 400 output coordinates and input coordinates $1,\ldots,102$. Introduce the following unit pivots, in order.

| Positions | Input pivot | Other restriction |
|---|---:|---|
| Freezes $1,\ldots,404$ | $106,\ldots,509$ respectively | Only earlier used coordinates besides the pivot |
| Freeze 405 | 104 | Same |
| Freeze 406 | 511 | Also use coefficient 31 on the untouched old axis 103 |
| Two plane lifts | 105 and 510 | Neither lift uses the other's pivot |

All freeze lifts are available when required. Before the last freeze there is no component on axis 103. Every pivot has coefficient $+1$. Modulo the preceding vectors one can eliminate all preceding pivot entries uniquely. The pivot minors are unimodular, so the flag is saturated in the ambient integer grid and hence in every graph containing it. Its input rank is 408 over every prime field. The final prefix span determines the reduced prefix columns by echelon form in the specified pivot order. The plane preimage determines both remaining columns modulo the prefix by their two pivot entries $(1,0)$ and $(0,1)$. Thus the count distinguishes **final pairs** $(F_{406},T)$ even if the intermediate flag and both sets of basis representatives are forgotten.

**Lemma 2 (number of extensions).** In the active integer coordinates, suppose the preceding prefix has determinant $P=\prod_{k<i}s_k$ and a unitriangular pivot minor. The orthogonal projection $K$ of the active integer grid off that prefix has determinant $1/P$. Its rank is the number $d$ of active coordinates minus the prefix rank. Its covering radius is at most $\delta_d=\sqrt d/2$. Indeed complete the primitive prefix to an integer basis and take orthogonal volumes. The projected coordinate units generate $K$ and have norm at most one. Choose $d$ independent ones. Backward rounding in their sublattice gives the covering radius bound by the sum of the squared GS lengths divided by four. [Covering-radius inequality, Lemma 4.3](https://cims.nyu.edu/~regev/papers/crp.pdf)

Each $z\in K$ gives exactly one extension modulo the earlier prefix when the new pivot is fixed to $+1$. Its squared GS length is $1+\|z\|^2$ for an ordinary pivot. If $V_d$ is the unit ball volume, covering a ball by Voronoi cells gives
$$
 P V_d(t-\delta_d)^d\le \#(K\cap B_t)\le P V_d(t+\delta_d)^d\qquad(t\ge\delta_d).
$$
For the upper estimate alone any $t\ge0$ suffices. Boundary cells have volume-zero overlaps. Thus an annulus $b-2\delta_d-1<\|z\|\le b$ supplies at least
$$
 P V_d\big[(b-\delta_d)^d-(b-\delta_d-1)^d\big]
 \tag{1}
$$
extensions when $b>2\delta_d+1$. This counts in a rank-502 projected grid during the prefix. The projection accounts for the shear and the equivalence of raw lifts exactly.

**Proposition (size of the membership sum).** Start $l_0=u_0=400\log q$. For $i=1,\ldots,405$ use $d=502$, $\delta=\sqrt{502}/2$ and
$$
 R_i=\min(q,\sqrt{56.2142}\,e^{l_{i-1}/506}),\quad
 b_i=\sqrt{R_i^2-1},\quad h_i=b_i-2\delta-1,
 \qquad l_i=l_{i-1}-\log R_i,\quad u_i=u_{i-1}-\log h_i .
$$
Restrict the choices to (1). Then $h_i<s_i\le R_i$ and $l_i\le\log(q^{400}/P_i)\le u_i$, where $P_i=\prod_{k\le i}s_k$. The caps here use the **lower** determinant envelope. Consequently they imply even the usual cap evaluated at the actual quotient determinant $q^{400}/P_{i-1}$. The recursion does not assert an upper bound on actual selected lengths from a lower bound on their determinant. [Part 192 determinant recurrence](wall1_rank2_tail.md#summing-charges-along-the-tour)

Let $W_i$ be the number of distinct partial configurations times $q^{-400i}$. Applying (1) to each parent gives the uniform lower multiplier
$$
 \frac{W_i}{W_{i-1}}\ \ge\ V_{502}e^{-u_{i-1}}
 \big[(b_i-\delta)^{502}-(b_i-\delta-1)^{502}\big].
 \tag{2}
$$
The factor $e^{-u_{i-1}}$ comes from $P_{i-1}/q^{400}$. This payment for membership is made at every pivot, including the last two.

At freeze 406 the squared GS length is $962+\|z\|^2$ in the same rank-502 grid, by the two orthogonal unused coordinates. Choose $s_{406}\le33.2$. The last length therefore exceeds 31, has newest-coordinate height one, and satisfies the terminal necessary cap $2^{1/4}\sqrt a$. The lower multiplier is
$$
 V_{502}e^{-u_{405}}
 \big(\sqrt{33.2^2-962}-\delta\big)^{502}.
$$
The radius after subtracting the covering bound exceeds $0.6396$. Put $u_{406}=u_{405}-\log\sqrt{962}$. For the plane lifts, restore all coordinates except the two plane pivots. There are $909-406=503$ old projected dimensions. Both lifts can independently use any point of this same grid of norm at most $\sqrt{27^2-1}$. Their lengths **after projection off the prefix** are at most 27 each. Their plane has rank two by the pivots, is saturated, and has area at most 729. Their combined lower multiplier is
$$
 \left[V_{503}e^{-u_{406}}
 \big(\sqrt{27^2-1}-\sqrt{503}/2\big)^{503}\right]^2.
$$

| Quantity | Enclosure for $\log_{10}$ of the calculated lower certificate |
|---|---:|
| Weighted prefixes through 100 | $(5000.0358,5000.0359)$ |
| Through 200 | $(10518.0262,10518.0263)$ |
| Through 300 | $(14821.0397,14821.0398)$ |
| Through 405 | $(15478.8820,15478.8821)$ |
| Through 406 | $(14592.4241,14592.4242)$ |
| Weighted terminal pairs | $(14220.3962,14220.3963)$ |
| Distinct unweighted terminal pairs | $(589062.0075,589062.0077)$ |

The exact per-pair cost is $3329^{-400\cdot408}$, with $-\log_{10}$ in $(574841.6113,574841.6114)$. The intervals enclose the **lower certificate**. The exact configuration count can be larger. The union bound after clipping is exactly one. To pay for this subfamily by a filtered first moment, the membership-weighted average surviving fraction would have to be below $10^{-14230.5842}$ vertically or $10^{-14230.5432}$ horizontally. Distinct geometric pairs can have overlapping membership events. An argument evaluating their union jointly could give a different bound. The discrete count above already uses full modular rank and removes basis multiplicities.

## Keeping only the last part of the prefix

For a prefix imposed by *linear membership equations alone*, compatible additional equations have conditional probability $q^{-400(r_{\rm total}-r_{\rm prefix})}$. This follows by dividing the two instances of Lemma 1. Conditioning on the selected prefix also restricts competitors. In particular an unused column need not be an independent new pivot for the suffix. Part 201 gives a draw-406 radial term whose 118 later old winners impose zero equations on the 118 unread marks. Recalibrating its certified $\log_{10}$ interval to the present allowances gives $\log_{10}(T/b)\in(620.73006889,620.73006892)$ vertically and $(620.68904165,620.68904168)$ horizontally. These are losses for that specific relaxed radial term if assigned the entire respective allowance. [Part 201 numerical audit](wall1_multistep_branch.md#audit)

There is an exact obstruction to **uniformly** absorbing the earlier lattice into its determinant. Fix any $0\le j\le406$ and any positive entry determinant $D$. In rank 505 take $j+2$ orthogonal periods of length $\epsilon<\min(1,D^{1/505})$ and make the other $503-j$ periods equal so that their product with $\epsilon^{j+2}$ is $D$. Under $j$ unit-height appends and actual shortest-line projections, at least two of the short axes remain, for every sequence of marks. Inductively each selected shortest is one of the unused short coordinate axes. A vector involving an appended coordinate has norm at least one by its last nonzero height, and the preceding projections only remove short coordinate axes. The terminal area is at most $\epsilon^2<a$. This works with an incoming mark subgroup of order $q^{400}$ as well. Thus the supremum terminal-hit probability over states specified only by rank, determinant and that group order is exactly one, for *every* suffix length $j$. This abstract example already has a plane hit at entry. Its occurrence under the doubly gated graph law is not asserted.

The two losses have different scopes. Equations (1)–(2) disprove the proposed estimate obtained by summing **only graph membership** under the stated window GS caps. Keeping only the entry determinant likewise gives a worst-case terminal charge of one, exceeding the vertical and horizontal allowances by approximately $1.5420200463\cdot10^{10}$ and $1.4030164854\cdot10^{10}$, respectively. A count that retains raw minimum, dual floors, internal shortest-vector inequalities, or first-hit exclusions inside the fixed-flag summands can be smaller. The lower certificate does not estimate the fraction of its configurations surviving those tests, or the hit probability of the selected restart. In particular it does not prove a lower bound on either residual. [Part 193 vertical class](wall1_z2_vertical.md) · [Part 206 horizontal accounting](wall1_raw_section_compression.md) · [Terminal-law budgets](wall1_distortion_sharpening.md)

Run `python docs/research/scripts/wall1_history_free_compression.py` from the repository root. The script checks the ball-volume recursions and all displayed numerical enclosures with outward interval arithmetic. [Verification script](scripts/wall1_history_free_compression.py)

## Audit

**Verdict. All four claims hold with the stated membership-only and worst-case quantifiers.** The verification script passed with all interval assertions enabled. An independent 100-digit evaluation using $\log V_d=(d/2)\log\pi-\log\Gamma(1+d/2)$ gave $14220.396229509994\ldots$ for the base-ten logarithm of the weighted lower certificate and $589062.007599078111\ldots$ for its unweighted counterpart.

The first 404 pivots arrive on their selection draws. Pivot 104 is already present at draw 405, and pivot 511 arrives on draw 406. At each ordinary step the old projected grid has rank 502 and covolume $1/P_{i-1}$. Subtracting the upper ball count at $b_i-2\delta-1$ from the lower count at $b_i$ gives (1). Since $P_{i-1}/q^{400}\ge e^{-u_{i-1}}$, this also verifies the direction of (2). The draw-406 width cap from the lower determinant envelope is $44.013111\ldots>33.2$. The two reserved entries give $s_{406}^2\ge962$, and the two projected plane lifts have area at most $27^2=729$.

Restriction to the 406 ordered prefix pivot rows is an isomorphism on $F_{406}$. In particular, $F_i$ is recovered by setting the later prefix pivot entries to zero. On $T$, imposing all prefix pivot entries zero and prescribing the two plane pivot entries uniquely recovers each reduced lift. Thus forgetting the flag and the representatives preserves the count of final pairs. The unitriangular 408-row input minor gives rank 408 modulo 3329. Each of the 400 rows of $A$ then satisfies 408 independent conditions, giving exact probability $3329^{-163200}$ for membership of the prescribed lifts. Their sum exceeds $10^{14220.3962}$ before clipping, even if some membership events coincide.

For each $0\le j\le406$, the long period $(D/\epsilon^{j+2})^{1/(503-j)}$ exceeds $\epsilon$. Throughout the suffix a vector using an append has absolute height at least one on its latest used append. Projection of a shortest line removes one short old axis and preserves those height coordinates. Every tie choice therefore leaves at least two short axes at exit. The incoming torus admits the subgroup generated by $1/q$ of each of any 400 basis periods, of order $q^{400}$. The construction succeeds for every mark sequence, attaining probability one and hence the allowance ratios $1.5420200463\cdot10^{10}$ and $1.4030164854\cdot10^{10}$ (vertical and horizontal, respectively). This supremum allows a hit at entry. A probability for a first hit on a reachable, doubly gated restart remains open.
