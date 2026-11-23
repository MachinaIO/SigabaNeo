# The enlarged plane cutoff in the width-506 restart

Let $M_h$ be the rank-505 retained lattice after $h$ selections from the unconditioned $400\times105$ restart, $q=3329$. Let $\tau_X=\min\{h\ge0:N_X(M_h)>0\}$, where $N_X$ counts unoriented saturated planes of area at most $X$. Put $a=1352/\sqrt3$ and $X_*=\sqrt{3/2}\,a=676\sqrt2$.

**Finite-chain bound.** For every $0<X\le X_*$,
$$
 \Pr(\tau_X\le154)<5.412\cdot10^{-36},\qquad
 \Pr(\tau_X\le160)<9.057\cdot10^{-16},\qquad
 \Pr(\tau_X\le161)<2.041\cdot10^{-12}.
$$
These are probabilities of at least one hit anywhere in the indicated prefix. They include horizontal and positive-height wins, with multiplicities relaxed only at the witness-counting step. In particular R64's wholly old first hits at the original cutoff through draw 162 can be charged once to the draw-161 bound. At the enlarged cutoff the new majorant crosses $10^{-11}$ between draws 161 and 162. The event probability after 161 remains open. [R64, pre-step interval](wall1_z1_old_planes.md) · [Restart law](wall1_first_tour.md) · [Part 192 and audit](wall1_rank2_tail.md#audit)

## Where the old sum grows

At horizon 154 the largest Part 192 term is $(i,j)=(38,0)$. The last coordinate used in the witness flag arrives at draw 38 and the first direction in the suffix already uses it. The length cap is $1901.39414\ldots$, below $q$. Its majorant lies in $(10038946.28,10038946.30)$ and the whole sum in $(99653782.23,99653782.25)$. Over $99.6472\%$ of the sum comes from $j=0$. The bound tests a single nonzero-height vector after replacing the hit plane by a short line and allowing the remaining 117 directions in the draw-38 window. It discards the requirement that those directions realize the flag. The cap excludes every nonzero height divisible by $q$. The $10^7$ term thus has no decomposition in the calculation into actual period-axis planes and generic planes. Its size comes from the radial count in dimension 506. Enlarging the terminal area by $c$ scales the terminal line radius by $\sqrt c$ and the theta-free term by $c^{253}$. [Part 192, prefix sum](wall1_rank2_tail.md#summing-charges-along-the-tour)

## Keeping two directions at the end of the flag

Take $X\in[a,X_*]$ and $f=24$. If a hit plane has minimum at most $f$, use the designated shortest line of the entire retained lattice as a terminal rank-one witness. Otherwise use a Gauss-reduced basis of a hit plane. In the latter case its first length $s$ belongs to $[f,\sqrt{2X/\sqrt3}]$, and its second length squared is at most $(X/s)^2+s^2/4$. This expression decreases throughout the interval. Write $b$ for the terminal rank and use
$$
 (d_1,K_1)=(f,f),\qquad (d_2,K_2)=(\sqrt X,\sqrt{(X/f)^2+f^2/4}).
$$
The terminal determinant is at most $d_b^b$, and every chosen terminal basis vector has length at most $K_b$. Splitting off short lines prevents a very long second generator from invalidating the fresh-coordinate test.

For each $b$, set $G_b=C_b=d_b$. Given Hermite upper bounds $g_l\ge\gamma_l$, use
$$
 G_l=G_{l-1}g_l^{1/(2(l-1))},\qquad
 C_l=\max(C_{l-1},\sqrt{g_l}\,G_l),\quad l>b.                 \tag{1}
$$
In a suffix of the flag present in one window, $G_l$ bounds the $l$-th root of its determinant and $C_l$ bounds its first winning length for $l>b$. In fact, writing $v$ for that length and $D'$ for the determinant of the remaining tail, Hermite gives $v\le\sqrt{g_l}(vD')^{1/l}$. Solving with $D'\le G_{l-1}^{l-1}$ proves (1). This argument uses the actual terminal area once. Multiplying two separate bounds for the terminal basis lengths would lose that information.

Fix a hit at any $h\le t$ and append the terminal witness to its selected winners. If draw $i$ supplies the last suffix coordinate used anywhere, every direction from draw $i$ onward has a lift from the window at $i$. Indeed all later input coordinates vanish on these directions and on the preceding frozen directions that could affect those coordinates. The identity input block removes those columns from the lifts. Take $j$ to be the number of winners starting at $i$ before coordinate $i$ is first used, allowing all remaining winners to precede its first use in the terminal witness. These $j$ winners coincide, in order, with the designated successive shortest vectors of the old lattice alone. Their competitors there were available at every comparison, with the same signed tie rule. Hence we may force this particular old flag before exposing column $i$. [Last-used-coordinate proof](wall1_uncovered_lines.md#3-a-separate-bound-at-the-unit-threshold)

Put $k=t-i+1+b$, $0\le j\le k-b$, $n=506-j$. Monotonicity of $C_l$ covers shorter actual tails and bounds the product of the first $j$ lengths by $P_{kj}=\prod_{v=0}^{j-1} C_{k-v}$. Discard an ineligible forced flag if a cap fails. Otherwise its projected old determinant is at least $e^{L_{i-1}}/P_{kj}$, with
$$
 L_0=400\log q,\qquad
 L_h=\max(L_{h-1}-\log q,\,505L_{h-1}/506-\tfrac12\log56.2142).
$$
Some vector using column $i$ has length at most $u=\max(C_{k-j},K_b)$. The $K_b$ alternative is necessary when all remaining winners have zero height and a terminal basis vector first uses the column. A fresh basis vector can be signed to positive height. If no suffix column is used at all, the initial raw graph contains a nonzero vector of length at most $u_0=\max(C_{t+b},K_b)$, from the first winner or a terminal basis vector.

**Counting in the forced projection.** The following elementary ball bound suffices. Let $K$ be the projected integer grid, including the independent last unit coordinate, of rank $n$ in the $N=505+i$ raw coordinates. Its covering radius is at most $\sqrt N/2$ by rounding in the ambient integer grid and projecting. In a centrally symmetric Voronoi cell about each grid point $z$ in the radius-$u$ ball, at least half the cell consists of $z+y$ with $\langle z,y\rangle\le0$. That half is in the ball of radius $\sqrt{u^2+N/4}$. Cell interiors are disjoint. Consequently the number of **positive-height** points is at most $V_n(u^2+N/4)^{n/2}/\det K$, by sign symmetry. Here $V_n$ is the unit ball volume.

For each integer height $1\le m\le u<q$, multiplication by $m$ permutes the projected mark group. Averaging the count on that layer therefore divides its full-grid count by the mark order. The projected old lattice extended by the mark group equals the projected integer grid in the old coordinates, since adjoining horizontal integer vectors to a raw graph supplies all coordinate units. Thus $|H_{\rm proj}|\det K$ is the forced old determinant. The mark law here is conditional only on the pre-draw history and forced old projections. It is never conditioned on a future flag. The resulting sum is
$$
 S_b(t,X)=
 \frac{V_{505}(u_0+\sqrt{505}/2)^{505}}{2q^{400}}
 +\sum_{i=1}^t\sum_{j=0}^{k-b}
 V_n\big(u^2+(505+i)/4\big)^{n/2}P_{kj}e^{-L_{i-1}}.          \tag{2}
$$
The first term uses unit cubes and the raw membership bound $q^{-400}$ for a nonzero sign pair of length below $q$. If $u_0<q$ in both branches, $\Pr(\tau_X\le t)\le S_1+S_2$. Each $(b,i,j)$ test already covers every shorter horizon. Equation (2) uses a candidate first moment to bound an existence event; it gives no upper bound on the selected plane multiplicity. Lean's rank-506 projected-ball theorem gives a different radial majorant on the same type of grid. The symmetric-cell argument allows every rank $506-j$ here. [ProjectedBallCount.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/ProjectedBallCount.lean) · [Projected-mark counting identity](wall1_uncovered_lines.md)

| Cutoff | Horizon | Enclosure for $S_1+S_2$ | Maximum tested radius, rounded up |
|---|---:|---:|---:|
| $X_*$ | 154 | $(5.4115,5.4116)\,10^{-36}$ | 2597 |
| $X_*$ | 160 | $(9.0563,9.0564)\,10^{-16}$ | 2794 |
| $X_*$ | 161 | $(2.0409,2.0410)\,10^{-12}$ | 2827 |
| $X_*$ | 162 | $(4.5465,4.5466)\,10^{-9}$ | 2861 |
| $1.1a$ | 164 | $(3.4342,3.4343)\,10^{-14}$ | 2777 |
| $1.1a$ | 165 | $(7.3894,7.3895)\,10^{-11}$ | 2809 |
| $a$ | 167 | $(1.1156,1.1157)\,10^{-14}$ | 2742 |
| $a$ | 168 | $(2.3191,2.3192)\,10^{-11}$ | 2774 |

At $X_*,t=162$ the single test with $b=2$ and $(i,j)=(47,0)$ already exceeds $4.5308\cdot10^{-10}$. The upper sums are nondecreasing in the horizon while the radii are valid, since each old term persists with weakly larger caps. Monotonicity of the event in $X$ extends each certified upper bound to every smaller positive cutoff.

## Raw configurations and membership conditioning

Write $\mathcal L(A)=\{(x,y)\in\mathbb Z^{400+p}:x=Ay\pmod q\}$ for the raw graph with $p$ input columns. For a fixed rational subspace $S$, put $Z(S)=S\cap\mathbb Z^{400+p}$ and
$$
 r_A(S)=\operatorname{rank}_{\mathbb F_q}([I,-A]\,Z(S)\bmod q).
$$
Restriction of the parity map to $Z(S)$ has kernel $\mathcal L(A)\cap S$. Its index is exactly $q^{r_A(S)}$. In particular a raw graph plane of area at most $X_*<q$ must have $r_A(S)=0$, since the Euclidean determinant of a rank-two integer lattice is at least one by its integer minors.

Take a basis of $Z(S)$ and write $(B;Y)$ for its reduction modulo $q$ in horizontal and input blocks. For any specified matrix $C$, the probability of $B-AY=C$ is $q^{-400\operatorname{rank}Y}$ if $\ker Y\subseteq\ker(B-C)$, and zero otherwise. Each row of $A$ has exactly the prescribed values on $\operatorname{im}Y$ and is free on a complement. For a primitive raw two-space the stacked basis has rank two modulo $q$ because it extends to a unimodular basis. Thus a small raw plane is possible exactly when $\operatorname{rank}Y=2$ and $AY=B$. Its membership probability for such $S$ is $q^{-800}$.

This gives an **exact raw first moment**. Multiply $q^{-800}$ by the number of primitive integer two-spaces of area at most $X$ whose input residues have rank two. It includes the initial law at $p=105$. In the complete raw graph through draw 406, $p=511$. Every earlier raw plane of area at most $X$ embeds in this graph by zero padding. A closed bound for this entire source of witnesses is
$$
 q^{-800}\sum_{m=1}^{\lfloor 2X/\sqrt3\rfloor}
 4V_{911}^2\left[(m+911/4)
       (X^2/m+m/4+911/4)\right]^{911/2}
 <10^{-604}\quad (X=X_*).                                      \tag{3}
$$
Indeed a reduced basis has first squared length $m\ge1$ and second squared length at most $X^2/m+m/4$. Count the two integer balls by the symmetric-cell bound above, allowing both signs and all vectors. This overcounts the integer planes before multiplying by their membership probability. Thus even before testing selection, small *raw* planes cost less than (3) for the whole tour.

For coordinate two-spaces the exact count is simpler still. A horizontal unit cannot belong to the graph. An input unit belongs exactly when its column vanishes. The number of qualifying coordinate planes at $X_*$ in the full raw graph is $\binom{Z}{2}$, $Z\sim\mathrm{Binomial}(511,q^{-400})$. Its expectation is $\binom{511}{2}q^{-800}$ and its nonempty probability is $1-(1-p_0)^{511}-511p_0(1-p_0)^{510}$, $p_0=q^{-400}$. In a raw coordinate plane the period axes themselves always belong. Saturation produces a small plane precisely in this zero-column case. Also, any draw selecting a period of *physical* length $q$ leaves no hit at $X_*$. The ternary preimage of a hit has determinant at most $qX_*$ and minimum $q$, contrary to $q^2\le\sqrt2 X_*$. This disposes of a hit on the positive-length prefix consisting solely of unshortened period selections. It does not control a later projection of a large raw plane.

**Projected coordinate planes.** There is also a finite exact expression when the frozen directions have changed the metric. This states explicitly which selector probabilities a finite evaluation would need. At draw $h$ use $p=105+h$. Let $F$ range over rational frozen $h$-spaces and $T\supset F$ over rational $(h+2)$-spaces. For the projected coordinate-pair class take only distinct $T=F+\mathbb R e_j+\mathbb R e_k$ of that dimension. Deduplicating $T$ counts each saturated plane once even if several axis pairs give it. In fact for the realized frozen span $F_h(A)=F$, the full preimage of the saturated output plane is $\mathcal L(A)\cap T$. Quotienting by $\mathcal L(A)\cap F$ gives area
$$
  \frac{\det Z(T)}{\det Z(F)}\,q^{r_A(T)-r_A(F)}.                 \tag{4}
$$
Here $\det Z(0)=1$. Both determinants use their intrinsic Euclidean measures. This quotient permits additional generators supplied by saturation. The wedge of the two projected period vectors alone could have much larger area.

Extend a basis of $Z(F)$ to one of $Z(T)$ and use its blocks $(B;Y)$ as above. For a compatible $C$, write $C_F$ for its first $h$ columns and put $r=\operatorname{rank}Y$. The contribution of $(F,T,C)$ to the finite first moment is exactly
$$
 q^{-400r}\,
 \mathbf1_{\{\det Z(T)q^{\operatorname{rank}C-\operatorname{rank}C_F}
                    \le X\det Z(F)\}}\,
 \frac{\#\{A:AY=B-C,\ F_h(A)=F\}}{q^{400(p-r)}}.             \tag{5}
$$
Sum over compatible $C$ and the specified $F,T$. For the generic complement omit exactly the coordinate-generated $T$ instead. The search can be made finite independently of the particular $A$. Indeed $\det Z(F)\le q^h$ since each winner has length at most $q$, and every contributing $T$ has $\det Z(T)\le Xq^h$. Primitive exterior coordinates of bounded norm give finite lists. Adding a survival test to the numerator gives the corresponding first-hit-weighted count. One can evaluate the numerator by extending the pinned map on $\operatorname{im}Y$ over all complementary basis vectors and executing the deterministic selector. In particular the final fraction is conditional on the pinned parity data. Reusing independent uniform marks on those same pivots can lose a factor $|H|$. Equation (5) is an exact counting formula. Its selected numerators at width 506 have not been summed. [Part 184, membership audit](wall1_penultimate_projection.md#audit) · [Part 195, selected incidences](wall1_plane_moment_recursion.md#audit)

## Size of the generic comparison still needed

For independent Haar shape in dimension $n=505$ and physical determinant $D$, the mean number of unoriented saturated planes is
$$
 U_X(D)=\frac{504\pi V_{505}V_{504}}{24\zeta(505)\zeta(504)}
              \frac{X^{505}}{D^2}.
$$
At $X_*$, $U_{X_*}(e^{L_{406}})\in(2.21908,2.21909)\,10^{-13}$ and $\sum_{h=0}^{406}U_{X_*}(e^{L_h})\in(2.22022,2.22024)\,10^{-13}$. Hence the floor sum fits $10^{-11}$ even with a multiplier of 45. This is a certified comparison scale. The theorem integrates over Haar measure on a fundamental domain. Removing raw coordinate-axis configurations from a selected finite law does not give that measure. For example two distinct pairs of equal input columns give a plane spanned by their two disjoint input differences, of area 2 at draw zero. Its span contains no coordinate axis. The specified pair equalities have probability $q^{-800}$. The scalar value of $D_0$ does not distinguish those histories. The rank-minimum and projection inequalities likewise do not assign probability to $F_h(A)=F$ conditional on $AY=B-C$. [RankTwoPlaneMean.lean, plane_mean](../../SigabaNeo/Lib/Lattices/Research/Wall1/RankTwoPlaneMean.lean) · [RankinWindow.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/RankinWindow.lean) · [Haar transverse law](wall1_rank2_transverse.md) · [Finite comparison audit](wall1_plane_comparison.md#audit)

For a concrete sufficient condition, let $Z_{\rm ax}$ be the mass of first hits on draws 162–406 with at least one projected coordinate-pair plane. Let $E_{\rm gen}$ be the sum over these draws of the expected number of other hit planes on histories surviving through the preceding draw. Counting the first hit gives $\Pr(\tau_{X_*}\le406)\le 2.041\cdot10^{-12}+Z_{\rm ax}+E_{\rm gen}$. If one could prove $E_{\rm gen}\le K\sum_{h=162}^{406}U_{X_*}(e^{L_h})$, it would suffice that $Z_{\rm ax}+K(2.22024\cdot10^{-13})<7.959\cdot10^{-12}$. Formula (5) expresses both required finite counts, with an existence indicator or a first-moment upper bound for the axis class. Formula (3) only pays for small raw ancestors. **Conjecture.** The enlarged-cutoff first-hit probability stays below $10^{-11}$ through 406. Neither the generic comparison nor the smallness of the full projected-axis charge is established by the floor calculation.

## Numerical and exact checks

The interval computation used 55 decimal digits in scratch. For (1), take $\log g_l$ initially as $2\min(\mathrm{LCZ},\mathrm{Part65})/(10^9 l)$ in the Part 77 integer table. Take the minimum with $2\log 2+(2/l)\log(\Delta_l/V_l)$ at the Part 82 published density caps, set $g_{24}=4$, and propagate $\log g_l\gets\min(\log g_l,(l-1)\log g_{l-1}/(l-2))$ for $l\ge3$. The input table contains upward-rounded caps. Minima and maxima of interval endpoints were taken outward. Generate volumes from $V_0=1,V_1=2,V_l=2\pi V_{l-2}/l$. For each $i$ in (2) initialize the weight at $e^{-L_{i-1}}$. After adding the term at $j$ multiply it by $C_{k-j}$ for the next term. The old-sum diagnostic instead uses Part 192's original Hermite caps and theta factor. For the Haar sum use $1\le\zeta(l)\le1+2^{-l}(1+2/(l-1))$. The base-ten logarithm of (3) lies between $-604.1040$ and $-604.1039$. [Part 77 cap table](wall1_lcz_all_widths.md) · [Part 82 density caps and Mordell propagation](wall1_small_d_caps.md) · [Cohn, certified packing tables](https://dspace.mit.edu/entities/product/d8a88a76-3fa7-4b75-89ef-ea71a0e05b77)

Two independent exact checks used small graphs. Over $\mathbb F_3$, for each of the 81 input matrices $Y$ of size $2\times2$, enumeration of all 81 maps $A$ gave $3^{2r}$ distinct $AY$, each with $3^{4-2r}$ preimages. The numbers of $Y$ of ranks $0,1,2$ were $1,32,48$.

For (4), take one horizontal coordinate, two old input columns and one new column over $\mathbb F_3$, choose the lexicographically least signed shortest vector $v$, and test squared output area at most 2. On the 27 graphs, 15 had one hit plane each and 12 had none. Exactly one of the 15 planes was generated up to saturation by projections of a coordinate pair. To reproduce the first count enumerate primitive integer normals $n$ up to sign with $n\cdot v=0$. In $T=n^\perp$ the parity index is one if $n\bmod3$ spans the parity row, and three otherwise. The area squared is $(\mathrm{index})^2\|n\|^2/\|v\|^2$. The second count uses primitive *graph-dual* normals $z/3$ with $z\cdot v=0$, $z_{j+1}+A_jz_0=0\bmod3$, and $\|z\|^2\le2\|v\|^2$. Primitivity is the gcd-one test on $z_0,(z_{j+1}+A_jz_0)/3$. Both counts gave the identical rational planes separately for every graph. The search boxes $[-2,2]^4$ for either normal are exhaustive since $\|v\|^2\le2$ on all 27 graphs.

## Audit

**Verdict — SOUND.** The enlarged-cutoff prefix bounds and the raw-plane and Haar calculations hold at the stated precision. Equation (2) last certifies a prefix below $10^{-11}$ at draw 161 for $X_*$ and at draw 167 for $a$. The location of either crossing is a property of the upper sum. The selected-chain claim through draw 406 remains conjectural.

**Independent interval calculation.** Scratch evaluation used 224-bit outward-rounded intervals, factorial and half-integer factorial formulas for ball volumes, and the stated Part 77 and Part 82 caps. All eight table enclosures and upward-rounded radii check. The low-rank 16-digit density inputs flagged in the earlier Part 82 audit appear in the May 10, 2025 edition of Cohn's Table 1, whose upper-bound column explicitly rounds upward. Its precision matters for the headline digits. [Cohn, archived table and rounding convention](https://dspace.mit.edu/server/api/core/bitstreams/6eda1660-ef8c-4d00-80cf-50805b5b2324/content)

| Cutoff | Draw | Independent enclosure for $S_1+S_2$ |
|---|---:|---:|
| $X_*$ | 154 | $(5.41158017,5.41158018)\,10^{-36}$ |
| $X_*$ | 160 | $(9.05634112,9.05634113)\,10^{-16}$ |
| $X_*$ | 161 | $(2.04097794,2.04097795)\,10^{-12}$ |
| $X_*$ | 162 | $(4.54658747,4.54658748)\,10^{-9}$ |
| $a$ | 167 | $(1.11564581,1.11564582)\,10^{-14}$ |
| $a$ | 168 | $(2.31912166,2.31912167)\,10^{-11}$ |

**Flag and fresh mark.** In the old draw-154 sum the unique largest term is $(38,0)$. Its radius lies in $(1901.39414053,1901.39414055)$, the term in $(10038946.28602,10038946.28604)$ and the sum in $(99653782.2375,99653782.2376)$. A single positive-height vector qualifies for that test. Its remaining 117 flag directions need never be realized in the counted window. In (1), keeping the terminal area gives the rank-two starting determinant $X$. Gauss reduction bounds both terminal basis lengths on the $s>24$ branch, and the other branch supplies a line of length at most 24. Until column $i$ is used, its height coordinate survives every forced old projection. The signed old choices can therefore be computed from the pre-draw history. Each tested positive height is below $q$ and preserves the uniform mark. Sign pairing cancels the factor two from retaining half a Voronoi cell. Monotonicity of the caps lets a single $(b,i,j)$ test cover every shorter eligible suffix. By Part 196, every wholly old first hit through draw 162 at cutoff $a$ has a predecessor at cutoff $X_*$ by draw 161.

**Raw and projected counts.** For a primitive two-space with $\det Z(S)\le X_*<q$, any nonzero parity rank multiplies its integer covolume by at least $q$. At rank zero, primitivity forces two independent input residues, whose prescribed images have joint probability $q^{-800}$. Zero padding preserves the plane and its area. Summing (3) through $m=1103$ gives a base-ten logarithm in $(-604.103983,-604.103982)$ for the raw first-moment bound over the entire prefix. For a projected plane, the lattice index must be taken in both $T$ and $F$, yielding (4). In (5) each compatible parity map has exactly $q^{400(p-r)}$ extensions and the selector test stays inside that fiber.

Enumeration of all $81^2$ pairs of two-by-two matrices over $\mathbb F_3$ reproduced the three rank counts and every fiber size. On the 27 selector graphs, primitive integer normals and primitive graph-dual normals gave identical planes graph by graph. Fifteen graphs had one plane, twelve had none, and one plane was coordinate-generated. Grouping the selectors by their pinned parity data in (5) also gave total mean $5/9=15/27$.

**Haar scope.** The terminal floor mean lies in $(2.21908300,2.21908302)\,10^{-13}$ and the sum over draws 0 through 406 in $(2.22022912,2.22022914)\,10^{-13}$. The latter is an independent-Haar comparison scale. A large raw ancestor can have a small quotient area in (4), and its frozen span is selected from the same matrix that supplies its parity data. Parts 184 and 190–196 supply no bound on that conditional selection weight at the required scale. The full projected-coordinate and surviving generic contributions therefore remain open.
