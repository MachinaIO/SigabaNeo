# The terminal void on projective lines of the mark

Consider plain LWE $(511,512,3329)$ with CBD(3) and the exact forward, no-lookahead first pass on the $qI$-first basis, with signed ambient lexicographic ties. At a fixed history, the last column has only **one** random value in the marked subgroup. Each individual competing lift of nonzero height that can beat the old winner specifies one value of that column in the mark. Thus the exact horizontal charge can be organized as a positive sum over projective lines, with no intersections between distinct lines. Within a line, the number of uncovered *scalars* matters. On an explicit width-506 terminal family, the covered points span all 400 mark dimensions but number only 803. The family's contribution is computed below. The averaged estimate on the other histories remains open.

## 1. Exact last-column count

Let $S$ be the state before a graph append, including the inherited frame. Write $L$ for its old lattice, $D=\det L$, $d=\beta-1$, $x_0$ for its signed shortest vector and $t=\|x_0\|$. The fresh height is one in physical units. In the old space $E$, the marked subgroup $H\subset E/L$ is a vector space over $\mathbb F_q$, since it is the image of the raw column space and $q=3329$ is prime. Conditional on $S$, the displacement $U$ is uniform on $H$. Put $Q_S=|H|$, $w(S)=\Pr(x_0\text{ wins}\mid S)$, and
$$
 I(S)=\mathbf1\{\lambda_1(\pi_{x_0^\perp}L)<cG_d(D/t)^{1/d}\},\qquad
 G_d=V_d^{-1/d},
$$
where $V_d$ is the unit ball volume. The horizontal charge at this draw is $h=\mathbb E[Iw]$. These laws concern the design alone. [First-pass law and audit](wall1_first_tour.md) · [Plane count and audit](wall1_plane_count.md)

For a class $a\in H$, let $\ell(a)$ be the minimum length of any representative in $E$. Among representatives of that length, let $\sigma(a)$ be the lexicographically earliest of all their two signs in the old ambient coordinates. For $k\ge1$ define the symmetric set
$$
 C_k=\{a\in H:\ \ell(a)^2+k^2<t^2
 \ \text{or}\ [\ell(a)^2+k^2=t^2\ \text{and}\ \sigma(a)<_{\rm lex}x_0]\}.
$$
These sets are nested, $C_{k+1}\subseteq C_k$. The tie test uses all closest representatives. At equal total length the old-coordinate part of a nonzero-height candidate cannot equal $x_0$ up to sign, since it has smaller norm than $t$.

**Theorem 1 (projective line formula).** Let $M=(q-1)/2$. For each one-dimensional $P\le H$ choose any generator $e_P$, and set
$$
 B(P)=\bigcup_{k=1}^{M}\bar k^{-1}
       \{a\in\mathbb F_q^\times:a e_P\in C_k\},\qquad b(P)=|B(P)|.
$$
At widths 406 and 506 of the original first pass, and on the width-506 restart,
$$
 w(S)=\frac{\mathbf1_{\{t\le1\}}+
             \sum_{\dim P=1}(q-1-b(P))}{Q_S}.                         \tag{1}
$$
The formula includes the trivial mark. Each summand is independent of the choice of generator.

*Proof.* At height $k$ the horizontal parts are precisely the representatives in $E$ of the class $kU$. Some vector at that height or its negative beats $x_0$ precisely when $kU\in C_{|k|}$. The earliest among the shortest horizontal vectors is still $x_0$, since adjoining the last coordinate preserves their order. Thus absence of these beaters is equivalent to a horizontal win.

At every graph draw $t\le q$. Indeed the processed integral graph $M_{\rm old}$ contains $q$ times each coordinate axis in its used space, by the graph congruence. Their projections span $E$, so some nonzero projection has norm at most $q$ and belongs to $L$. A nonzero multiple-of-$q$ height can consequently compete only at equality, with zero old component and height $\pm q$. The signed $x_0$ has its first nonzero coordinate negative, before the fresh coordinate, and wins that tie. For every other residue of a height, replacing it by its least absolute representative and allowing both signs keeps the same horizontal class up to sign and weakly decreases the length. It suffices to use $1,\ldots,M$. In particular each feasible equation $kU=a$ eliminates exactly the point $\bar k^{-1}a$ of $H$. In the raw column space this point pulls back to a coset of a common kernel. Two such cosets coincide or are disjoint.

At $U=0$ the fresh unit beats $x_0$ exactly when $t>1$. Every nonzero $U$ belongs to exactly one $P$, and writing $U=u e_P$ gives the excluded scalars $u\in B(P)$. Changing $e_P$ rescales the list bijectively. Counting the remaining points proves (1). ∎

## 2. Which subspaces contribute

For a line $P$, let $L_P=\{y\in E:y+L\in P\}$, an index-$q$ extension of $L$ of determinant $D/q$. Call a line *empty* if $b(P)=0$, and *partial* if $0<b(P)<q-1$. Let $n_0(S)$ count empty lines. On $t>1$, the following identifies them using the minimum of the extension.
$$
 \begin{array}{ll}
 \lambda_1(L_P)>\sqrt{t^2-1} &\Longrightarrow P\text{ is empty},\\
 \lambda_1(L_P)<\sqrt{t^2-1} &\Longrightarrow P\text{ is nonempty}.
 \end{array}                                                        \tag{2}
$$
At equality $P$ is nonempty exactly when some signed shortest vector of $L_P$ precedes $x_0$ in the old coordinates.

*Proof.* $P$ is nonempty exactly when $P\setminus\{0\}$ meets $C_1$. One direction uses nestedness and the other uses height one. Every nonzero vector of $L_P$ at or below the threshold has norm strictly below $t$, so its class in $P$ is nonzero. This proves (2) and the equality test. In particular the empty lines have extension minimum in the closed interval $[\sqrt{t^2-1},t]$, with the endpoint rule above. ∎

If $t\le1$, every displacement leaves the old winner horizontal, including at the unit tie. Averaging (1) therefore gives three nonnegative contributions.
$$
 h=\Pr(I=1,t\le1)+
 \mathbb E\!\left[
  \frac{I\,\mathbf1_{\{t>1\}}}{Q_S}
  \left((q-1)n_0(S)+
        \sum_{P\ {\rm partial}}(q-1-b(P))\right)\right].              \tag{3}
$$
This is an exact identification of the configurations carrying mass. It makes no claim about which contribution dominates at the recorded terminal time. A conditional upper bound on the partial term follows already from one shortest extension vector. If its nonzero class is $a e_P$ and $K\le M$ positive heights satisfy $\lambda_1(L_P)^2+k^2<t^2$ for $1\le k\le K$, then $b(P)\ge 2K$. The $2K$ distinct excluded scalars are $\pm a/\bar k$. Formula (1) also counts the extra coverage by other representatives and exact ties.

**Span test.** Write $r=\dim H$ and $s=\dim\langle C_1\rangle$, with empty span zero. All beating displacements lie in $\langle C_1\rangle$, by (1), so $w\ge 1-q^{s-r}$. In particular a proper span gives $w\ge1-1/q$. Under the equal horizontal allocation this would require
$$
 \Pr(I=1,\ s<r)\le 0.00488848\,q/(q-1).
$$
A low-dimensional span of the entire competitor list leaves *more* points in the void. Moreover, if $t>\sqrt2$, then $s=r$ on every recorded graph history. Indeed the projected unit horizontal coordinate axes have norm at most one, their classes generate $H$ by construction, and each such class passes the strict height-one test. A span dimension of $r$ does not measure the fraction of excluded points.

## 3. A full-span terminal list with exactly 803 covered displacements

**Proposition 2.** In the unconditioned width-506 restart let $m'=400,\ n_0=105,\ q=3329,\ Q=q^{400}$. Take all 105 restart columns equal to the same $v\in\mathbb F_q^{400}$ with at least two nonzero coordinates, followed by 406 zero columns. Leave draw 407 unread. This penultimate family has probability
$$
 p=\frac{Q-1-400(q-1)}{Q^{511}}.
$$
At each such history $I=1$, $H=\mathbb F_q^{400}$ under the raw column identification, and the complete set of displacements beating $x_0$ is
$$
 \{0\}\ \cup\ \{\pm e_i:1\le i\le400\}\ \cup\ \{\pm v\}.
$$
Consequently $w=1-803/Q$, and the family's exact contribution to the horizontal average is $p(1-803/Q)$. There are 401 partial lines, each with exactly two excluded scalars. Every other projective line is empty.

*Proof.* The restart lattice is the integral graph $x\equiv v\sum_j y_j\bmod q$. It contains no unit. Its squared-length-two vectors are precisely the signed differences of two distinct old graph axes. Indeed, two horizontal entries alone cannot have zero residue, a horizontal and a graph entry would require $v=\pm e_i$, and two graph entries of the same sign would require $2v=0$. The designated signed winner is $-e_{g_1}+e_{g_{105}}$, where the $g_j$ are the ordered graph coordinates. Each zero append supplies a unique fresh unit line, whose removal restores that same lattice and coordinate order. At the last draw $D=Q$, $t=\sqrt2$, and the mark is injective on raw columns because $L$ meets the pure horizontal coordinates in $q\mathbb Z^{400}$. Another independent old difference projects to length at most $\sqrt2$. The recorded cutoff $0.954G_{505}(Q/\sqrt2)^{1/505}>\sqrt2$, since $G_{505}\ge1/2$ and $Q/\sqrt2>4^{505}$. This proves $I=1$.

Only height one up to sign can compete. Its old component must be zero or an integral signed unit. The zero component gives the winning fresh unit at $U=0$. For an old horizontal coordinate unit the possible displacements are $\pm e_i$, and its negative signed coordinate beats $x_0$ at the first differing horizontal coordinate. For an old graph unit the congruence gives $\pm v$. In both cases of this latter sign, orient the competing vector to have $-1$ at $g_1$. It has zero at $g_{105}$ and precedes $x_0$. This exhausts the ball of squared radius two. The support assumption on $v$ gives 401 distinct lines. There are $Q-1-400(q-1)$ choices for $v$, and the 511 exposed columns are independent, which gives $p$. ∎

The contribution is below $Q^{-510}$, far below the horizontal allocation. The audited Part 144 family with two surviving old unit axes instead contributes its full binomial mass to the first term of (3). Both examples are statements about the marginal restart history law. [Horizontal families and audit](wall1_horizontal_core.md)

## 4. Möbius sum before conditioning on the history

For comparisons along a *fixed proposed path*, raw graph constraints have a different intersection structure. The following gives a subspace version of Part 145's subset sum. It retains the right-hand sides of the equations. [Fixed lifts and audit](wall1_averaged_charge.md) · [Finite-field arrangement counting](https://www.sciencedirect.com/science/article/pii/S0001870896900596)

**Proposition 3.** Let $A:V\to W$ be uniform linear over $\mathbb F_q$, $m'=\dim W$. A raw constraint $Ay=x$ prescribes $(y,x)\in\Gamma_A$, its graph. Suppose required pairs span $G\subset V\oplus W$. Inconsistent requirements, equivalently $G\cap(0\oplus W)\ne0$, give zero mass. Otherwise form $Z=(V\oplus W)/G$, let $W'$ be the image of $0\oplus W$, and let $B\subset Z$ be the images of the forbidden pairs. On the poset of spans of subsets of $B$, including zero, define in increasing dimension
$$
 c(T)=\mathbf1_{\{B\cap T=\varnothing\}}-\sum_{R<T}c(R).
$$
Conditional on the requirements, the exact void probability is
$$
 \sum_{\substack{T\\T\cap W'=0}}c(T)\,q^{-m'\dim T}.                 \tag{4}
$$
For unconditional joint mass multiply by $q^{-m'\dim G}$. If $0\in B$, every coefficient vanishes.

*Proof.* A consistent $G$ prescribes $A$ on a subspace of dimension $\dim G$ in $V$. Values on a complementary basis are free and independent. Given those requirements, $T\subset\Gamma_A/G$ has probability zero if $T\cap W'\ne0$. Otherwise its inverse image prescribes $\dim T$ further independent input values. For any realized graph the sum of $c(T)$ over the spans it contains equals the sum over all $T$ below $\langle B\cap(\Gamma_A/G)\rangle$. By the recursion this sum is one exactly when the graph contains no forbidden point. Taking expectations gives (4). The same argument on the full subspace lattice gives its usual Möbius inversion. Spans not generated by forbidden points have coefficient zero, as also follows by grouping the ordinary inclusion–exclusion sum by the span of each subset. ∎

For Part 145's $q$ affine lines $Y-iX=f(i)$, the grouped constant term is 1 and the line term is $-q/q$. An intersection point incident to $j\ge2$ lines has coefficient $j-1$, since the constant and its $j$ line coefficients sum to $1-j$. For $f=0$ there is one $q$-fold point. For $f(i)=i^2$ there are $\binom q2$ double points, since a fixed point solves a quadratic in $i$ and each pair intersects. Their respective voids are $(q-1)/q^2$ and $\binom q2/q^2$, reproducing the two recorded fractions. It is the **weighted multiplicity of compatible intersections**, even in rank two, that separates them.

For projected tests, absence means excluding every admissible raw lift at the appropriate prefix. Presence requires a union over those lifts, which can be disjointized before applying (4). For a fixed projected candidate and fixed projection the possible raw residue pairs form a finite set, even when the candidate has infinitely many integer lifts. Using a single representative can change the event. Earlier winner exclusions must remain in the path law. Equations (1)–(3) integrate the last draw conditional on that law. Formula (4) for a fixed raw list does not supply the distribution of lists across histories. [Availability and selection](wall1_annealed_selection.md) · [Averaged charges and audit](wall1_averaged_charge.md)

## 5. Small exact enumerations

All checks used scratch code and integer or rational arithmetic.

- **Affine intersections and conditioning.** Enumerating all $q^2$ points for $q=3,5,7$ gave void numerators $(2,3),(4,10),(6,21)$ for the two affine lists, respectively. In a separate check over $\mathbb F_3$, prescribe $Ae_1=(1,2)$ for $A:\mathbb F_3^3\to\mathbb F_3^2$. In quotient coordinates (two free input, two output coordinates), take forbidden labels $(1,0,0,0)$ twice, $(0,1,1,0),(1,1,2,2),(1,1,1,0),(0,0,0,1)$. Formula (4) grouped by dimension gives $1-4/9+4/81=49/81$. Exactly 49 of the 81 extensions passed direct evaluation. Adding a forbidden required pair gave zero by both methods.
- **Metric ties.** In Proposition 2's construction with $q=5$, two horizontal and three old graph coordinates, all 16 two-coordinate choices of $v$ and all 25 final columns were enumerated. Sorting every signed integral unit and root by squared norm and ambient coordinates is exhaustive because an old root is always available. Exactly 288 of 400 windows had a horizontal winner, agreeing for each $v$ with $25-(1+4+2)=18$.
- **Higher heights and partially covered lines.** In the full cube $L=5\mathbb Z^{10}$, full mark, enumerate all $5^{10}$ displacements. At height $k$ compare $k^2+\|[kU]_5\|^2$ to 25, using coordinatewise centered residues. The old negative first axis wins all equalities. Direct comparison at heights 1 through 5 and an independent count on lines gave 64,512 empty, 430,080 partial (two of four scalars covered), and 1,946,814 fully covered lines. Thus $4(64{,}512)+2(430{,}080)=1{,}118{,}208$ displacements won horizontally. There were 1,408,384 displacements beaten at a higher height but missed by height one. To reproduce the line count, group a generator by the counts $i,j$ of coordinates of centered absolute value 1 and 2. Its first two squared lengths are $1+i+4j,\ 4+4i+j$. Multiplication by 2 swaps $i,j$, and negation preserves both. Weight each type by $\binom{10}i\binom{10-i}j2^{i+j}$, omit zero, and divide the grouped counts by four. This checks why identifying the nonempty *lines* by height one does not suffice to count their covered *scalars*.

## Remaining estimate

**Conjecture (recorded terminal budget, open).** At draw 407 of the marginal width-506 restart ($c=0.954$), the right-hand side of (3) plus $\mathbb E F_*$ is at most $0.00977696$. Here $F_*$ counts saturated positive-height witness planes through the actual winner on draws without a horizontal witness, in conditional expectation. An equal allocation would give $0.00488848$ to each charge.

Equation (3) requires the joint law of old-plane incidence and the empty-line and missing-scalar counts on the selected penultimate lattice. Proposition 2 evaluates one full-span part of that law. None of the enumerations gives the frequency of empty or partial extensions in the remaining width-506 histories. The residual plane count also retains its multiplicity after a winner is selected. The Part 117 coupling transfers a bound for the terminal *event* at additive cost below $0.00022304$. Earlier original-pass charges can exceed the entire terminal budget. The projective formula holds at those draws as well, but gives no common small upper bound across time. [Suffix coupling](wall1_idea_round2.md) · [Terminal plane multiplicity and audit](wall1_averaged_charge.md)

## Audit

**Verdict — SOUND.** Equations (1)–(4), the 803-point terminal count and all the reported small enumerations check out. The terminal budget remains open.

**Conditional exclusions and ties.** Part 108 gives uniform $U$ on $H$ after fixing the history and ambient frame. The projected $q$-axes from all used coordinates span the old space, giving $t\le q$. At height $q$ an equality requires zero old component, so the first negative coordinate of $x_0$ settles the tie in its favor. At any tie of nonzero height, the old part has norm strictly below $t$. Its coordinates therefore decide the comparison with $x_0$ before the fresh coordinate is read. Both signs of every closest representative are available in the two opposite layers, which justifies $\sigma(a)$. Replacing a height by its least absolute residue preserves the horizontal class up to sign and can only improve its length.

For a nonzero height residue, multiplication by $\bar k$ is a bijection **on $H$**. Different lifts or heights may exclude the same $U$, and the union in $B(P)$ counts it once. The zero class survives exactly for $t\le1$, in which case every class survives. For $t>1$ the nonzero survivors partition by their unique line, with $q-1$ on each empty line, $q-1-b(P)$ on each partial line and zero on each full line. This gives (3) also for the trivial mark. Nestedness of $C_k$ reduces line nonemptiness to height one. At the threshold in (2) every shortest extension vector has nonzero class, since its length is strictly below $t$. For the $2K$ bound the residues $\pm1,\ldots,\pm K$ are distinct modulo $q$. The span bound follows since scaling stays within the span, and the projected horizontal axes generate $H$ and pass the strict height-one test when $t>\sqrt2$.

**Fixed raw constraints.** If $T$ avoids $W'$ it fixes $\dim T$ independent additional inputs, each costing $q^{-m'}$. A nonzero vertical element makes the prescriptions inconsistent. On the full subspace lattice the coefficient is explicitly
$$
 c(T)=\sum_{\substack{R\le T\\B\cap R=\varnothing}}
 (-1)^j q^{\binom j2},\qquad j=\dim T-\dim R.
$$
A gap of dimension $j$ has $\genfrac{[}{]}{0pt}{}{j}{i}_q$ intermediate subspaces of relative dimension $i$. The Gaussian binomial identity $\sum_i\genfrac{[}{]}{0pt}{}{j}{i}_q(-1)^i q^{\binom i2}=\mathbf1_{\{j=0\}}$ gives the inversion. Grouping inclusion–exclusion by the actual span gives the same coefficients, zero off the poset in Proposition 3. The calculation retains the right-hand sides of the equations. Its application to a proposed path requires the earlier winner exclusions.

**Terminal family.** The 406 fresh units remove their own coordinates and preserve the restart graph. The old signed minimum is $-e_{g_1}+e_{g_{105}}$ because choosing the latest possible positive coordinate wins among the old differences starting at $g_1$. An independent difference survives projection with length at most $\sqrt2$, strictly below the cutoff. For $U=\pm v$, a competitor with old component $-e_{g_1}$ has the required fresh sign and precedes $x_0$ at $g_{105}$. The negative horizontal axes handle $U=\pm e_i$. Integrality makes zero and signed units exhaustive at height one. The 400 coordinate lines and $\langle v\rangle$ are distinct, giving $1+2(400+1)=803$ covered displacements with full span. Of the $Q^{511}$ equally likely prefixes, $Q-1-400(q-1)$ qualify. Their exact horizontal contribution is
$$
 \frac{(Q-1-400(q-1))(Q-803)}{Q^{512}}
 <Q^{-510}<0.00488848.
$$
This is a contribution under the marginal restart law. The other histories and the residual positive-height moment still enter the $0.00977696$ budget. Part 117 transfers a terminal event probability with its stated coupling error. Transferring a plane-count expectation would additionally require a multiplicity bound on disagreements.

**Independent exact checks.** Fresh scratch programs gave the following results.

| Check | Enumeration | Result |
|---|---|---|
| Signed metric ties, $q=5$ | Sorted all signed units and two-coordinate roots by squared length and ambient coordinates. Tested the graph congruence on each of 16 choices of $v$ and each of 25 final columns. | The seven predicted displacements beat $x_0$ for every $v$. There were 288 horizontal wins in 400 windows. |
| Conditional Möbius sum, $q=3$ | Enumerated all 212 subspaces of the four-dimensional quotient. Compared full-lattice inversion, the generated-span recursion and direct evaluation of the 81 extensions of the prescribed input. | Compatible coefficient sums by dimension were $1,-4,4$, giving $49/81$. Adding the required pair to the forbidden list gave $0/81$. |
| Affine lists | Counted points incident to no forbidden line at $q=3,5,7$. | The two void numerators were $(2,3)$, $(4,10)$ and $(6,21)$. |
| Cube, $q=5$ | Tested all $5^{10}$ displacements at heights 1 through 5, keeping the old winner at equality. Tabulated the four scalars on each line using its unique generator with leading nonzero entry one. | There were 64,512 empty, 430,080 partial and 1,946,814 full lines. Every partial line covered two scalars. There were 1,118,208 horizontal wins and 1,408,384 displacements beaten only above height one. |
