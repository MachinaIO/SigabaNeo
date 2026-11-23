# Counting framed states for the radius-26 quotient event

A reachable framed parent with mark group of order $h$ fixes one coset for **each of its 510 raw columns**. Its reach probability is therefore at most $h^{-510}$. At maximal mark rank this is exact. The other half of the proposed count is unresolved. Even requiring two raw lifts in the Part 184 annulus, a saturated raw plane, and two independent congruences modulo $q$ gives an existence event of probability **one** if the selected projections are dropped. Below, a fixed pair also witnesses hits at many distinct *reachable* parents. Counting the projected planes requires controlling which frames the shortest-vector rule selects.

## The reach bound

Use the unconditioned width-506 marginal restart of Parts 183–186. Write $V=\mathbb F_q^{400}$, $q=3329$, and $Q=|V|$. The initial graph has 105 columns. After 405 further columns there are $Q^{510}$ equiprobable prefixes. Write $S=(F,M)$ for their framed state, with retained space $F$ in the original ordered axes, projection $P_F$, and retained lattice $M$. At draw 406 let $v$ be the selected window winner, $M'$ the quotient by $v$, and $x$ its designated signed shortest vector. The event is $E=\{\lambda_1(P_{x^\perp}M')\le26\}$. Draw 407 is unused. All counts here refer to the marginal restart. [First-tour law](wall1_first_tour.md) · [Finite chain and audit](wall1_finite_chain.md#audit) · [Local-comparison audit](wall1_local_comparison.md#audit)

Use the graph convention $b+Ac=0\pmod q$. Put $\phi_S(a)=[P_F(a,0)]\in F/M$, $C_S=\ker\phi_S$, $H(S)=\operatorname{im}\phi_S$, $h_S=|H(S)|$. The append displacement then has the sign $-\phi_S(a)$. Let $N(S)$ count prefixes reaching $S$, and $k_S$ the number of displacements yielding $E$. The exact probability, including horizontal wins, is
$$
 \Pr(E)=\sum_S \frac{N(S)}{Q^{510}}\frac{k_S}{h_S}.
 \tag{1}
$$
Indeed each such displacement has $Q/h_S$ preimages among the $Q$ choices of the last column. The denominator is $Q^{511}$ if the numerator counts completed designs.

**Path count.** At time $i$ let $n=105+i$. For a fixed initial graph and a specified sequence $\gamma$ of actual marks, the number of raw paths is $\prod_{j=0}^{i-1} (Q/h_{S_j})$. The initial framed graph recovers its matrix modulo $q$. Induction gives the product because at each step all raw columns in the mark fiber give the same next state. Consequently
$$
  \frac{N_i(S)}{Q^n}
  = Q^{-105}\sum_{\gamma\to S}\prod_{j=0}^{i-1} h_{S_j}^{-1},
 \tag{2}
$$
where the sum includes the initial graph in the path specification. For an output recording the embedded quotient and oriented positive-height winner of height coprime to $q$, Part 176 gives a unique incoming state and mark. The raw multiplicity of that output is $N_i(S)Q/h_S$. This uses exactly the local uniqueness hypothesis `hinv` of `raw_fiber_card`. A product for one path bounds the whole sum only with control of the number or weights of its paths. In particular, the recorded winner in the inverse theorem and the horizontal sector both matter. [Inverse-branch audit](wall1_inverse_branch.md#audit) · [Lean statement](../../SigabaNeo/Lib/Lattices/Research/Wall1/InverseBranch.lean)

**Framed column bound.** There is a direct upper bound on the sum in (2) that needs no inverse on horizontal wins. For each $j\le n$, every design reaching $S$ contains $(-a_j,e_j)$ in its raw graph. Its projection belongs to $M$, so
$$
 \phi_S(a_j)=[P_F(0,e_j)]\quad(1\le j\le n).
 \tag{3}
$$
Everything on the right is known from the frame. Reachability makes each of these affine fibers nonempty, and each has size $|C_S|=Q/h_S$. Thus
$$
 N_i(S)\le |C_S|^n,\qquad \Pr(S_i=S)\le h_S^{-n}.
 \tag{4}
$$
Equality holds at $h_S=Q$ since a reachable state then identifies all raw columns. At other ranks (3) can admit designs whose signed winners select a different frame.

For $B_d=\#\{S:k_S>0,\ h_S=q^d\}$ at time 405, a rigorous version of the proposed cardinality bound is
$$
 \Pr(E)\le \sum_{S:k_S>0}h_S^{-510}\frac{k_S}{h_S}
       \le \sum_{d=0}^{400} B_d q^{-510d}.
 \tag{5}
$$
One can also cap the right side by one. Using the actual maximum reach probability times $\sum_d B_d$ follows directly from (1). Stratification in (5) keeps the small probabilities of large-rank states. Charging all rank-deficient histories as an exit already costs more than $0.72982006$ at the first suffix step. This is a statement about rank loss, with no implication that those histories hit $E$. [Finite-chain audit](wall1_finite_chain.md#audit)

## What the primitive-plane count buys

On $E$ let $y$ be a shortest nonzero quotient point in $P_{x^\perp}M'$, and lift it in $M'$ to $w$ with $|\langle w,x\rangle|\le\|x\|^2/2$. Shortestness gives $\|x\|^2\le\|w\|^2\le 26^2+\|x\|^2/4$, so both lengths are at most $52/\sqrt3$. The pair spans a saturated plane in $M'$ because $x$ is primitive and $y$ is primitive modulo $\mathbb Zx$. Lift $x,w$ to raw vectors $z_1,z_2$ by reverse rounding along the 406 frozen lines. Both then have squared length at most
$$
 B^2=406q^2/4+4\cdot26^2/3=6749090177/6.
$$
Indeed the orthogonal component at each discarded winner of length $s_j\le q$ costs at most $s_j^2/4$. The projected vectors are independent. Their raw span over $\mathbb Z$ is also saturated *in the raw graph*: its image is saturated, and its real span projects injectively. This independence gives no uniform rank-two guarantee on the **input residues** of the lifts. On the Part 184 raw-good event both raw lengths exceed 250. [Penultimate projection and audit](wall1_penultimate_projection.md#audit)

For a fixed ordered pair $z_l=(b_l,c_l)$, let $D=[c_1\ c_2]$ and $U=[b_1\ b_2]$ over $\mathbb F_q$, and put $s=\operatorname{rank}D$. With $I_z$ denoting joint membership, rowwise linear algebra gives
$$
 \Pr(I_z)=\mathbf1_{\ker D\subseteq\ker U}\,Q^{-s}.
 \tag{6}
$$
In fact, one can intersect these conditions with (3). Fix a parent and final mark, hence a coset for *all 511 columns*. Choose any representative matrix $A_0$ of those cosets. All candidates have the form $A_0+T$ with $T:\mathbb F_q^{511}\to C_S$. The membership equation is $TD=-U-A_0D$. It is soluble exactly when the right side takes values in $C_S$ and kills $\ker D$. In that case the number of algebraically compatible designs is exactly $|C_S|^{511-s}$, by extension from $\operatorname{im}D$ to a basis. The number actually selecting the specified branch and plane is at most this count. For a compatible pair, multiplying the affine-coset fraction $h_S^{-511}$ by $Q^{-s}$ would undercount the algebraic intersection by $h_S^s$. Equations (3) and (6) can constrain the same columns. [Part 41 tuple count](wall1_sublattice_union.md) · [Part 184 pinned-mark calculation](wall1_penultimate_projection.md#audit)

There is also a direct upper bound on the number of compatible parents for a pair. Write $\epsilon=1$ if row 511 of $D$ is nonzero, and $\epsilon=0$ otherwise. For a consistent pair the $Q^{511-s}$ member designs project onto exactly $Q^{510-s+\epsilon}$ distinct raw prefixes. When $\epsilon=0$ each compatible prefix has $Q$ completions; when $\epsilon=1$ it has exactly one, since one linear combination fixes the last column. Every parent compatible with a *selected* occurrence of this pair is reached by at least one of these prefixes. Thus for any witness list $\mathcal W$ covering the event,
$$
 \#\{S:k_S>0\}\ \le\ \min\!\left(Q^{510},\ \sum_{z\in\mathcal W:\,\Pr(I_z)>0} Q^{510-s(z)+\epsilon(z)}\right).
 \tag{7}
$$
For a list covering only good hits, restrict the set on the left to parents admitting a good hit. This bound needs no assumption that a pair determines a frame. It pays for every raw prefix that admits the congruence, whether or not its projection meets the radius cutoff.

**The raw-pair relaxation covers every design.** Fix two distinct input axes $e_j,e_k$. For each axis choose $c=e_j$ or $e_k$ and the centered representative $b$ of the negative graph column. Then $\|(b,c)\|^2\le1+400\cdot1664^2=1107558401<B^2$. If its length is at most 250, add $q$ in the first horizontal coordinate. The new length is strictly greater than 250 and at most $q+250<B$. Do this separately for the two columns. The raw pair now satisfies the Part 184 annulus, has input rank two even modulo $q$, and spans a direct summand of the raw graph since its input coordinates have a unit minor. Over all designs there are exactly $Q^2$ fixed pairs in this construction: the two residues recover the original two columns, and the representative adjustment is deterministic. Their membership events partition design space. Taking $j,k\le510$ also makes their prefix counts in (7) sum to exactly $Q^{510}$, the entire prefix space. Thus their contributions to (6) alone sum to $Q^2Q^{-2}=1$. This obstruction already occurs within the rank-two sector; removing dependent pairs cannot repair the unselected first moment. The lengths used here are the deterministic raw lift caps. The short lengths in the *selected quotient* are additional restrictions. Part 185 also exhibits a fixed unselected coordinate kernel with short quotient witnesses at the actual ranks. [Winner-alignment note](wall1_winner_alignment.md)

**One fixed pair can occur at many selected states.** Prescribe the first two restart columns to be the first two horizontal units, and take each of the other 103 restart columns to be any nonzero element of $V$. Prescribe zero columns on the next 405 draws. The old graph has no unit vector, so the fresh unit axis wins uniquely up to sign at each zero draw. Its projection preserves the initial graph in the original axes. These choices give $(Q-1)^{103}$ distinct reachable parents with $h_S=Q$. At final mark zero the same argument preserves their graph once more. In all of them $(-e_1,e_1)$ and $(-e_2,e_2)$ are orthogonal graph members of length $\sqrt2$ (horizontal and input indices shown separately). To ensure the first is the designated line, restrict the other columns to avoid all signed horizontal units and all previously used columns up to sign. Then a squared-length-two member has one horizontal and one input entry from the first two columns, or two input entries from a repeated signed column. The latter is excluded, and two horizontal entries alone cannot satisfy the congruence. Signed ambient ties therefore designate the first line. Projecting off it preserves the second vector at length $\sqrt2$. In fact this is the unique shortest quotient line. Any competitor of length at most $\sqrt2$ has a lift reduced along the first vector with squared norm at most $2+2/4<3$. Integrality forces such a nonzero lift onto one of the two enumerated shortest lines. At least $(Q-1010)^{103}$ distinct parents satisfy these stronger restrictions, since at each choice at most $1+800+2\cdot104$ residues are forbidden. For *all* $(Q-1)^{103}$ parents the two independent short vectors suffice for $k_S>0$ regardless of which line wins. The restricted example makes the same raw pair a witness through the designated line. These histories are inside Part 184's raw exit. Their contribution along the prescribed zero completions is tiny. Their role is to disprove uniqueness of a compatible reachable frame given a pair.

## Comparison with Part 41 and remaining estimate

Part 41 counts all admissible sublattices of a full planted embedding; its shear family gives a bad prefix on every design at widths through 1007. Here the design has a single selected frame at each time, and $E$ is a different event on the marginal restart. A determinant-admissible sublattice never selected by a design contributes zero for that design in (1). The reach weight can therefore improve a union bound, and Part 41 supplies no impossibility theorem for (5). But neither its tuple count nor Part 176 bounds $B_d$ at the scale needed in (5). Replacing selection by raw membership spends at least one in the explicit subfamily above. Conversely the many reachable frames for a fixed pair do not rule out a small **weighted** sum.

An exact formulation of the missing count is to choose $x,y,w,z_1,z_2$ by deterministic ties and shortest lifts, retaining the rounding bounds above. Let $D_z$ be the event that this pair is selected and $E$ and the Part 184 raw and dual good events hold. Then the disjoint events $D_z$ exhaust the good hits. The required sum is $\sum_z \Pr(I_z)\Pr(D_z\mid I_z)$ over the finite pair annulus with positive membership mass. The first factor is (6); the second includes the selected frame and both shortest-vector comparisons. Equivalently (1) requires the parent-weighted fraction of passing marks. The two audited exits cost less than $4.249\cdot10^{-12}+8.147\cdot10^{-14}$ in total, leaving a sufficient upper bound of $3.9999566953\cdot10^{-7}$ on the good-hit sum. The separate draw-407 discrepancy is irrelevant to $E$. **Conjecture.** $\Pr(E)\le4\cdot10^{-7}$. The reach bound, the affine intersection count and the two examples above do not establish that estimate. [Part 183 audit](wall1_terminal_tail_047.md#audit) · [Parts 184–186](../PROOF_GAP.md)

## Finite checks

At $q=2$ take four horizontal axes and two input columns $a,b\in\mathbb F_2^4$. The signed first winner is $-2e_1$ exactly when $1+|a|,1+|b|,2+|a+b|$ are all at least four, where the bars are Hamming weights. These are the least squared lengths in the three nonzero input parity classes, and a period axis attains four. On this sector the retained state is the graph given by deleting the first row, its mark order is eight, and (4) permits four designs per state. Integer enumeration of all 256 ordered pairs yielded 12 designs in the sector and 12 distinct projected matrices, each reached there once. The retained space fixes the removed line, so these are also their full reach counts. This checks strictness of (4). The enumeration groups by the two three-bit column tails after testing the three weight inequalities. Separately, 70-decimal-digit outward interval arithmetic gave $33538.75911290<B<33538.75911291$ and $33280.00001502<\sqrt{1+400\cdot1664^2}<33280.00001503$. All comparisons for the pair relaxation can equally be made by squaring integers.


For the affine intersection, take $V=\mathbb F_3^2$, three columns, and $C$ the first coordinate line. Fix second coordinates $(1,2,0)$, and let $A_0$ have those coordinates and zero first row. Enumerate all $9^3$ matrices for $U=-A_0D$. The two input vectors $(1,0,1),(0,1,1)$ gave 9 member designs, 9 compatible two-column prefixes and 3 members in the specified cosets. Replacing them by $(1,0,0),(0,1,0)$ gave counts $(9,1,3)$. Using $(1,0,1),(2,0,2)$ gave $(81,81,9)$. These test both final-pivot cases of (7) and both ranks in the affine intersection formula.

## Audit

**Verdict — SOUND.** No correction is needed for the unconditioned width-506 restart with the ordered ambient frame and signed lexicographic ties. The estimate $\Pr(E)\le 4\cdot10^{-7}$ remains open.

**Reach and inverse multiplicity.** For each of the 510 prefix coordinates, projecting the raw graph generator $(-a_j,e_j)$ gives (3) with the displayed sign. The set of prefixes reaching a fixed frame is contained in the Cartesian product of those 510 fibers. Its size is at most $(Q/h_S)^{510}$ without any conditional independence assumption. At $h_S=Q$ the product is a singleton, and reachability supplies its element. Part 108 gives the uniform next mark for every such prefix, including prefixes whose next winner is horizontal. Part 176 uses the embedded output and the oriented coprime positive-height winner to identify the parent and mark. The local hypothesis `hinv` in `raw_fiber_card` gives the claimed multiplicity for that output. Rechecking `InverseBranch.lean` succeeded, with only `propext`, `Classical.choice` and `Quot.sound` reported for the inverse and counting lemmas.

**The probability-one relaxation.** For either fixed input axis, a centered lift of length at most 250 moves to a length in $[q-250,q+250]$ under the prescribed adjustment. Both endpoints lie strictly inside the annulus. Reading off input coordinates $j,k$ defines a retraction from the raw graph onto the subgroup generated by the two adjusted lifts. This proves saturation, and the same input minor has determinant one modulo $q$. Each possible pair specifies exactly the two design columns by reduction modulo $q$. Its membership event has $Q^{509}$ completed designs, and the $Q^2$ events partition all $Q^{511}$. With $j,k\le510$, the same partition has $Q^{508}$ prefixes per pair. This establishes probability one for raw membership with the stated length, saturation and rank constraints.

**Multiplicity after both selections.** Each zero append splits off a unit axis orthogonal to an integral graph with no unit vector. Removing that axis leaves the original graph in its original frame, with horizontal kernel zero modulo $q$. Distinct restart matrices therefore give distinct maximal-rank parents. Under the signed-column exclusions, the only squared-norm-two lines are the displayed pair. The negative first horizontal coordinate decides the first tie. A competitor at quotient length at most $\sqrt{2}$ lifts, after rounding, to a graph vector of integral squared norm at most $5/2$. Of the two possible lines only the second has nonzero projection. This verifies the same designated pair in at least $(Q-1010)^{103}$ reachable parents. Both raw vectors have length $\sqrt{2}$, so these histories contribute to the radius-250 exit. Their multiplicity gives no lower bound for the good-hit sum.

**Independent finite checks.** Direct enumeration of signed vectors through squared norm four for all 256 binary designs gave 12 wins for $-2e_1$, with 12 distinct retained lattices of multiplicity one in the same retained space. Enumeration of all 729 ternary designs in each case gave the triples $(9,9,3)$, $(9,1,3)$ and $(81,81,9)$ in the stated order. In a separate $q=5$ toy with two horizontal and three input coordinates, the two-axis construction partitioned all 15,625 designs into 625 classes of 25. The signed-column exclusions in this dimension also gave 20 distinct parents with the prescribed two shortest lines after zero appends. Exact rational squaring verified both printed radius intervals and the good-hit budget. Part 41 concerns all determinant-admissible prefixes in the planted embedding. As in Parts 183–187, the good-hit sum still depends on the selected frame. The draw-407 discrepancy adds no charge to this draw-406 event.
