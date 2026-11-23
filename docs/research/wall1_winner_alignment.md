# What winner alignment says about an integer relation

Conditioning on a raw vector gives an exact first moment for any *prescribed* set of additional raw vectors. The difficulty is turning the small orthogonal projection into such a set. For the shortest raw lift of a quotient witness, zero is already a closest integer combination of the winners to every point of the segment from zero to the lift. Integer multiples beyond that segment give a precise test involving returns in a 407-dimensional torus. A width-three example below has genuine shortest winners, the same prime and both physical cutoffs, and **no** nonzero raw relation of length at most 250, at any multiplier. The width-506 probability remains open.

## Which vector is being counted?

Use the marginal restart through draw 406. Write $L=L(A)\subset\mathbb Z^{400+511}$ for the graph with equation $b+Ac=0\pmod q$, where $q=3329$ and $Q=q^{400}$. Let $T$ be the span of the 406 frozen directions and the designated shortest vector of the retained lattice, embedded in the raw frame. Put $K=L\cap T$ and let $P$ project onto $T^\perp$. Then $K$ has rank 407, and $E$ says that $PL$ has a nonzero point of norm at most 26. These are design events. Part 135's independent plant supplies no randomness to this conditional law. [Parts 108, 135, 176 and 183](../PROOF_GAP.md)

The proposed sum over all long lifts diverges. Each nonzero quotient witness has infinitely many lifts obtained by adding multiples of a nonzero element of $K$. Their fractional loss tends to one, and the zero design has positive mass and satisfies $E$. A fractional loss threshold alone also allows zero projection and does not enforce the absolute upper bound 26. Use the signed shortest quotient point $p$ and its shortest raw lift $y$, with the fixed lexicographic tie rules. On $E$ the squared lifting radius is at most $B^2=6749090177/6$ by reverse rounding. Let $G$ be the joint raw-minimum and dual-floor good event of Part 184, and $D_y$ the event that $E\cap G$ selects this particular lift. Then
$$
 \Pr(E\cap G)=\sum_{250<\|y\|\le B}\Pr(I_y)\Pr(D_y\mid I_y),\qquad I_y=\{y\in L\},
$$
omitting zero-mass terms. The audited exit bounds leave $3.9999566953\cdot10^{-7}$ as a sufficient budget for this sum. [Part 183, raw lifts](wall1_terminal_tail_047.md) · [Part 184, finite sum and audit](wall1_penultimate_projection.md#audit)

## The conditional first moment

Fix $y=(b,c)$ with $\bar c\ne0$, using bars for residues. For $w=(d,e)$ fixed independently of the design, the exact answer is
$$
 \Pr(I_w\mid I_y)=
 \begin{cases}
 Q^{-1} & \bar e\notin\mathbb F_q\bar c,\\
 1 & \bar e=t\bar c,\quad \bar d=t\bar b,\\
 0 & \bar e=t\bar c,\quad \bar d\ne t\bar b .
 \end{cases}                                                     \tag{1}
$$
Each row of $A$ is uniform subject to its pairing with $\bar c$. Pairing with a second independent input is uniform, independently in all 400 rows. In the dependent case the already specified pairing decides membership. More generally, a fixed tuple whose inputs add $s$ dimensions modulo $\mathbb F_q\bar c$ costs $Q^{-s}$ if every input relation is respected by the prescribed outputs, and has probability zero otherwise. This follows by extending an input basis. As a finite check, take two input and two output coordinates over $\mathbb F_3$, and condition on a specified first column. For every one of the nine first columns and all 81 choices of the second test vector $(d,e)$, enumeration of the nine completing matrices gave exactly the three cases of (1). If $\bar c=0$, membership requires $\bar b=0$, in which case the law of $A$ is unchanged.

For a bounded deterministic search set depending on $y$, summing (1) is a computable conditional first moment. In particular, let $C(t y)$ be the coordinatewise centered representative mod $q$. For $\bar c\ne0$ there is the following dichotomy.

* If some $1\le t<q$ has $\|C(t y)\|\le250$, then $I_y$ forces a nonzero raw vector of norm at most 250. The summand for $D_y$ vanishes.
* Otherwise, conditional on $I_y$, the probability of **any** nonzero raw vector of norm at most 250 is below $4.249\cdot10^{-12}$.

Indeed the centered representative minimizes norm in its residue class. The zero class has no nonzero vector this short. In the second case every possible short member costs $1/Q$ by (1). Taking sign pairs and applying Part 183's integer-ball majorant proves the claim uniformly in $y$. For a numerical check put $z=250\sqrt{2\pi/911}$ and $\Theta=1+2e^{-\pi z^2}/(1-e^{-3\pi z^2})$. At 60-decimal-digit outward precision, $e^{911/2} z^{911}\Theta^{911}/(2Q)\in(4.24859833,4.24859835)\cdot10^{-12}$. Thus modular division or rescaling along the known residue line gives a deterministic exclusion test. This conditional bound concerns the raw short-vector event. It gives no upper bound for $D_y$ on the surviving lines. [Part 183, raw first moment](wall1_terminal_tail_047.md)

## Real alignment and integer rounding

Write $y=u+p$ with $u\in T$ and $0<\|p\|\le26$. Canonical shortest lifting gives $u\in\operatorname{Vor}(K)$, the closed Voronoi cell at zero. Indeed $2\langle u,k\rangle\le\|k\|^2$ for every $k\in K$, by comparing $y$ with $y-k$. By symmetry and convexity, $a u\in\operatorname{Vor}(K)$ for every real $|a|\le1$. Consequently
$$
 \min_{k\in K}\|a y-k\|=|a|\,\|y\|\qquad (|a|\le1).                  \tag{2}
$$
This covers all integer combinations of raw winner lifts, including ties. Despite the fractional loss exceeding 0.989184, rounding any point of this segment to the winner lattice cannot improve on zero. The putative common winner length of 55 cannot be used as a raw basis bound either. The winners live in successive projected windows, and the first suffix winner has length $q$ with probability exceeding 0.72982006. [Finite chain, Theorem 3 and audit](wall1_finite_chain.md) · [Part 183, physical scale](wall1_terminal_tail_047.md)

For an integer $t\ne0$, Pythagoras gives the exact rescaling criterion
$$
 \min_{k\in K}\|t y-k\|^2=t^2\|p\|^2+\operatorname{dist}(t u,K)^2.       \tag{3}
$$
As $t$ and $k$ vary, these vectors exhaust the raw members with nonzero projection on the line $\mathbb Rp$ and zero component perpendicular to that line in the quotient. The intersection of $PL$ with that line is $\mathbb Zp$ by shortestness of $p$, and two lifts of $tp$ differ by $K$. Thus for radius $R$, only $1\le |t|\le\lfloor R/\|p\|\rfloor$ can work. At the endpoint $\|p\|=26, R=250$ there are nine positive trials. Each needs the class $t u+K$ to approach zero to distance at most $\sqrt{R^2-t^2\|p\|^2}$. This torus and its starting class depend on the selected kernel. Uniformity on the affine space of matrices in (1) supplies no uniform law for either. On the raw-good event all these returns fail at $R=250$.

Dropping selection altogether gives a quantitative check at the **actual ranks**. Choose the fixed coordinate plane $T_0$ spanned by all 400 horizontal axes and the first seven input axes. For *every* design the projection of $L$ off $T_0$ is exactly $\mathbb Z^{504}$, since each graph column projects to zero or a unit axis. The kernel $L\cap T_0$ is saturated in $L$. On raw-good designs even a shortest lift of a shortest quotient point has length greater than 250, while its projection has length one. Hence this relaxation with a saturated rank-407 kernel and canonical lifts holds with probability greater than $1-4.249\cdot10^{-12}$. The comparison uses an unselected plane. It identifies the information lost by charging only membership and the existence of a plane.

## A selected example with no short raw relation

In the following smaller $qI$-first chain, the minimum in (3) exceeds $250^2$ at **every** nonzero integer multiplier. Use width three, 18 horizontal axes and four input columns, with the same signed ambient tie rule. Describe graph columns by their horizontal lifts, so the matrix in the plus-sign convention is their negative. Give each column its own disjoint block of four of the first 16 horizontal rows, with entries $h=(19,71,283,947)$ and zeros in the other private blocks. On the last two horizontal rows the four columns, in order, are
$$
 (56,0),\quad(0,56),\quad(392,0),\quad(0,392).
$$

**Raw check.** Let $c_q(v)$ denote the centered residue of an integer. For $1\le t\le250$, direct integer minimization gives
$$
 \min_t\left(t^2+\sum_{j=1}^4 c_q(t h_j)^2\right)=428269
 \quad\text{at }t=190 .
$$
Any nonzero input coefficient of magnitude at most 250 incurs at least this squared norm in that coefficient and its own four rows. A larger coefficient already exceeds the cutoff, and a nonzero purely horizontal member has norm at least $q$. Hence the entire raw lattice has minimum above 250.

**Selected chain.** Processing the initial $q$-axes removes the first 16 by the signed tie rule. The retained orthogonal factors initially have lengths $q,q$. Each append acts in one factor and its fresh height coordinate, leaving the other factor orthogonal. Before the first update of either factor, the squared norm minimized at positive height $t$ is $t^2+c_q(56t)^2$. The minimum is 3137 at height one, strictly below the squared horizontal period. After projection the factor has length $q/\sqrt{3137}$, by area divided by winner length. The projected original horizontal unit in this factor has signed length $\pm1/\sqrt{3137}$, by the determinant with the winner $(56,1)$. For its second update the positive-height minimum is therefore
$$
 \min_{t\ge1}\left(t^2+c_q(392t)^2/3137\right)=156801/3137
$$
at height one. This too beats the horizontal period. Its projection leaves a factor of length $D=q/\sqrt{156801}$. At the four appends the untouched lengths are respectively $q,q/\sqrt{3137},q/\sqrt{3137},D$, each strictly above the corresponding winning length. Thus all four planar winners are global shortest vectors of their windows. The final retained lattice is an orthogonal square of side $D$. Removing either designated shortest line leaves minimum $D\in(8.40696774,8.40696775)$. Every raw lift of this witness loses more than 99.8869% of its squared norm, even though every nonzero raw remainder in (3) exceeds 250.

The integer checks can be reproduced by taking $c_q(v)=((v+1664)\bmod3329)-1664$. Enumerate heights 1 through 56 for the first minimum and 1 through 7 for the second. Larger heights already exceed the height-one candidate. The private-block calculation uses all 250 heights. Squaring the decimal endpoints verifies the enclosure for $D$. This is a counterexample to an implication from the selection rule and the two cutoffs alone. Its width and initial horizontal phase differ from the marginal restart.

## Remaining probability estimate

Conditioning first on $I_y$ charges each fixed extra relation according to (1), without a spurious factor of $1/|H|$. To apply it one still needs either a deterministic family of witnesses, small in that conditional first moment, that is forced by **width-506 selection**, or a bound directly on the selected classes in (3) and the weights of their histories. The inverse identifies a compatible positive-height parent and mark, the Voronoi law transports a uniform law on a given set of marks, and character transport preserves the specified pairing. None of these identities bounds the total mass of the compatible parents. **Conjecture.** $\Pr(E)\le4\cdot10^{-7}$ for the marginal restart. The conditional counting identity, rounding obstruction and examples above leave this estimate undecided. [Part 176 and audit](wall1_inverse_branch.md) · [InverseBranch.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/InverseBranch.lean) · [VoronoiMarkLaw.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/VoronoiMarkLaw.lean) · [CharacterTransport.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/CharacterTransport.lean)

## Audit

**Verdict — SOUND.** The width-three example disproves the implication from shortest-vector selection and the two length cutoffs alone. The probability of the penultimate event in the width-506 marginal restart remains open.

**Conditional counting.** Given $I_y$ with $\bar c\ne0$, prescribing the images of $s$ further independent input directions fixes $s$ independent field elements in each of 400 rows. This gives $Q^{-s}$ for consistent prescriptions, including $s=0$, and zero for inconsistent ones. Summing the single-vector probabilities over a prescribed family gives its conditional expected count even when the membership events overlap. For $\bar c=0$ and $\bar b=0$ the original matrix law applies. An independent check over $\mathbb F_3$ found 486 tests with one compatible completion, 27 with nine, and 216 with none. The sign-pair Gaussian majorant lies in $(4.24859833,4.24859835)\cdot10^{-12}$. It bounds the raw short-vector event on surviving residue lines. Selection imposes a further condition.

**Closest points and multiples.** Comparing the shortest lift with both $y+k$ and $y-k$ gives $2|\langle u,k\rangle|\le\|k\|^2$ for every $k\in K$. Multiplication by $|a|\le1$ preserves those inequalities, proving (2) for the full kernel, including ties. Shortestness of $p$ makes it primitive in the quotient lattice. Thus $tp$ with integer $t\ne0$ exhausts the nonzero quotient points on its line, and $ty+K$ is the complete fiber. Equation (3) gives the exact distance threshold on $T/K$ for each such $t$. The nine positive trials apply at $\|p\|=26$.

**Exact width-three rerun.** A separate rational calculation projected all 22 original columns in processing order. At each window the two retained generators were orthogonal. For each signed height whose perpendicular component fit within the candidate radius, testing the adjacent integers in both retained coordinates included every closest lift at that height. At height zero the shorter retained axes gave all minimizers. Signed ambient lexicographic comparison removed the first 16 horizontal axes in order. Each of the four graph appends then had exactly one shortest line, with squared lengths $3137,3137,156801/3137,156801/3137$. The final two generators were orthogonal with common squared length $11082241/156801$. Projecting off the designated shortest line left that same squared minimum, whose square root lies in $(8.40696774,8.40696775)$. Independently minimizing the private-block cost over all 250 positive coefficients gave $428269$ uniquely at 190. Sign symmetry covers negative coefficients, larger absolute coefficients exceed 250 on their own, and a purely horizontal vector has minimum nonzero length 3329. This certifies the raw cutoff for every nonzero vector, including every multiplier in (3).

**Remaining mass.** The two tie rules count each design in $E\cap G$ exactly once, including any selected deterministic member of $q\mathbb Z^{911}$. Subtracting the raw and dual exit allowances from $4\cdot10^{-7}$ leaves $3.9999566953\cdot10^{-7}$ for the membership-weighted sum. Part 183's last-draw discrepancy concerns a different event. Part 176 recovers a parent and mark on its reachable positive-height branches with coprime height, while the probability of reaching that parent remains in the sum. Neither the fixed rank-407 plane nor the selected width-three example estimates this mass for width 506. No numerical or substantive correction is required.
