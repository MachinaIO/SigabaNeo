# Framed transfer and the cost of forgetting the signed tie frame

In the audited rank-four example, the gated mark fraction has mean $2/4913$. The least pointwise majorant determined by the **entire ordinary theta series of the parent** has mean $8/4913$. Adding the dual theta series, all intrinsic primitive-plane counts, or even the theta series of every individually labelled mark coset gives the same optimum. The loss occurs at the terminal observable, before estimating any drift. Two theta coefficients identify the four parents responsible. The frequency of such a loss at width 506 is unknown.

## The count operator and its probability normalization

Use the unconditioned marginal restart of Part 169. Let $t$ count suffix appends already processed. The state $S$ includes time, the retained space and lattice in the ordered ambient frame, and the mark map. Write $Q=3329^{400}$ for the number of raw column values, $H_S$ for the image of the mark map, and $C_S$ for its kernel. Let $F_t(S,u)$ be the framed successor for mark $u$, including the signed tie rule. All state sets below consist of reachable states. [First-tour law](wall1_first_tour.md) · [Finite chain and audit](wall1_finite_chain.md)

**Proposition 1.** With measures written as columns, the raw and probability transfer matrices are
$$
 A_t(S',S)=|C_S|\,\#\{u\in H_S:F_t(S,u)=S'\},\qquad K_t=Q^{-1}A_t .
$$
Write $N_t$ for prefix counts and $\mu_t=N_t/Q^{105+t}$. Then $N_{t+1}=A_tN_t$, $\mu_{t+1}=K_t\mu_t$, and the probability adjoint on observables is
$$
 (K_t^*f)(S)=|H_S|^{-1}\sum_{u\in H_S} f(F_t(S,u)).
$$
If $g$ is Part 164's gated fraction of marks, set to zero off its good-history set, then
$$
 P=\langle g,K_{404}\cdots K_0\mu_0\rangle.
$$
The inherited residual has its own mark fraction $g_a$ from Part 169. Replacing $g$ by $g+g_a$ in this display gives $P+p_a$, with the good-history restriction for $g$ applied only to its own term. [Selected-hit law and audit](wall1_selected_hit_direct.md) · [Part 169](wall1_finite_chain.md)

*Proof.* Each mark has $|C_S|$ raw preimages. Summing over marks with the same successor counts all extensions of any one prefix reaching $S$, even when several marks have the same successor. The column sum is $|C_S||H_S|=Q$, so division by $Q$ gives the conditional probability kernel. Transposing this matrix in the sum pairing gives the adjoint. Initially the 105 graph columns are random, giving total count $Q^{105}$. After 405 suffix appends the denominator is $Q^{510}$. Averaging the fraction at that parent accounts for draw 406, including both selections on its single mark. Equivalently one can start from a point mass at a dummy root and first draw the initial graph, or sum a terminal indicator over $Q^{511}$ raw designs. On the upper band Part 176 recovers the parent and the mark from the decorated output. Its $N_{405}(S)|C_S|$ multiplicity follows from the same count. The forward formulas hold also at steps where the decorated inverse has not been established. ∎ [Inverse branch and audit](wall1_inverse_branch.md)

## Slack in an affine drift certificate

**Proposition 2.** Let $T=405$, $b=g+g_a$, and let $V_t$ be finite real functions on the full framed state sets. For deterministic $\lambda_t\ge0$ and $c_t\in\mathbb R$, put
$$
 d_t(S)=\lambda_t V_t(S)+c_t-(K_t^*V_{t+1})(S),\qquad
 L_j=\prod_{i=j}^{T-1}\lambda_i,\quad L_T=1 .
$$
Then
$$
 L_0\langle V_0,\mu_0\rangle+\sum_{t<T}L_{t+1}c_t-(P+p_a)
 =\langle V_T-b,\mu_T\rangle+
   \sum_{t<T}L_{t+1}\langle d_t,\mu_t\rangle .
$$
For a pointwise certificate with $V_T\ge b$ and all $d_t\ge0$, its excess is at least its terminal mean overestimate, irrespective of the affine coefficients.

*Proof.* Pair the definition of $d_t$ with $\mu_t$. The last term pairs $V_{t+1}$ with $\mu_{t+1}$ by Proposition 1. Multiply by $L_{t+1}$ and sum, using $L_{t+1}\lambda_t=L_t$. All intermediate expectations cancel. Add $\langle V_T-b,\mu_T\rangle$ and use the terminal identity. Nonnegativity of the products proves the inequality, also if some $\lambda_t=0$. ∎

The full-state value $h_T=b$, $h_t=K_t^*h_{t+1}$ has zero slack with $\lambda_t=1,c_t=0$. For these coefficients it is pointwise least by backward induction and positivity of $K_t^*$. Its initial expectation is the unknown probability itself. This is Part 139's duality with a fractional terminal observable and a random initial graph. [Potential duality and audit](wall1_lyapunov.md)

## A sharp obstruction for theta and intrinsic plane data

Use the existing one-append graph over $\mathbb F_{17}$. The parent lattice and its labelled mark cosets are
$$
 M_{A,B}=\{(z,x,y)\in\mathbb Z^3:z\equiv Ax+By\bmod 17\},\qquad
 M_{A,B}+j e_z,\quad j\in\mathbb F_{17}.
$$
The parent $(A,B)$ is uniform. Let $g_{17}(A,B)$ be the fraction of uniform final columns passing the signed upper-band and two quotient tests in Part 164's rank-four example, which omits the width-specific good-history restriction. Its audited finite count is
$$
 g_{17}(A,B)=\tfrac{2}{17}\,\mathbf 1_{\{(A,B)=(-1,-1)\}}.
$$
The two winning columns there are $j=1,-1$. [Part 163 reflection example](wall1_restart_haar_ratio.md) · [Part 164 finite certificate](wall1_selected_hit_direct.md) · [Part 167 ordered winning triples](wall1_new_tools.md)

**Theorem 3.** Among all pointwise majorants of $g_{17}$ depending only on the ordinary theta series of $M_{A,B}$, the pointwise least on this family is
$$
 V_{\rm inv}(A,B)=\tfrac{2}{17}\,\mathbf 1_{\{A,B\in\{-1,1\}\}} .
$$
It is still least if the available data also include the ordinary dual theta series, counts of primitive sublattices by rank and covolume, and the entire tuple of ordinary theta series of the labelled cosets $M_{A,B}+j e_z$. Thus the optimum mean is $8/4913$, with excess $6/4913$. The strict overestimate occurs with parent probability $3/289$.

*Proof.* Independently reflect the old input coordinates $x,y$. These isometries carry $M_{-1,-1}$ to each of the four displayed lattices and fix $e_z$. They preserve each mark label, the coset length multisets, dual lengths, and the ranks, covolumes and primitivity of sublattices. Thus even the enlarged observation identifies all four parents with one another. Any function of it majorizing $g_{17}$ must have value at least $2/17$ at each. The signed comparison still uses the original coordinate order, explaining how the event fractions can differ on these parents.

It remains to show that the proposed majorant is a function of the observation. Let $n_i$ count sign pairs of squared length $i$ in the parent, so $2n_i$ is a theta coefficient. The parent is the kernel modulo 17 of the row $(1,-A,-B)$. Absence of coordinate units is equivalent to all three row entries being nonzero. Under this condition, each unordered pair of axes contributes exactly one sign pair of squared length two if its two row entries are equal up to sign, and zero otherwise. Indeed the only possibilities on those axes are the lines generated by $e_i+e_j$ and $e_i-e_j$, and an odd prime prevents both congruences from holding. Hence $n_1=0,n_2=3$ is equivalent to all three entries being equal up to sign. As the first is 1, these are exactly the four parents claimed. Two theta coefficients therefore realize the displayed majorant. Outside the four parents zero is least because $g_{17}=0$. Each parent has mass $1/289$, giving the stated mean, excess and probability. ∎

**Finite check.** An independent exact enumeration in scratch reproduced both winning triples and all four parents with $(n_1,n_2)=(0,3)$. For each graph use the signed list of its nonzero integer vectors through squared length three. Take its least member by squared length and signed lexicographic key, requiring squared length two and nonzero final coordinate. Project the list, select the least nonzero signed image $x$, and project once more. Put $T_x=\|x\|^2$ and let $Z$ be the least nonzero squared length on the second projected list. An empty list cannot witness its gate. Write $h=(17/(\sqrt 2\,V_3))^{1/3}$ where $V_3=4\pi/3$. With $C=(477/500)^2h^2$, the two tests are $T_x>1$, $(T_x-1)^3\le C^3$ and $Z^3T_x<C^3$, where
$$
 C^3=\frac{(477/500)^6\,17^2}{2(4\pi/3)^2}.
$$
Rational orthogonal projection preserves the ambient tie comparisons. Bounding $\pi$ between $333/106$ and $355/113$ separates every tested endpoint. Part 164's rounded-lift bounds give completeness of the short list. Every first image within the length gate's upper radius has a lift of squared length below four. After $T_x>1$ the same holds for a passing second image. The signed minimum in a window containing a band candidate is already visible through squared length two. [Finite certificate and audit](wall1_selected_hit_direct.md)

## Scope and remaining conjecture

Theorem 3 concerns radial data at the parent, after averaging its mark. It differs from closing an event on triples under permutations. It allows a fixed mark label on every coset because the reflections preserve the marked direction. A weight that reads signed coordinates can distinguish the four parents. Their toy frequency gives no lower bound on the frequency of analogous parents in the physical restart.

The Lean kick and lineage theorems constrain the lift of a dual vector along a given projection. The Voronoi law assigns equal probability to the chosen shortest representatives of a finite set of marks. The index and covolume formulas, and the pathwise Rankin inequality, concern a given window and projection. These results are consistent with the reflected-parent example. A radial theta transformation by Poisson summation preserves isometry invariance, so applying that transformation to the same data cannot distinguish the four parents. [Character transport](../../SigabaNeo/Lib/Lattices/Research/Wall1/CharacterTransport.lean) · [Lineage](../../SigabaNeo/Lib/Lattices/Research/Wall1/MarkedLineage.lean) · [Voronoi law](../../SigabaNeo/Lib/Lattices/Research/Wall1/VoronoiMarkLaw.lean) · [Vertical refinement](../../SigabaNeo/Lib/Lattices/Research/Wall1/VerticalRefinement.lean) · [Projected covolume](../../SigabaNeo/Lib/Lattices/Research/Wall1/ProjectedCovolume.lean) · [Rankin inequality](../../SigabaNeo/Lib/Lattices/Research/Wall1/RankinWindow.lean)

**Open conjecture (physical restart).** Under the specified marginal law, $P+p_a\le0.00019770868$. Proposition 2 gives the exact accounting for a certificate. The initial expectation of the full-state value function remains unevaluated, and no explicit affine drift bound achieving the allowance is established here. The factor four is exact only for the stated toy upper-band fraction. [Parts 157 and 162–176](../PROOF_GAP.md)

## Audit

**Verdict — SOUND.** An independent scratch enumeration tested all $17^3=4913$ ordered designs using both signs of each raw vector through squared length four, exact rational projections, and signed ambient lexicographic comparisons. The bounds $333/106<\pi<355/113$ isolate squared length two in the first band and separate every tested gate comparison. The rounded-lift bounds in Part 164 ensure completeness. There were 1,150 designated positive-height winners in the band, 430 passed the first quotient gate, and only $(16,16,1)$ and $(16,16,16)$ passed both.

Across the 289 parents, the ordinary theta coefficients at squared lengths one and two were $(0,6)$ exactly at $(1,1),(1,16),(16,1),(16,16)$. These coefficients identify the four as a set. Reflections of the old input axes fix $e_z$, giving a length-preserving bijection at each individual coset label and an isometry of the duals. Hence the full observation has exactly these four parents in the winning parent's class. A pointwise majorant must take their common class maximum $2/17$ and can take zero elsewhere. Its mean is $8/4913$, versus $2/4913$ for the signed event. The excess $6/4913$ comes entirely from the three losing parents.

For the unconditioned restart, each column of $A_t$ sums to $|C_S||H_S|=Q$. Thus $K_t=A_t/Q$ advances the probability law and its transpose averages uniformly over marks. The 105 initial columns and 405 transitions give $Q^{510}$ equiprobable prefixes. The terminal mark average accounts for the single remaining column in the $Q^{511}$ designs through draw 406. This agrees with Part 176's multiplicity $N_{405}(S)|C_S|$ per reachable decorated upper-band output. The good-history restriction applies only to $g$.

For Proposition 2, write $m_t=\langle V_t,\mu_t\rangle$. The adjoint gives $L_{t+1}\langle d_t,\mu_t\rangle=L_tm_t-L_{t+1}m_{t+1}+L_{t+1}c_t$. Summing leaves the terminal coefficient $L_T=1$, even if an earlier $\lambda_t$ vanishes. Every drift contribution is nonnegative under the stated certificate hypotheses, so the terminal mean excess survives in full. The factor four concerns the toy upper-band observable alone. The width-506 target for $P+p_a$ remains open. No corrections are required.
