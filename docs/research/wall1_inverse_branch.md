# Inverting the selected positive-height branch

On the upper band of draw 406, the embedded first quotient and its oriented winner determine the **incoming geometric state and the mark uniquely**. The reason is arithmetic. Undoing the projection gives an extension of the incoming lattice killed modulo that lattice by the winner height. Intersecting with the ambient mark lattice removes this extension, since the mark group is killed by a coprime integer. The mass of the resulting inverse branch still contains the probability of reaching its parent. This gives an exact answer to the inverse-multiplicity question and leaves the numerical upper bound open.

## Experiment and output data

Use the marginal plain LWE $(511,512,3329)$ width-506 restart. The CBD(3) plant plays no role in these design events. The parent at time 405 has a retained space $E\subset\mathbb R^{910}$ and a full lattice $M\subset E$ in the original ordered frame. Write $K=P_E\mathbb Z^{910}$ and $H=K/M$. The map $\phi_S$ from a raw column in $V=\mathbb F_q^{400}$ to $H$ projects its horizontal lift and reduces modulo $M$. It is onto, $qK\subseteq M$, and the fresh raw column is independent and uniform. These are the graph-prefix properties of Parts 108, 142 and 169. Thus $S=(E,M)$ with the known time and ambient axes determines the marked state used here. Several raw prefixes may realize $S$. [First-tour law](wall1_first_tour.md) · [Marked state and audit](wall1_finite_chain.md)

For $u\in H$, choose a lift $\tilde u\in K$. The window is $W=(M,0)+\mathbb Z(\tilde u,1)$. Select its shortest sign pair by squared norm and then the lexicographically smaller signed representative. For a nonhorizontal winning pair, write $v=(y,k)$ for its generator oriented to $k>0$ *after* resolving the signed comparison. Let $L=P_{v^\perp}W$. The second designated shortest pair $x$ belongs to $L$. Use its original ambient coordinates for ties as well.

For precision, let $D=\operatorname{covol}M$, $d=505$, $g=(D/V_{506})^{1/506}$, $s=\|v\|$, $h=(D/(sV_d))^{1/d}$, $t=\|x\|$, and $c=477/500$, where $V_j$ denotes unit ball volume. A selected hit contributing to $P$ satisfies
$$
32.18553<g<203.888,\qquad 0.990g<s\le1.097193g,\qquad
1<t\le\sqrt{1+c^2h^2},\qquad
\lambda_1(P_{x^\perp}L)<ch\,t^{-1/d}.
$$
Record a single canonical witness for the last inequality, for instance the designated shortest sign pair in the twice-projected lattice. Both selections and the witness use the same draw. On this event $1\le k\le s<224<q$. The inherited event of mass $p_a$ has horizontal first winner and is counted separately. [Selected-hit definition and audit](wall1_selected_hit_direct.md) · [Quotient gates and audit](wall1_upper_band_quotient.md)

## The inverse on embedded lattices

**Proposition 1.** Let $M\subseteq K\subset E$ with $qK\subseteq M$, and form $W,v,L$ as above. Assume $\gcd(k,q)=1$. It suffices to record $(L,v)$ in the original ambient coordinates, with scale. Define the linear map
$$
 B_v(z,j)=z-(j/k)y.
$$
Then the real span of $L$ together with $v$ is $E\times\mathbb R$, and
$$
 R=B_v(L),\qquad M=R\cap K,\qquad u=k^{-1}[y]\ \text{in } K/M.                 \tag{1}
$$
For the restart $K$ is determined by $E$. Consequently there is exactly one geometric state–mark pair above every reachable output of this type. Appending the designated second winner and canonical witness preserves this assertion.

*Proof.* The window spans $E\times\mathbb R$. Orthogonal projection drops precisely its real winner direction from this span, so adjoining $v$ recovers the span and hence its horizontal space $E$. The map $B_v$ kills $v$ and satisfies $B_v(z,0)=z$. Therefore $B_v(P_{v^\perp}w)=B_v(w)$, which gives
$$
 R=M+\mathbb Z(\tilde u-y/k).
$$
Since $v\in W$, $\ell=y-k\tilde u\in M$. Thus $M\subseteq R$ and $kR\subseteq M$. If $r\in R\cap K$, then $kr,qr\in M$. Bézout's identity gives $r\in M$. The reverse inclusion is immediate. Finally $[y]=ku$ in $K/M$, where multiplication by $k$ is invertible. This recovers the entire window and its deterministic comparisons. The proof asserts uniqueness on the image. A proposed $(L,v)$ outside that image need not arise from any raw prefix or satisfy the winning comparisons. ∎

In particular projection preserves the size of the current mark group on such a branch. Indeed the old mark represented by $z\in K$ dies under projection exactly when $P_{v^\perp}(z,0)\in L$. The restriction of $B_v$ to the projected real space is injective, since its kernel in the window span is $\mathbb Rv$. The membership criterion is therefore $z\in R\cap K=M$. Projected old generators generate the next group by Part 108. This argument applies only at the stated heights. Prior rank losses remain part of the incoming law. [Finite chain and audit](wall1_finite_chain.md)

The distinction between this inverse and a Jacobian can be seen on the same lattice. Projection restricted to the horizontal space has volume factor $k/s$. Its squared Gram operator is $I-yy^\top/s^2$, of determinant $1-\|y\|^2/s^2=k^2/s^2$. The refinement $R/M$ has order $k$ for a primitive $v$. Indeed the class of $\tilde u-y/k$ generates it, and $j(\tilde u-y/k)\in M$ exactly when $(j/k)v\in W$, which by primitivity is equivalent to $k\mid j$. Consequently $\operatorname{covol}L=(k/s)(D/k)=D/s$. These are geometric volume factors for a specified vector. The number of raw inputs mapping to that same vector and lattice is given below. [VerticalWinnerIsometry.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/VerticalWinnerIsometry.lean) · [ProjectedCovolume.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/ProjectedCovolume.lean)

## The mass of one inverse branch

**Proposition 2.** Put $m=|V|=q^{400}$ and let $N(S)$ count raw $400\times510$ graph prefixes producing the framed geometric state $S$. For a reachable output $o=(L,v)$ as in Proposition 1, let $S_o$ be the recovered parent. Out of $m^{511}$ equiprobable raw designs through draw 406, the number giving $o$ is exactly
$$
 N(S_o)\,|\ker\phi_{S_o}|=N(S_o)\frac{m}{|H(S_o)|}.                     \tag{2}
$$
Let $\mathcal B$ be the set of distinct reachable outputs satisfying the upper band and both gates, retaining one canonical witness if witnesses are recorded. Then
$$
 P=\sum_{o\in\mathcal B}\frac{N(S_o)}{m^{510}|H(S_o)|}.                  \tag{3}
$$

*Proof.* Each of the $N(S_o)$ prefixes yields the same marked state. For any one of them, exactly one mark leads to $o$ by (1), and its raw lifts constitute one coset of the kernel. No other parent can produce $o$. This proves (2). Deterministic selection partitions the designs by output. Summing their masses over $\mathcal B$ gives (3). Dropping the embedded frame or retaining only a coarser quotient statistic groups these atoms and adds their weights. Counting all possible witnesses instead would require dividing each occurrence by the witness multiplicity within its window. ∎

This also describes inversion over several successive *appends*. On a recorded suffix with coprime positive winner heights at every step, (1) applied backwards at each step identifies a single starting state and a single sequence of marks. Given that starting state, independence of fresh raw columns gives the product of the reciprocal group sizes along the suffix. Its probability still includes the starting-state mass. The second shortest-line selection used in the draw-406 test is a deterministic projection within that draw and contributes no further mark factor.

Vallée–Vera's planar formula follows by integrating the input density over each disjoint preimage of an output set, changing variables there, and summing. The input density is evaluated at each inverse image even in the continuous formula. For (3), the input mass on framed parents is $N(S)/m^{510}$. At fixed parent an injective shortest section carries uniform marks to uniform representatives, and the dual transport identities determine the character of each surviving label. Neither identity evaluates $N(S)$. The reported $4.36018\cdot10^{-11}$ is an **upper bound** under Haar, combining a flag count and an unconditioned empty-ball estimate. Replacing $N(S)$ or the winning comparisons by $k/s$ has no change-of-variables justification for the finite input law. [Vallée–Vera, §4.1, Theorem 1](https://dmtcs.episciences.org/articles/3549/download) · [VoronoiMarkLaw.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/VoronoiMarkLaw.lean) · [CharacterTransport.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/CharacterTransport.lean) · [Haar comparison and audit](wall1_restart_haar_ratio.md)

## Exact checks

**A nontrivial refinement.** Take $W_j=\{(z,h)\in\mathbb Z^2:z\equiv jh\pmod {17}\}$ for every $0\le j<17$. Enumerate signed vectors through norm 17 and choose the least signed key. This finite search is exhaustive because $(17,0)\in W_j$. Nine winners have height one, four have height two, and four have height three. The height-two marks are $7,8,9,10$ and the height-three marks are $5,6,11,12$. For each winner $(y,k)$, the spacing of $B_v(L)$ computed from the two projected generators is $\gcd(17k,|kj-y|)/k$. In every case its reduced numerator is 17, so intersecting with $\mathbb Z$ gives $17\mathbb Z$. Reducing $y/k$ modulo 17 recovers each original mark. For example $j=8$ gives $v=(-1,2)$ and $R=(17/2)\mathbb Z$.

**Framed inverse and selected gate.** Use Part 164's order-17 graph $z=A u_1+B u_2+j u_3$ modulo 17, omitting the width-specific restriction on $g$. Enumerating all $17^3$ designs gave 2,259 horizontal winners and 2,654 positive-height winners, all at height one. The latter 2,654 outputs each recovered the original $(A,B,j)$. Exactly two passed the selected band and both gates, at $(16,16,1)$ and $(16,16,16)$.

The following details specify the scratch enumeration. Sort signed nonzero integer vectors of squared norm at most nine by the signed key. Every design had a graph member on this list, so the first such member is the true winner. For each positive winner, project the four graph basis vectors by the rational matrix $I-vv^\top/s^2$. Apply $kB_v$ to the projected generators. Their reductions modulo 17 span a plane in $\mathbb F_{17}^3$. A cross product of two independent columns, normalized to first coordinate one, gives its normal $n=(1,-A,-B)$. The recovered last mark is $n\cdot y/k$ modulo 17. This verifies the inverse directly from the quotient generators and $v$.

For the gate check, $D=17$, $d=3$, and the band contains only $s^2=2$. Write $C=(477/500)^6\,2601/(32\pi^2)=(c^2h^2)^3$. The projected minimum must satisfy $t^2>1$ and $(t^2-1)^3\le C$. A nonzero twice-projected point of squared norm $b$ passes when $t^2b^3<C$. Use signed raw vectors through squared norm three for these tests. A first projected point in range lifts with squared norm at most $1+C^{1/3}+1/2<4$ by rounding along $v$. A passing final witness lifts with squared norm less than $C^{1/3}+(1+C^{1/3})/4+1/2<4$ by rounding along $x$ and then $v$. All projections and ties were rational. Bounding $\pi$ between $3.14159$ and $3.14160$ separates every cutoff used, including the band endpoints from integer squared norms. [Original toy and cutoff audit](wall1_selected_hit_direct.md)

There is a simple check on the role of the parent weights. Under uniform prefixes the mass is $2/4913$. Modify only the probabilities of $(16,16)$ and $(1,1)$ from $1/289$ each to $3/(2\cdot289)$ and $1/(2\cdot289)$ respectively. These parents are isometric by reflecting the first coordinate. This preserves their total mass, the distribution of unmarked isometry classes, and every conditional transition rule in the original frame. The selected mass becomes $3/4913$ because only the first parent contributes winning marks. Reversing the two weights gives $1/4913$. These are alternative input laws for the finite example. The actual restart fixes its own parent weights.

## Remaining estimate

Let $b(S)$ be the fraction of marks producing outputs in $\mathcal B$. For clarity about exactly which incoming information suffices, suppose only totals $w_i$ for a partition of the reachable parents into nonempty finite classes $C_i$ are known. The sharp upper bound over all parent laws with those totals and the same conditional mark kernels is
$$
 \sum_i w_i\max_{S\in C_i} b(S).
$$
Indeed each conditional average is at most its class maximum, and putting the class mass at a maximizing parent attains equality. If strict positivity on every reachable parent is required and all class totals are positive, the same value is the supremum by mixing with an arbitrarily small full-support law of the given totals. Thus a coarser record can suffice through bounds on these maxima or through information on how the true history law distributes mass *within* its classes. The exact framed inverse supplies neither estimate.

**Conjecture (audited sufficient target).** For the specified marginal restart, $P+p_a\le0.00019770868$. Equation (3) leaves the weighted sum over parents of selected gated outputs unevaluated. Allocating $10^{-4}$ to that sum would leave $0.00009770868$ for the inherited event. Proposition 1 uses positive height and gives no inverse for that horizontal contribution. The dual-floor exits and markwise theta estimates in Parts 172–173 do not give the required parent-weight bound. The conclusions here are counting and lattice identities with finite checks. No width-506 probability estimate at the target scale follows. [Parts 162–173](../PROOF_GAP.md) · [Gated theta and audit](wall1_gated_theta.md)

## Audit

**Verdict — SOUND.** On every reachable upper-band output with positive winner height, Proposition 1 recovers the framed parent and the unique final mark. The embedded span recovers $E$, which fixes $K=P_E\mathbb Z^{910}$. For $r\in B_v(L)\cap K$, both $kr$ and $qr$ lie in $M$. Since $1\le k<224<q$ and $q$ is prime, Bézout gives $r\in M$. Conversely $B_v$ returns each horizontal generator of $M$ from its projection. This proves the intersection identity, and $ku=[y]$ recovers the mark. The signed tie rule selects the line before its generator is oriented.

At draw 405 the 105 initial graph columns and 405 appends give 510 prefix columns. Each prefix producing the recovered state has exactly one coset of raw final columns giving the output, of size $|\ker\phi_S|$. Thus its raw multiplicity is exactly $N(S)|\ker\phi_S|$ among $m^{511}$ designs. A canonical witness counts the design once. The cited Lean declarations cover the forward isometry, refinement index, covolume and uniform shortest section. Importing all four modules and checking the axioms of those results returned only `propext`, `Classical.choice` and `Quot.sound`. The inverse and prefix count above are paper proofs.

An independent scratch enumeration used rational projections, signed ambient lexicographic ties, and raw squared norms through nine. It found a first winner for each of the 4,913 graphs. Of these, 2,259 were horizontal and 2,654 had height one. The quotient generators and oriented winner recovered the original triple in all 2,654 cases. Only $(16,16,1)$ and $(16,16,16)$ passed the band and both gates. Rational bounds using $3.14159<\pi<3.14160$ separated the cutoffs. In the planar check, the projected generators gave spacing $17/k$ for all 17 marks. The four height-two marks were $7,8,9,10$ and the four height-three marks were $5,6,11,12$. Each intersection gave $17\mathbb Z$, and every mark was recovered.

Equation (3) still requires the width-506 prefix law, weighted by each parent's fraction of selected marks passing the gates. The two toy hits occur at the same parent, so its contribution under the uniform toy law is $(1/289)(2/17)$. The inherited horizontal residual $p_a$ requires a separate estimate within the shared allowance. The note states $P+p_a\le 0.00019770868$ as a sufficient target and leaves it open.
