# Finite marks, surviving labels, and the selected terminal weight

In the marginal width-506 restart, the first suffix selection permanently kills the **first horizontal mark direction** with probability greater than **0.72982006**. Consequently, even after averaging over histories, a label sampled from the surviving dual labels need not resemble a uniform element of the original label space. In fact its total variation distance from that uniform law exceeds 0.7295 at every subsequent time. In the other direction, the next displacement is exactly uniform on its *current* mark group at every history. Neither statement estimates the fraction of that group passing the signed terminal tests.

All probabilities below use the unconditioned 400-by-105 graph restart, prime $q=3329$, physical lengths, no lookahead, and ambient signed lexicographic ties in processing order. The 407 suffix appends use independent uniform columns. The two events $P,p_a$ are tested at **suffix draw 406**, before draw 407. The independent CBD(3) plant does not enter these design events. Part 117 couples the original first pass to this marginal experiment at an additive cost below 0.00022304. Conditioning the smaller design on successful coupling would change its law. [Part 108](wall1_first_tour.md) · [Part 117 and audit](wall1_idea_round2.md) · [Frontier](../PROOF_GAP.md)

## 1. A finite state with a common label space

Put $V=\mathbb F_q^{400}$ and $d=505$. After $i$ suffix appends keep the time, the physical retained space $E_i$ and lattice $M_i$ in the original ordered coordinate frame, and the homomorphism
$$
 \phi_i:V\longrightarrow E_i/M_i,\qquad a\longmapsto[P_{E_i}(a,0)].
$$
Use $H_i=\mathrm{im}\,\phi_i$, $C_i=\ker\phi_i$, and $L_i=C_i^\perp\subseteq V^*$ with the finite-field pairing. Thus $H_i\simeq V/C_i$ and its character group identifies with $L_i$ via pullback and the character $j\mapsto\exp(2\pi i j/q)$. These are the labels of Part 142. Indeed, in any basis of $M_i$ the $q$-torsion is $\mathbb F_q^d$, and a linear functional on its subspace $H_i$ extends to the entire space by basis extension. The corresponding integer coordinates give a dual-lattice representative. Two representatives give the same character exactly when their difference pairs integrally with the whole marked preimage lattice. A label specifies a coset of dual vectors. It carries no designation of a shortest representative. [Part 142, Theorem A and audit](wall1_dual_cusp.md)

**Proposition 1.** The displayed state is a finite, time-inhomogeneous Markov chain on its reachable states. Given the state, draw $u$ uniformly in $H_i$, form $W=(M_i,0)+\mathbb Z(\tilde u,1)$, select the shortest sign pair using the key $(\|v\|^2,\min_{\rm lex}(v,-v))$, and project off it by $Q_v$. The new retained lattice is $Q_vW$ in the induced ambient frame, and $\phi_{i+1}=(Q_v)_*\phi_i$. In particular
$$
 C_0=0,\quad L_0=V^*,\qquad C_i\subseteq C_{i+1},\quad L_{i+1}\subseteq L_i.
$$

*Proof.* At initialization the graph intersects the horizontal coordinate space in $q\mathbb Z^{400}$. At later times $qP_{E_i}(a,0)\in M_i$ for any integral horizontal lift. Changing the next raw column by a member of $C_i$ changes its projected lift by a member of $M_i$, preserving $W$, the signed winner, and the new frame. Projection of each marked generator gives the claimed composition and hence the inclusions. Each mark has exactly $|C_i|$ preimages. Independence of the raw column gives the transition law, also when several histories lead to the same state. At time $i$ there are at most $q^{400(105+i)}$ raw prefixes, each determining one state. Thus the geometric representation has finite image. It can equivalently be encoded by a rational basis in the ordered ambient frame and the marked generator classes. Orthogonal projection along a rational vector has rational entries, and the initial basis is integral. No quotient by rotations or permutations is assumed. ∎

## 2. What a fresh kick randomizes

**Proposition 2.** Fix a history through time $i$. Choose rows $z_1,\ldots,z_j\in L_i$ using only this history and let $B$ have those rows. The vector of next kicks, in residue units, is $-Ba$ for a fresh raw column $a$. It is uniform on $\mathrm{im}\,B$. Its total variation distance from uniform on $\mathbb F_q^j$ is $1-q^{\operatorname{rank} B-j}$. In particular independent predictable labels have jointly uniform kicks on every history. For a label that survives the projection, its transported label equals its old label.

*Proof.* For $c\in\mathbb F_q^j$, the Fourier coefficient of the kick law is the average of $\exp(-2\pi i\langle B^\top c,a\rangle/q)$ over $V$. It equals one for $B^\top c=0$ and zero otherwise, by summing one coordinate with a nonzero coefficient. Equivalently every image point has $q^{400-\operatorname{rank}B}$ preimages. Comparing the two constant probabilities on the image and its complement gives the stated distance. A character of $H_{i+1}$ pulls back along $(Q_v)_*$ to a character of $H_i$. Its pullback all the way to $V$ is the same row by Proposition 1. The kick gives the new lift coordinate modulo one, $-\langle z,a\rangle/q$. It does not add anything to the row $z$. ∎

For a fixed nonzero raw row $z$, its pairings against distinct independent future columns are iid uniform whether or not one tracks a dual lift. If $z$ is required to survive those columns, that conditioning can change their law. More generally, at fixed history an observation with nonempty acceptance set $A\subseteq H_i$ makes the posterior mark uniform on $A$, at distance $1-|A|/|H_i|$ from the original mark law. This follows by direct division of point probabilities. For a positive-height Part 164 band candidate $(y,k)$, inclusion requires $ku=[y]$. On the specified band $0<k<224<q$, so a compatible incidence fixes one mark. The posterior distance is then exactly $1-1/|H_i|$, even before revealing a compatible witness. Thus one-step character cancellation for a predictable row gives no cancellation after this reveal. [Part 142](wall1_dual_cusp.md) · [Part 164 and audit](wall1_selected_hit_direct.md)

## 3. A rank exit of probability greater than 0.72982006

**Theorem 3.** Let $e_1\in V$ be the first horizontal unit at restart. At the first suffix step, loss of mark rank is equivalent to $\lambda_1(W)=q$. On this event $C_1=\mathbb F_q e_1$. In particular, for every $1\le i\le407$,
$$
 \Pr(e_1\in C_i)\ \ge\ \Pr(\lambda_1(W)=q)
 \ \ge\ 1-\frac{\pi^{253}(q^2+506/4)^{253}}{253!\,q^{400}}
 \ >\ 0.72982006 .
$$

*Proof of the rank criterion.* The first full window is the coordinate graph $W=\{(x,y)\in\mathbb Z^{400+106}:x\equiv By\pmod q\}$ for a uniform $400\times106$ matrix $B$. The syndrome $(x,y)\mapsto x-By$ identifies $\mathbb Z^{506}/W$ with $V$, generated by the horizontal units. For the winning vector $v$ let $w=v/\gcd(v_1,\ldots,v_{506})$, taking a positive gcd. The kernel of the induced projection of this quotient into the new torus is precisely the image of $\mathbb Zw$. Indeed $Q_v x\in Q_v W$ for an integer $x$ iff $x$ differs from a member of $W$ by an integer point of $\mathbb Rv$. Those integer points are $\mathbb Zw$.

The order of $[w]$ is either one or $q$. Its order equals the positive gcd just used, because $v$ is primitive in $W$ by shortestness. If the order is $q$, then $\|v\|=q\|w\|\ge q$. All $q$-axes belong to $W$, so equality holds. Conversely if $\lambda_1(W)=q$, the signed tie rule selects $-q e_1$. No vector of length $q$ can have first coordinate smaller than $-q$, and equality fixes the other coordinates to zero. The kernel in this case is exactly the syndrome line $\mathbb F_qe_1$. Proposition 1 preserves this line in all later kernels. ∎

*Proof of the probability bound.* Any nonzero graph point strictly shorter than $q$ must have $y\bmod q\ne0$, since otherwise all its coordinates are multiples of $q$. Each fixed point with $y\bmod q\ne0$ belongs with probability $q^{-400}$ by independence of the rows of $B$. Count sign pairs to bound the probability of a shorter point by their expected number.

For any nonzero integer point $p$ of norm less than $q$, take the half of its centered unit cube consisting of $p+h$ with $\langle p,h\rangle\le0$. Its volume is $1/2$, and
$$
 \|p+h\|^2\le\|p\|^2+\|h\|^2<q^2+506/4 .
$$
The half-cubes have disjoint interiors. Counting both signs, their total volume equals the number of sign pairs, which is consequently at most the volume of this enlarged ball. Multiplication by $q^{-400}$ gives the bound. The subtracted term lies in $(0.27017993630,0.27017993632)$. This enclosure can be checked with rational arithmetic using $\pi=16\arctan(1/5)-4\arctan(1/239)$ and the 12- and 13-term alternating partial sums for each arctangent. ∎

**Corollary 4.** Any good-history condition requiring all 400 independent labels to remain available has exit probability greater than 0.72982006 by step one. More generally, let $Z_i$ be *any* sampled label in $L_i$, under any history-dependent selection rule that returns a label on every history. Then for $i\ge1$,
$$
 d_{\rm TV}(\mathcal L(Z_i),\mathrm{Unif}(V^*))
 \ \ge\Pr(e_1\in C_i)-1/q>0.7295 .
$$

*Proof.* On the exit event every surviving label lies in the same hyperplane $z(e_1)=0$, whereas its mass under uniform sampling from $V^*$ is $1/q$. Use this hyperplane as the TV test. The statement allows uniform sampling within each $L_i$. It makes no estimate on a law conditioned on the existence of a particular short vector. ∎

**Exact small check.** Take $q=2$, four horizontal coordinates, one restart column and one append. Enumerating all 256 binary $4\times2$ matrices gives counts $31,115,98,12$ for first-window minimum squared $1,2,3,4$, respectively. On exactly the last 12 the mark loses rank. To reproduce, list all signed representatives $v\in\{-2,-1,0,1,2\}^6$ with $0<\|v\|^2\le4$, keep the smaller of each sign pair, and sort by the signed key. For each matrix take the first entry satisfying the graph congruence and test the syndrome of $v/\gcd(v)$. A nonzero syndrome occurs exactly for winner $(-2,0,0,0,0,0)$. The list is exhaustive since every graph contains the doubled axes. The check concerns the rank criterion alone.

## 4. The terminal statistic is a zero Fourier coefficient

Let $S$ be the state after 405 suffix appends. For $u\in H(S)$ write $v,x$ for the designated minima first in $W_u$, then in its projection off $v$. Set $s=\|v\|$, $t=\|x\|$, $D=\det M$, $g=(D/V_{506})^{1/506}$, $h=(D/(sV_{505}))^{1/505}$, and $c=477/500$, with $V_j$ the unit-ball volume. Define two indicators on the **same** finite group.

* $f_S(u)=1$ when $32.18553<g<203.888$, the fresh height of $v$ is nonzero, $0.990g<s\le1.097193g$, $1<t\le\sqrt{1+c^2h^2}$, and the lattice after both projections has a nonzero point strictly shorter than $ch\,t^{-1/505}$.
* $a_S(u)=1$ when the same $t$ and final witness length gates hold and $v,x$ and a passing witness all admit height-zero lifts at this append. Both designated minima are selected in the full lattices. There is no $g$ or $s/g$ band for this event. The witness only needs to exist. [Part 155, equation (1)](wall1_inherited_witness.md) · [Part 164](wall1_selected_hit_direct.md) · [Part 168](wall1_subset_ustat.md)

**Proposition 5.** For $b_S=f_S+a_S$, use the normalized Fourier coefficient $\widehat b_S(z)=|H|^{-1}\sum_{u\in H} b_S(u)\overline{\chi_z(u)}$. Then
$$
 P=\mathbb E\widehat f_S(0),\qquad p_a=\mathbb E\widehat a_S(0),\qquad
 P+p_a=\mathbb E\widehat b_S(0).
$$
If $\tau$ is the first exit from a specified sequence of good state sets through time 405, its discarded contribution is at most $\Pr(\tau\le405)$.

*Proof.* Each window and both projections are functions of $(S,u)$. On a horizontal first win $v$, the height-zero sublattice after projection is $Q_vM$. If the second win $x$ is horizontal too, the height-zero sublattice after both projections is $Q_xQ_vM$. This proves sufficiency of the state for the old-lift test, including projected vectors shortened earlier in the pass. Averaging each deterministic indicator over the uniform mark gives the displayed constant coefficient. The two indicators are disjoint by first height, so $0\le b_S\le1$ and the exit bound follows. If desired, the exit probability itself is the sum over times of the probabilities of surviving to the preceding state times its conditional fraction of exit marks, with initial exits counted separately. This is the partition by first exit. ∎

Even within a stratum of fixed mark rank, all nontrivial Fourier coefficients of the *fresh law* already vanish. For the *test*, adding a constant changes only the coefficient at zero. Thus vanishing character means of the law do not control the mean of the test. There is a reachable example for this particular selected statistic in the audited $q=17$ one-append toy. Its mark map is the same abstract isomorphism $\mathbb F_{17}\to H$ at each prefix, since the old graph intersects the horizontal axis in $17\mathbb Z$. The winning fraction is $2/17$ at the prefix $(-1,-1)$ and zero at all other prefixes, from the exact enumeration in Part 164. The marked geometry distinguishes the prefixes. [Part 164, audit](wall1_selected_hit_direct.md)

Two different exits in the earlier audits clarify the scope of Theorem 3. Write $Q=q^{400}$. Part 144 gives a family with maximal restart mark and horizontal charge one at draw 407. Its exact raw probability is $Q^{-511}\sum_{j=0}^{103}\binom{511}{j}(Q-1)^j$ because at most 103 of 511 columns are nonzero. This is at most $\binom{511}{408}Q^{-408}$ by a union over prescribed zeros. Its maximal rank is 400, while full torus $q$-torsion in rank 505 has rank 505. Part 157 gives a prescribed draw-406 prefix of probability $Q^{-510}$ on which revealing positive winning height pins the mark to zero, a joint mass $Q^{-511}$. Its winner has length one and its diagnostic plane cutoff is $3/2$. Neither example gives a lower bound at the Part 164 upper-band gates. Theorem 3 instead quantifies the cost of discarding *rank loss*, an event common under the marginal restart. It too gives no lower bound on the terminal hit. [Part 144 and audit](wall1_horizontal_core.md) · [Part 157 and audit](wall1_bounded_bias.md)

**Remaining conjecture.** The audited sufficient target is $P+p_a\le0.00019770868$. An allocation $P\le10^{-4}$ leaves $0.00009770868$ for $p_a$. The proof above rules out a uniform comparison on the original 400 label directions with a small exceptional set. It also identifies what remains under a comparison on the actual quotient $V/C_i$, where sampling the next mark already incurs zero TV error. One needs an upper bound on the history average of the fraction of marks passing the two terminal tests. No such upper bound, or small exit bound for histories with a large passing fraction, follows here. The first-step exit, the rare diagnostics, and the coupling cost belong to different events and have not been added to the terminal mass. [Part 161 and audit](wall1_band_plane_hits.md) · [Part 163](wall1_restart_haar_ratio.md) · [Part 164 and audit](wall1_selected_hit_direct.md)

## Audit

**Verdict — SOUND.** The rank-loss criterion, its probability bound, the unconditional label comparison and both terminal identities hold for the stated marginal restart and signed processing-order ties. No correction is required.

**First selection.** Write the winning vector as $v=mw$ with $w$ primitive in the ambient integer lattice. The kernel on marks is generated by the syndrome of $w$, since the integer points on the line removed by projection are precisely $\mathbb Zw$. The order of that syndrome equals $m$ by shortestness of $v$ in the graph. A nontrivial kernel therefore forces $m=q$ and $q\le\|v\|\le q$, the upper bound coming from the coordinate axes. At equality the signed key selects $-qe_1$, whose primitive direction has syndrome $-e_1$. This fixes the same kernel line on every rank-loss history.

**Numerical certificate.** Each eligible shorter sign pair has graph membership probability $q^{-400}$. The two inward half-cubes for that pair have combined volume one, and all such half-cubes have disjoint interiors inside the enlarged ball. Independent exact rational arithmetic with the 12- and 13-term Machin bounds enclosed the ball-volume term in $(0.270179936309851,\,0.270179936309852)$. Thus the first-step rank-loss probability exceeds $0.729820063690148$. Since kernels are nested, the hyperplane $z(e_1)=0$ has at least this mass for every subsequent label rule returning a surviving label on every history. Its uniform mass is $1/3329$. Exact subtraction gives a TV lower bound greater than $0.729519673182488$ through draw 407.

**Exhaustive check.** The six-dimensional integer ball through squared norm four contains 242 nonzero sign pairs. For every binary design I selected the first graph member by signed key and tested each of the 16 horizontal residues $h$ directly for $(h,0)\in W+\mathbb Rv$. For any nonzero coordinate $v_j$, an admissible multiple $t v$ must have $t|v_j|$ integral, and $t$ can be reduced modulo one because $v\in W$. This gives a finite kernel test independent of the syndrome-of-the-primitive-vector criterion. The counts at squared minima $1,2,3,4$ were respectively $31,115,98,12$. The first 244 kernels were trivial when grouped by minimum. Each of the remaining 12 was exactly $\{0,e_1\}$.

**Terminal law and budget.** Every present mark has the same number of raw preimages. Conditional on the prefix through step 405, draw 406 is therefore uniform on its image group. The ordered physical state and this single draw determine both signed minima. On two horizontal wins the projections preserve fresh height, so membership in $Q_xQ_vM$ tests whether a final witness admits an old lift. This recovers both indicators, including the strict witness cutoff and the absence of a band restriction for $p_a$. Charging every rank-deficient history at its full probability would already cost more than $0.72982006$ at step one. Its actual terminal contribution is the expectation of the passing-mark fraction on those histories. That contribution and the sufficient target $P+p_a\le0.00019770868$ remain unevaluated. [Part 155 and audit](wall1_inherited_witness.md) · [Part 164 and audit](wall1_selected_hit_direct.md) · [Part 168 and audit](wall1_subset_ustat.md)
