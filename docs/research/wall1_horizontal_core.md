# Horizontal incidence and aligned atoms in the first pass

Two uniform estimates fail under the exact finite design law. At width 506 there are penultimate histories with the largest possible restart mark for which **every final column** selects an old line in an old plane of area one. Their family has an exact binomial probability. A different obstruction occurs already at restart. On a set of restart states of probability greater than 0.99800814, the singular rank-one direction test in Part 139 has **infinite conditional expectation**. The retained minimum on these states is below its Gaussian heuristic, and an aligned winning draw has length $\sqrt{901}>30$. Neither obstruction determines the terminal history average.

## The conditional count

Use the exact forward, no-lookahead pass, with the $qI$ columns first, unit graph heights, and signed lexicographic ties in the inherited ambient frame. All probabilities below concern the uniform design. The CBD(3) plant does not enter this experiment. Let $L$ be the old retained lattice, $d=\beta-1$, $D=\det L$, $x_0$ its designated shortest vector and $t=\|x_0\|$. Put $G_d=V_d^{-1/d}$, where $V_d$ is the Euclidean unit ball volume. The old-plane indicator and the new-column test are
$$
 I=\mathbf 1\{\lambda_1(\pi_{x_0^\perp} L)<cG_d(D/t)^{1/d}\},
 \qquad b_S(u)=\mathbf1\{\text{the winner in }L+\mathbb Z(\tilde u,1)
                              \text{ is horizontal}\}.
$$
Here $L$ is embedded at height zero and $S$ includes the history and tie frame. Every horizontal winner equals $x_0$. A shortest projected old line lifts to a saturated plane through $x_0$ with area $t\lambda_1(\pi_{x_0^\perp}L)$, by projecting the second member of a plane basis. Thus $I$ tests existence, irrespective of the number of witnesses. [Part 108](wall1_first_tour.md) · [Part 120](wall1_plane_count.md) · [Part 121](wall1_global_quotient.md)

**Conditional Fourier identity.** Let $T$ be the old torus and $A=T[q]$. Define $b_S$ on all of $A$ by the same window test. For characters $\chi$ of $A$, write $\widehat b_S(\chi)=|A|^{-1}\sum_{a\in A} b_S(a)\overline{\chi(a)}$. Given the history, the joint horizontal charge is exactly
$$
 Iw_0=I\sum_{\chi:\,\chi|_H=1}\widehat b_S(\chi),
 \qquad w_0=|H|^{-1}\sum_{u\in H}b_S(u).
$$
Indeed, each marked class has the same number of raw-column preimages. Fourier inversion followed by summation over $H$ keeps precisely the characters trivial on $H$, since translating a nontrivial character sum by a point with character value different from one forces the sum to vanish. The old incidence is constant on every such fiber. Even when $H=A$, its contribution multiplies the trivial Fourier coefficient. The rank counts for fixed modular constraints in Parts 40, 92 and 101 do not average this factor over the old design. [Part 40](wall1_finite_family.md) · [Part 92](wall1_qary_gap.md) · [Part 101](wall1_qary_rogers.md)

## 1. Maximum mark and horizontal charge exactly one at the terminal draw

**Theorem 1 (unconditioned Part 117 restart).** Write $m'=400,\ n_0=105,\ h=406,\ q=3329,\ Q=q^{m'}$. Expose the $n_0$ restart columns and the next $h$ columns, leaving the last draw unread. Let $E$ be the event that at most $n_0-2=103$ of these 511 columns are nonzero in $\mathbb F_q^{m'}$. Then
$$
 \Pr(E)=Q^{-511}\sum_{j=0}^{103}\binom{511}{j}(Q-1)^j.
$$
At every history in $E$, $|H|=Q$, $D=Q$, $t=1$, and $Iw_0=1$ at the recorded cutoff $c=0.954$. This extends the all-zero history in Part 122 to arbitrary locations and values for the nonzero columns. The displayed probability is exact for this sufficient family. [Part 122](wall1_depth_truncation.md)

*Proof.* For a list of active columns $B$, the coordinate graph is
$$
 L(B)=\{(x,y)\in\mathbb Z^{m'}\oplus\mathbb Z^{n_0}:x\equiv By\bmod q\}.
$$
Its unit vectors are exactly the signed vertical coordinate axes belonging to zero columns. When an old zero column is present, appending any column leaves the window integral and preserves its old unit vector. The earliest old negative unit vector precedes the new negative unit vector in every tie. Projecting off the winner deletes that old zero column and its coordinate, so the retained lattice is again the coordinate graph of the remaining list. Here “horizontal winner” means height zero relative to the new append. An old graph coordinate axis has precisely that height.

There are at least $h+2$ zero columns among the exposed inputs. After any $i$ suffix draws, at most $h-i$ of these zeros are still unread. At most $i$ have been deleted. Consequently at least two are active, by induction from restart using the preceding update. At the penultimate state two such old axes span a saturated plane of area one through the designated winner (choose that axis and any other unit axis). The graph has index $Q$ in the coordinate integer lattice by the surjection $(x,y)\mapsto x-By\bmod q$. Its horizontal intersection is $q\mathbb Z^{m'}$, so the mark map is injective on all $Q$ horizontal residues. Its order is maximal for this experiment. The cutoff exceeds one since $G_{505}\ge 1/2$ by inclusion of the unit ball in the side-two cube and $q^{400/505}>3$. Every final draw therefore contributes one. Counting histories by their $j$ nonzero locations and the $Q-1$ choices at each proves the probability formula. ∎

This family is inexpensive to discard. A union over the locations of 408 prescribed zeros gives $\Pr(E)\le\binom{511}{408}Q^{-408}$. It gives a lower bound of $\Pr(E)$ on the reduced horizontal average, far below the proposed budget. The calculation uses the **marginal** restart law. Part 117 bounds the cost of coupling that law to the original pass by 0.00022304. It does not assign the same probability to this rare family in the original pass. [Part 117](wall1_idea_round2.md) · [Part 126](wall1_band_moments.md)

## 2. Full torus torsion in the original pass

**Theorem 2.** In the original pass at either recorded width, let $C$ prescribe zero *displacement* in the first 511 graph draws. Then $\Pr(C)=q^{-511d}$. At the last draw the mark equals $T[q]$. The conditional horizontal charge exceeds $1-2^{-303}$ at width 406 and $1-2^{-398}$ at width 506, for the ratio cutoff 0.925 at both widths and also 0.954 at width 506.

*Proof.* At the first graph append the lattice is $q\mathbb Z^d$ with full mark. A zero displacement selects the new unit axis and leaves the same lattice and mark. Each such draw has conditional probability $q^{-d}$, irrespective of raw entries projected away. This is the cubic cylinder of Part 109. Here we resolve which winner produces the old-plane witness. The old shortest line and any other coordinate axis span a plane of area $q^2$. The old projected minimum divided by $G_d(D/t)^{1/d}$ equals $q^{1/d}/G_d<0.21$ at both widths. Hence $I=1$. [Part 109](wall1_terminal_mixing.md)

Let $a$ be the uniform final class in $\mathbb F_q^d$ and $[x]_q$ its coordinatewise centered representative. At positive height $k$ the squared minimum equals $k^2+\|[ka]_q\|^2$. The earliest negative old $q$-axis wins every length-$q$ tie, since a vector with that earliest coordinate equal to $-q$ and norm $q$ has all other coordinates zero. Thus a horizontal loss requires a strict improvement at some $1\le k<q$. For each such $k$, $ka$ is uniform. At most 15 of its centered coordinates can have magnitude at least 833 in an improvement, since $16\cdot 833^2>q^2$. There are 1664 residues of that magnitude or greater and 1665 others. A union bound, with no independence assumption across heights, gives
$$
 1-w_0\ \le\ (q-1)q^{-d}\sum_{j=0}^{15}\binom dj1664^j1665^{d-j}.
$$
Integer comparison gives the stated powers of two. ∎

This example has index one inside the full $q$-torsion. The Fourier sum consists of its trivial coefficient alone. A condition on the index that accepts full torsion therefore cannot by itself give a small bound uniformly over its accepted histories.

## 3. The discrete direction test has an aligned atom

**Theorem 3.** At the width-506 restart, every state satisfies
$$
 \lambda_1(L)/\mathrm{GH}(L)\le q/(G_{505}q^{400/505})<0.98579072.
$$
With probability greater than 0.99800814 equality holds in the first inequality and the following assertion holds. For the old shortest line $\Delta=\mathbb R e_1$ and every $0<p<504$,
$$
 \mathbb E\!\left[(1-\|P_\Delta\hat v_h\|^2)^{-p/2}
             \,\middle|\,L,\ |k|=1,\ s\ge30\right]=+\infty .
$$
Here $s$ is the winner length and $\hat v_h$ the direction of its horizontal component. The assertion also holds without the length restriction, for any nonnegative convention when that component vanishes. For the uniform sphere direction the same expectation is finite. Thus the literal rank-one discrete $\mathrm{DS}_M$ of Part 139, Proposition 6, fails for every finite $M$ on these states. This concerns the singular test that the proposition chooses as a majorant. [Part 139](wall1_lyapunov.md) · [Part 142 and its audit](wall1_dual_cusp.md)

*Proof.* The coordinate graph has $D=q^{400}$ and contains all $q$-axes. For a nonaxis vector $(x,y)\ne0$ of length at most $q$ in the graph, $y\bmod q$ must be nonzero, since otherwise every coordinate is divisible by $q$. Each fixed candidate with nonzero input residue belongs with probability $q^{-400}$. Counting sign pairs and enclosing the disjoint unit cubes centered at integer candidates in a ball of radius $q+\sqrt{505}/2$ bounds the probability of any such nonaxis vector by
$$
 B=\frac{V_{505}}{2q^{400}}\big(q+\sqrt{505}/2\big)^{505}
   <0.00199186 .
$$
On the complement $t=q$ and the first horizontal coordinate axis is the designated shortest line.

In this fixed old state take either fresh raw residue $a=\pm30e_1$. Each has probability $q^{-400}$. The vector $(a,1)$ has length $\sqrt{901}$. At height zero the minimum is $q$. For $1\le k\le30$, the vector $(ka,k)$ has length $k\sqrt{901}$, and adding any nonzero old lattice vector to its horizontal part leaves horizontal norm at least $q-30k\ge2429$. At $k\ge31$ the height alone exceeds $\sqrt{901}$. Negative heights follow by sign. The winner is therefore unique up to sign and its nonzero horizontal component is parallel to $e_1$. Conditioning on the stated positive-probability event preserves positive mass on exact alignment. There the integrand is infinite. Under uniform spherical measure, writing $\theta$ for the angle to $e_1$, the same integral is proportional to $\int_0^\pi\sin^{d-2-p}\theta\,d\theta$, finite for $p<d-1$. ∎

The Part 117 coupling places the same restart geometry in the original pass with probability greater than $1-0.00199186-0.00022304=0.99778510$. This transfer uses a union bound on the prefix and restart exceptions. The next raw column is still fresh. The state probability must be distinguished from the conditional mass $2q^{-400}$ of the two specified draws.

The Part 142 audit gives a direction-density upper bound for a **continuous** conditional model. Even an old minimum below GH and a length cutoff at 30 leave the discrete pole in Theorem 3. In the exact geometric factor of Part 139 the denominator contains $1-(1-s^{-2})\|P_\Delta\hat v_h\|^2$, which equals $s^{-2}>0$ at alignment. The theorem leaves open an estimate for that finite factor, or for a joint state-and-draw truncation that pays for aligned draws. Discarding whole restart states to make the literal singular estimate valid would cost at least the state probability above. There is no proof here of a near-GH upper cap on later reachable states.

## Exact checks and remaining probability

Scratch checks used integer arithmetic unless noted. Each small enumeration tested the stated event directly.

| Experiment | Check | Result |
|---|---|---|
| Reduced graph, $q=3$, $(m',n_0,h)=(2,3,2)$ | Enumerate every history, test all signed coordinate units by graph membership and apply the lexicographic winner on the family | 41 of 59,049 histories in the family, all 369 final continuations horizontal with an old unit plane |
| Same, $(m',n_0,h)=(1,4,2)$ | Same enumeration | 73 of 729 histories, all 219 continuations |
| Full cube, $q=3$, $d=9$ | Enumerate every draw and both relevant height minima | 2,816 of 19,683 draws horizontal, exactly those with at least eight nonzero entries |
| One-column restart, $q=17$, graph column $(1,\ldots,8,1,\ldots,8)$ | Check all nonzero graph-input residues, then all heights and graph-input coordinates that can meet squared length 5 for $a=\pm2e_1$ | Old minimum 17, both draws have a unique winning line with squared length 5 and exact alignment |

For Theorem 2 the check multiplies the numerator in the displayed bound by $2^{303}$ or $2^{398}$ and compares to $q^d$. For the real constants, 60-decimal interval arithmetic with $V_d=\pi^{d/2}/\Gamma(1+d/2)$ gives $0.00199185<B<0.00199186$ and $0.98579071<q/(G_{505}q^{400/505})<0.98579072$.

**Open conjectural estimate.** Under Part 120's proposed equal allocation one needs $\mathbb E[Iw_0]\le0.00488848$ and $\mathbb E[F_*]\le0.00488848$ in the reduced terminal law, where $F_*$ counts the positive-height witness planes on draws not already charged to an old horizontal plane. The weaker sufficient target is their sum at most 0.00977696. The two horizontal examples disprove a pointwise replacement based on maximal mark size. Their probabilities do not establish the sign of the across-history covariance of $I$ and $w_0$, or violate the conjectured average. The direction example disproves a separate discrete moment hypothesis even on common restart states. The horizontal average over the remaining histories, the positive-height charge, and the late-state minimum upper tail remain unresolved.

## Audit

**Verdict — SOUND.** The three theorems hold for the stated signed lexicographic tie rule and the specified first-pass laws. The Fourier identity follows from character orthogonality with the given normalization. A shortest projected vector is primitive in the quotient by the primitive line generated by $x_0$, so its inverse image is a saturated plane. This justifies using an existence indicator in the horizontal charge.

1. **Penultimate family.** After $i$ deletions at least $(408-(406-i))-i=2$ zero columns are active. An old unit axis wins each append, including ties against a new unit axis. Projection deletes its coordinate and preserves the graph description. Two surviving unit axes give a primitive plane of area one. The horizontal kernel is exactly $q\mathbb Z^{400}$, hence $|H|=D=q^{400}$ throughout this family. Independence gives the displayed binomial probability. For a numerical check, put $U=\binom{511}{103}Q^{-408}$. Counting exactly 103 nonzeros gives $U(1-1/Q)^{103}\le\Pr(E)\le U$, the upper bound coming from the union over 408 prescribed zeros. These bounds give $-1909216.508<\log_2\Pr(E)<-1909216.507$. Its entire contribution to the reduced horizontal average is $\Pr(E)$, well below $0.00488848$.
2. **Original-pass cube.** Each zero displacement has probability $q^{-d}$ and freezes only the fresh unit axis. Thus the cylinder has mass $q^{-511d}$ and retains full torsion. The projected ratios at ranks 405 and 505 are respectively $0.20766985$ and $0.18552282$ to eight decimal places. Signed ties at length $q$, including the pure height-$q$ vector, go to the earliest old negative axis. For $1\le k<q$ the residue $ka$ is uniform. Direct integer comparison confirms both loss bounds. The base-two logarithms of their displayed union bounds are approximately $-303.782806$ and $-398.899977$.
3. **Direction spread.** Pairing nonaxis candidates of norm at most $q$ with their negatives gives the factor $1/2$ in $B$. Independent interval evaluation gives $B=0.001991852369\ldots$, the restart GH ratio upper bound $0.985790713827\ldots$, and the Part 117 prefix cost $0.0002230399378\ldots$. On the specified states each of the two raw residues has a unique minimizing line of length $\sqrt{901}$. Both lie in $J=\{|k|=1,\ s\ge30\}$. Their combined mass given the state is $2q^{-400}$, and given the state and $J$ it is $2q^{-400}/\Pr(J\mid S)>0$. Hence the singular moment diverges even under this extra conditioning, while its sphere integral converges for $0<p<504$. Part 142's audited density estimate applies to a continuous model conditional on $k=1$. In Part 139's exact geometric factor, the quantity raised to the power $-p/2$ equals $s^{-2}$ at alignment, giving the finite value $s^p$.
4. **Independent reproduction.** Fresh scratch code enumerated all $59{,}049$ and $729$ toy graph histories, tested signed coordinate units by the graph congruence, and followed the lexicographic winner. The two families contained 41 and 73 histories, with all 369 and 219 final continuations horizontal in an old unit plane. Enumeration of all $3^9$ cube draws, including ties at heights $\pm3$, returned 2,816 horizontal winners. For the stated $q=17$ graph, centered residues over all feasible old input coordinates gave minimum squared length 289. For each appended sign, exactly one sign pair met the squared-length cutoff 5, aligned with the first axis. The real bounds above used 85-decimal interval arithmetic and the independent recurrence $V_j=2\pi V_{j-2}/j$.

No correction to the proofs or reported numbers is needed. The exact family probability is for the marginal restart experiment. The coupling transfers the common-state lower bound to the original pass at additive cost below $0.00022304$. The two terminal examples obstruct a history-uniform horizontal estimate. The history-averaged horizontal and positive-height budgets remain open.
