# Random column order in the first pass

For one unconditioned width-506 restart, putting the graph columns in an independent uniform order leaves the two terminal masses \(P\) and \(p_a\) **exactly unchanged** when the ambient coordinates used for signed ties are numbered in processing order. This holds for each fixed permutation after averaging over designs. There is a second convention, keeping the original coordinate names for ties while moving the columns. In the audited Part 164 toy, this latter convention **increases** the selected-hit probability by a factor of \(4/3\). Neither convention gives the proposed numerical bound by exchangeability.

## Which order the reducer sees

Use the \(qI\)-first, no-lookahead pass of [Part 108](wall1_first_tour.md). In the marginal restart of [Part 117](wall1_idea_round2.md), the \(400\) surviving rows of the first \(105\) graph columns initialize the retained lattice. The next \(407\) graph columns are fresh. Together these entries form a uniform \(400\times512\) array \(A\) over \(\mathbb F_{3329}\). This is the *unconditioned* restart. Conditioning on agreement of the original and forced coordinate prefixes would change the measure. The CBD(3) plant is independent of the design and plays no role in these two null events. [Part 47](wall1_decoupled.md)

Write \(A_\pi=(a_{\pi(1)},\ldots,a_{\pi(n)})\). The graph generator associated to \(a_i\) carries a unit input coordinate \(e_i\). We distinguish two experiments.

* **Processing-order coordinates.** Read \(a_{\pi(j)}\) at position \(j\), give it unit coordinate \(e_j\), and run the ordinary rule in this frame. Equivalently, use the original ambient space and transport the coordinate priorities along with the columns. The event's old subspace, fresh height, and both signed selections use the same frame.
* **Original coordinates.** At position \(j\) append \((a_{\pi(j)},e_{\pi(j)})\), retaining the original signed lexicographic priorities. The fresh height refers to \(e_{\pi(j)}\). In processing-order coordinates this experiment has a permutation-dependent tie rule. A reducer using the original tuple order literally implements this second convention.

An order is sampled independently of the *design* as well as the plant. Plant-blindness alone allows choices depending on \(A\), for which the following proof need not hold.

## The ordered path and its incidence weights

**Proposition 1.** In processing-order coordinates, conditional on any fixed order \(\pi\), the entire marked path, including all signed winners in that frame, has the fixed-order law. The statement holds for a permutation of all graph columns, or just of the fresh suffix. An independently chosen ordered subset of distinct design rows of the prescribed size and independent sign changes of rows or columns give the same result when used to form the canonical input array in the processing frame.

*Proof.* Fix the order. Every \(r\times n\) array in processing order has exactly one preimage under \(A\mapsto A_\pi\), of mass \(q^{-rn}\). Fixed sign changes are also bijections. If \(r\) rows are taken from a larger independent uniform design, every prescribed subarray on those ordered distinct rows has the same number of completions. These facts hold conditional on all independent index and sign choices. In this frame the initialization, projections, mark updates and signed selections are the very same functions of the ordered entries as in the fixed-order pass. Applying these functions proves equality in law, also with independent reducer coins by conditioning on them. Permuting only the suffix gives the same proof conditional on the initial graph. The original \(qI\)-first pass obeys the corresponding identity before taking the marginal restart, by applying the argument to its full array. This row statement is about resampling labels of i.i.d. rows. Choosing a pivot set conditional on an invertibility test or interleaving deterministic \(q\)-axes with graph columns changes the experiment. ∎

This is the input symmetrization of [Part 135, Proposition 3.2](wall1_plant_symmetry.md) **at the level of an ordered path**. For a given \(A\), processing \(A_\pi\) can select different directions. Equality is obtained by changing variables in the design average, without assuming that projection steps commute. If the path is mapped back to the original space, transport its frame and all label-dependent predicates too. Merely applying the inverse isometry to the lattice while retaining a new tie priority does not implement that transport.

For example, let \(F(A)\) denote the indicator of a specified terminal event and \(\bar F(A)=\mathbb E_\pi F(A_\pi)\). Then \(\bar F\) is symmetric and \(\mathbb E_A\bar F(A)=\mathbb E_A F(A)\). This symmetric statistic still evaluates the **selected** event. A bad history specified by its processing positions has precisely its former probability, even if any one named input is now unlikely to occupy a prescribed position. This applies to the reachable families of [Part 144](wall1_horizontal_core.md) and the diagnostic zero-mark history of [Part 157](wall1_bounded_bias.md). Their reachability obstructs uniform bounds, while their small masses alone give no lower bound near the terminal budget. Label exchangeability likewise gives no time exchangeability of retained lattices or of winners.

**Corollary 2.** In processing-order coordinates, order averaging preserves the two members of [Part 164, equation (4)](wall1_selected_hit_direct.md) separately for any incidence group recorded in that frame. It also preserves the selected mass \(P\) of equation (1) and the inherited residual \(p_a\).

*Proof.* For a fixed history \(S\) and group \(f\), put \(d_f(S)=\mathbf1_G |I_S(f)|/|H(S)|\) and \(n_f(S)=\mathbf1_G\sum_{i\in I_S(f)}J_S(v_i)/|H(S)|\), taking both as zero off the gate. The ratio is \(\mathbb E n_f/\mathbb E d_f\) when the denominator is positive. Each expectation is an integral of a function of the same framed history in Proposition 1. For canonical witnesses or reciprocal multiplicities use the corresponding weights in both sums. Apply the same argument to the indicator of the designated upper-band event and to the inherited-event indicator. ∎

Pooling incidence groups defined instead by original names can mix different denominators. If \(N_\pi,D_\pi\) are the two masses at order \(\pi\), pooled conditioning gives \(\sum_\pi N_\pi/\sum_\pi D_\pi\). Thus orders with \(D_\pi>0\) enter with weights proportional to \(D_\pi\). Uniformity of the order before conditioning supplies no common multiplier for the gated incidence counts. In particular, given \(S\) and a compatible positive-height band candidate, the congruence \(kU=[y]\) still fixes \(U\), since \(0<k<q\). The signed winner indicator is then deterministic. Random order introduces no independent second window for that incidence. [Parts 163](wall1_restart_haar_ratio.md) and [164](wall1_selected_hit_direct.md)

## Exact counterexample with the original coordinate priorities

**Proposition 3.** In Part 164's one-append toy, select the fresh column uniformly from the three inputs, taking the other two as the old graph. Keep the original signed lexicographic priorities on \((z,u_1,u_2,u_3)\) throughout. The selected-hit probability is \(8/(3\cdot17^3)\). With fixed last column \(3\) it is \(2/17^3\), as it also is with processing-order ties and random order.

*Proof.* For a design \(c\in\mathbb F_{17}^3\), the full window is \(z=c\cdot u\bmod17\), independent of which coordinate arrived last. In this toy the old graph initializes the pass without earlier selections. The two original-frame winners and their lengths therefore do not depend on the order. Positive absolute height of the first winner means that its coefficient on the designated fresh coordinate is nonzero. Use exactly the Part 164 band and gates with \(b=4,d=3,D=17\), omitting the width-506 gate \(G\).

The following finite count reports the fresh indices yielding a hit. Signs stand for \(1,-1\) modulo 17.

| Design \(c\) | Number of designs | Fresh indices yielding a hit |
|---|---:|---|
| \((+,\,\pm,\,\pm)\) | 4 | \(1\) |
| \((-,\,+,\,\pm)\) | 2 | \(2\) |
| \((-,-,\,\pm)\) | 2 | \(3\) |
| All others | 4905 | none |

For the eight sign designs the short vectors, after coordinate sign changes, are the roots \(e_i-e_j\) and their negatives. The successive squared lengths are \(2,3/2,4/3\) and satisfy the gates, as in [Part 163, Proposition 3](wall1_restart_haar_ratio.md). In the original frame the signed first winner starts with output \(-1\). Among such roots it uses the first positive input coefficient if one exists, and the last input otherwise, by lexicographic comparison. This explains the label asymmetry in the table.

For completeness, the following finite certificate also excludes every other design. All operations after the cutoff enclosures use integers or rationals. Let \(\operatorname{sgnrep}(v)=\min_{\rm lex}(v,-v)\), and order by squared norm, then lexicographically. The Part 164 outward enclosures imply that only \(s^2=2\) is in band and that \(l<C<u\) for \(C=\gamma^2 h^2,\ l=183792/100000,\ u=183793/100000\). Here \(\gamma=477/500\) and \(h=(17/(\sqrt2 V_3))^{1/3}\). A point meeting the first gate lifts to raw squared norm at most \(1+u+2/4<4\). A witness after the second projection lifts to raw squared norm less than \(u+(1+u)/4+2/4<4\), since \(t>1\). These follow by rounding the coefficient on each removed generator to its nearest integer. Thus the list through raw squared norm three suffices for accepting or rejecting the event.

~~~~text
for each c in {0,...,16}^3:
    L = signed representatives in {-1,0,1}^4 with squared norm 1, 2 or 3
        satisfying z = c·u (mod 17)
    skip if L is empty or its minimum v in the stated order has |v|² != 2
    B = distinct nonzero sgnrep(2w - <w,v>v) for w in L
    skip if B is empty
    x = minimum of B in the stated order
    T = |x|²/4
    assert T <= 1+l or T > 1+u
    skip unless 1 < T <= 1+l
    Y = positive values of (|w|² |x|² - <w,x>²)/(4 |x|²) for w in B
    skip if Y is empty
    Z = min(Y)^3 T
    assert Z < l^3 or Z >= u^3
    if Z < l^3: record each input index j for which v[j] != 0
~~~~

Here \(T=t^2\), and the cubed comparison tests the strict transverse gate \(p^2<C T^{-1/3}\). Scaling all first projections by two preserves their ordering and signed ties. The certificate gives the counts \(4,2,2\) for the three fresh indices. There are two orders per choice of fresh index. Thus 16 of \(6\cdot4913\) design-order pairs pass with original-frame ties. With processing-order ties each of the six orders has the fixed-last count two, giving 12 passing pairs. The ratio of the masses is \(16/12\). ∎

## Remaining width-506 question

**Open conjecture (Part 164).** For the specified single marginal restart, \(P+p_a\le 0.00019770868\). This audited sufficient allowance is slightly tighter than \(2\cdot10^{-4}\). It concerns a sum of unconditional masses. Equation (4) is an incidence-conditional ratio used to study \(P\); the allowance is not a pointwise requirement on every such ratio. [Part 161 and audit](wall1_band_plane_hits.md) · [Part 164 and audit](wall1_selected_hit_direct.md)

Under processing-order ties the conjecture is exactly the fixed-order conjecture, including residual (a). Under original-frame ties the toy rules out a general monotone improvement. The width-506 mass for that modified selector remains unknown, and transferring earlier tie-dependent budget estimates would require checking them for that selector. Neither result disproves the numerical inequality at width 506. Repeating several orders on the same design and selecting among their outcomes is a different experiment with dependent paths.

## Audit

**Verdict — SOUND.** The stated invariance and toy counterexample hold. No correction is needed.

For each fixed independent column order, reindexing the uniform design is a bijection. In the processing frame the ordered raw prefix, fresh height, mark update and both signed selections are functions of that reindexed design under the same rule as in the fixed pass. This gives equality of their joint law, including the raw prefix if an inherited-event test needs it. In Part 164, equation (4), apply this identity separately to the winning-incidence count and the total incidence count, each weighted by the gate indicator divided by the mark-group size. Their expectations agree order by order for a group defined in the processing frame. The same change of variables preserves the two unconditional event probabilities \(P\) and \(p_a\). The exceptional histories in Parts 144 and 157 retain their probabilities when specified by processing positions. [Part 108](wall1_first_tour.md) · [Part 135](wall1_plant_symmetry.md) · [Part 164 and audit](wall1_selected_hit_direct.md)

An independent scratch enumeration visited all \(4{,}913\times6=29{,}478\) design–order pairs. It used raw vectors through squared norm four, exact signed lexicographic ties at both selections, and Gram determinants to compute the squared distance to the plane spanned by the two selected lifts. Outward intervals enclosed the gate cutoffs, and exact rational comparisons separated every tested value from the uncertain endpoints. In lexicographic order of the six permutations of \((1,2,3)\), the original-coordinate hit counts were \((2,2,2,4,2,4)\). Processing-order ties gave two hits in every permutation. The eight contributing sign designs and their fresh indices matched the table. [Part 163, Proposition 3](wall1_restart_haar_ratio.md) · [Part 164 toy and audit](wall1_selected_hit_direct.md)

Thus the original-coordinate rule increases the toy selected-hit probability by exactly \(16/12=4/3\) relative to fixed order. This refutes a universal claim that one random ordering can only reduce that mass. The width-506 inequality \(P+p_a\le 0.00019770868\) remains open.
