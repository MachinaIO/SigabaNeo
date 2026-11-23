# Score rejection and prefix lifting on the width-506 restart

Two parts of the selected-output law can be bounded without a model for the reducer. On a horizontal last win, competitors using the last graph coordinate contribute less than **\(1.17349\cdot10^{-7}\)** to the mean score, summed over all plant heights and both signs of the graph coordinate. On either kind of win, the mean score from terminal lines of syndrome codimension at most 131 is less than **\(10^{-920}\)**, including every signed multiple. For the lift, the first 210 of the 407 selected lengths all exceed 13 outside a set of probability **less than \(5\cdot10^{-18}\)**. Higher-codimension cases remain in both problems. There is a reachable physical output with exact score zero that loses 407 secret coordinates in its prefix.

## The two probabilities

Use Part 117's **unconditioned marginal restart**. The \(400\times512\) matrix \(A\) has independent uniform entries in \(\mathbb F_{3329}\). The first 105 columns initialize the rank-505 graph. Each of the next 407 appends freezes the signed shortest vector of a rank-506 window, with the Part 108 tie rule. Write \(D=(A,\omega)\) if the specified plant-blind reducer uses independent tie or preprocessing coins. The concrete estimates below use the stated forward pass and signed rule. Write \(P=P_D\) for the final physical projector in \(\mathbb R^{912}\), \(H=P L(A)\) for the projected raw graph, and \(s_i=\|b_i^*\|\) for the frozen lengths in selection order. The independent \(X\) has 912 product CBD(3) coordinates, including both error and secret coordinates with the fixed sign convention. Put \(Z=\|PX\|^2,\ a=959.5,\ B=960.5,\ \tau=0.00012938\). [Forward pass](wall1_first_tour.md) · [Restart coupling](wall1_idea_round2.md) · [Part 182 audit](wall1_restart_passes_test.md#audit)

The first open probability is \(\delta_s=\Pr_D(C(D)>\tau)\), with proposed target \(0.005\), where
\[
 C(D)=\mathbb E_X\!\left[{\bf1}_{Z\le a}
 \sum_{k=0}^{30}\sum_{0\ne v\in H}
 {\bf1}_{\|v+kPX\|^2+k^2\le1+Z}\,\middle|\,D\right].
\]
The score counts equalities and signed points. At positive \(k\) it already uses one representative of the two plant-height signs. The multiplication by two for \(v,-v\) at height zero is retained. Markov gives the sufficient condition \(\mathbb E_D C\le6.469\cdot10^{-7}\). A direct bound on \(\delta_s\) also suffices. A test that computes a certified upper bound needs its own rejection probability. [Score definition](../../SigabaNeo/Lib/Lattices/Research/Wall1/FixedBlockScore.lean) · [Part 181](wall1_test_acceptance.md)

For lift allowance \(\ell\), put \(S(D)=\sum_{i=1}^{407}2e^{-s_i^2/12}\). The second open quantity can be written as the **additional** rejection \(\delta_p=\Pr_D(C\le\tau,\ S>\ell)\). The joint rejection is exactly \(\delta_s+\delta_p\). For each accepted output, with probability taken over the true plant, terminal failure is less than \(0.000607731\), and Babai failure from a lift of the planted projection has probability at most \(S(D)\). No independence between these plant events is required. For one block the sufficient 99% budget is
\[
 \delta_s+\delta_p \ \le\ 0.01-0.000607731-\ell .
\]
The Lean product in `restartScore_lwe` requires disjoint row indices. Only one disjoint block of 400 rows fits in 511. The original forward pass has 518 frozen directions. On Part 117 coupling agreement these comprise 111 sample \(q\)-axes and the same 407 directions as in the marginal restart. Its score agrees and its prefix charge equals \(S+222e^{-q^2/12}\). Allow for that increment when transferring a joint test, and pay the coupling disagreement \(<0.00022304\) once. This transfers an indicator. The older `smoothError` bound uses a minimum-floor test. Part 171's determinant obstruction and Part 181's pivot obstruction concern different acceptance predicates. [Width-506 terminal theorem](../../SigabaNeo/Lib/Lattices/Research/Wall1/FixedBlockScore506.lean) · [Joint test and composition](../../SigabaNeo/Lib/Lattices/Research/Wall1/FixedBlockScoreRestart.lean) · [Lift bound](../../SigabaNeo/Lib/Lattices/Research/Wall1/RestartLift.lean) · [Older smooth bound](../../SigabaNeo/Lib/Lattices/Research/Wall1/FixedBlockChernoff.lean)

## What spacing can imply

Let \(E=\{\lambda_1(P_{x^\perp}M_{406})\le26\}\), for the designated old shortest vector \(x\), and \(F=\{\lambda_1(H)\le26\}\). The Lean discrepancy is \(<5.244\cdot10^{-9}\). On \(F\) the score exceeds \(1.49842372\). Even a proof of the proposed residual bounds for \(Z_1,Z_2\) would bound an occurrence probability at one radius. The height-zero mean weights the whole signed counting measure through \(\sqrt B\). For \(k>0\) a counted \(v\) obeys
\[
 \|v\|\le k\sqrt a+\sqrt{B-k^2}.
\]
This increasing enclosure reaches \(937.052085\) rounded up at \(k=30\). Plant height \(k\) and the height in the last graph column are distinct integers. [Part 237 dependency audit](wall1_detect_repair.md#audit) · [Concrete discrepancy](../../SigabaNeo/Lib/Lattices/Research/Wall1/ConcreteTerminal506.lean)

**A reachable rejection outside both spacing events.** In the first 105 columns, use one column \(27e_1\) and put the other 104 on the remaining 399 rows. Choose that \(399\times104\) graph with minimum \(>938\). Such a choice exists by the raw count below, whose failure bound is \(<10^{-279}\). Set the 407 suffix columns to zero. Each new unit axis is strictly shorter than the old minimum and is removed. The retained lattice is the orthogonal sum of the large-minimum graph and the two-dimensional graph with basis \((3329,0),(27,1)\). Its minimum is \(\sqrt{730}\): outside the primitive line of \((27,1)\) the transverse spacing is \(3329/\sqrt{730}>123\). Thus \(E,F\) are both false. At \(729\le Z\le a\) both signs of the shortest vector count at height zero. With \(\mathbb E Z=757.5,\ \mathrm{Var}(Z)\le2272.5\), Cantelli and the cap bound give
\[
 C\ge2\left(\frac{28.5^2}{2272.5+28.5^2}-0.00047835048014\right)>0.52566 .
\]
This example has positive design mass and disproves the event implication. Positive plant heights also depend on orientation. In Part 182's rank-one check, the same spacing-2 lattice embedded along \((1,0)\) or \((3,4)/5\) gives different height-one scores, \(1920/4096\) and \(462/4096\), at cap 1.9. Thus even the complete intrinsic centered length spectrum does not determine the shifted score. This last example illustrates the dependence and supplies no frequency estimate for rank 505. [Moments, cap and orientation check](wall1_restart_passes_test.md)

## A translated count on horizontal last wins

Force the old signed shortest vector before revealing the last column. On a horizontal win this gives the true projector, and the output is \(\Gamma+\mathbb Z(\widetilde U,1)\), where the old \(\Gamma\) has rank 504, and \(U\) is the image of the last uniform column in a finite mark group \(G\). The forced projector and \(X\) determine \(y=PX\) before the mark is drawn. Write \(j\) for the last graph coordinate of \(v\). Then \(|j|\le3k+\sqrt B<122\) because the last axis is unchanged. Every contributing \(j\ne0\) permutes \(G\) by multiplication.

For log determinant floors define \(L_0=400\log q\) and \(L_{i+1}=\max(L_i-\log q,505L_i/506-\tfrac12\log56.2142)\). On a feasible forced branch \(\det\Gamma=\det H\ge e^{L_{407}}\). Discard forced states below this floor first. On the others, drop the horizontal-win indicator to upper-bound the nonnegative count. This avoids conditioning the last column on who won. [Forced-old comparison](wall1_penultimate_tail.md) · [Marked-grid identity](wall1_uncovered_lines.md)

Fix \(X\). For each eligible \(j\ne0\), averaging its old lattice coset gives \(1/|G|\) times the count in the marked preimage \(K\), translated by the old component of \(ky\). Here \(|G|\det K=\det\Gamma\), and \(K^*\) is the section of the **integral** grid in the forced old subspace. Enlarge the resulting Gaussian sum to all integer \(j\) after the averaging identity has been used. This costs no uniformity assumption at \(j=0\) or \(j\equiv0\bmod q\). The Gaussian shift in the last coordinate is \(ky_{\rm last}\). Poisson summation bounds a translated Gaussian by the centered dual sum using absolute values. Restriction to 504 independent coordinate rows injects \(K^*\) into \(\mathbb Z^{504}\) and shortens norms. The extra integer axis gives the 505th factor. The weaker integrality \(qH^*\subseteq\mathbb Z^{912}\) for the selected lattice alone would have the wrong Gaussian scale here. [Integral dual](wall1_integrality_bound.md) · [Fresh-mark count](wall1_fresh_mark_extension.md)

Take \(d=505,\ t=d/(2B),\ z=\sqrt{\pi/t}\), and \(\Theta(z)=1+2e^{-\pi z^2}/(1-e^{-3\pi z^2})\). Majorizing the competitor indicator by \(e^{t(1+Z-k^2-\|v+ky\|^2)}\) gives the factor \(z^d\Theta(z)^d e^{-L_{407}}\). For \(u=(1-3d/(2a))/3\in(0,t)\), the fixed-projector CBD moment gives
\[
 \mathbb E[{\bf1}_{Z\le a}e^{tZ}]
 \le e^{(t-u)a}(1-3u)^{-d/2}.
\]
Thus at each \(k\) the **joint** mean contribution on horizontal wins from \(j\ne0\), conditional on any history before the last draw, is at most
\[
 e^{-tk^2}\exp(tB-ua)(1-3u)^{-d/2}z^d\Theta(z)^d e^{-L_{407}} .
\]
The prefactor is \(<5.26586\cdot10^{-8}\). Summing over \(0\!:\!30\) costs \(<1.17349\cdot10^{-7}\), over \(1\!:\!30\) costs \(<6.46897\cdot10^{-8}\), and over \(10\!:\!30\) costs \(<2.02445\cdot10^{-19}\). These are nested bounds. They include signed multiplicities. For \(j=0\) the old coset never refreshes. On a nonhorizontal win the true projector depends on this same mark, so the fixed-center calculation does not extend directly.

## Two estimates that apply to either last winner

**Translated raw lifts.** With \(X\) fixed, count \(v\ne0\) admitting a raw lift \(w\in L(A)\), \(Pw=v\), with \(\|w+kX\|\le250\). The ball center is integral and independent of \(A\). Distinct \(v\)'s give distinct \(w\)'s at fixed \(k\). All coordinates of \(w\) have magnitude at most \(250+90<q\). A nonzero graph member in this ball must have nonzero input residue, since zero input residue forces every coordinate to vanish modulo \(q\). Each remaining fixed candidate belongs with probability exactly \(q^{-400}\). In particular there is no need to condition on the selected projector.

Write \(G_n(R)=e^{n/2}z_R^n\Theta(z_R)^n\), \(z_R=R\sqrt{2\pi/n}\), the Gaussian upper bound on the number of integer points in an origin-centered ball. Translation by \(kX\) preserves the integer count. The mean contribution of **all** such score terms is at most \(31G_{912}(250)/q^{400}<5.468\cdot10^{-9}\). The same calculation with \(R=938\) and \((n,m)=(505,400),(503,399)\) gives the two existence estimates used in the examples. For an uncharged competitor at \(R=250\), every lift has \(\|(I-P)(w+kX)\|>\sqrt{250^2-B}>248.07\). This is the missing component in the naive Part 236 transfer. Conditioning on \(X\) fixes the raw center but does not fix the cylinder cut out by \(P_A\), or bound its multiplicity. The width-638 note itself uses 511 secret coordinates and 512 available rows, transposed relative to this restart. We use its fixed-center argument with the dimensions above. [Part 236](wall1_selfdual_envelope.md) · [Part 238](wall1_cvp638_cost.md) · [Dependence of selected raw lifts](wall1_penultimate_projection.md)

**Section count with signed multiples.** For a terminal line containing a competitor, let \(T\) be its full rational inverse image, including the frozen span \(W=\ker P\). Here \((N,b)=(912,408)\) are ambient and section ranks. Write \(h(T)=\det(T\cap\mathbb Z^N)\) and \(d_T=400-\dim_{\mathbb F_q}\sigma(T\cap\mathbb Z^N)\) for \(\sigma(x,y)=x-Ay\bmod q\). Since \(\det(L\cap T)=q^{400-d_T}h(T)\) and \(\det(L\cap W)=q^{400}/\det H\), the primitive spacing on that line is exactly
\[
 \lambda_T=h(T)\det H/q^{d_T}.
\]
For signed multiple \(\pm m\), \(m\ge1\), to have norm \(\le R\) requires \(h(T)\le H_d/m,\ H_d=q^d R e^{-L_{407}}\) at exact deficiency \(d\). This is a deterministic list for each \(d,m\), before revealing the design. For each fixed \(T\), Part 223 bounds the deficiency tail by \(2q^{-d(b-400+d)}\) in the ranges used. Drop \(W\subset T\) after using the implication. Each actual terminal line contributes at most once for each sign and \(m\). [Fixed-space probability](wall1_wholly_old_mass.md) · [Section counts, equations (2) and (4)](wall1_high_codim_sections.md)

For clarity, let \(\mathcal U(N,b,B',d_*)\) denote the Part 226 upper sum through deficiency \(d_*\), using height \(q^d B'\), chart-rank split 144, and its \(1/(1-q^{-100})\) geometric allowance. All nonempty chart-count bounds used here are sums or maxima of monomials in height of exponent at least 2. The rank-zero graph is bounded by the same positive-power envelope for heights \(\ge1\). Below height one the count is zero. Replacing the height by \(H_d/m\) therefore divides the bound by at least \(m^2\), even before summing over deficiencies. Both signs and all multiples cost less than \(2\sum_{m\ge1}m^{-2}<4\). This step converts the occurrence argument into an estimate on the **point count**. The interval checker evaluates the cited chart expressions with the new ranks, heights and determinant floors.

| Terms in the score | Mean contribution under the actual design law |
|---|---:|
| \(d_T\le131\), all plant heights | \(124\,\mathcal U(912,408,938e^{-L_{407}},131)<10^{-920}\) |
| \(d_T\le132\), height zero | \(4\,\mathcal U(912,408,31e^{-L_{407}},132)<10^{-258}\) |
| \(d_T\le132\), height one | \(<10^{-69}\) |

For the last row, height one requires \(\langle X,v\rangle\le-\|v\|^2/2\). Conditional on the design, its probability is at most \(e^{-\|v\|^2/12}\) by the one-sided CBD moment. Use radius 50 without this weight, then bound \(50<\|v\|<62\) by the radius-62 estimate times \(e^{-2500/12}\). For \(k\ge2\), the enclosing radius alone gives the first row. Parts 225–226's large-deficiency examples concern selected flags for a different predicate. They explain why dropping all selection tests can be expensive, without proving that every remaining term here is equivalent to a specific long-winner event.

## What the prefix law gives

**A uniform early segment.** Write \(B_l\) for the nondecreasing envelope of the Part 151 Hermite flag caps \(\sqrt{\gamma_l}\prod_{v=2}^l\gamma_v^{1/(2(v-1))}\), with \(B_1=1\) and the proved Part 224 upper coefficients substituted for \(\gamma_l\). Put \(P_k=\sum_{l=1}^k\log B_l\). For any short winner \(s_t\le u=13\) with \(t\le T=210\), stop the flag at that winner. If its last used suffix column is \(i\), the trailing flag in window \(i\) has \(t-i+1\) terms. The Hermite argument bounds the heads of its tails by \(uB_l\). Pad the **bounds** to \(k=T-i+1\) using monotonicity. If the first \(j\) in that window omit column \(i\), they agree with the deterministic successive old shortest choices. Their product is at most \(u^j e^{P_k-P_{k-j}}\). Test these bounds before seeing the fresh mark. The first direction using column \(i\) has length \(\le uB_{k-j}<q\), so the positive-height permutation bound applies. The resulting test depends on \(i,j,T\); it covers every stopping time \(t\le T\) without a factor of 210. If the whole flag omits the suffix, the initial raw minimum is \(\le uB_T\). [Last-used-coordinate proof](wall1_penultimate_tail.md) · [Proved profile](wall1_budget_ledger.md)

Explicitly, start the sum with \(V_{505}(uB_T+\sqrt{505}/2)^{505}/(2q^{400})\). For \(1\le i\le T,\ 0\le j<k=T-i+1\), put \(n=506-j,\ w=B_{k-j},\ z=\max(1,w\sqrt{2\pi/n})\). Add
\[
 \tfrac12 u^{506} e^{\pi(w/z)^2-L_{i-1}+P_k-P_{k-j}}z^n\Theta(u)^{505}.
\]
Here \(\Theta(uz)^{n-1}\le\Theta(u)^{505}\). The upper sum is \(<4.9300\cdot10^{-18}\), with \(uB_{210}<2329<q\). Outside this event the first 210 prefix charges sum to \(<0.000321319\).

**Later small winners.** If \(s_i\le13\) on \(211\le i\le407\), its frozen section \(T_i\) including that winner has rank \(i\) in \(\mathbb Q^{505+i}\), and
\[
 \det(L_i\cap T_i)/q^{400}=s_i/D_{i-1}\le13 e^{-L_{i-1}},
\]
where \(D_{i-1}\) is the incoming determinant. Shortest-vector primitivity at every step gives the full frozen section in this identity. The same fixed-space count, now without multiples, gives
\[
 \sum_{i=211}^{407}\mathcal U(505+i,i,13e^{-L_{i-1}},132)<10^{-1314}.
\]
There is a further geometric restriction even at larger deficiency. Unless some draw has a positive-graph-height vector of length \(\le26/\sqrt3\), a small winner on draw \(i\) is old. Round its lift along the previous winner. If its projection has length \(r\le13\), shortestness and the half-length rounding strip bound both the previous winner and the reduced lift by \(2r/\sqrt3\). Both must therefore have graph height zero at draw \(i-1\). They span a plane of area at most \(2r^2/\sqrt3\le338/\sqrt3\) in the state after draw \(i-2\), containing the previous winner. Saturation can only decrease area. The probability of the fresh-vector exception across all 407 draws is \(<1.02\cdot10^{-162}\), using the Part 183 positive-height Gaussian bound at \(R=26/\sqrt3,\ z=R\sqrt{2\pi/506}\), summed conservatively as \(407 e^{253}z^{506}\Theta(z)^{505}/(2e^{L_{406}})\). [Rounding and positive-height bound](wall1_terminal_tail_047.md)

Thus the outstanding small-prefix event can be restricted to \(d_{T_i}\ge133\) **and** such an old plane on a cut between 209 and 405. A later plane may disappear. Part 224's residuals include a terminal hit, so its terminal-event upper bound cannot be substituted for this path event. At \(\ell=0.000623\), length \(>13\) on all 407 draws suffices since \(814e^{-169/12}<0.000622746\). This is a sufficient floor. A single length below 13 need not make \(S>\ell\).

**A deterministic lift fails even after score acceptance.** Choose the initial \(400\times105\) graph with minimum \(>938\), possible by the raw count above, and set all 407 suffix columns to zero. Each new secret unit axis is the unique shortest line and is frozen. The final lattice is exactly the initial graph. The enclosing radius proves \(C=0\); the prefix charge is \(814e^{-1/12}>748\). With retained plant coordinates zero, \(PX=0\) and the signed height-one plant is uniquely shortest. Varying the discarded secret coordinates changes neither the projection nor the public data. Babai rounds these unit axes to zero. Conditional on this design and these retained coordinates, even the best single-answer decoder guesses the 407 independent hidden coordinates with probability at most \((5/16)^{407}\).

For Part 236's prescribed discarded **sample** axes the GS vectors are \(qe_i\). The strip check is exactly \(|X_i|<q/2\), which holds throughout the CBD support. For a general horizontal GS vector \(b^*\), the strict strip holds throughout that support precisely when \(6\|b^*\|_1<\|b^*\|^2\), by maximizing the inner product over the product support. Equality needs a rounding convention. Part 117's 111 prescribed axes enjoy deterministic lifting on coupling agreement. The actual remaining 407 vectors need a distributional bound. [Part 47](wall1_decoupled.md) · [Part 236 discarded coordinates](wall1_selfdual_envelope.md)

## Outstanding numerical budgets

For the proposed mean-score proof, assign each score summand to the union of the fresh-column, short-raw-lift and paid section classes above, or to its complement. Overlaps within the union are harmless for an upper bound. A sufficient remaining **mean** allowance is \(5.2408\cdot10^{-7}\), since adding the three upper charges gives less than \(6.469\cdot10^{-7}\). What remains requires long translated raw lifts, deficiency at least 133 for \(k=0,1\) or at least 132 for \(2\le k\le30\), and either a nonhorizontal last winner or graph height zero on a horizontal last win. This includes inherited signed multiplicities beyond radius 26 and shifted counts whose embeddings depend on the selected history. Bounding \(E\) alone settles none of these totals.

For one marginal block at \(\ell=0.000623\), a score-rejection proof of \(0.005\) would leave \(0.003769269\) for \(\Pr(C\le\tau,S>\ell)\). Transferring the same sufficient floor and the score test to the 511-row pass leaves \(0.003546229\) after the coupling charge; the 111-axis increment fits within the rounded \(\ell\). The early and low-deficiency bounds above leave the joint mass of score-accepted designs with a late, high-deficiency small prefix unresolved. The counterexamples bound no typical frequency. Neither the 0.005 rejection target nor end-to-end 99% recovery follows.

The new estimates are paper derivations. The 50-decimal outward interval checks run with `python -B docs/research/scripts/wall1_score_rejection.py` from the repository root. [Numerical checker](scripts/wall1_score_rejection.py)

## Audit

**Verdict — confirmed for the unconditioned marginal restart with the signed forward-pass selector.** Both constructions are reachable, and all four stated bounds hold. The checker passed every assertion. The total score-rejection probability and joint prefix-rejection probability remain open.

**Reachable designs.** In the first example each zero append deletes its own unit axis. At cut 406 the designated old shortest line is generated by \((27,1)\). Its length is \(\sqrt{730}>26\), and projecting it out leaves spacing \(3329/\sqrt{730}>123\) in its two-dimensional factor. The independent factor has minimum greater than 938 throughout. This verifies \(F^c\) and \(E^c\) separately. The signed height-zero pair gives \(C>0.52566\). In the second example the entire retained graph has minimum greater than 938, while the largest enclosing score radius is below 937.053. Hence \(C=0\). With all retained plant coordinates zero, the unique shortest projected line is the height axis. The zero suffix columns make the public observation independent of the 407 discarded secret coordinates. Their conditional maximum joint atom is \((5/16)^{407}\), even given that terminal outcome. The two required initial graphs exist because each corresponding raw first moment is below one.

**Mean score.** On a horizontal win the old signed minimizer can be fixed before the last draw. Its projector also fixes the center given the plant. Every contributing nonzero last-coordinate height has absolute value below 122 and permutes the mark group. Discarding forced states below the determinant floor and then dropping the win indicator therefore bounds the joint mean under the original draw law. The checker gives an upper bound below \(1.173483\cdot10^{-7}\) over all 31 plant heights. For translated raw lifts, count candidates at the fixed integral center before selection. Each eligible candidate costs \(q^{-400}\), and distinct projected points at a fixed height require distinct lifts. The resulting bound is below \(5.467503\cdot10^{-9}\).

For either winner the saturated inverse image of a terminal line has primitive spacing \(h(T)\det H/q^{d_T}\). At multiple \(m\) the height cutoff divides by \(m\). Every chart envelope, including the rank-zero majorant above height one, then decreases by at least a factor \(m^2\). Below height one the list is empty. Thus both signs cost at most \(2\sum_{m\ge1}m^{-2}<4\) together, and the 31 heights give the stated factor 124. The checker gives less than \(9.408\cdot10^{-921}\) through deficiency 131. The two extra deficiency-132 estimates for heights zero and one also pass.

**Prefix and budgets.** Stopping at any small winner by draw 210 gives the padded last-used-column test indexed by \((i,j)\). The same test covers every admissible stopping draw for that pair. An independent evaluation over the 22,155 pairs gave \(13B_{210}\approx2328.865<3329\) and reproduced the interval checker's sum to ten significant digits. The checker bounds the early exception by \(4.929920\cdot10^{-18}\) and the late exception through deficiency 132 by \(4.407\cdot10^{-1315}\). Outside these exceptions, \(C\le\tau,\ S>0.000623\) requires a score-accepted design with some \(211\le i\le407\), \(s_i\le13\), and \(d_{T_i}\ge133\). The reverse implication is unnecessary since one small length can fit the lift allowance.

Adding \(5.2408\cdot10^{-7}\) to the rounded fresh and raw bounds gives \(6.46897\cdot10^{-7}\), leaving \(3\cdot10^{-12}\) for the much smaller section charges before the Markov threshold. The proposed remaining mean allowance is sufficient. If the score-rejection target is proved, the available joint prefix budgets are \(0.003769269\) for the marginal restart and \(0.003546229\) after the single coupling charge. These are sufficient budgets. The estimates above leave their outstanding probabilities unbounded at those levels.
