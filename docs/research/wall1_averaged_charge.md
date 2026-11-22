# History averages of the first-pass plane charges

At width 506 and the recorded ratio 0.954, the original pass has expected horizontal charge greater than $1-6.05\cdot10^{-15}$ on graph draw 102 and less than $2.05\cdot10^{-11}$ on draw 103. The designated horizontal axis wins with probability above $1-2.02\cdot10^{-11}$ on both draws. The old-plane cutoff crosses the length of a second coordinate axis between them. This rules out substituting a common rate measured over horizontal steps for the rate at a specified time. It leaves the terminal draw open.

There are two different losses at the terminal draw. Even exact one- and two-candidate modular inclusion probabilities can allow competitor-void probabilities on opposite sides of the entire failure budget. Even exact winner exclusions can leave excess multiplicity in the positive-height first moment. Below, the first obstruction is a finite-field example, and the second has an explicit positive-probability witness in the actual width-506 restart law.

## The design average and the winner constraint

Use the $qI$-first, exact, no-lookahead pass with signed ambient lexicographic ties. The design is uniform. The CBD(3) plant does not enter the history law. Just before a graph draw let $L$ be the old lattice, $d=\beta-1$, $D=\det L$, $x_0$ its designated shortest vector and $t=|x_0|$. Write $G_d=V_d^{-1/d}$ for unit-ball volume $V_d$, $R(s)=cG_d(D/s)^{1/d}$ and $I=\mathbf1\{\lambda_1(\pi_{x_0^\perp}L)<R(t)\}$. Let $b$ indicate that the winner of the enlarged window is horizontal relative to the new column. Conditional on the old state, $w=\Pr(b=1\mid L,H,\text{frame})$.

For a uniform $m'$-by-$n$ graph $A$ and a specified draw $j$, the exact identity is
\[
 h_j=\mathbb E[Iw]=q^{-m'n}\sum_A I_j(A)b_j(A).
\]
Indeed $I$ is determined before the draw and the fresh raw column maps onto the mark $H$ with equal fiber sizes. Integrating out unread columns gives the same identity at intermediate draws. When $\Pr(b)>0$, restricting to horizontal wins changes the history measure by the density $w/\mathbb Ew$, giving $h_j=\Pr(b)\Pr(I=1\mid b)$. Pooling several draws weights each time by its own horizontal-win probability. [First-pass law](wall1_first_tour.md) · [Terminal plane identity](wall1_plane_count.md)

For a proposed path, at each window require the proposed vector to belong and exclude every nonzero vector earlier in the order (squared norm, signed ambient coordinates). On a fixed path the projections are fixed. Only lifts available in that prefix may compete. Within a projected ball one needs one test per distinct projected candidate, allowing all its admissible lifts. An individual lift can be absent even though another representative of the same projected point belongs. With all these tests each design has one winning path. For the residual positive-height charge, let $N_+$ count saturated positive-height planes through that winner of area below $sR(s)$. Then
\[
 \mathbb E F_*=\mathbb E[(1-Ib)N_+],\qquad
 \mathbb E[Iw]+\mathbb E F_*-\Pr(\mathrm{failure})
 =\mathbb E[(1-Ib)(N_+-1)_+].
\]
This follows by splitting each draw at the existence of a horizontal witness. A horizontal winner can still belong to a positive-height plane. For height image $k\mathbb Z$, the mass of a feasible displacement $kU=y+L$ is $1/|kH|$, with uniform conditional mass $1/|H[k]|$ on its fiber. Both incidence and the winner test belong inside that average. [Plane count and audit](wall1_plane_count.md) · [Two-winner count](wall1_two_winner.md)

## Two neighboring draws at the recorded widths

**Proposition 1.** The following bounds hold on the unconditional original design law. Draws are numbered from the first graph column after the cubic prefix.

| Width | Ratio $c$ | Earlier draw and horizontal charge | Next draw and horizontal charge |
|---|---|---|---|
| 406 | 0.925 | $h_{75}>1-3.27\cdot10^{-17}$ | $h_{76}<1.09\cdot10^{-13}$ |
| 506 | 0.954 | $h_{102}>1-6.05\cdot10^{-15}$ | $h_{103}<2.05\cdot10^{-11}$ |

*Proof.* Force the earliest horizontal coordinate axis through graph draw $j$. At draw $i$ its forced window is a coordinate graph with $d+1-i$ rows and $i$ graph inputs. A competitor of norm at most $q$ other than the signed $q$-axes has nonzero input residue, so each fixed such label has membership probability $q^{-(d+1-i)}$. A union bound over sign pairs and the unit cubes centered at them gives the Part 117 bound on the probability of any disagreement,
\[
 B(j)=\tfrac12 V_{d+1}(1+\sqrt{d+1}/(2q))^{d+1}\sum_{i=1}^j q^i .
\]
This uses marginal graph laws along the deterministic path. It does not condition a uniform submatrix on past wins. [Coordinate-prefix theorem and audit](wall1_idea_round2.md)

On agreement through $j$, the last winner has length $q$. Projecting the **old** lattice along it deletes one more horizontal coordinate. The resulting graph has rank $d-1$, with $d-j$ rows and $j-1$ inputs. The retained determinant *after the actual append and freeze* is $q^{d-j}$, so the cutoff for the old projected minimum is $R_j=cG_d q^{(d-j)/d}$. When $R_j>q$, any remaining $q$-axis witnesses $Ib=1$. When $R_j<q$, every qualifying nonzero vector in the projected old graph must have nonzero input residue. Ignoring coordinate agreement in counting these vectors only increases their probability. The same sign-pair cube argument now gives
\[
 h_j\le B(j)+\frac{V_{d-1}(R_j+\sqrt{d-1}/2)^{d-1}}{2q^{d-j}} .
\]
In particular a horizontal win alone contributes no lower bound on $h_j$ in this second case.

At width 406, $R_j/q$ lies in $(1.0120,1.0121)$ and $(0.9919,0.9920)$ respectively. At draw 76 the two upper-bound terms are below $1.0871\cdot10^{-13}$ and $8.05\cdot10^{-17}$. At width 506 the ratios lie in $(1.0155,1.0156)$ and $(0.9993,0.9994)$. At draw 103 the two terms are below $2.013\cdot10^{-11}$ and $3.459\cdot10^{-13}$. Substitution in $B(j)$ gives the earlier-draw errors in the table. These enclosures use $V_k=\pi^{k/2}/\Gamma(1+k/2)$ with outward-rounded interval arithmetic. ∎

## What exact pair counts can lose

For fixed required integer lifts with residue matrices $X,Y$, the equations $AY=X$ are consistent exactly when $\ker Y\subseteq\ker X$, and then have probability $q^{-m'\operatorname{rank}Y}$. Each row is prescribed on $\operatorname{im}Y$ and is free on a complement. Conditional on these required lifts the remaining choices are uniform on that affine space. More explicitly, let $P$ be a finite list of required raw lifts and $B$ a finite list of forbidden raw lifts for a fixed path. Set $g(J)=q^{-m'\operatorname{rank} Y_J}$ for consistent $J$, and zero otherwise. The unconditional mass satisfying these tests is
\[
 \sum_{S\subseteq B}(-1)^{|S|}g(P\cup S).
\]
Expand the product of the required membership indicators and the factors $1-\mathbf1_{z\text{ belongs}}$ for $z\in B$, then take expectations using the row count. This formula concerns fixed raw labels. A projected point with several possible lifts requires a union on its membership side; any relaxation using a subset of its lifts for exclusion must allow the other lifts to compete in the true process.

For an old incidence event $I=1$ of positive probability, count the *competitors beating the designated horizontal winner* by $K$. The horizontal charge is $\Pr(I=1)\Pr(K=0\mid I=1)$. If $\mathbb E[K^2\mid I=1]>0$, Cauchy–Schwarz gives the upper bound
\[
 h_j\le\Pr(I=1)\left(1-
 \frac{\mathbb E[K\mid I=1]^2}{\mathbb E[K^2\mid I=1]}\right).
\]
Here $K$ is counted on the incidence-weighted law **before** selecting horizontal wins. On the horizontal-win law it is identically zero. Testing a subset of beaters gives a valid, weaker void bound. [Finite family count](wall1_finite_family.md) · [Ambient modular counts](wall1_qary_gap.md) · [Mixed modular identity](wall1_qary_rogers.md) · [Availability of lifts](wall1_annealed_selection.md)

**Proposition 2.** Under a uniform graph law, exact individual and pair membership probabilities, even with pairwise independence of the competitor events, do not bound a general modular void below $0.00977696$.

*Proof.* Read two independent entries $X,Y$ of one row of $A$, over an odd prime field. For each $i\in\mathbb F_q$ declare a forbidden competitor if $Y-iX=f(i)$. These are graph constraints on the input $(-i,1)$; with extra output rows the event is the disjoint union over their unrestricted output labels. Each event has probability $1/q$. Each pair has probability $1/q^2$ because the two inputs are independent. Thus the total count $K$ has $\mathbb EK=1$ and $\mathbb E K^2=2-1/q$, regardless of $f$. The same calculations hold conditional on prescribed data in other independent columns.

For $f(i)=0$ the void consists of $X=0,Y\ne0$ and has probability $(q-1)/q^2$. For $f(i)=i^2$, fix $X$. Completing the square shows that $i^2+iX$ takes exactly $(q+1)/2$ values. The void probability is $(q-1)/(2q)$. At $q=3329$ these probabilities are respectively $3328/11082241$ and $1664/3329$, about $0.00030030$ and $0.49985$. The first two moments even give the same Cauchy–Schwarz upper bound $(q-1)/(2q-1)$ for both. ∎

These lists are finite-field counterexamples to a rank-and-pair inference. They are not claimed to be the metric competitor lists of the recorded terminal window. A proof from two moments for those specific lists would need quantitative information about their geometry or conditioning absent from the general rank weights.

## A terminal contribution on an exactly countable family

**Proposition 3.** In the unconditioned width-506 reduced law let $Q=q^{400}$. Let $C$ be the event that all 105 restart columns are nonzero and all 407 subsequent raw columns are zero. Its probability is $(1-Q^{-1})^{105}Q^{-407}$. Its horizontal contribution is zero, and its contribution to $\mathbb EF_*$ is less than $1.364\cdot10^{-10}Q^{-407}$. On the full reduced law the excess of the sum of Part 120 charges over the true failure probability is at least
\[
 2\,(Q-1)^{103}/Q^{512}>0 .
\]

*Proof.* The restart graph is integral. Its only possible unit vectors are the signed graph axes of zero columns, so on $C$ its minimum exceeds one. Each zero append introduces an orthogonal unit winner and removes it again. Its quotient, including at the last draw, is the original graph. Every short primitive quotient line gives exactly one positive-height plane through the fresh winner. The cutoff is $R=cG_{505}q^{400/505}<q$. Discarding the restriction that the restart columns be nonzero bounds the contribution by $Q^{-407}$ times the unconditional restart line moment. Sign pairs, nonzero input residue and unit cubes give the latter at most $V_{505}(R+\sqrt{505}/2)^{505}/(2Q)<1.364\cdot10^{-10}$. On this family the penultimate $\lambda_1/\mathrm{GH}$ is at most $q/(G_{505}q^{400/505})<0.985791$ by the horizontal $q$-axes. [Restart band and audit](wall1_moment_closure.md) · [Restart minimum and audit](wall1_horizontal_core.md)

Within $C$, prescribe that the first three restart columns coincide. There are $(Q-1)^{103}$ designs in this event. The three pairwise differences of their graph-coordinate axes give distinct primitive unoriented lines of length $\sqrt2<R$. Each is primitive already in the ambient integer lattice. All three are counted on the final draw, whose failure indicator is one. The excess identity gives the lower bound after averaging. ∎

This example isolates multiplicity with every one of the 407 winners exact. Its small mass is compatible with the proposed budget. In the other direction, the audited terminal family with at most 103 nonzero penultimate columns has horizontal charge exactly one for every final column. Its full contribution is its binomial mass. The two families leave the bulk of the design law unaccounted for. [Horizontal family and audit](wall1_horizontal_core.md)

## Exact two-draw enumeration with a random old lattice

**Proposition 4.** A complete small terminal law violates $\mathbb E[Iw]\le\mathbb E[I]\mathbb E[w]$. Take one horizontal row over $\mathbb F_2$, twelve independent restart columns, and two more graph draws under the same selector. The retained rank is 13. Use the recorded ratio $c=0.954$. All $2^{14}$ designs have the same weight.

| Terminal observable | Numerator over 16,384 designs |
|---|---:|
| Old-plane indicator $I$ | 16,200 |
| Horizontal win $b$ | 16,370 |
| Horizontal hit $Ib$ | 16,200 |
| Residual positive-height plane count $(1-Ib)N_+$ | 78 |
| True terminal failure | 16,278 |
| Penultimate $\lambda_1/\mathrm{GH}>1.0014$ | 28 |

*Proof.* Let $Z$ be the number of zeros among the twelve restart columns and the first draw, so $Z\sim\operatorname{Bin}(13,1/2)$. If $Z\ge1$, the first winner deletes the earliest zero axis. The old lattice at the final draw has $Z-1$ free unit axes and an orthogonal even-coordinate-sum lattice on the remaining coordinates, of determinant two. When $Z\ge2$, an old unit wins for either final bit. At $s=1$ the cutoff lies strictly between 1 and $\sqrt2$. Thus $I=1$ exactly when $Z\ge3$. If $Z=2$, a zero final bit supplies the unique short quotient line, the fresh unit after the old unit is removed. A one supplies none. If $Z=1$, the old lattice is the even-sum lattice in dimension 13. A fresh zero unit wins for bit zero, and an old signed root wins the lexicographic tie for bit one. The output minimum in these cases is at least $\sqrt{3/2}$, above the cutoff.

If $Z=0$, the first window is the even-sum lattice in dimension 14 and its winner is $-e_1-e_2$. Projecting off this root gives minimum $\sqrt{3/2}$: every nonzero quotient lift can be rounded along the root, giving squared length at least $2-2/4$, attained by a root sharing one coordinate. The old determinant is $\sqrt2$. A final zero supplies a fresh unit; a final one extends the even-sum lattice by one coordinate before the same root projection. In the latter case the shortest projections come from roots sharing one coordinate with the first root. The earliest signed minimizer uses an old coordinate for its other index. Thus the win is horizontal exactly for final bit one. The cutoff in either case is less than one, and the quotient minimum exceeds one (for the root-sharing winner it is at least $(\sqrt3/2)\sqrt{3/2}$). The old projected-line test also fails by the same rounding bound.

For the old upper tail, when $Z\ge2$ the old minimum is one and the determinant is two. For $Z=1$ the minimum is $\sqrt2$ at determinant two. For $Z=0$ the minimum is $\sqrt{3/2}$ at determinant $\sqrt2$. Substitution of $G_{13}=1.00722753\ldots$ gives the table's upper-tail event exactly when $Z\le1$. Summing binomial counts and the two equally likely final bits proves the table. In particular every history passing the old-plane test wins horizontally, whereas 14 of the 16,384 designs lose horizontally. The covariance is exactly $(16200/16384)(14/16384)>0$. ∎

**Independent enumeration.** Scratch code tested all 16,384 ordered designs by the parity equation and the signed comparator on projected ambient coordinates. It enumerated all signed unit vectors and roots (integer squared length at most two). For exhaustiveness, a shortest candidate at the second selection has squared norm at most two and admits a lift of squared norm at most $2+2/4<3$. A terminal witness below the cutoff has a lift of squared norm less than $1.028+2/4+2/4<3$ by successive rounding. The same argument covers the old-plane test. Projection used integer numerators. Strict squared cutoffs were converted to integer cutoffs only when both interval endpoints gave the same floor. Deduplicating projected sign pairs gave the six numerators above. Separately, direct enumeration in the affine example gave void counts $(2,3),(4,10),(6,21)$ out of $3^2,5^2,7^2$ respectively. These small enumerations verify the finite examples and carry no probability transfer to width 506.

## Remaining terminal estimate

Part 124 lost selected-line incidence by charging every small sublattice and used a packing majorant for the cosets. Part 125 retained the modular weight of specified lifts, but a witness can first become available in the last window, and its presence does not enforce the outside-competitor void. Part 126 kept incidence through rank two; relaxing the next horizontal pullback charged unrestricted rank-three lattices. The first-exit accounting itself has coefficient one. Keeping Part 108's exact cosets and Part 120's split removes each of those replacements in the *identity*. It supplies no estimate for the old incidence-weighted void or for the surviving positive-height multiplicities. [Moment closure](wall1_moment_closure.md) · [Annealed selection](wall1_annealed_selection.md) · [Band moments](wall1_band_moments.md)

**Conjecture (terminal budget, open).** At draw 407 of the marginal width-506 restart, $h_{407}+\mathbb EF_*\le0.00977696$; the proposed equal allocation is $0.00488848$ each. Proposition 1 concerns the original coordinate prefix. Proposition 2 obstructs a general two-moment inference. Propositions 3 and 4 do not decide either recorded terminal inequality. For a bound on true failure alone one can replace the residual multiplicity by its nonempty-set indicator. Part 117 transfers such an event bound at additive cost below 0.00022304; transferring a plane count with the same error would also require control of its multiplicity on coupling disagreements.

The general late-state upper tail of $\lambda_1/\mathrm{GH}$ also remains open. In the audited Part 142 continuous direction comparison the relevant quantity is $(\lambda_1/\mathrm{GH})^d/p_1$, where $p_1$ is the conditional probability of a height-one win. A bound for the ratio alone would still need control of $p_1$ and a transfer to the discrete law. The toy tail and the explicit terminal family above establish neither estimate at the recorded dimensions. [Direction comparison and audit](wall1_dual_cusp.md) · [Wall 1, Parts 134–143](../PROOF_GAP.md)

## Audit

**Verdict — MINOR CAVEATS.** All four propositions and all six enumeration totals check out. One qualification concerns the comparison of two Cauchy–Schwarz bounds. The terminal estimate remains open.

**Coordinate draws and the budget.** On agreement through draw $j$, deleting the winning axis from the old graph leaves $d-j$ rows and $j-1$ inputs. A second surviving old axis has length $q$. It witnesses the strict old-plane test exactly when $R_j>q$. Below this crossing, any old witness needs a nonzero input residue. Counting it on the marginal forced graph and adding $B(j)$ is valid even though agreement depends on the design. Recomputing the ball volumes by $V_0=1$, $V_1=2$, $V_k=2\pi V_{k-2}/k$ with 65-decimal interval arithmetic gave the following values (rounded for display).

| Width | Draws | Earlier $B(j)$ | Earlier and later $R_j/q$ | Later upper bound for $h_j$ |
|---|---|---:|---|---:|
| 406 | 75, 76 | $3.265414\cdot10^{-17}$ | $1.01201051$, $0.99194582$ | $1.087861\cdot10^{-13}$ |
| 506 | 102, 103 | $6.045626\cdot10^{-15}$ | $1.01551955$, $0.99934032$ | $2.047178\cdot10^{-11}$ |

The earlier $h_j$ alone exceeds even $0.00977696$ at either width. A budget of that size imposed at each draw would therefore fail. Part 120 imposes it only at reduced draw 407 (original draw 512). Draw 102 can fail its own ratio test *on coordinate agreement*. Part 117 charges only coordinate disagreement through draw 105, with probability at most $B(105)<0.00022304$. Earlier ratio failures are never added to the terminal failure probability. At draw 103 the horizontal term alone is small, and the positive-height contribution at that draw is a separate quantity.

**Modular void and the moment qualification.** Two distinct slopes prescribe a unique $(X,Y)$, giving the same labeled singleton and pair probabilities in both lists. Directly counting omitted $Y$ values for every $X$ at $q=3329$ gave 3,328 and 5,539,456 void designs out of 11,082,241, exactly the two stated fractions. This rules out a universal upper bound of $0.00977696$ from these particular first- and second-order inclusion data alone. Other moment values or extra geometric restrictions on the actual metric lists can give stronger conclusions.

In the sentence “Testing a subset of beaters gives a valid, weaker void bound,” the exact void event enlarges under deletion. The *numerical Cauchy–Schwarz upper bounds* need not be ordered. For two nested beater events of probabilities $1/4$ and $1/2$, the full count has first and second moments $3/4$ and $5/4$, giving the upper bound $11/20$. Testing only the more probable event gives $1/2$. Both bounds are valid.

**Independent two-draw enumeration.** A fresh scratch script tested all $2^{14}$ ordered designs against the parity equation, minimized by squared norm and signed projected coordinates, and deduplicated the quotient lines up to sign. It used integer Gram determinants and interval-certified cutoffs. Successive rounding lifts every relevant witness to integer squared length below three, so signed units and two-coordinate roots suffice. In table order the counts were $(16200,16370,16200,78,16278,28)$. The joint horizontal charge exceeds the product of its marginals by exactly $14175/16777216$. This establishes the sign in the toy law only.

**Terminal family and excess.** On $C$ the fresh unit is the unique winning line on each append. Its quotient is the original restart graph, so the terminal horizontal charge vanishes. Every short primitive quotient line then contributes one saturated positive-height plane. Dropping the nonzero-column restriction from the *unnormalized* line count leaves the independent suffix factor $Q^{-407}$. The ball majorant multiplying it lies in $(1.36296,1.36297)\cdot10^{-10}$. Requiring the first three columns equal leaves 103 free nonzero column choices, and their three pairwise differences give distinct unoriented primitive lines. Each such design contributes excess at least two. This verifies $2(Q-1)^{103}/Q^{512}$ as a lower bound on excess, with the full-law normalization. The marked-fiber identity and the residual nonempty-set split agree with Parts 108 and 120. Transferring a terminal event costs at most the coupling disagreement probability. Transferring the plane-count expectation would additionally require a multiplicity bound there.
