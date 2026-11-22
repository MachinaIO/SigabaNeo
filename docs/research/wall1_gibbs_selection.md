# Gibbs selection in a projected lattice window

The Gaussian rule gives an exact probability law for a first pass with fresh columns. Its normalizers depend on intermediate windows. Two histories can have the same initial window, final retained lattice, frozen plane and total Gaussian energy, yet different probabilities. There is also a positive-temperature example in which conditioning on the selected vector raises the mean number of short quotient pairs from $9/4$ to more than $3.5330$. Thus replacing a shortest-vector test by a positive weight does not supply the comparison of selected and unselected averages needed in Wall 1.

Throughout, a call inserts its sampled vector unconditionally. The pass freezes one direction per call, keeps the whole projected window and reads each new column on entry. A strict-improvement test, a retry rule or a later tour on reused columns specifies a different stochastic process. The statements below concern an ideal primitive Gaussian oracle. The recorded application is the plant-free part of the plain LWE $(511,512,3329)$, CBD(3) analysis at widths 406 and 506. The distinction between an input-block theorem, a returned-basis predicate and a terminal probability is essential here. [Wall 1, Parts 45, 105–112, 120 and 134–154](../PROOF_GAP.md) · [Reducer variants and audit](wall1_reducer_variants.md)

## 1. What is explicitly distributed?

Use oriented primitive vectors $W_{\rm pr}$ of a Euclidean lattice $W$. Equivalently one can sum over lines and give each pair twice the oriented mass. With the lattice Gaussian convention, put
$$
 w_W(v)=\exp(-\pi\|v\|^2/\sigma(W)^2),\quad
 Z(W)=\sum_{v\in W_{\rm pr}}w_W(v),\quad p_W(v)=w_W(v)/Z(W).
$$
The scale is positive and measurable, for example $\sigma(W)=c\lambda_1(W)$. Every $Z$ is finite and positive. To see convergence, disjoint balls of radius $\lambda_1/2$ about lattice points of norm at most $r$ lie in a ball of radius $r+\lambda_1/2$. Polynomial growth of the count suffices. Restricting only to nonzero vectors would include proper multiples, which cannot be inserted as basis vectors by unimodular completion.

**Proposition 1 (first-pass law).** At a graph append, let $S$ be the revealed state including the physical retained lattice $L$, its marked subgroup $H$ and the inherited frame. For $u\in H$, let $W_u=(L,0)+\mathbb Z(\tilde u,1)$. Conditional on $S$, the mass of the oriented extension $(u,v)$ is
$$
 |H|^{-1}p_{W_u}(v),\qquad v\in(W_u)_{\rm pr}.
$$
With $Q_v$ the orthogonal projection away from $v$, the new lattice and subgroup are $Q_v W_u$ and $(Q_v)_*H$. The mass of a complete marked history multiplies these factors and the initial-state mass, using the prescribed append law at deterministic columns.

*Proof.* The unread column and new oracle coins are independent of the revealed data. The map from raw residues to $H$ is a surjective group homomorphism and has equal fibers. Conditional on its image the oracle has law $p_{W_u}$. Primitivity permits a basis completion, so projection gives the entire quotient and carries each old marked generator to its projected class. Iterated conditional probability gives the product. Each step sums to one. The finite sum over $u$ now contains a countably infinite sum over $v$ in rank at least two. Even on an initial cubic block the oracle can select a non-axis line, so initialization by the deterministic cubic *quotient* of the exact-SVP rule need not apply. [First-tour law](wall1_first_tour.md)

For example, at fixed $S$ and a mark $v$ primitive on every draw, write $\bar p=|H|^{-1}\sum_u p_{W_u}(v)$. The conditional density of $u$ given selection of $v$, relative to uniform on $H$, is exactly $p_{W_u}(v)/\bar p$, by Bayes' formula. Its mean is one. The bound $1/\bar p$ depends on the event one has conditioned on. The terminal distribution still requires summing over the histories that reach it. With a finite input design and discrete marks the possible finite histories form a countable set, by induction on their length. Thus at quotient rank at least two the induced shape law is singular to nonatomic Haar, even up to isometry. This leaves comparisons for particular observables open. [Chain law and audit](wall1_chain_law.md) · [Reducer variants, U1 and audit](wall1_reducer_variants.md)

**A one-step comparison that does hold.** Suppose the *whole input block* has unimodular Haar law $\mu_b$, $b\ge2$, and $\sigma$ is fixed in physical units. Let $Q$ be the probability on marked lattices proportional to $d\mu_b(W)\sum_{v\in W_{\rm pr}} w_W(v)\delta_v$. Let $P$ first draw $W$ from Haar, then use $p_W$. Then
$$
 \frac{dP}{dQ}(W,v)=\frac{\sigma^b}{\zeta(b) Z(W)}
 \le \frac{\sigma^b}{2\zeta(b)}\exp(\pi\gamma_b/\sigma^2),
$$
where $\gamma_b$ is the Hermite constant. Under $Q$ the determinant-normalized transverse shape is Haar, so this constant also dominates the one-step quotient law under $P$ relative to Haar.

*Proof.* Primitive Siegel integration gives $\int Z\,d\mu_b=\sigma^b/\zeta(b)$ by the Euclidean Gaussian integral. The two shortest signed marks contribute at least $2\exp(-\pi\gamma_b/\sigma^2)$ on any unimodular input. Dividing the joint measures proves the inequality. In primitive marked Haar disintegration, conditional on the marked ambient vector, the normalized quotient has Haar law. The extra factor under $Q$ depends only on that vector, and integration preserves the Haar marginal. With adaptive $\sigma(W)$ the weight can also depend on the reconstructed parent, and even for fixed $\sigma$ a subsequent sliding input need not be Haar. [Marked Haar calculation and audit](wall1_selection_law.md)

## 2. Two obstructions with proofs

**Proposition 2 (equal endpoints and equal energies).** For every $c>0$ there is an inherited width-two pass with $\sigma=c\lambda_1$ in which the Gaussian path probability is not a function of the initial and terminal retained data and the sum of normalized squared lengths.

*Proof.* Use orthonormal $e_1,e_2,e_3$. The first window is spanned integrally by $e_1,2e_2$, and the appended column is $e_3$. Compare the oriented selections $(e_1,2e_2)$ and $(2e_2,e_1)$. Both end at $\mathbb Ze_3$, freeze the same plane, and have sum of normalized squared lengths $5$, since both second windows have minimum one. Write $Z_r$ for the primitive normalizer of the rectangle with side lengths $1,2$ and $Z_s$ for that of the unit square. The two probabilities are respectively
$$
 e^{-5\pi/c^2}/Z_r^2,\qquad e^{-5\pi/c^2}/(Z_rZ_s).
$$
Indeed the intermediate windows are a rectangle and a square. Index their primitive vectors by coprime integer pairs $(i,j)$. Termwise $i^2+4j^2\ge i^2+j^2$, strictly for $(0,1)$, hence $Z_r<Z_s$. The result holds with trivial marks and deterministic appends. It rules out cancellation of the displayed path normalizers to a function of those endpoints. It does not exclude a comparison against another process with its own path-dependent likelihood.

**Proposition 3 (positive-temperature conditioning increases a quotient count).** Use the rank-four finite-mark example of Part 112. Append $(g,1)$ to $2\mathbb Z^3$ with three independent uniform bits $g=(a,b,d)$, and distinguish the common oriented mark $v=(-2,0,0,0)$. At the toy temperature $e^{-\pi/c^2}=2^{-12}$ with $\sigma=c\lambda_1(W_g)$,
$$
 3.5330 < \mathbb E[N\mid v\text{ selected}] < 3.5331,
 \qquad \mathbb E_g N=9/4 ,
$$
where $N$ counts nonzero pairs with squared norm below $7/2$ in $Q_v W_g$. Both expectations concern the same marked quotient observable.

*Proof and exact arithmetic certificate.* Write a window point as $(x,k)$ with $x\equiv kg\pmod2$. The squared minimum is $m_g=\min(4,1+a+b+d)$ by considering heights zero, one and at least two in absolute value. Projection deletes the first coordinate. At height one there are $2^{b+d}$ choices in the disk, at height minus one their negatives, and no other nonzero points inside the ball. Thus $N_g=2^{b+d}$. Its uniform mean is $(3/2)^2$. Define $p_g=p_{W_g}(v)$. Bayes gives $\sum_g N_gp_g/\sum_g p_g$. In particular the proof uses every Gaussian mark in the denominator, including ties. [Part 112 and audit](wall1_void_monotone.md)

The following finite sums specify a reproducible rational enclosure. Enumerate $(x,k)\in\{-4,\ldots,4\}^4$ with $n=\|x\|^2+k^2\le24$, retain the congruence and $\gcd(k,(x-kg)_1/2,(x-kg)_2/2,(x-kg)_3/2)=1$, and sum $2^{-12n/m_g}$ to obtain $A_g$. These exponents are integers. The omitted mass is at most $T=2\cdot51^4\,2^{-75}$, since shell $n\ge25$ contributes at most $(2n+1)^4 2^{-3n}$ and successive bounds have ratio less than $1/2$. Set
$$
 l_g=2^{-48/m_g}/(A_g+T),\qquad u_g=2^{-48/m_g}/A_g .
$$
Then $l_g\le p_g\le u_g$. In the scratch check, the floor of $10^4\sum N_gl_g/\sum u_g$ was $35330$ and the ceiling of $10^4\sum N_gu_g/\sum l_g$ was $35331$. The inequalities are strict because the omitted mass is positive and strictly below $T$. As $c\downarrow0$, selection of $v$ concentrates the posterior on $g=(1,1,1)$, the only window on which $v$ is shortest. The conditional mean tends to $4$. Thus the dependence persists in the regime of highly accurate local selections.

## 3. Local length, quotient quality and sampling cost

**Proposition 4 (shortest shell and cold limit).** On a fixed window with minimum $\lambda$, the primitive Gibbs law tends in total variation as $c\downarrow0$ to the uniform law on its oriented shortest vectors. On a fixed finite first pass with finite initial design and finite append choices, the full history law likewise tends in total variation to the pass that chooses uniformly among shortest ties.

*Proof.* Divide all weights by $e^{-\pi/c^2}$. Shortest marks have weight one; every other weight tends to zero. For $0<c\le c_0$ the resulting series is dominated by the rescaled Gaussian at $c_0$, which is summable by the packing argument above. Conditional on a shortest hit, the choice is already uniform on that shell. For the pass, couple the two processes up to their first disagreement using the same append and the same shortest choice whenever the Gaussian hits that shell. The exact-shortest tree of fixed depth is finite, so its largest per-node probability of missing the shortest shell tends to zero. A union bound over the depth proves convergence. This argument yields neither a rate uniform over all lattices nor convergence of unbounded witness multiplicities. It preserves a specified deterministic signed tie convention only where the induced updates agree.

For any fixed $c>0$ and rank at least two the oracle gives positive mass outside every finite near-shortest cutoff, since primitive coordinates $(j,1,0,\ldots)$ have unbounded length. Multiplicity also matters within the first few shells. On a cubic rank-$b$ window, the first two shells contain $2b$ and $4\binom b2$ primitive vectors, from one or two signed unit coordinates. Thus for $1\le a<\sqrt2$,
$$
 \Pr[\|v\|\le a\lambda_1]\le [1+(b-1)e^{-\pi/c^2}]^{-1}.
$$
At the recorded widths the coefficients are $405$ and $505$. Enumeration of the two shells in ranks two through five reproduced both counts exactly. This bound concerns a single cubic call. The Part 45 profile inequality assumes the near-shortest inequalities on the **returned basis**. Unconditional Gaussian insertion gives no such deterministic cap and a later update can change an earlier block. Even a verified profile would leave the terminal selection law to determine. [Part 45, profile hypothesis and audit](wall1_randomized_reducer.md)

Local support also permits arbitrarily poor normalized quotients. On $\mathbb Z^b$, $b\ge3$, select $(j,1,0,\ldots)$ of length $s=\sqrt{1+j^2}$. In its coordinate plane the perpendicular projection of $e_1$ has length $1/s$ and generates the projected plane lattice, since $Qe_2=-jQe_1$. All other unit directions remain orthogonal. The rank-$(b-1)$ quotient has determinant and minimum $1/s$, hence its minimum divided by its own Gaussian heuristic is $s^{-1+1/(b-1)}/G_{b-1}$, where $G_r$ is the inverse $r$th root of the unit-ball volume. This tends to zero. The example rules out a pathwise floor and gives no failure probability at the recorded terminal distribution.

The Gibbs oracle has the same input dimension as the replaced call. Runtime equivalence requires a separate argument. ADRS Theorem 3.7 samples the ordinary lattice Gaussian up to statistical distance, in a batch. Even given independent *exact* ordinary samples, rejection to primitive points has acceptance $Z(W)/\sum_{x\in W} w_W(x)$, by summing their masses. At fixed $W$ this tends to zero as $c\downarrow0$ since the ordinary mass includes the origin and the primitive mass tends to zero. An adaptive prescription also has to supply its scale. An exact-SVP cost or the batch sampling theorem alone supplies neither that conditional sampler cost at a recorded width nor a returned-basis quality guarantee. [ADRS, Theorem 3.7](https://arxiv.org/html/1412.7994v5) · [Part 140](wall1_adrs_explicit.md) · [Part 141](wall1_sampler_wordram.md)

## 4. Status of the terminal obligations

For a nonnegative marked observable $B(S,u,v)$, the exact final expectation is
$$
 \mathbb E_{S\sim\mu_{\rm Gibbs}}
 \left[\frac1{|H(S)|}\sum_{u\in H(S)}
 \frac{\sum_{v\in(W_u)_{\rm pr}} w_{W_u}(v)B(S,u,v)}{Z(W_u)}\right].
$$
This follows by Proposition 1 and Tonelli, including for multiplicities. It is an expectation of ratios under the selected history law. Averaging the numerator and denominator separately would instead weight parents by $Z(W_u)$.

| Recorded quantity | Dependence on exact selection |
|---|---|
| Horizontal charge | Exact SVP can select horizontally only at the old minimum. Gibbs can select any primitive old line, including one with a strictly shorter competitor. The uncovered-displacement test for the signed old winner therefore computes a different event. |
| Plane hits | For a primitive mark, planes through its line still correspond to lines in its quotient, by taking inverse images under projection. The quotient minimum can be arbitrarily small relative to the selected length even in a cube. The exact-SVP lower floor $\sqrt3\,\|v\|/2$ and its survivor tests do not follow. |
| Residual multiplicity $F_{\rm rem}$ | Part 152 uses $s=\|v\|\le t=\lambda_1(L)$ to truncate its cylinder, and Part 154 uses shortestness in every incident plane. A longer horizontal line or a longer nonhorizontal mark has positive Gibbs mass. Rounding a lift modulo $v$ still bounds its parallel component by $s/2$, but does not give the lost shortestness inequalities. |

For the plane correspondence, lines mean primitive rank-one sublattices and planes mean saturated rank-two sublattices in the parent. A basis completion identifies the lattice quotient by $\mathbb Zv$ with the projected lattice. The inverse image of a saturated line is saturated of rank two, and quotienting such a plane gives the inverse operation. This incidence identity alone sets no probability on the mark or its plane. [Plane count](wall1_plane_count.md) · [Cylinder average and audit](wall1_cylinder_average.md) · [Winner exchange](wall1_winner_exchange.md)

**Remaining gap.** At width 506, $0.954$ is the recorded relative-minimum target, and $h_{\rm long}+F_{\rm rem}\le0.0097738000$ is a stronger *sufficient condition for the audited exact-winner decomposition*. Its terms and their previously charged complements have not been certified for Gibbs insertion. In particular the per-preselected-line estimate in Part 152 does not sum itself over a history-dependent family of old lines, and the cold-limit result for bounded observables does not justify transferring that multiplicity estimate. The selector-uniform counterexample of Part 106 uses a freely changed presentation and hence does not decide this inherited-window process either. Specific terminal probability bounds and a cost-and-quality comparison at either recorded width remain open. No conjectural Gaussian approximation is used in these conclusions. [Chain law and audit](wall1_chain_law.md) · [Parts 147–154](../PROOF_GAP.md) · [Part 152 audit on the sufficient condition](wall1_cylinder_average.md)

## Audit

**Verdict — MINOR CAVEATS.** The four propositions and the numerical enclosure hold for the stated primitive Gibbs oracle on Part 108’s first pass. Proposition 1 needs one explicit scope qualification.

**Graph order.** Read “at a graph append” as applying after all horizontal $qI$ axes have entered, with independent uniform residue columns and no lookahead. The fresh coordinate then has perpendicular height one, and the projected horizontal residues give a homomorphism onto $H$. Its equal fibers give the factor $1/|H|$ for a history recording the displacement. Conditional on that displacement the oracle contributes $w_{W_u}(v)/Z(W_u)$. Projection carries the retained lattice and each marked generator to the claimed next state. Freshness alone does not fix the height in a reordered basis. For example, a first column $(a,1)$ before the horizontal axis has height $\sqrt{1+a^2}$. The one-step Haar calculation also checks out under its separate fixed-scale, Haar-parent hypothesis. [Part 108 and audit](wall1_first_tour.md) · [Part 105 and audit](wall1_selection_law.md)

**Equal endpoints.** Selecting $e_1$ first leaves $\mathbb Z(2e_2)$, while selecting $2e_2$ first leaves $\mathbb Ze_1$. Appending $e_3$ gives second windows with side lengths $(2,1)$ and $(1,1)$. Both have minimum one. Both histories freeze $\operatorname{span}(e_1,e_2)$, end at $\mathbb Ze_3$ and have normalized energy $1+4$. The ratio of the first path probability to the second is $Z_s/Z_r>1$ for every $c>0$, directly from the strict primitive-pair comparison. This establishes the claimed dependence on the intermediate window.

**Independent rank-four check.** Scratch enumeration used the basis coordinates $(i,j,h,k)$ with ambient vector $(2i+ka,2j+kb,2h+kd,k)$ and primitive test $\gcd(i,j,h,k)=1$. Through squared norm 24 each basis coefficient has absolute value at most four. The computation counted distinct projected vectors up to sign and summed each oriented primitive shell using exact fractions. For the stated tail majorant, the ratio of successive shell bounds is at most $(53/51)^4/8<1/2$. Substituting its rational tail bound into both sides of the posterior ratio gave
$$
3.5330362536244 < \mathbb E[N\mid v\ \mathrm{selected}] < 3.5330362536251 .
$$
The uniform displacement mean is $9/4$. Only $g=(1,1,1)$ admits $v$ as a shortest mark. That window has 24 oriented shortest marks and four quotient pairs inside the cutoff. Part 112’s signed lexicographic rule selects $v$ there with probability one, and a uniform-shortest rule selects it there with probability $1/24$. Both give conditional mean four. [Part 112 and audit](wall1_void_monotone.md)

**Cooling and terminal scope.** At each window the total variation distance to uniform shortest selection equals the mass outside the shortest shell. Summable Gaussian domination sends this mass to zero. The exact-shortest tree has finitely many nodes at fixed depth under the stated finite design. Coupling until the first miss bounds history total variation by the depth times the largest miss probability on that tree. Bounded terminal event probabilities therefore converge to their uniform-tie values. A numerical terminal guarantee at positive temperature still needs an estimate for the reference event and its error. Part 45 requires a returned-basis predicate. The exact-winner charges in Parts 144–155 use selection and history hypotheses beyond the plane correspondence of Part 120. In particular, transferring $F_{\rm rem}$ would require control of witness multiplicity on exceptional paths as well as accounting for the tie rule. The sufficient allowance $0.0097738000$ remains specific to the audited exact-winner decomposition. [Part 45](wall1_randomized_reducer.md) · [Part 120](wall1_plane_count.md) · [Part 152 audit](wall1_cylinder_average.md) · [Part 154 audit](wall1_winner_exchange.md) · [Part 155 audit](wall1_inherited_witness.md)
