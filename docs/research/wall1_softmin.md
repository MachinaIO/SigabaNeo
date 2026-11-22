# A theta-ratio majorant for the selected shortest line

For each window, two Gaussian sums give an upper bound on the signed shortest-line indicator. The infimum over inverse temperatures is reached in the cold limit and counts the shortest shell, including ties. The obstruction occurs on averaging over marks. Pooling the numerator and denominator gives a different mark law. At width 506 the pooled expression tends to **zero** for the entire upper band, solely because the zero mark contributes a unit vector to its denominator. In an exact two-mark example the pooled expression is below 0.118 for an event of probability 1/2. The valid expression retains the average of the individual ratios. Its history average at width 506 remains unknown.

## The event at draw 406

Condition on the physical state $S$ after 405 suffix appends of the marginal restart for plain LWE $(511,512,3329)$, CBD(3). Let $d=505$, $b=506$, $q=3329$, $M$ be the retained lattice, $D=\det M$, $K$ the inverse image of the mark group, and $H=K/M$. The next mark $u$ is uniform in $H$, a quotient of $\mathbb F_q^{400}$. In the inherited ordered frame the window is $W_u=(M,0)+\mathbb Z(\tilde u,1)$. Its determinant is $D$ by its unit append height. The plant and draw 407 are absent from this law. [First-tour law and audit](wall1_first_tour.md) · [Finite chain, Propositions 1 and 5](wall1_finite_chain.md)

Write $V_j$ for unit ball volume and $g=(D/V_b)^{1/b}$. On $32.18553<g<203.888$, let $A_u$ be the following finite set of primitive sign pairs. A candidate $v$ has positive absolute fresh height and length $s$ in $(0.990g,1.097193g]$. Force projection off $v$, take the signed designated shortest pair $x$ in that quotient, and put $l=\|x\|$, $h=(D/(sV_d))^{1/d}$, $\gamma=477/500$. Require $1<l\le\sqrt{1+\gamma^2h^2}$ and a nonzero vector of length strictly below $\gamma h l^{-1/d}$ after projecting off $x$. Set $A_u=\varnothing$ outside the stated $g$ range. Also set $A_0=\varnothing$: at the zero mark the window contains a unit vertical vector, so its minimum cannot reach the band. One passing candidate counts once regardless of how many witnesses it has. The event of mass $P$ is that the designated first pair belongs to $A_u$. The inherited event of mass $p_a$ has a horizontal first winner and its own gates. [Selected-hit identity and audit](wall1_selected_hit_direct.md) · [Budget and audit](wall1_band_plane_hits.md)

## A pointwise upper bound and its optimal temperature

For a window $W$, sum over all nonzero vector pairs $v\sim-v$, including proper multiples. Put
$$
 w_t(v)=e^{-\pi t\|v\|^2},\qquad
 Z_t(W)=\sum_{\{\pm v\}}w_t(v)=\tfrac12(\Theta_t(W)-1),\qquad
 \Theta_t(W)=\sum_{v\in W}e^{-\pi t\|v\|^2}.
$$
Here $t>0$ is inverse temperature. Including multiples permits ordinary Poisson summation. The candidate set stays primitive. Let $m=\lambda_1(W)^2$, $w_*=e^{-\pi tm}$, and let $n$ count shortest pairs.

**Proposition 1.** The least scalar multiplying $w_t(v)/Z_t$ that majorizes the designated-pair indicator at every $v$ is $Z_t/w_*$. It is $n$ plus the positive tail $\sum_{\|v\|^2>m} e^{-\pi t(\|v\|^2-m)}$. A correction computable without $m$ is $Z_t^2/Z_{2t}$. In particular, writing $J_W$ for signed designation,
$$
 J_W(v)\le {\bf1}_{\|v\|^2=m}\le B_t(W,v),\qquad
 B_t(W,v)=w_t(v)\frac{Z_t(W)}{Z_{2t}(W)}.                         \tag{1}
$$

*Proof.* At the designated pair the required scalar is at least $Z_t/w_*$, and that scalar suffices since its product with the Gibbs mass is one there and nonnegative elsewhere. Each term of $Z_{2t}$ is $w_t(v)^2\le w_*w_t(v)$. Sum and divide by the positive normalizers to get (1). The sums converge since disjoint balls of radius $\lambda_1/2$ give polynomial growth of the number of lattice points in balls. Thus multiplying the Gibbs mass by the shortest multiplicity alone falls short at every finite $t$. The initial expression $e^{\pi t(\|v\|^2-m)}$ is at least one even for every losing candidate. The sharp corrected weight has the opposite sign in its exponent. [Primitive Gibbs law and its cold limit](wall1_gibbs_selection.md)

**Proposition 2.** Define the capped upper bound
$$
 F(t)=\mathbb E_S\frac1{|H|}\sum_{u\in H}
       \min\left\{1,\frac{Z_t(W_u)}{Z_{2t}(W_u)}
                                  \sum_{v\in A_u}w_t(v)\right\}.
$$
Then $P\le F(t)$ for every $t$, and
$$
 \inf_{t>0}F(t)=\lim_{t\to\infty}F(t)
 =\Pr\{A_u\text{ contains at least one shortest pair of }W_u\}.       \tag{2}
$$
One may delete from $A_u$ every candidate with an equal-length pair of smaller signed ambient key, checking ties against the **whole window**. With this deletion the infimum equals $P$.

*Proof.* Equation (1) bounds each shortest pair separately, so the capped sum dominates the indicator on the right of (2) for every $t$. Divide $Z_t$ by $e^{-\pi tm}$ and $Z_{2t}$ by $e^{-2\pi tm}$. Both scaled sums tend to $n$ by dominated convergence, using the scaled sum at any fixed positive inverse temperature for domination. Hence $B_t(W,v)$ tends to one on each shortest pair and zero on each longer pair. Each $A_u$ is finite. The cap bounds the integrand by one, so the limit commutes with the mark and history averages. The pointwise lower bound by the limiting indicator proves the infimum claim without assuming monotonicity. The tie deletion retains precisely the designated member of a shortest shell whenever that member passes the gates. This proves the last assertion. The audited order-17 toy in Part 164 has 24 gated candidates with empty *open* shorter ball and only two signed winners across 4,913 designs. Those are candidate counts before capping. [Part 164 exact counts and audit](wall1_selected_hit_direct.md)

Thus $t\to\infty$ is optimal for this family in the infimum sense. With exact tie filtering it gives back the original unknown. The alternative penalty $\exp(-\pi t N_{<}(v))$, where $N_{<}$ counts all pairs of smaller signed key, also converges to $J_W(v)$ from above. Indeed $N_{<}$ is zero precisely on the designated pair and at least one otherwise. Its exponent requires a ball count with a boundary tie test on each mark.

## What Poisson summation computes

**Proposition 3.** With $k$ the signed append height and $\xi$ in the dual of $M$,
$$
 \mathbb E_u\Theta_t(W_u)=
 \frac{t^{-d/2}}{D}\sum_{k\in\mathbb Z}e^{-\pi tk^2}
 \sum_{\substack{\xi\in M^*\\ k\xi\in K^*}}e^{-\pi\|\xi\|^2/t}.    \tag{3}
$$
For $q\nmid k$ the surviving inner lattice is $K^*$, while for $q\mid k$ it is $M^*$.

*Proof.* The height-$k$ layer is $M+k\tilde u$. The Gaussian Fourier transform on the old space is $t^{-d/2}e^{-\pi\|\xi\|^2/t}$. Applying lattice Poisson summation to that layer gives the inner sum over $M^*$ with phase $e^{2\pi i k\langle\xi,\tilde u\rangle}$. Its mean over $H$ is one for a trivial character and zero otherwise. Triviality means $k\xi\in K^*$. All sums converge absolutely, and each restricted character has order dividing the prime $q$. This proves both assertions, including the horizontal and all $q$-divisible layers. [Gaussian Poisson summation](https://cseweb.ucsd.edu/classes/wi24/cse206A-a/LecGaussian.pdf) · [Part 142, Theorems A–C and audit](wall1_dual_cusp.md)

Equation (3) evaluates each **linear** mean normalizer. Before the cap in $F(t)$ the required mean is $\mathbb E_u[N(u)/T(u)]$ for $N(u)=Z_t(W_u)\sum_{v\in A_u}w_t(v)$ and $T(u)=Z_{2t}(W_u)$. The pooled ratio $\mathbb E N/\mathbb E T$ averages $N/T$ with mark probabilities $T(u)/\sum_a T(a)$. This follows by multiplying out the weighted sum. Furthermore, $N$ contains the forced quotient tests. On the upper band, orienting a candidate $(y,k)$ upwards gives $0<k<224<q$, so $u=k^{-1}[y]$ is already fixed by incidence. The same mark determines the quotient gates and the denominator. Part 152 keeps an analogous acceptance factor inside its fiber sum, for a different statistic at draw 407. [Part 164](wall1_selected_hit_direct.md) · [Cylinder average, Proposition 1 and audit](wall1_cylinder_average.md)

**Width-506 consequence for pooling.** At any fixed gated history the pooled ratio tends to zero. For $t\ge1$, its numerator is bounded by $C(S)e^{-\pi t(0.990g)^2}$ with $C(S)=\mathbb E_u[Z_1(W_u)|A_u|]<\infty$. Its denominator is at least $e^{-2\pi t}/|H|$ from the pair $(0,\pm1)$ at $u=0$. Thus the pooled ratio is at most
$$
 |H|C(S)e^{-\pi t((0.990g)^2-2)},\qquad (0.990g)^2-2>1013.29376 .
$$
On other histories the numerator vanishes. There are finitely many raw prefixes, so the pooled ratio also tends to zero on averaging these statewise expressions. The proof used no information about which gated candidate wins. The following example shows that treating this decay as an upper bound can underestimate a positive selected probability.

## Exact two-mark check

Take $M=2\mathbb Z$, $K=\mathbb Z$, $u\in\{0,1\}$, and $W_u=\{(x,k)\in\mathbb Z^2:x\equiv uk\pmod 2\}$. Use a single test pair $v=\pm(1,1)$ wherever present. Enumeration through squared norm four gives the following counts of sign pairs.

| Mark | Squared norm 1 | Squared norm 2 | Squared norm 4 | Signed winner |
|---:|---:|---:|---:|---|
| 0 | 1 | 0 | 2 | $(0,-1)$ |
| 1 | 0 | 2 | 2 | $(-1,-1)$ |

Every candidate for the minimum lies in this enumeration since both windows contain $(2,0)$. The true selected probability is $1/2$. Set $e^{-\pi t}=1/4$ exactly. With $Z_t(i)=Z_t(W_i)$ the uncapped mean of (1) and its pooled substitute satisfy
$$
 0.52931964 < \frac{Z_t(1)}{32Z_{2t}(1)} < 0.52931965,\qquad
 0.11798045 < \frac{Z_t(1)}{16[Z_{2t}(0)+Z_{2t}(1)]} < 0.11798046.
$$
The markwise cap makes the first bound exactly $1/2$. The second fails even before capping. Both dual minima are at least $1/2$, as each window contains $2\mathbb Z^2$ and hence has dual contained in $\tfrac12\mathbb Z^2$.

For the numerical certificate, enumerate the lex-negative sign representatives with $\max(|x|,|k|)\le6$ and sum $B^{-(x^2+k^2)}$ as rationals for $B=4,16$. The omitted mass is bounded by $16\cdot7 B^{-49}$ since the square shell of radius $r$ contains $8r$ points, each of squared length at least $r^2$, and successive shell bounds have ratio below $1/2$ for $r\ge7$. Dividing the resulting positive intervals with outward rounding at 80 decimal digits gives both displayed enclosures. The same scratch check enclosed the width-506 exponent at the lower endpoint $g=32.18553$ in $(1013.29376538,1013.29376539)$.

## Width-506 bound and remaining conjecture

A lower bound on $\lambda_1(M^*)$ applies to the appended dual through
$$
 W_u^*=\{(\xi,j-\langle\xi,\tilde u\rangle):\xi\in M^*,\ j\in\mathbb Z\}.
$$
This follows by pairing with both types of generators. It gives $\lambda_1(W_u^*)\ge\min(1,\lambda_1(M^*))$ for all marks. Part 142 Theorem C gives a probabilistic floor for the retained dual, with an all-times exit bound $10^{-3}$ and a fixed-time raw bound $10^{-3}/408$ at its specified radius. Even within that floor the theta sum depends on the shell counts and on $u$. As $t\to\infty$, each fixed nonzero dual weight $e^{-\pi\|\xi\|^2/t}$ tends to one. Removing a neighborhood of zero does not make the other modes negligible in this limit. The exact two-mark inequality shows the pooling issue persists with a common positive dual floor. [AppendDual.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/AppendDual.lean) · [Theorem C and audit](wall1_dual_cusp.md)

There is a precise loss in using only the zero dual frequency for a common denominator. Full-window Poisson summation gives $Z_{2t}(W_u)=[(2t)^{-b/2}\Theta_{1/(2t)}(W_u^*)/D-1]/2$. Keeping only the zero frequency gives the lower bound $[(2t)^{-b/2}/D-1]/2$. This is a positive denominator only for $t<1/(2D^{2/b})$. Substituting $D=V_{506}g^{506}$, $V_{506}=\pi^{253}/253!$, gives threshold enclosures $(0.01450948,0.01450949)$ at $g=32.18553$ and $(0.00036156,0.00036157)$ at $g=203.888$ by outward interval arithmetic. This particular relaxation loses its positive denominator before the cold limit. Estimating the remaining dual mass inside the gated mark average is a separate problem.

A numerical bound that follows unconditionally here is $P\le F(t)\le1-3329^{-400}$ for every $t>0$. Indeed $|H|\le3329^{400}$, the integrand vanishes at $u=0$, and each other mark contributes at most one. Outward intervals give $-1408.92552<\log_{10}(3329^{-400})<-1408.92551$. This upper bound is between **5057.94687 and 5057.94688 times** the full shared allowance. It is an evaluation of the probability cap with the zero-mark exclusion. The sharper expression $F(t)$ has no small numerical certificate here. If one drops both quotient gates, primitivity and selection and simply counts all positive-height candidates in the band, Part 161 already proves a conditional mean above 74.85561 on the interior shell alone. This last number concerns that specific relaxation. [Part 161, Proposition 3 and audit](wall1_band_plane_hits.md)

The rank-506 Haar calculation supplies the **upper bound** $4.36018\cdot10^{-11}$ on the joint selected event under Haar input. The full allowance divided by this upper bound is in $(4{,}534{,}415,4{,}534{,}416)$, before reserving anything for $p_a$. Both budget ratios above use outward interval arithmetic with the stated decimal inputs. Part 105 starts with a Haar input, and Parts 162–164 give the Haar benchmark and the conditioning obstruction for the restart. [Part 105 and audit](wall1_selection_law.md) · [Haar comparison and audit](wall1_restart_haar_ratio.md) · [Part 164 numerical certificate](wall1_selected_hit_direct.md)

**Remaining conjecture.** For the specified marginal restart, $P+p_a\le0.00019770868$. For $P$, the missing estimate is the history average of the markwise gated expression in Proposition 2, or its signed cold limit. The theta identities compute the unfiltered normalizers. They supply neither the needed correlation with the gates nor a bound on the separate inherited event $p_a$.

## Audit

**Verdict — MINOR CAVEATS.** The majorant, its signed cold limit, the pooling counterexample and the width-506 probability cap hold. In the opening paragraph, replace “solely because the zero mark contributes a unit vector to its denominator” with “the zero mark’s unit vector alone suffices to prove this decay.” The estimate never removes the zero mark and recomputes the ratio, so it establishes sufficiency only.

**Pointwise bound and ties.** Writing $w_*=e^{-\pi t\lambda_1(W)^2}$ gives $Z_{2t}\le w_*Z_t$. Thus every shortest pair contributes at least one to the uncapped majorant for every $t>0$. The scaled sums $Z_t/w_*$ and $Z_{2t}/w_*^2$ both converge to the number of shortest sign pairs by Gaussian domination. Each longer pair’s contribution tends to zero. Consequently the capped sum dominates its limiting indicator at every temperature, which proves the infimum claim even if a finite temperature also attains it. Testing equal-length ties against all pairs of the window leaves exactly the designated shortest pair eligible on that shell. Bounded convergence then gives $P$ under the original history and mark law. Part 156’s uniform-tie Gibbs limit concerns a different selection rule. [Part 156 audit](wall1_gibbs_selection.md) · [Part 169 audit](wall1_finite_chain.md)

**Independent two-mark calculation.** A scratch script enumerated sign pairs by integer squared norm $n\le64$. For $B=4,16$, the discarded Gaussian mass is at most $18\cdot65 B^{-65}$ since the number of pairs at norm squared $n$ is at most $(2\sqrt n+1)^2\le9n$, and successive bounds $9nB^{-n}$ decrease by a factor below $1/2$ for $n\ge65$. The signed winners were $(0,-1)$ and $(-1,-1)$, giving selected probability $1/2$. Exact rational interval division enclosed the uncapped markwise mean in $(0.52931964,0.52931965)$ and the pooled ratio in $(0.11798045,0.11798046)$. Only mark one contributes to the numerator, so the markwise cap gives exactly $1/2$. Pooling instead weights each ratio by $Z_{2t}(W_u)/\sum_a Z_{2t}(W_a)$.

**Width 506 and Haar.** The numerator’s band cutoff and the denominator term $e^{-2\pi t}/|H|$ give exponential decay even without any winner information. At the lower endpoint the exponent gap $(0.990\cdot32.18553)^2-2$ is exactly $1013.29376538742009$. Under the uniform mark law, $A_0=\varnothing$ instead gives the statewise cap $1-1/|H|\le1-3329^{-400}$. Averaging certifies this upper bound for $P$. Character orthogonality in (3) computes a mean theta sum. It gives no comparison of gated mark fractions with their determinant-matched Haar probabilities. The bound $4.36018\cdot10^{-11}$ therefore remains specific to Haar input, and the shared restart target $P+p_a\le0.00019770868$ remains open. [Part 163 audit](wall1_restart_haar_ratio.md) · [Part 164 audit](wall1_selected_hit_direct.md)
