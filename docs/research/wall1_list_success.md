# Terminal list membership and the random-translate hypothesis

There are three different success events. They are inclusion in a complete radius enumeration, inclusion among a prescribed number of shortest vectors, and recovery after lifting. The first two already give different answers at the level of a deterministic lattice. In particular there is no nontrivial smallest width for unrestricted radius-list *inclusion*. A radius covering the plant support gives inclusion with probability one at every width. The output size then has to be bounded separately.

## The first moment conditional on the prefix

Use embedding width $\beta$, horizontal dimension $d=\beta-1$, and condition on the design and independent reducer coins $D$. Write $Y=QX$, $v=(Y,1)$, $R^2=1+\|Y\|^2$, and $T=(H,0)+\mathbb Zv$. The conditional law of $X$ is product CBD. The law of $Y$ can depend on $D$. A basis determinant expanded along the height row gives $\det T=\det H=\det L_0/\det K$, where $K$ is the primitive prefix lattice. The last equality follows by factoring the Gram–Schmidt product at the cut. [Part 47](wall1_decoupled.md)

Let $n_H(a,s)=\#((H+a)\cap B_d(s))$ for the closed ball. The exact conditional expected number of **signed** nonzero competitors, counting boundary ties and excluding both plants, is
$$
\mathbb E_X\!\left[n_H(0,R)+2\sum_{k=1}^{\lfloor R\rfloor}
 n_H(kY,\sqrt{R^2-k^2})-3\mid D\right].
$$
This follows by partitioning by the integral height. The three removed points always occur. All sums are finite because the plant has finite support.

For a fixed $s$, Haar probability on the torus gives the mean $V_ds^d/\det H$ by integrating the sum of translated indicators over one fundamental domain and tiling the horizontal space. Independence of the input plant from the prefix gives no such integral. For example, take $Q=1$, $H=7\mathbb Z$, $X$ a single CBD(3) variable, $k=1$, and $s=1/4$. The expected translated count is $\Pr(X=0)=20/64$, whereas the volume ratio is $1/14$. This discrepancy persists with the actual plant-dependent slice radius. At height one the interval radius is $|X|$ and the slice always has exactly one point since $2|X|<7$. The proposed averaged volume is at most $6/7$. Subtracting the guaranteed plant from each side cannot restore equality. Even marginally Haar shifts would require care if one conditioned on the radius computed from the same shift. Multiplication by an integer also need not preserve uniform measure on a finite quotient.

## Upper bounds and Markov's inequality

For $d\ge1$ let $a$ be a certified positive lower bound on $\lambda_1(H)$. Around the points of any translated slice put disjoint open balls of radius $a/2$. Volume comparison gives $n_H(t,s)\le(1+2s/a)^d$. If $2s<a$ the sharper bound is one, regardless of the translate. At height zero there are no competitors for $s<a$. Both refinements matter because translating an entire slice costs no factor growing with its height. These inequalities inserted in the displayed finite expectation give a rigorous upper bound without a mixing assumption. In particular, if $2R<a$, every occupied slice contains at most one point and the signed count is at most $2\lfloor R\rfloor-2$. This linear-in-radius estimate allows high-height competitors. The uniqueness criterion of Part 58 instead excludes every such competitor. [Part 58](wall1_height_union_fix.md)

A determinant bound alone does not bound the horizontal count in dimension at least two. For example $H=\epsilon\mathbb Z\oplus (D_0/\epsilon)\mathbb Z$ has determinant $D_0$ and at least $2\lfloor R/\epsilon\rfloor$ nonzero points in the ball. This example concerns the proposed determinant implication, not the distribution of graph lattices. Deterministic prefix-volume caps apply through the determinant identity above. The numerical chain probabilities in Part 82 use Haar measure. Part 54 gives an exact finite-design weight for prescribed complete bases. A sum over admissible prefixes or completions would need an upper bound on its **count-weighted** mass, including height-zero points. The fixed-basis membership weight alone does not evaluate that sum. [Part 54](wall1_qary_basis_count.md) · [Part 82](wall1_small_d_caps.md)

Write $C$ for the signed competitor count. If an exact list of $L\ge1$ shortest nonzero signed vectors misses both signs, its $L$ outputs are competitors. Thus $\Pr(\mathrm{miss})\le\mathbb E C/L$, including adversarial tie breaking. The threshold is *at least* $L$. For a list of $L$ unoriented pairs the numerator becomes $\mathbb E C/2$. For any good event $G$, the sharper truncated bound is $\Pr(G^c)+\mathbb E[C\mathbf1_G]/L$. In particular a norm quantile or a minimum certificate used on $G$ spends part of the same failure budget. Radius enumeration instead has miss probability $\Pr(R>R_{\rm list})$ for a closed cutoff, irrespective of the competitor count.

## Interpretation of width and cost

At $\beta=1$ the entire horizontal space is removed. The projected lattice is the height line and the plant is its unit, so even the shortest-list inclusion failure belongs to the exact interval $[0,0]$. The lift then carries the whole recovery problem. More generally the Part 47 prefix Babai error bound must be added to the list miss probability, or bounded jointly. Lifting every height-one candidate guarantees presence of the correct lift on the Babai good event. Identifying it among multiple compatible outputs is another condition if a single recovered vector is required. [Part 47, audit note](wall1_decoupled.md)

Writing $L$ distinct outputs costs at least $\Omega(L)$ vector emissions. A saturated two-sieve list of nominal size $(4/3)^{\beta/2}$ carries no completeness guarantee for a ball or for the first $L$ order statistics. Accordingly the heuristic $2^{0.2925\beta+o(\beta)}$ work estimate supplies no certified running time for the oracle used in the Markov argument. Exact enumeration supplies completeness when finished, with a search-tree cost in addition to the output cost.

For the full shape the horizontal rank is 1023 and the empty-prefix embedding width is 1024. The repository reports failure below $2^{-1900}$ there. For fixed deletion of 377 sample coordinates the inherited width is **647**, with failure in $[0,0.0048336]$ by Part 39. The retained secret coordinates are intact. These bounds transfer to an exact shortest list containing at least one signed vector because the plant is uniquely shortest up to sign on the certified event. Part 39 establishes minimality only for its own uniqueness certificate. Its design average for fixed coordinate deletion is valid and is distinct from a uniform translate assumption for a reducer-selected suffix. The difference between the inherited punctured certificate and the estimator width 406 is exactly **241**. This is a gap between benchmarks. The optimal list-and-lift width is undetermined by the translate argument. [Part 39](wall1_projected_reference.md) · [Part 47](wall1_decoupled.md)

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT WITH MINOR ISSUES. The signed competitor count, the packing refinement and the Markov bounds
were all verified.

**Operational correction.** A signed list can contain only −v. Before lifting, orient every output of absolute height one to
positive height. Otherwise a singleton list {−v} passes the inclusion test and sends no candidate to Babai.
