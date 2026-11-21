# The one-pass shortest-in-block chain on Haar lattices

At rank 1023 the proposed rule specifies a family of laws. For each of the four widths the **infimum of the terminal 1% quantile over basis selectors is exactly zero**. Every fixed terminating selector has a strictly positive quantile. The obstruction already occurs at the penultimate call, even if the entire earlier algorithm is fixed. A fresh-basis implementation has an exact Markov kernel on projected lattices. Its transition on lengths requires a posterior distribution on those lattices.

## Exact marked transition

Use zero-based indices, physical covolume $D_d$ at remaining rank $d$, and determinant-one state $H=D_d^{-1/d}L_d$. Start with $D_N=1$ and Haar $H$. Fix measurable transverse frames for projections. One concrete selector takes a Borel basis section $B(H)$ (for example, minimize squared Frobenius norm over all bases and break ties lexicographically in the frame), draws a uniform column permutation, and uses its first $b=\min(d,\beta)$ columns. The minimum defining the section exists by local finiteness. This defines an integral even if finding this particular section is expensive. More generally use a supplied basis, keep it in the state, and use fresh independent permutations after each primitive completion and projection. These two conventions can give different laws.

For the section convention let $p_H(U)$ be the mass of a primitive rank-$b$ block. For permutations it is $1/\binom db$ on the coordinate blocks. Write $q_H(v)$ for the resulting probability of selecting the oriented primitive vector $v$, obtained by summing $p_H(U)$ times the shortest-vector tie and sign probabilities in $U$. Take uniform shortest vectors including signs. Let $r=|v|$, $P_v$ be orthogonal projection onto $v^\perp$, and $T_v H=r^{1/(d-1)}P_vH$. For $d>1$ the marked transition is

$$
 K_d((D,H),\cdot)=\sum_v q_H(v)\,
 \delta_{(D^{1/d}r,\ D^{1-1/d}/r,\ T_vH)}.
$$

The entries are the emitted GS length, next determinant and next normalized lattice. Primitivity gives a basis completion, hence the projected covolume identity and the normalization of $T_vH$. This also proves that lifting choices cannot change the emitted length. At rank one emit $D$. Integrating the product of these kernels from the initial Haar law gives the exact joint law, with zero approximation error. On observing lengths alone, integrate each kernel against the conditional law of $H$ given previous lengths and update by disintegration. The determinant is known from their product. For example lattices with bases $(1,0),(t,1)$ at $t=0,1/2$ have identical GS diagonals but different shortest-vector lengths after choosing the second column as a rank-one block. These bases can be used as supplied presentations. This rules out a general transition depending only on the GS diagonal for presented states.

There is also an integral formula for the hidden-shape update. If the parent law has Haar density $f$ in fixed coordinates, use the primitive incidence fiber $E(v,J,t)$ of Part 46, with $J$ the normalized rank-$(d-1)$ quotient and $t$ its lift character. The joint density of $v,J$ with respect to $dv\,d\mu_{d-1}(J)$ is

$$
 A_v(J)/\zeta(d),\qquad A_v(J)=\int f(E)q_E(v)\,dt .
$$

Indeed weighting each marked incidence by its selection probability sums to one per parent before multiplying by $f$. At positive marginal density put $a_v=\int A_v\,d\mu$. The exact one-step TV error from replacing the conditional quotient by Haar is $\int|A_v/a_v-1|\,d\mu/2$. For length-only observations average the joint density over directions before normalizing. These formulas recursively propagate the posterior, including directional dependence if frames are used. For a Haar full-width parent $A_v=w_r/2$ and the Part 46 bound is $\min(1,V_d r^d/2)$ for $d\ge3$. More generally, a hybrid replacement with one-step errors $e_i(h)$ on the joint emitted value and next state has path error at most $\min(1,\sum_i\mathbb E_{\rm comparison} e_i(h))$ when each comparison prefix supplies the conditioning history $h$ and the remaining kernels agree. This follows by telescoping prefix replacements and TV contraction. No error smaller than one follows merely from drawing new basis coins. Conditional on a fixed parent, even the normalized block shape is countably supported and has TV distance one from continuous Haar shape for $b\ge2$.

## Why the shortest-vector estimate does not close the recursion

The integer basis group acts transitively on an infinite countable set of primitive proper blocks. An invariant probability would give them equal singleton masses, which cannot sum to one. Finite symmetric sets define valid walks once the starting basis and the set are fixed. Symmetry under inversion does not give an invariant probability on blocks. An unconditional Haar block marginal is a different requirement, and would still leave its physical covolume and its dependence on the exterior lattice to determine.

In particular the rank-$(b-1)$ shortest-vector quotient inside $U$ is only a sublattice of the rank-$(d-1)$ next state. Under bounded-covolume split incidence the block and exterior normalized shapes are Haar, but the ordinary parent is size-biased by the eligible-block count. Part 51 gives the exact parent-and-mark replacement cost $\mathbb E|1-C/\mathbb EC|/2$ for uniform eligible selection with failure. Its recursive split discards the whole block. Keeping one vector retains the other $b-1$ directions and their gluing to the exterior. Even for full width Part 46 gives a product of acceptance tests inside one integral. At the median Haar minimum the bound $V_b r^b/2$ is at least $\zeta(b)/2$ by the primitive first moment. It cannot certify a percent-level approximation there. [Part 46](wall1_haar_prefix_law.md) and [Part 51](wall1_random_block_reducer.md)

## A terminal counterexample at all four widths

**Theorem.** Fix any earlier prefix algorithm down to physical rank $b+1$, with $b=\beta<N$. For every $c>0$ there is a fresh randomized basis selector there for which $\Pr(g_{N-b}<c)$ is arbitrarily close to one. This holds for every input probability law on nonsingular presented lattices.

**Proof.** Let $B$ be the physical basis at that stage. In integer coordinates choose columns $u_j=k e_j+e_{j+1}$ for $1\le j\le b$, with a fresh integer $k$ uniform on $\{K,\ldots,2K\}$, $K\ge2$. Append $e_1$. Expansion along that column gives determinant $\pm1$. Random permutations and signs within the first block preserve it. For $z\in\mathbb Z^b$ the reverse triangle inequality gives
$\|\sum z_j u_j\|\ge(k-1)\|z\|$.
Thus the chosen physical minimum $a$ exceeds or equals $(K-1)\sigma_{\min}(B)$. The next call has full width and determinant $|\det B|/a$. Minkowski gives the pointwise bound

$$
 0<g_{N-b}\le 2 V_b^{-1/b}
 \left(\frac{|\det B|}{(K-1)\sigma_{\min}(B)}\right)^{1/b}.
$$

The distribution of $B$ is independent of $K$ because the earlier algorithm is fixed. Dominated convergence applied to the indicator that the right side is at least $c$ proves the claim. For a fixed selector, continuity of probability at zero gives $Q_{.01}>0$, where $Q_p=\inf\{x:F(x)\ge p\}$. Taking $c$ arbitrarily small proves the asserted infimum. Equivalently the log quantiles have infimum $-\infty$. This example concerns the unrestricted fresh-basis proposal; it does not refute concentration for a particular well-chosen walk. The same bidiagonal construction in the first $b+1$ coordinates at the initial call on $\mathbb Z^N$ gives first-vector approximation ratio at least $K-1$. Thus no dimension-only BKZ first-vector guarantee holds across these selectors. Re-randomizing the suffix can change the earlier tested window in the final basis.

The quantile obstruction also holds for an explicitly **inverse-symmetric** finite set independent of the parent. Write $M_k$ for the displayed completion, changing the sign of its last column if needed for determinant one. Draw uniformly from the matrices $M_k,M_k^{-1}$ for $K\le k\le2K$. These are distinct for $b\ge2$: $M_k$ has first column $k e_1+e_2$, whereas $M_k^{-1}$ has first column $\pm e_{b+1}$, and inversion is injective. With probability one half the forward construction applies. Hence for any $c>0$ the liminf of the probability of a terminal value below $c$ is at least one half, already enough to force the 1% quantile to zero in the limit. In contrast, every fixed finite-set selector has positive 1% quantile. This uses precisely the finite symmetric set option in the proposal.

## Numerical quantiles and their scope

For comparison one quantity admits tight enclosures. For a **fresh unit-covolume Haar** rank-$b$ minimum $S_b$, let $h=V_b x^b/(2\zeta(b))$. The primitive pair count has mean and variance $h$ by Siegel and Rogers, hence $h/(1+h)\le\Pr(S_b\le x)\le h$ by Cauchy–Schwarz and Markov. Inverting at $h=1/100,1/99$ gives the following outward enclosures. The last column is an exact infimum for the physical terminal quantile, in determinant-one input units.

| $b$ | Terminal index | $Q_{.01}(S_b)$ | $\inf_{\rm selectors} Q_{.01}(g_{1023-b})$ |
|---:|---:|---:|---:|
|406|617|[4.87154, 4.87167]|0|
|506|517|[5.44056, 5.44068]|0|
|647|376|[6.15383, 6.15394]|0|
|800|223|[6.84399, 6.84408]|0|

To reproduce the interval computation use 50-decimal-place interval arithmetic, $V_b=\pi^{b/2}/\Gamma(1+b/2)$ and bound $1\le\zeta(b)\le 1+2^{-b}(1+2/(b-1))$ by the integral test. Evaluate $(2h\zeta(b)/V_b)^{1/b}$ with the lower endpoints at $h=1/100$ and the upper endpoints at $h=1/99$. No Gaussian or Poisson approximation enters the table.

Indeed writing $s_d=g_{N-d}/D_d^{1/d}$, the exact terminal log length is
$$
 \log g_{N-b}=\log s_b-\sum_{d=b+1}^N\frac{\log s_d}{d-1}.
$$
This follows by telescoping the determinant update. A concentration theorem needs the accumulated conditional drift and fluctuations in this sum as well as the final normalized minimum. Assuming independent Haar minima would also replace the unknown physical block scales at proper widths. The table supplies no quantile for the permutation implementation. Part 47's index after deleting $1024-b$ horizontal directions has remaining rank $b-1$, one step later than the index requested here. The all-reduced-bases bounds through Part 83 require final reducedness conditions. [Part 47](wall1_decoupled.md) and [frontier](../PROOF_GAP.md)

## Work bound

Through the terminal observation the implementation needs $N-b+1$ exact SVPs of rank $b$ if it discards the rest of each HKZ basis. Computing those bases literally takes at most $b$ projected SVPs per call. A supplied-basis permutation and the bidiagonal change use polynomially many arithmetic operations apart from primitive completion and projection, which use integer basis operations and linear algebra. As for one BKZ tour, the oracle dimension is bounded by $b$. With polynomial-cost presentation updates and polynomial-size finite input and intermediate encodings, single-exponential SVP gives $2^{O(b)}\operatorname{poly}(N,\text{encoding length})$ work. Exact Haar real inputs require an arithmetic/oracle model or a precision analysis for bit complexity. The count does not pay for computing a shortest-basis section or sampling an incidence block. The bounded oracle budget alone yields neither final BKZ reducedness nor a quantile for an efficiently chosen selector. [Micciancio and Voulgaris](https://cseweb.ucsd.edu/~pvoulgar/files/voronoi.pdf)

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT.

* **Penultimate construction.** It works pointwise, and bounded convergence handles any earlier-prefix law. This means the
  infimum of the terminal 1% quantile over unrestricted fresh-basis selectors is zero, and the zero comes from the freedom to
  choose the penultimate basis.
* **Fixed selectors.** Every fixed terminating selector has a positive quantile.
* **Outward enclosures.** These were computed independently with 65-digit interval arithmetic:

  | b | fresh-Haar Q_.01(S_b) |
  |---:|---|
  | 406 | [4.87154, 4.87167] |
  | 506 | [5.44056, 5.44068] |
  | 647 | [6.15383, 6.15393] |
  | 800 | [6.84399, 6.84408] |

* **Still open.** The quantile of the concrete section-plus-permutation rule is not evaluated.
