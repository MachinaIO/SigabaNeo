# Random primitive blocks on ordinary Haar input

The bounded-covolume split gives an exact **one-step comparison law** for a specified selector. The comparison error is a first absolute moment of a lattice-point count. Shortening the covolume window until it typically contains at most one block does not suffice, since the selector must also find a block. I obtain no certified block width at rank 1023 from this construction.

## A split with a failure state

Let the input be a Euclidean lattice of rank $n$ and determinant one, with law $\mu_n$. Fix $1\le b<n$ and $T>0$. Form the list of *unoriented primitive sublattices* of rank $b$ and covolume at most $T$. Its size $C(L)$ is finite because distinct entries give distinct pairs of opposite vectors in the discrete exterior-power lattice, of norm at most $T$. Return a uniform list entry, or a cemetery state if the list is empty. Complete the chosen primitive sublattice to an integer basis, reduce the block internally and continue in the orthogonal quotient, first scaling that quotient to determinant one. Internal changes of block basis preserve the quotient. This specifies a mathematical split kernel. Exhaustive listing has no established cost of the prescribed size.

Put $m=\mathbb E C$, and let $I$ be normalized incidence probability, giving mass $d\mu_n(L)/m$ to each eligible pair $(L,U)$. Primitive split unfolding gives $m=a_{n,b}T^n$ for a positive constant $a_{n,b}$. Under $I$, conditional on covolume $D$, the normalized shapes of the block and the quotient are independent Haar shapes. The distribution function of $D/T$ is $x^n$ for $0\le x\le1$, by taking ratios of mean counts. These are laws of pairs. [Kim, mean value formula](https://arxiv.org/abs/2005.10874) and [Part 46, split averaging](wall1_haar_prefix_law.md).

**Exact error theorem.** Retain the parent lattice even on failure. On the common space of marked parents and failed parents, let $P$ denote the split on ordinary Haar input. Then
$$
 \|P-I\|_{\rm TV}=\tfrac12\mathbb E_{\mu_n}|1-C/m|.
$$
Indeed the ambient marginals have densities $1,C/m$ relative to Haar. Given a parent with positive count, the conditional mark is uniform under both laws. On a zero-count parent choose the cemetery state for both conditional kernels, which is a permissible version for incidence. Applying the common kernel contracts TV and forgetting the mark gives the reverse inequality. In particular the distance dominates $\Pr(C=0)$ and is at most $\sqrt{\operatorname{Var}C}/(2m)$ when that variance exists. The same exact identity holds for positive summable weights if $C$ denotes their sum and both kernels choose proportionally to weight. Factorization of shapes requires a separate unfolding for the weight in question.

**Short-block obstruction.** For any one-block-per-parent selector, even one with unlimited search,
$$
 \Pr(D\le t)\le\min(1,a_{n,b}t^n).
$$
This follows from the indicator of existence being at most the count. At the mean-one cutoff $T_*=a_{n,b}^{-1/n}$, the probability of finding a block with $D\le0.99T_*$ in rank 1023 is at most $0.99^{1023}<0.000035$. This is a covolume statement, independent of assumptions about the shapes. Conversely, placing the cutoff above $T_*$ gives no lower bound on the chance of finding an entry via this argument.

## What a recursive comparison actually costs in probability

For a deterministic sequence of split ranks and cutoffs acting only on the current normalized quotient, consider an ideal chain that uses the incidence output law afresh at each rank, retaining the block shape and covolume. Its next normalized quotient shape is Haar independently of the entire retained history, by split factorization and induction (use rotation-invariant shape observables). If the corresponding ordinary-Haar counts at the successive ranks are $C_i$ with means $m_i$, the TV distance on retained histories, including failure, is at most
$$
 \min\!\left(1,\sum_i \tfrac12\mathbb E|1-C_i/m_i|\right).
$$
To prove this, replace steps in order using hybrids with an ideal prefix and a real suffix. At the first differing step the ideal prefix supplies an independent Haar input conditional on the retained data. The one-step theorem followed by forgetting the parent bounds the change. The common remaining real kernels contract TV. This argument does not condition on a revealed quotient lattice or on a full ambient input basis. For an overlapping tour the retained state and the comparison kernels would have to change.

Even the ideal chain requires a scale calculation. If the parent has physical determinant $V$, the selected physical block has determinant $V^{b/n}D$ and the quotient has determinant $V^{1-b/n}/D$, by the base-times-height formula. All internal GS lengths of the two normalized shapes must be multiplied by the respective determinant roots. Haar marginal shapes alone imply no log-linear GS slope. In particular, optimizing over candidate splits changes the mark kernel and invalidates the uniform-mark comparison.

## Numerical normalization and unresolved estimates

For Part 47 the physical length unit of the determinant-one rank-1023 null lattice is $s=3329^{511/1023}\in(57.4692,57.4693)$. With $j=1024-\beta$ prefix entries, a sufficient normalized prefix minimum for the stated Babai failure bound $\delta$ is $\sqrt{12\log(2j/\delta)}/s$ for $j>0$. Uniformly for $j\le1023$, upper roundings are $0.21079$ at $\delta=0.01$ and $0.43461$ at $\delta=2^{-64}$. These budgets concern lifting alone. The Part 47 terminal sufficient threshold in the same units is $R^2/s$ for the physical projected plant norm $R$. Part 48's fixed comparison length $\sqrt{6\beta}/s$ serves a different event. [Part 47](wall1_decoupled.md) and [Part 48](wall1_null_terminal.md).

The missing Haar estimates are a small cumulative selection error at useful cutoffs, an efficient sampler on a specified parent, and simultaneous lower tails for the scaled within-block GS lengths and terminal minimum. The exact TV expression can overestimate the error after projecting to shapes, so a large count fluctuation alone cannot rule out a different proof. No GSA or independence heuristic is used to assign a width here. For the finite q-ary input the ambient measure is discrete and has TV distance one from continuous Haar. Transfer would require control of the selected profile events, including sampling failures and ties, under that discrete input law.
