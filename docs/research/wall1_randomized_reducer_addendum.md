# Random prefixes, randomized winners and the marked void

**Result.** Among the four proposals, a uniformly sampled primitive prefix with a covolume cutoff gives the clearest new comparison experiment. It preserves the ambient lattice, specifies the exact law of its projected quotient, and admits an arithmetic equidistribution theorem in a reference model. Its covolume simultaneously sets the *physical* scale of that quotient. No finite cutoff or sampling cost is certified here for the required marked void. Randomizing the winner has a different advantage: with no lookahead it preserves the fresh-column law of Part 108. Neither construction establishes the long-winner ceiling or an end-to-end success probability.

## The event that needs fresh randomness

In the graph phase of Part 108, fix the observed columns, the reducer's past coins and its frame. The state includes a retained lattice $M$, a projected grid $K$, and the finite subgroup $H=K/M$. The new height-one column gives one uniform mark $u\in H$. For a physical radius $1\le r<q$, the exact probability that the appended block has minimum greater than $r$ is
$$
 {\bf1}_{\lambda_1(M)>r}\,\frac1{|H|}\sum_{u\in H}
 \prod_{k=1}^{\lfloor r\rfloor}
 {\bf1}_{\operatorname{dist}(k\tilde u,M)>\sqrt{r^2-k^2}} .
$$
All the multiples use the same mark. A new coin drawn *after* this block is formed can change its selected line and future states. Its conditional draw cannot fill a void already present in the block. Part 47 allows prefix choices based on the null lattice and independent coins while maintaining the conditional product law of the plant. Projected uniqueness and lifting still depend on the resulting geometry. [Part 47](wall1_decoupled.md) · [Part 108](wall1_first_tour.md) · [Part 229](wall1_sumset_covering.md)

Two numerical benchmarks distinguish the issues. For the original width-506 chain, the concrete comparison of the terminal short-vector event to its old-witness event has error below $5.244\cdot10^{-9}$. It leaves the frequency of the old witness open. A separate sufficient estimate in Part 230 is a conditional height-one void ceiling of 0.18 over the specified draws and corridor. Part 227 counts more than $2.14\cdot10^{52}$ raw candidates per draw on a high-probability event. Their number gives no lower bound on coverage by their projections. Part 231 exhibits equal radial profiles and a common winner with distinct next voids on opposite sides of 0.18. Those examples lie below the reachable scale. Changing the winner changes the chain to which all these figures refer. [Proof-gap register, Parts 183–231](../PROOF_GAP.md) · [Two-mark drift](wall1_inductive_typicality.md) · [Radial counterexample](wall1_drift_recursion.md)

## (a) Sample the prefix itself

Let $L$ have rank $n$, let $1\le k<n$, and set $d=n-k$. Let $\mathcal P_T(L)$ consist of the unoriented primitive rank-$k$ sublattices $P$ with covolume at most $T$. It is finite because the primitive decomposable exterior vector specifying each entry, up to sign, belongs to a bounded ball in $\bigwedge^k L$. Return a failure symbol if the list is empty. Otherwise choose an entry uniformly and extend a basis of it to a basis of $L$. With $Q_P$ denoting orthogonal projection off its span, the exact conditional probability of any quotient event $B$ is
$$
 \frac{1}{|\mathcal P_T(L)|}\sum_{P\in\mathcal P_T(L)}
 {\bf1}_{Q_PL\in B},\qquad
 \det(Q_PL)=\frac{\det L}{\det P}.
$$
The determinant follows by taking base times perpendicular volume in a completed basis. The completion does not affect the whole quotient. For a block of width $b<d$, its law also needs a rank-$(k+b)$ primitive extension $F\supset P$, since the block is $Q_P F$. A law on prefixes alone leaves this choice unspecified. One can sample from a finite list of nested flags with both covolume cutoffs, or specify a completion and use its first $b$ columns. Uniform flags weight a prefix proportionally to its number of extensions.

This separation also applies to short-vector sampling. For instance, at each step choose a primitive line in the current quotient with mass proportional to $e^{-\pi\|v\|^2/s^2}$, using its primitive generator up to sign. Pulling back the line gives the next saturated prefix. A given path of lines has probability equal to the product of these weights divided by their **state-dependent** partition sums. Different internal flags can give the same final prefix, so its probability is the sum over those paths. A random unimodular matrix supplies yet another law, given by the pushforward of its sampling distribution. Even an exact uniform law on prefixes modulo a prime controls only residues. In $\mathbb Z^2$, $v=(1,mp)$ always reduces to $e_1$, while the physical quotient spacing is $1/\sqrt{1+m^2p^2}$.

For uniformly counted primitive sublattices of $\mathbb Z^n$ at fixed ranks and increasing height, Horesh and Karasik prove joint equidistribution of the direction and normalized shapes. The projected factor lattice is dual to the orthogonal integral lattice, so the corresponding normalized quotient shape has the invariant limiting law. Their flag theorem addresses successive quotient shapes under its flag ordering. For a fixed finite cutoff the law above is atomic. The theorem does not supply the needed finite error for the joint metric lattice, finite mark subgroup and completion in this graph process. A full-input prefix choice can also reveal unread graph columns. Sampling from the already revealed integral span preserves independence of the next column provided that the window update and projected height still have the Part 108 form. [Primitive lattices, Horesh–Karasik](https://academic.oup.com/qjmath/article/74/4/1253/7191043) · [Primitive flags, Horesh–Karasik](https://arxiv.org/abs/2202.12724) · [Local comparison models](wall1_lit_projections.md)

**Physical obstruction.** Hermite's bound implies
$$
 \det P\ \ge\ \det L\,(\sqrt{\gamma_d}/r)^d
 \quad\Longrightarrow\quad \lambda_1(Q_PL)\le r .
$$
For fixed $L$, $k$ and $r>0$ with $0<k<n$, the uniformly counted quotient hits this physical ball with probability tending to one as $T\to\infty$. Only finitely many prefixes fall below the displayed threshold, while the number of primitive prefixes grows without bound by shearing one generator of a coordinate prefix in a complementary basis direction. Thus a near-Haar normalized shape can accompany an almost certain short horizontal competitor at any fixed radius. This result concerns a quotient minimum. The marked affine void and the projected length of the plant require separate comparisons. A small quotient minimum can rule out a long winner in that block and also invalidate a terminal uniqueness certificate requiring horizontal separation.

**Exact finite example.** For $L=\mathbb Z^3,k=1,T=16,r=1/2$, **7,092 of 7,117** primitive lines yield a quotient vector of length at most $1/2$. The rank-two Hermite bound alone certifies 6,936 of them. Write $P=\mathbb Zv$, $h^2=v\cdot v$. The determinant is $1/h$, so the bound with $\gamma_2=2/\sqrt3$ suffices when $3h^2\ge64$. For the rest, the exact criterion is existence of a nonzero integer $a\perp v$ with $4\|a\|^2\le h^2$. Indeed $v\times\mathbb Z^3=v^\perp\cap\mathbb Z^3$. Choose integral $t$ with $v\cdot t=1$, then $v\times(a\times t)=a$ for $a\perp v$. Also $\|Q_v w\|=\|v\times w\|/h$. The arithmetic check below uses no floating-point comparisons.

The explicit-list implementation visits every list entry and can use reservoir sampling. General flag enumeration and exact discrete-Gaussian line sampling have no competitive cost proved here. A prefix inside the horizontal null lattice leaves the height-one plant nonzero in the full quotient. Its projected image remains a lattice vector, and neither shortestness nor correct lifting follows from this membership.

## (b) Choose a near-shortest line uniformly

Fix the new block $W_u$ and $1\le a=1+\varepsilon<2$. Let $S_u$ be the unoriented lines whose primitive generators have norm at most $a\lambda_1(W_u)$. Every nonzero vector in this shell is primitive up to sign because division by its integer multiplicity would give a shorter vector than the minimum. Let $s$ be the norm drawn. For every $r$,
$$
 {\bf1}_{\lambda_1(W_u)>r}\ \le \Pr(s>r\mid W_u)=
 \frac{\#\{\ell\in S_u:\|v_\ell\|>r\}}{|S_u|}
 \ \le\ {\bf1}_{\lambda_1(W_u)>r/a}.
$$
In particular the current long-winner probability can only increase compared to selecting a shortest vector on the same incoming block. For the next draw the kernel averages the next-state void over $u\in H$, then averages uniformly over $\ell\in S_u$, using the *same* selected projection for both the lattice and the image of the mark subgroup. The next raw independent column is uniform on that image by equal fiber sizes, conditional also on the independent winner coin. The unresolved term is the average of the void with these directional weights.

The conditional entropy is exactly $\log_2|S_u|$ bits. It can be zero in every dimension. A rectangular lattice with spacings $1,M,\ldots,M$ and $M>a$ has only one eligible line. Conversely, in a cubic lattice of rank $b$ with $a<\sqrt2$ there are $b$ equiprobable axis lines. Every resulting unmarked quotient is the same cubic shape, so $\log_2 b$ bits need not randomize even that shape. A sieve list can implement uniform choice on its *stored* lines after deduplication. Equality with this kernel requires complete coverage or a proved sampling law, and certification of the radius. At a terminal block with $m$ eligible lines including one desired line, its conditional selection probability is $1/m$. Earlier null-lattice steps preserve ambient membership. An exact terminal test can be kept separately. No cost or success bound for the modified trajectory follows from a list size. [Existing near-shortest reducer note](wall1_randomized_reducer.md)

## (c) Signed permutations and sample subsets

For a distribution-preserving signed permutation group $G$ and input $X$, an equivariant success test has exactly the same outcome on $gX$ after transporting its frame and coins. For a coordinate-order-sensitive test, one uniformly reordered run samples the orbit average $p(X)=|G|^{-1}\sum_g\Pr_C[\mathrm{success}(gX,C)]$. In particular it *can* change a fixed instance's one-run probability. For invariant input law, $\mathbb E p(X)$ equals the original one-run mean. Use permutations and signs within independent exchangeable coordinate types, with the corresponding transformations of the public data and the plant. An arbitrary exchange of secret, error and embedding coordinates need not be a symmetry.

Independent restarts conditional on $X$ have failure probability $(1-p(X))^R$. Averaging yields $\mathbb E(1-p(X))^R\ge (1-\mathbb E p(X))^R$. For example, if $p(X)$ is zero or one with equal probabilities, ten restarts still fail with probability $1/2$, versus $1/1024$ for genuinely independent inputs of mean success $1/2$. This example illustrates the effect of dependence. Applying a signed permutation costs linear time in the entries moved, apart from rerunning reduction.

For $s$ uniform indices without replacement out of $m$ iid sample rows conditional on a shared secret, the one-run marginal is exactly the $s$-row model. Given the realized data the law is a finite subset average with $\binom ms$ terms. Drawing the sample indices is inexpensive compared to reducing each chosen instance. A random ordering without replacement of unread iid rows still gives fresh rows conditional on the revealed rows and secret. Reusing a known table instead supplies randomness only in the indices. Disjoint sets of iid rows are independent conditional on the shared secret if no other data-dependent state is shared. Puncturing sample coordinates also changes the lattice and dimension. The restricted plant survives, but success on the full instance requires the reconstruction and verification appropriate to the omitted data. This symmetry or subset law proves no new marked-void tail at a fixed width.

## (d) Condition a sublattice step on known winners

Work in the physical rank-$n$ lattice $U$ immediately **before** the downward index-$p$ step, including any preceding superlattice extension. Let $W\subset U/pU$ be the span of images of the known winners, $t=\dim W<n$, and $j=n-t$. The admissible sublattices correspond to the projective nonzero functionals on $(U/pU)/W$. There are $(p^j-1)/(p-1)$. For a uniform admissible step and a fixed unknown vector $x\in U$,
$$
 \Pr(x\text{ retained}\mid U,W,x)=
 \begin{cases}
 1,&\bar x\in W,\\
 (p^{j-1}-1)/(p^j-1),&\bar x\notin W .
 \end{cases}
$$
This follows by counting functionals annihilating the image of $x$. When $t=n$ there is no admissible index-$p$ step. For $p=2$, $j=4$, the unprotected survival probability is exactly $7/15$. For $j=1$ it is zero. Across $h$ steps, the probability of *continuous survival while unprotected at each of those steps* is at most $p^{-h}$ by conditional multiplication. A later superlattice can reintroduce a lost vector. No independent-survival assumption or claim about final re-entry is needed.

All physical superlattices contain all old vectors, but can introduce a shorter vector or make an old primitive vector divisible. To guarantee containment for *every possible* plant in a specified support $D\subseteq U$, a down-step must contain its span modulo $p$. Known lines suffice only if they imply this constraint or the chosen kernel imposes it separately. For one up-step $L\subset U$ and one equal-index down-step $S\subset U$, retaining every vector of $L$ forces $S=L$ by equality of indices. Every other such $S$ has $[L:L\cap S]=p$, since the image of $L$ in $U/S$ is nonzero and hence surjective. This covers a full-span support in $L$ modulo $pL$ as well. For a restricted support, its actual span matters.

Sampling a nonzero functional on the quotient costs a finite-field basis computation and $j$ field elements per random trial. The zero-trial probability is $p^{-j}$. This accounts only for choosing a neighbor. It gives no mixing time. The conditioned kernel has different transitions from the unrestricted Hecke kernel. Part 214's **46,595,465** index-two steps and endpoint area bound **below $2.19843\cdot10^{-58}$** apply to its unrestricted construction at the stated gated starts. Unprotected survival over that many downward steps is below $2^{-46{,}595{,}465}$ in that construction. Its area estimate does not transfer to a walk constrained to contain a known flag. [Part 213](wall1_hecke_randomization.md) · [Part 214](wall1_hecke_gated_mixing.md)

## Reproduce the finite-prefix count

Run this block with Python 3.9+ from `docs/research/scripts/` or any other directory. It writes no files.

```python
from itertools import product
from math import gcd

small_duals = [a for a in product(range(-2, 3), repeat=3) if any(a)]
forced = extra = misses = 0
for v in product(range(-16, 17), repeat=3):
    h2 = sum(x*x for x in v)
    if h2 > 256 or gcd(*v) != 1 or next(x for x in v if x) < 0:
        continue
    if 3*h2 >= 64:
        forced += 1
    elif any(4*sum(x*x for x in a) <= h2
             and sum(x*y for x, y in zip(a, v)) == 0 for a in small_duals):
        extra += 1
    else:
        misses += 1
assert (forced, extra, misses) == (6936, 156, 25)
print(forced + extra, forced + extra + misses)
```

**Completeness.** The finite counting laws, the physical-scale obstruction, and the restart identity are proved above. The numerical enumeration checks a rank-three reference lattice. The missing result for (a) is an effective bound at a *usable physical prefix covolume* on the joint projected block and its mark subgroup, together with an affordable sampler and lifting control. For (b) it is the shell-weighted directional void along the modified chain. Neither a finite-dimensional success probability nor a verified runtime for a successful modified reducer is established.

## Audit

**Verdict.** The finite-prefix law, the enumeration, the one-block winner bound and the index-$p$ retention formula are correct. Two distinctions matter when using the results: fixed-input retries can amplify success, and an unprotected vector can survive a particular down-step.

1. **Prefix and physical scale.** Primitivity gives a basis completion in $L$. The block-triangular volume formula gives $\det(Q_PL)=\det L/\det P$, so counting prefixes gives the exact pushforward law on full quotients. A shorter block requires the additional flag specified in (a). Horesh–Karasik give an effective count for direction and normalized shapes in their arithmetic model. The physical minimum also depends on the quotient covolume, and the marked void depends on the subgroup. For fixed $r>0$, Hermite's bound confines possible full-quotient misses to finitely many prefixes even as the total count tends to infinity. [Horesh–Karasik, Theorems 1.1, 3.2 and 3.4](https://arxiv.org/pdf/2012.04508)
2. **Independent enumeration.** The embedded code returned 6,936 Hermite-certified hits, 156 further hits and 25 misses. A second enumeration checked projected lifts directly. For each primitive $v$, subtract a nearest integer multiple of $v$ from a lift $w$. A hit then has $\|w\|^2\le(1+\|v\|^2)/4\le257/4$, hence $\|w\|^2\le64$ by integrality. Testing $0<4(\|v\|^2\|w\|^2-(v\cdot w)^2)\le\|v\|^2$ over that ball gave **7,092 of 7,117**. The misses have sorted absolute coordinates $(0,0,1),(0,1,1),(1,1,1),(1,1,2)$, with respective unoriented multiplicities $3,6,4,12$.
3. **Randomized winner.** On the same incoming block, $\lambda_1\le s\le a\lambda_1$ gives both stated tail inequalities, including equality cases at the thresholds. Conditional on the revealed columns and winner coins, the selected projection is fixed. With no lookahead, the unread column remains uniform and its displacement is uniform on $Q_*H$ by equal fiber sizes. The comparison of long returns applies to the current block only.
4. **Restarts.** For independent permutation or subset draws and fresh coins on a fixed input $X$, success after $R$ trials is exactly $1-(1-p(X))^R$. This strictly improves on $p(X)$ for $0<p(X)<1$ and $R>1$. Symmetry and the one-subset marginal alone give no positive lower bound on $p(X)$ for each input. Substituting the population mean for $p(X)$ can therefore overstate the gain.
5. **Protected vectors.** For prime $p$ and $j>0$, membership of $\bar x$ in $W$ is equivalent to **guaranteed** retention over all admissible down-steps. Outside $W$, the fraction of retaining hyperplanes is $(p^{j-1}-1)/(p^j-1)<1/p$, positive for $j\ge2$. The multistep bound concerns the joint event of remaining unprotected and surviving at every specified step. Finally, $L\subseteq S\subseteq U$ and $[U:L]=[U:S]=p$ force $[S:L]=1$.
