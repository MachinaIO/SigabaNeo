# Transferring a Haar void bound to a Gram–Schmidt profile

Write $p(g)$ for the probability, under the independent uniform size-reduction coefficients, that the open ball of radius $g_0$ contains no nonzero vector. Two transfers hold. At fixed coefficients there is an exact order on normalized profiles that suffices for comparison. In the Haar basis integral one can integrate out whole HKZ blocks and use a Haar minimum tail on each resulting quotient. Neither gives the requested rate in the fixed-profile mean $E$ on the rank-1023 bad domain.

## Comparing profiles with the same coefficients

In orthonormal GS coordinates let $U$ be the upper unitriangular coefficient matrix. For each integer column $z$,
\[
 \|Bz\|^2/g_0^2=\sum_j (g_j/g_0)^2 (Uz)_j^2 .
\]
Consequently if $g_j/g_0\le h_j/h_0$ for every $j$, the strict competitor set for $h$ is contained in that for $g$, pointwise in $U$. Thus $p(g)\le p(h)$ and $E(g)\ge E(h)$. In particular the void probability decreases weakly with excess slope in the geometric family. The same inclusion holds simultaneously for any collection of projected windows if each within-window ratio to its own head satisfies the comparison. Increasing every adjacent log drop suffices. These statements include ties since the test is strict.

**Ordering by the mean alone fails.** In rank three take $g=(1,4/5,2)$. The nearest lift of column two has squared norm at most $1/4+16/25<1$. Thus $p(g)=0$. Only last nonzero coordinate at index 1 with coefficient 1 up to sign can contribute, and averaging the number of horizontal lifts gives $E(g)=2\sqrt{1-16/25}=6/5$.

For an integer $m\ge2$, take a square transverse lattice of spacing $s=11/10$. Use the primitive first transverse column $s(m,1)$ and the completing column $s(-1,0)$, reducing the latter by integer multiples of the former. The resulting profile after adjoining an orthogonal unit head is $h=(1,H,d)$, where $H=s\sqrt{m^2+1}$ and $d=s^2/H$. Every vector outside the head line has length at least $s>1$ at this example. That strict gap persists on a positive-volume neighborhood of coefficients at fixed profile (the inverse basis norm is locally bounded, so only finitely many integer candidates matter). Hence $p(h)>0$. For this profile,
\[
 E(h)=\frac{\pi}{H}\sum_{1\le k<1/d}(1-k^2d^2)
 \longrightarrow \frac{2\pi}{3s^2}>6/5 .
\]
Indeed for last coefficient $k>0$, integrating the first two coefficient rows and summing over the first two integer coordinates gives horizontal disk area divided by $H$. One may integrate the head row first, using the uniform phase of $kU_{02}$ modulo one, and then the second row using $kU_{12}$. No pair ending earlier is strict. The limit is a Riemann sum. This gives the reversed order for all sufficiently large $m$. Overall rescaling each profile to covolume one preserves both statistics. This counterexample concerns arbitrary profiles and does not contradict the geometric comparison.

## Which measure has independent coefficients?

Let $Q_w(r)=\Pr_{X_w}(\lambda_1\ge r)$ for Haar probability on determinant-one lattices. The profile is a function of a *basis*. With signs identified, the Part 50 chart has intensity $dI_w(g)\,du=2^{1-w}K_w\exp(2\sum_{j=1}^{w-1}S_j)\,dS\,du$, with $S_j=\sum_{i<j}\log g_i$. Unfolding integrates the **number** of marked size-reduced bases per input. For instance in dimension two, at $g=(a,1/a)$ the radial factor is proportional to $a^2\,d\log a$, of infinite total mass. Selecting one basis by a fundamental domain or a reduction algorithm inserts its selection indicator into the chart. Selecting HKZ forces the head to pass with conditional probability one. [Part 50, basis intensity](wall1_volume_method.md) · [Part 46, selected quotient law](wall1_haar_prefix_law.md)

Here is a pointwise transfer with the missing multiplicity explicit. Normalize determinants to one. Take a bounded profile patch $A$ of positive intensity on the side $h_j/h_0\ge g_j/g_0$, with $r=\inf_A h_0>0$. Let $C_A(L)$ count the unsigned size-reduced marks in that patch. Then
\[
 p(g) I_w(A)\le \int_A p(h)\,dI_w(h)
 \le \mathbb E_{X_w}[C_A(L)\,\mathbf1_{\lambda_1(L)\ge r}].
\]
The first inequality is the coupling. For the second, each passing mark has its head shortest, so its lattice passes the common radius. For example, if all column lengths in the patch are at most $T$ (one can use $T^2=\sup_A\sum h_j^2$), the right side is at most $(1+2T/r)^{w^2}Q_w(r)$. Pack disjoint radius-$r/2$ balls at lattice points in the radius-$T$ ball and then count ordered tuples. Sharper multiplicities can replace this crude bound. In particular the transfer costs both the multiplicity and the inverse one-sided patch mass. Markov on normalized patch measure instead bounds the fraction with $p(h)>t$ by the same right side divided by $t I_w(A)$. Neither operation justifies replacing that right side by the unweighted Haar tail. Normalizing the head ratios upwards at fixed determinant also reduces the head radius, weakening the tail.

## An integrated transfer that removes the internal multiplicity

Fix a partition into consecutive blocks of lengths $d_j\le\beta$. Forget the internal flags but retain the primitive flag at block boundaries. Denote by $D_j$ the covolume of the projected block lattice and by $d\eta(D)$ the pushforward of Haar *coarse-flag counting intensity* to those covolumes. Their product is one. At fixed $D$, before any acceptance tests, the determinant-normalized diagonal block shapes have independent Haar laws. This follows by iterating the primitive split disintegration of Part 46 in each remaining quotient, or by factoring the Part 50 density into within-block densities and a factor depending only on boundary sums. The cross-block lift tori have mass one. [Primitive split](wall1_haar_prefix_law.md) · [Disjoint HKZ integral](wall1_volume_svp_weights.md)

Every BKZ completion induces HKZ within each block: each suffix of that block lies in the tested window beginning at the same index and contains its head. Almost surely these internal unsigned HKZ flags are unique by successive shortest-line uniqueness (countably many marked flags suffice to discard ties). In particular the head of block $j$ has length $D_j^{1/d_j}\lambda_1(H_j)$ for normalized shape $H_j$. Suppose every bad completion under consideration forces $D\in A$ and normalized block heads at least $r_j(D)$. Then
\[
 \Pr(\exists\text{ such completion})\le
 \int_A \prod_j Q_{d_j}(r_j(D))\,d\eta(D).
\]
Indeed count the eligible coarse flags and discard crossing tests, then apply the conditional product law. In dimension one use the deterministic minimum one. This also works for one interior block by splitting at its boundaries and leaving the other shapes unrestricted. A restriction on the terminal head from *above* calls for a lower-tail factor instead. If the bad condition retains internal GS coordinates, one must integrate the corresponding joint HKZ profile law or relax the condition to implications at the boundaries. Choosing a partition after observing a profile requires accounting for the union of choices. The formula specializes to an ordinary Haar tail for a single full-width block. At finite width, overlapping windows share internal data and do not give extra independent Haar factors. The integral with the true joint acceptance of Part 50 is sufficient in principle. This coarse-flag inequality explains which marginal tails one can actually substitute into it.

## Range of the Haar estimates

For $V=V_w r^w$, Rogers' fixed-volume limit gives $Q_w(r)\to e^{-V/2}$ as dimension increases. Södergren gives the associated point-process limit. Schmidt's sieve gives a Poisson approximation with an exponentially small additive error in a sufficiently small linear-volume range (Kim, Theorem 1.5). Neither is an exact finite-rank exponential law. At $r=c\,V_w^{-1/w}$, the volume is $c^w$, already exponential for fixed $c>1$. Monotonicity can evaluate a tail bound at a smaller linear volume, but this only retains the exponent at that smaller volume. Strömbergsson treats shape-dependent avoidance, including displaced balls and cut balls. For a centered ball the fixed-dimensional large-volume limit is eventually identically zero by Minkowski, for $V>2^w$. It does not supply a Poisson upper tail throughout the intermediate exponential-volume range. [Södergren](https://arxiv.org/abs/1001.3623) · [Kim, Theorems 1.1 and 1.5](https://newton.kias.re.kr/~seungkikim/onbound.pdf) · [Strömbergsson, §1.1](https://www2.math.uu.se/~ast10761/papers/lprob.pdf)

One explicit all-volume bound for Haar is $Q_w(r)\le(1+V/(2\zeta(w)))^{-1}$ for $w\ge3$, from the primitive-pair second moment in Part 46. It gives logarithmic suppression in $V$. Even allowing each disjoint block a linear-volume Poisson exponent $V/2\le c d_j/2$ gives at most $c\,1023/2$ nats in those factors. This comparison concerns the factors alone: changing from full flags to coarse flags also changes the outer intensity. In particular the old Part 71 witness-box masses cannot be used as lower bounds for that new integral, and the boxes themselves have since been excluded by packing. The fixed-profile mean is also distinct from the Haar mean $V/2$, even where Part 70 proves an approximation for geometric profiles. [Geometric mean calculation](wall1_window_asymptotics.md) · [Packing exclusions](wall1_dense_packing_ld.md)

**Outcome.** The coupling transfers a bound from a componentwise larger normalized profile, and the flag inequality transfers Haar tails after integrating away internal profiles. No new positive rate $f(E)$ of the required magnitude, or improved rank-1023 terminal certificate, follows here. The pointwise route still needs a quantitatively favorable one-sided average with controlled completion multiplicity. The integrated route instead needs a small outer flag integral with the bad condition retained, or a joint estimate for crossing tests under that flag law.
