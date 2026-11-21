# A plant-independent prefix and the ambiguity of the lift

Reducing the horizontal kernel gives an exact conditional projection law. Two distinct questions survive projection. One concerns shortest vectors in the quotient. The other concerns the information lost along the prefix, even on the event that the quotient oracle returns exactly the projected plant.

## Splitting and conditioning

Write $N=m+n$, $d=N+1$, $X=(e,s)$ and $u=(X,1)$. Height is a surjective homomorphism from $L$ to $\mathbb Z$ with kernel $L_0$. For each $v\in L$ of height $t$, the unique decomposition is $(v-tu)+tu$, since $u$ has height one. This is an internal direct sum of abelian groups. Its summands need not be perpendicular.

Fix a canonical input basis for $L_0(A)$ and a terminating reducer with deterministic tie breaking. Its prefix span $W$ and the projected null lattice are measurable functions of the finite-valued $A$. For a measurable randomized reducer include its independent coins in the conditioning variable $D=(A,C)$. Under independent planting, the conditional law of $X$ given $D$ is the original product law. In particular $X$ is independent of the pair consisting of $W$ and the projected null lattice. Conditioning also on $b$ need not preserve this identity.

With $j=d-\beta$, let $K$ be the integer span of the first $j$ basis vectors. Then $W\cap L=K$ by height and uniqueness of basis coordinates. Since $W$ is horizontal, projection onto its orthogonal complement is $P=Q\oplus 1$, where $Q$ has rank $\beta-1$. Write $H=P L_0$, identifying horizontal vectors with their first $N$ coordinates. The remaining projected basis rows are a basis of $H$ by real linear independence modulo $W$. Thus $P L$ is discrete and its height-$k$ slice is exactly $(kQX+H,k)$. Conditional on $D$, $H$ is fixed and $QX$ has the pushforward CBD law. Unconditionally the map producing $QX$ itself depends on $D$.

## Projection law for an arbitrary orthogonal projector

For any fixed rank-$r$ orthogonal projector write its horizontal compression as $B$, its last column as $(h,a)$, and $p_\eta(z)=4^{-\eta}\binom{2\eta}{\eta+z}$ on $[-\eta,\eta]\cap\mathbb Z$. For every Borel set $S$ the exact probability is
$$
\sum_{x\in[-\eta,\eta]^N\cap\mathbb Z^N}
 {\bf1}_{S}(x^TBx+2h^Tx+a)\prod_i p_\eta(x_i).
$$
Here $a=\|Pe_d\|^2$, $\operatorname{tr}B=r-a$. Centering and covariance $(\eta/2)I$ give mean $\mu=(\eta/2)(r-a)+a$. Even at fixed rank the distribution can depend on the orientation. For the horizontal prefix the mean is exactly $1+(\beta-1)\eta/2$.

An explicit two-sided bounded-differences bound follows by realizing each coordinate as a sum of $2\eta$ independent fair signs divided by two. Flipping one sign at coordinate $i$ changes the squared norm by at most
$$
 c_i=(2\eta-1)B_{ii}+2\eta\sum_{l\ne i}|B_{il}|+2|h_i|.
$$
Indeed the midpoint of the two possible values of coordinate $i$ has magnitude at most $\eta-1/2$, and the two values differ by one. Exposing the signs successively gives Doob increments of conditional range at most $c_i$ per sign. Hoeffding's lemma and exponential Markov, optimized over the tilt on each side, give
$$
 \Pr(|\|Pu\|^2-\mu|\ge t)\le
 2\exp[-t^2/(\eta\sum_i c_i^2)]\qquad(t>0).
$$
If the denominator vanishes the squared norm is constant. This bound is orientation dependent and can be loose for dense projectors.

## Higher heights

Set $v=QX$ and $R=\sqrt{1+\|v\|^2}$. At height zero the exact strict test is $\lambda_1(H)>R$. At height one, $v$ must lie in the open Voronoi cell of zero for $H$ (in its span). The condition $\lambda_1(H)>2\|v\|$ suffices by the triangle inequality. By symmetry it suffices to test positive higher heights. For each integer $2\le k\le R$ the exact additional test is
$$
 \operatorname{dist}(kv,H)^2 > R^2-k^2 .
$$
All tests count ties as failures. Larger heights have length exceeding $R$ automatically. A competitor with horizontal correction $h'\ne0$ in this slice would require
$$
 \|h'\|\le k\sqrt{R^2-1}+\sqrt{R^2-k^2}\le R^2
$$
by Cauchy–Schwarz on $(k,\sqrt{R^2-k^2})$ and $(\sqrt{R^2-1},1)$. A zero correction gives length $kR$. Consequently $\lambda_1(H)>R^2$ suffices simultaneously at every height (also $R^2\ge2\|v\|$). This quadratic threshold is much stronger than the proposed linear comparison.

For a concrete obstruction take $H=7\mathbb Z$ and $v=3$. The projected plant has squared norm 10 and the minimum 7 exceeds twice its norm. Yet height two has a representative $(-1,2)$ of squared norm 5. This is a horizontal sample quotient of a null lattice with modulus 7 and zero design. The coordinate event has positive probability under CBD(3). Independence does not give a uniform measure on Voronoi cells, even for a fixed null lattice.

## What the SVP output determines

Orient an output equal to $\pm Pu$ to height one. Its entire fiber in $L$ is $u+K$. The zero correction in $H$ fixes a projected point, while every element of $K$ projects to zero. An arbitrary lift has the planted secret for every choice of representative exactly when the secret-coordinate map annihilates $K$. Part 39's deleted sample axes have this property. More generally, decoding with a support constraint would require the compatible secrets in the fiber to form a singleton, together with a method and cost for identifying it.

Even full HKZ reduction of the null lattice and an arbitrarily large projected null minimum do not imply this lifting statement. Take $m=n=1$, $A=0$, $q>2$, $e=0$ and let the secret vary in the CBD support. A shortest-first orthogonal null basis consists of the secret unit and the sample vector of length $q$. At $\beta=2$ the prefix removes the secret unit. The observed $b=0$, null basis and projected lattice are identical for every secret. The unique projected shortest pair is the pair of signed height units, also identical for every secret. No function of these data recovers all such secrets. This is a counterexample to a deterministic implication, not a bound on average success for large random designs.

## Consequences for reduction bounds

Using zero-based indices and $g_i=\|b_i^*\|$, exact overlapping BKZ gives $\lambda_1(H)=g_j$ whenever $j<N$. Its window at $j$ contains the whole remaining rank $\beta-1$ suffix. Part 6 therefore gives $\lambda_1(H)\ge\lambda_1(L_0)\exp(-P_j)$ with its width-specific prefix recurrence. For any basis, the last nonzero coefficient of a lattice vector already gives $\lambda_1(H)\ge\min_{i\ge j}g_i$ without a dimension loss. Neither identity supplies a numerical GSA lower bound. Part 44's ambient head upper bounds concern a different rank and bound a different quantity. [BKZ definition](../../SigabaNeo/Lib/Lattices/Reduction/BKZ.lean) · [Prefix bound](wall1_prefix.md) · [Head bounds](wall1_zshape.md)

The slide checker uses rank a multiple of its width, primal checks at aligned starts and shifted reciprocal checks. Even when the null rank is a multiple of $\beta$, the last $\beta-1$ rows omit the first row of the final primal block. Its shortest-first check does not assert shortest-first reduction at the next row. Applying a slide certificate requires specifying the block partition and deriving the desired suffix inequality. [Slide conditions](../../SigabaNeo/Lib/Lattices/Reduction/Slide/Conditions.lean)

At $(511,512,3329)$, CBD(3), the empty prefix reduces to previously certified exact SVP. On the full shape this is width 1024 (Part 41 reports failure below $2^{-1900}$). After Part 39 deletion it is width 647 with success at least 0.9951664. Initial null reduction is redundant in both cases. Part 7 obtained full dimension 701 after its own sample optimization at a different confidence. Width 406 is the estimator comparison under GSA. These are existing results. No smallest positive-prefix width for the proposed recovery procedure follows from this argument. [Frontier and Part 41](../PROOF_GAP.md) · [Part 39](wall1_projected_reference.md) · [Part 7](ratio_unique.md)

A null-only lower quantile for $g_j$ at a specified reducer and input law would address one term. At a linear threshold one still needs a bound for the higher-height tests under the conditional discrete law. Even the quadratic threshold leaves the lift unresolved. A high-probability recovery theorem needs control of the compatible lifts and the cost of choosing one. Part 46 concerns Haar shortest-vector selection. The Rogers theorem integrates lattice sums under normalized Haar probability; applying it here would require a comparison for the selected suffix of the finite q-ary ensemble. Neither result supplies the conditional CBD cell or lift estimates. [Part 46](wall1_haar_prefix_law.md) · [Rogers theorem](../../SigabaNeo/Lib/Lattices/Reduction/Rogers/RogersAllOrders.lean)

The counterexamples above admit exact integer checks (Python 3).

```python
q, v = 7, 3
assert q*q > 4*(1+v*v)
assert (2*v-q)**2 + 2**2 < 1+v*v
# Orthogonal null basis (0,1,0), (7,0,0), b=e=A=0.
fibers = {(0,s,1) for s in range(-3,4)}
project = lambda w: (w[0],w[2])
assert {project(w) for w in fibers} == {(0,1)}
assert all((q*i)**2+k*k > 1 for i in range(-1,2)
           for k in range(-2,3) if i or abs(k)>1)
# Outside this box either horizontal length >= 14 or height >= 3.
```

## Audit note (independent audit, Nov 2026)

* The HKZ lifting example is information-theoretically degenerate (A = 0: b carries no information about s); it refutes
  only the deterministic implication.
* **Lifting is resolved by Babai under a null-only condition.** Given D = (A, coins), Babai nearest-plane on the prefix basis,
  applied to any lift of the SVP output, returns u exactly when |⟨X, b*_i⟩| < g_i²/2 for all prefix indices i (the box is a
  fundamental domain of K = W ∩ L and b*_i is horizontal). Since X is product CBD (sub-Gaussian, variance proxy η/2) given D,
  Pr[lift fails | D] ≤ Σ_i 2·exp(−g_i²/(4η)). For η = 3 and ≲ 1024 indices, min_i g_i ≳ 12 gives < 1% and ≳ 25 gives < 2^-64.
* The quadratic threshold λ_1(H) > R² is essentially sharp (H = k²Z, v = k fails at height k).
* What remains open is therefore a **null-only** statement: lower quantiles of the Gram–Schmidt profile (min over the prefix of
  g_i, and the terminal g_j / λ_1(H)) of BKZ/slide on the plant-free q-ary lattice L_0.
