# Plant symmetry, planting and plant-blind reduction

This note tests whether the randomness of the planted vector can stand in for path control in Wall 1. It follows three
directions: planted-versus-null comparison, exchangeability over symmetries, and plant-blind decomposition of the reducer.

**Verdict.** For every reducer whose decisions do not read the plant, the plant's randomness integrates out exactly. The
success probability is then sandwiched between two **plant-free** quantities of the null trajectory, up to explicit errors
(Theorems 4.4 and 4.5). So no plant-symmetry argument can replace a lower-quantile statement for the selected null block.

* **Positive.** The single-block δ of `conditionalReduction` can be replaced by δ_𝒯: the probability that **no** checkpoint
  along the null run has a good block. This holds for a fork reducer at the cost of one extra SVP per checkpoint.
* **Negative, quantitative.**
  * The planted and null laws are almost mutually singular: TV ≥ 1 − 2^−3107.2, KL ≥ 3592.1 bits.
  * Symmetrization cannot change δ.
  * The standard (non-decoupled) reducer can leave the null trajectory early, in ways unrelated to the final block.
  * Any 99% proof for a K-look plant-blind reducer at β = 506 must prove the null statement
    Pr[max_t λ1(H_t) ≤ ℓ_K] ≤ 0.0101, with ℓ_1 = 16.858 and ℓ_10 = 13.174. Part 101 certifies only 8.1588.

## 0. Setting

* Plain LWE (m, n, q) = (511, 512, 3329), with N = m + n = 1023.
* X = (e, s) ∈ ℤ^N has i.i.d. CBD(3) coordinates, with law p. Each coordinate has variance σ² = 3/2, fourth moment 6, and
  fourth cumulant κ₄ = 6 − 3σ⁴ = −3/4.
* u = (X, 1). L_0(A) = {x ∈ ℤ^N : [I | A] x ≡ 0 (mod q)}, and L = L_0 ⊕ ℤu (Part 47).
* A reducer is a map from (A, C) to a basis trajectory of L_0, where C denotes coins independent of (A, X).
* At a state with horizontal prefix span W of rank N − β + 1:
  * Q is the orthogonal projector onto W^⊥ ∩ ℝ^N, of rank d = β − 1;
  * H = Q L_0 and T = P L = H ⊕ ℤ(QX, 1);
  * Z = ‖QX‖², so that ‖Pu‖² = 1 + Z.
* "Good(L, g)" is `FinalBlock.Good` in [ConditionalReduction.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/ConditionalReduction.lean):
  minimum ≥ L and GS floor ≥ g.
* ε(L, g) is `reductionError N d g L`. Lifting is not part of that theorem. Its Part 47 bound is
  ε_lift(g') = 2(N − β + 1)·exp(−g'²/12), for prefix GS floor ≥ g' and η = 3.

## 1. What "independent of the plant" means

**Lemma 1.1 (σ-algebras).** X is independent of σ(A, C). The lattice L is σ(A, b)-measurable, with b = [I|A]X mod q, and
it is not σ(A, C)-measurable.

**Lemma 1.2 (the lattice determines the plant).** Write 𝔅 = [−3, 3]^N ∩ ℤ^N. Then
Pr_{A,X}[some X' ∈ 𝔅 with X' ≠ X satisfies [I|A]X' ≡ [I|A]X] ≤ (7^N − 1)·q^−m < 2^−3107.2.

*Proof.* Put w = X' − X ∈ [−6, 6]^N, w ≠ 0, and split w = (w_e, w_s). Suppose w_s ≡ 0 mod q. Since |w_s| ≤ 6 < q, this
forces w_s = 0. Then w_e ≡ 0 forces w_e = 0, so w = 0, a contradiction. Hence w_s ≢ 0, and A w_s is uniform on F_q^m.
So Pr_A[w_e + A w_s ≡ 0] = q^−m for each fixed pair (X, X'). Summing over the at most 7^N − 1 choices of X' and
averaging over X gives the bound. Numerically, 1023·log₂7 − 511·log₂3329 = −3107.22. ∎

So a reducer that reads L (equivalently b) has, in principle, all the information about X. **"Plant-blind" must therefore
mean that the reducer's decisions are σ(A, C)-measurable, possibly up to a stopping time.** Weaker readings such as "the
direction of u is random relative to L" are false. Given L, the posterior of X is a point mass outside an event of
probability < 2^−3107. This also disposes of the resampling form of direction (1): drawing "the lattice, then a uniformly
random admissible short vector in it" returns the plant itself.

## 2. Planted versus null (direction 1)

Let P be the planted law of (A, b) and Q₀ the null law, under which (A, b) is uniform. Define the CBD-weighted count
Z(A, b) = Σ_{X ∈ 𝔅, [I|A]X ≡ b} p(X).

**Proposition 2.1 (exact planting identity).** dP/dQ₀ = q^m·Z. Consequently, for every event E of (A, b, C) with C
independent:
* P(E) = E_{Q₀}[q^m Z·1_E];
* the posterior of X given (A, b) is p(X)·1{X ∈ coset}/Z.

*Proof.* P(A, b) = q^−mn·Σ_X p(X)·1{[I|A]X ≡ b}, while Q₀(A, b) = q^−m(n+1). ∎

**Proposition 2.2 (non-contiguity).**
1. Q₀(Z > 0) ≤ 7^N·q^−m < 2^−3107.2, while P(Z > 0) = 1. Hence TV(P, Q₀) ≥ 1 − 2^−3107.2.
2. KL(P‖Q₀) ≥ m·log₂q − N·H(CBD(3)) = 5979.14 − 1023·2.33336 = 3592.12 bits.
3. The rare-event transfer of [wall1_information](wall1_information.md) gives x·log₂(1/p) ≤ KL + 1. Bounding a planted
   probability x ≤ 0.01 through it therefore needs a null probability p ≤ 2^−359,313.

*Proof.*
1. The expected number of points of 𝔅 in a uniform coset is |𝔅|/q^m, so Markov's inequality bounds Q₀(Z > 0).
2. Z ≥ p(X) because the true plant appears in the sum. So KL = E_P[log₂(q^m Z)] ≥ m·log₂q + E[log₂ p(X)].
3. Substitute the value from item 2. ∎

**Proposition 2.3 (the decoupled case is exactly trivial).** For every σ(A, C)-measurable statistic, in particular the final
block (Q_A, H_A) of any decoupled reducer, the laws under P and Q₀ coincide. So δ_planted = δ_null.

*Proof.* The A-marginal is uniform under both laws, and C is independent of (A, b). ∎

**Consequence.** No intermediate regime exists for change of measure. A statistic either ignores b (Proposition 2.3: δ is
literally a null quantity, and planting adds nothing) or uses b, in which case the likelihood ratio lives on a null event of
probability < 2^−3107. Low-degree or contiguity transfers from null to planted reducer behaviour are therefore impossible for
any reducer whose output depends non-trivially on b.

The null analogue of the final block does not help either. It replaces QX by QY, with Y a uniform coset representative, so
QY mod H is uniform on the finite group Qℤ^N/H. Its mark has norm of the order of the covering radius of H, not √(1 + 1.5d).
The null and planted "plant failure" events therefore concern different objects.

## 3. Exchangeability (direction 2)

Let G be the group generated by two kinds of signed permutations:
* signed permutations of the rows, acting jointly on the rows of A and on the coordinates of e;
* signed permutations of the columns, acting jointly on the columns of A and on the coordinates of s.

Each g ∈ G acts on designs by A ↦ gA and on ℝ^N by an isometry ĝ (a signed permutation matrix). The plant law p is
moreover invariant under the full hyperoctahedral group B_N, since e and s are both i.i.d. CBD(3).

**Lemma 3.1.** ĝ·L_0(A) = L_0(gA), and the uniform law of A is G-invariant.

*Proof.* Write g = (D_r P_r, D_c P_c). Then [I | gA]·ĝx = D_r P_r [I | A] x, and D_r P_r is invertible mod q. ∎

**Proposition 3.2 (symmetrization closure).** For a reducer R, define R^G(A; g, C) = ĝ⁻¹·R(gA; C), with g uniform on G and
independent of everything else. Let Φ be any isometry-invariant failure predicate of the final block (minimum, GS floor,
uniqueness of a mark transported by ĝ). Then:
1. R^G is G-equivariant in law.
2. δ_Φ(R^G) = δ_Φ(R).
3. The joint success probability with the independent plant is the same for R and R^G.

*Proof.*
1. Equivariance in law follows by reparametrizing g ↦ g·h.
2. δ_Φ(R^G) = E_g E_A[Φ(ĝ⁻¹R(gA))] = E_g E_A[Φ(R(gA))] = E_A[Φ(R(A))], using isometry invariance of Φ and then
   invariance of the law of A.
3. Use the B_N-invariance of p and the independence of X from (A, g, C). ∎

**Corollary 3.3.** Fix a hypothesis class ℋ of reducers that is stable under R ↦ R^G (for example, "outputs a fully
BKZ-β-reduced basis"). Any bound on δ derived from "law invariance + R ∈ ℋ" also holds for every symmetrized R^G.
Symmetrization does not change δ (Proposition 3.2), so such a bound is a bound on sup_{R∈ℋ} δ(R). The orbit average
δ = E_A[|G|⁻¹ Σ_g Φ(R(gA))] is exact, but it is just δ of a randomized reducer, so computing it is the original problem.
[Part 106](wall1_chain_law.md) exhibits equivariant selectors that force the terminal minimum below any fraction of its GH
(Haar setting). Parts [104](wall1_markov_reducer.md) and [109](wall1_terminal_mixing.md) show that unrestricted selectors
and reachable histories behave badly.

**Proposition 3.4 (what the plant orbit does compute).** For any fixed symmetric matrices Q₁ and Q₂:
* E[XᵀQ₁X] = σ² tr Q₁;
* Cov(XᵀQ₁X, XᵀQ₂X) = 2σ⁴ tr(Q₁Q₂) + κ₄ Σ_i (Q₁)_ii (Q₂)_ii = 4.5 tr(Q₁Q₂) − 0.75 Σ_i (Q₁)_ii (Q₂)_ii.

In particular, for a rank-d projector, Var Z = 4.5d − 0.75 Σ_i Q_ii² ≤ 4.5d. Averaging Q over B_N gives
E_g[ĝᵀQĝ] = (d/N)·I. These are the only orbit-invariant data, and they concern the plant, not H.

*Proof.* Expand Σ Q₁_ij Q₂_kl E[X_i X_j X_k X_l]. The nonzero terms are those with indices paired (i=j, k=l), (i=k, j=l)
or (i=l, j=k), plus the i=j=k=l correction μ₄ − 3σ⁴. ∎

The information-set re-presentations of the same lattice (choosing another set of m pivot coordinates of ker[I|A]) give the
same L_0 with a different canonical basis. Randomizing over them is input randomization, which
[wall1_exchangeable](wall1_exchangeable.md) shows retains the presentation (worst-case TV 1) and is not preserved through
reduction.

## 4. Plant-blind decomposition (direction 3)

### 4.1 Coupling the standard reducer with the null run

**Plant-last BKZ (PL-BKZ).** The input basis is (b_0, …, b_{N−1}, c), where (b_i) is a basis of L_0 and c is any height-1
vector, for example (b, 0, 1).
* Windows [j, j+β−1] with j ≤ N − β are horizontal.
* Windows [j, N] with j ≥ N − β + 1 contain c, and their projected lattice is π_j L = H_j ⊕ ℤ(Q_j X, 1). Here π_j fixes the
  height coordinate because the prefix is horizontal.
* The SVP rule:
  * If horizontal vectors attain λ1(π_j L), return the null rule's choice in H_j and insert it among (b_j, …, b_{N−1}),
    leaving c last (c may be size-reduced, which does not change the horizontal part).
  * Otherwise the window is **visible**: return a strictly shorter vector of nonzero height.

The null run is the same algorithm on L_0 with windows truncated at N − 1. Its states S_t are σ(A, C)-measurable.

**Theorem 4.1 (coupling).** Let τ be the first visible call. For t < τ, the PL-BKZ state equals (S_t, c_t). The call at a
window [j, N] in state S_t is visible if and only if
∃ k ≠ 0 : k² + dist(k Q_j X, H_j)² < λ1(H_j)².
Given (A, C), this is an event in X alone, with the fixed (σ(A, C)-measurable) pair (Q_j, H_j).

*Proof.* Induct on t. The horizontal vectors of π_j L are exactly π_j L_0 = H_j, because heights are preserved. A vector of
height k has squared norm k² + ‖kQ_j X − h‖² with h ∈ H_j. When horizontal vectors attain the minimum, both runs make the
same choice from the same candidate set, and the insertion acts only on the horizontal part. ∎

**Corollary 4.2 (monotonicity).** Suppose PL-BKZ never becomes visible (τ = ∞). Then its last full window [N−β+1, N] at
termination is T of the null final state, and a horizontal vector attains λ1(T). So
Pr[τ = ∞] ≤ Pr[decoupled final SVP does not return ±Pu].

**Proposition 4.3 (visibility is not recovery, and occurs before the final block).** Suppose in some null state the last
horizontal GS length satisfies g_{N−1} > 2/√3. Then the rank-2 window [N−1, N] is visible **for every X**.

*Proof.* Here H_{N−1} = ℤ·b*_{N−1}, so dist(Q X, H) ≤ g/2. Hence the shortest height-1 vector has squared norm
≤ 1 + g²/4 < g² = λ1(H)². ∎

The visible vector is (QX − h, 1), which is ambiguous modulo the prefix. After it is inserted, the trajectory is no longer
σ(A, C)-measurable. For q-ary profiles with a unit tail (g_{N−1} = 1) the trigger does not fire. In general, though, the plant
can affect the standard reducer before the final block, in ways unrelated to whether that block is good. A δ-type bound for
the unmodified standard reducer would therefore need control of post-visibility dynamics. The next construction avoids this.

### 4.2 The fork (checkpoint) reducer

Run any null trajectory on L_0, determined by (A, C). At σ(A, C)-measurable checkpoints t₁ < … < t_K:
1. call SVP on T_t;
2. orient the output to height +1 and lift it by Babai on the prefix (Part 47);
3. **verify** the candidate: it must lie in 𝔅 and satisfy [I|A]X' ≡ b;
4. output the first verified candidate, and otherwise continue the null run unchanged.

The cost is at most K extra rank-β SVP calls.

**Theorem 4.4 (stopping-time conditional reduction).** Let Good_t be the event that the block at checkpoint t satisfies
Good(L, g) and has prefix GS floor ≥ g'. Put δ_𝒯 = Pr_{A,C}[no t has Good_t]. Then
Pr[fork reducer fails] ≤ δ_𝒯 + ε(L, g) + ε_lift(g') + (7^N − 1)·q^−m.

*Proof.*
* **Selector.** Let t*(A, C) be the first good checkpoint (or t_K if there is none). It is σ(A, C)-measurable. The map
  (A, C) ↦ block at t* is a reducer in the sense of `conditionalReduction`, with D = designs × coins. Its geometry
  hypothesis holds with δ_𝒯.
* **Uniqueness and lifting.** Given (A, C), X is product CBD, so the uniqueness bound gives (1 − δ_𝒯)(1 − ε) for
  "±P_{t*}u is the unique shortest pair of T_{t*}". The Part 47 Babai bound adds ε_lift(g') on Good_{t*}.
* **Verification.** On these events the lift at t* is u, which passes verification. An earlier checkpoint can output a
  wrong verified candidate only if a second point of 𝔅 lies in the coset (Lemma 1.2). ∎

Note that δ_𝒯 ≤ min_t δ_t, so any single checkpoint can be used. In particular this includes the first-pass terminal of
Part 108, whose obligation is Part 117's p_suffix. The plant's randomness has been used completely: the residual δ_𝒯 is a
statement about the null trajectory alone.

### 4.3 The converse: the plant cannot lower the null requirement much

**Lemma 4.5a (lower tail of Z).** Fix a rank-d orthogonal projector Q, put μ = 1.5d and V = 4.5d, and take 0 < s < μ and
r > 0. Then:
* (Cantelli) Pr[Z ≤ μ − s] ≤ V/(V + s²);
* (Talagrand) Pr[‖QX‖ ≤ √(μ − s) − r] ≤ e^{−r²/24} / (1 − V/(V + s²)).

*Proof.* The first bound is Cantelli's inequality with the variance from Proposition 3.4.

For the second, write X_i = Σ_{l≤3} η_il − Σ_{l>3} η_il with η ∈ {0,1}^{6N} i.i.d. Bernoulli(1/2). Then ‖QX‖ = ‖QSη‖,
where SSᵀ = 6I. This is a convex function of η with Lipschitz constant ‖QS‖ = √6. Apply Talagrand's convex-distance
inequality (Ledoux 2001, Cor. 4.10, one-sided form P(B)·P(F ≤ M − r) ≤ e^{−r²/4} for 1-Lipschitz convex F with
F ≥ M on B) to F = ‖QSη‖/√6, with B = {‖QX‖ ≥ √(μ − s)}. The Cantelli bound gives P(B) ≥ 1 − V/(V + s²). ∎

Write τ_d(ℓ) for the minimum over s of the two bounds at threshold ℓ² − 1.

**Theorem 4.5 (necessity for K looks).** Consider any reducer whose interaction with the plant consists of K SVP calls on
blocks T_t = H_t ⊕ ℤ(Q_t X, 1), where (Q_t, H_t) is σ(A, C)-measurable and rank Q_t = d. The fork reducer and the
decoupled reducer (K = 1) are examples. Then for every ℓ,
Pr[success] ≤ Pr_{A,C}[max_t λ1(H_t) > ℓ] + K·τ_d(ℓ)·Pr_{A,C}[max_t λ1(H_t) ≤ ℓ].

*Proof.* Success at look t requires the output to be ±P_t u, which requires 1 + Z_t ≤ λ1(H_t)². On the event
{max ≤ ℓ}, apply Lemma 4.5a conditionally on (A, C) and a union bound over t. ∎

**Corollary 4.6 (exact remaining gap).** A proof of 99% success for such a reducer implies the null lower-quantile statement
Pr_{A,C}[max_t λ1(H_t) ≤ ℓ_K] ≤ 0.01/(1 − 0.01), where ℓ_K is the largest ℓ with K·τ_d(ℓ) ≤ 0.01. For comparison, the
"½" column gives the largest ℓ with K·τ_d(ℓ) ≤ 1/2.

| β (d) | K = 1 | 2 | 10 | 100 | 1000 | ½, K = 1 |
|---|---:|---:|---:|---:|---:|---:|
| 406 (405) | 13.555 | 11.819 | 10.308 | 8.413 | 6.737 | 23.787 |
| 506 (505) | 16.858 | 14.688 | 13.174 | 11.274 | 9.591 | 26.661 |

Part 101 certifies a q-ary head minimum of 8.1588 at width 506 (probability 0.990001). That is below ℓ_K for every K ≤ 1000
at β = 506, so the necessary null statement is not certified there even with 1000 looks. At β = 406 the certified
normalized radius (Part 92) is smaller still.

**Sufficiency side (heuristic only).** Multiple looks lower the *sufficient* floor only slightly. Model the standardized
(Z_t − μ)/√V as Gaussian and equicorrelated. The correlation for two independent generic rank-d projectors, computed from
Proposition 3.4, is ρ ≈ 0.353 at d = 405 and ρ ≈ 0.448 at d = 505. The height-zero floor for 99% conditional success is then:

| β | K = 1 | 2 | 10 | 100 | 1000 |
|---|---:|---:|---:|---:|---:|
| 406 | 26.605 | 26.003 | 25.079 | 24.272 | 23.695 |
| 506 | 29.486 | 28.948 | 28.123 | 27.400 | 26.880 |

Even 1000 generic looks gain about 9%. Real checkpoints of one run are more correlated, so the gain is smaller. Diversity
can help in principle: a family of all C(N, d) coordinate projectors makes min_t Z_t ≈ 185 instead of 757.5, because about
31% of the coordinates of X are 0. But such a family is not produced by BKZ.

## 5. Conjectures and the remaining gap

**Conjecture 5.1 (necessary null quantile, single look).** For BKZ-506 on L_0 of (511, 512, 3329), with the canonical input
and either the Part 108 first pass or full BKZ, Pr_A[λ1(H_final) ≤ 16.858] ≤ 0.0101. By Corollary 4.6 this is
**necessary** for any single-look plant-blind proof at 99%. It is weaker than the Part 103 floor 27.4538 needed on the
sufficiency side. Part 123's proportional-width experiments support the stronger physical floor empirically.

**Conjecture 5.2 (checkpoints are nearly redundant).** For BKZ-β tours on L_0, δ_𝒯 ≥ c·δ_final for an absolute c > 0 and
K = O(number of tours). This is supported only by the heuristic that late-tour final blocks are highly correlated. If it
holds, Theorem 4.4 gains at most a constant factor.

**Conjecture 5.3 (multi-look CLT).** For projectors with pairwise tr(Q_sQ_t) ≤ ρd, the joint height-zero failure
Pr[∀t: Z_t > λ_t² − 1] is within o(1) of the equicorrelated Gaussian value as d → ∞. A multivariate Berry–Esseen bound for
Rademacher quadratic forms would prove it. Section 4.3 shows that even this would move the sufficient floor by less than 10%.

**Exact remaining gap.** Plant randomness is fully exploited by Theorem 4.4, and Theorem 4.5 shows the exploitation is
essentially sharp. Wall 1 for plant-blind reducers is therefore equivalent, up to explicit errors, to a two-sided null
problem:
* **Sufficiency.** Bound δ_𝒯(L, g) — the probability that no checkpoint of the null run has a good block — at an (L, g)
  with ε(L, g) + ε_lift < 1%, for example L ≳ 27.5 at β = 506.
* **Necessity.** Before that, establish Pr[max_t λ1(H_t) ≤ ℓ_K] ≤ 1.01%. No symmetry, planting or exchangeability
  argument supplies either; both need the selection-weighted law of the null BKZ block, as in Parts 105–130.
* **Unmodified standard reducer.** It also needs control after premature visibility (Proposition 4.3). The fork reducer
  removes that need at the cost of K extra SVP calls.

### Reproduction

```python
from math import log2, sqrt, exp, comb
q, m, N = 3329, 511, 1023
p = [comb(6, 3 + z) / 64 for z in range(-3, 4)]
H = -sum(x * log2(x) for x in p)
print(N * log2(7) - m * log2(q), m * log2(q) - N * H)  # -3107.22, 3592.12

def tau(ell, d):
    mu, V = 1.5 * d, 4.5 * d
    c = 1.0 if ell * ell - 1 >= mu else V / (V + (mu - ell * ell + 1) ** 2)
    best = c
    for k in range(1, 2000):
        s = k * sqrt(V) / 100
        if s >= mu:
            break
        r = sqrt(mu - s) - sqrt(ell * ell - 1)
        if r > 0:
            best = min(best, exp(-r * r / 24) / (1 - V / (V + s * s)))
    return best
# bisect K*tau(ell, d) <= 0.01 for d = 405, 505 to reproduce the table
```

## Audit

**Verdict: MINOR CAVEATS.** The mathematics of every numbered result holds: Lemmas 1.2, 3.1 and 4.5a, Propositions 2.1–2.3,
3.2, 3.4 and 4.3, Theorems 4.1, 4.4 and 4.5, and Corollaries 4.2 and 4.6, with the precisions listed below. All numbers were
recomputed independently: an mpmath script that optimizes over s continuously rather than on the note's grid, plus a
quadrature for the equicorrelated Gaussian model. The scripts are kept in a scratch directory and are not committed. No attack
parameter was searched. The main issue is interpretive: the note places the **sufficiency** threshold at L ≈ 27.5 and calls
the necessity bound "essentially sharp". Both are wrong as stated (issue 1).

**Confirmed.**
* Lemma 1.2. Since q is prime and |w_s| ≤ 6 < q, a nonzero w_s makes A·w_s uniform. The exponent is
  1023·log₂7 − 511·log₂3329 = −3107.2221.
* Proposition 2.1, exactly.
* Proposition 2.2.
  * Item 1: Markov's inequality on the expected count |𝔅|·q^−m.
  * Item 2: H(CBD(3)) = 2.3333620 and m·log₂q = 5979.1462, so KL ≥ 3592.1168 bits.
* Proposition 2.3, trivially. So δ_planted = δ_null for decoupled reducers.
* Lemma 3.1, with gA = D_rP_r·A·(D_cP_c)⁻¹.
* Proposition 3.2. Equivariance in law follows from the reparametrization; isometry invariance of Φ and G-invariance of the
  law of A give δ_Φ(R^G) = δ_Φ(R); invariance of the product CBD law under the block-diagonal ĝ gives the joint statement.
* Proposition 3.4. μ₄ = 6, κ₄ = −3/4, Var Z ≤ 4.5d, and E_{B_N}[ĝᵀQĝ] = (d/N)·I.
* Theorem 4.1. Given the PL-BKZ definition, the visibility criterion is exactly k² + dist(kQX, H)² < λ1(H)².
* Proposition 4.3. A rank-1 H gives dist ≤ g/2, and 1 + g²/4 < g² holds iff g > 2/√3.
* Theorem 4.4. The trajectory is never modified, so t* is σ(A, C)-measurable. Before t*, a wrong verified output needs a second
  point of 𝔅 in the coset. ε_lift = 2(N−β+1)·exp(−g'²/12) agrees with Part 47's 2·exp(−g²/(4η)) at η = 3.
* Lemma 4.5a.
  * Cantelli holds with mean exactly 1.5d.
  * For Talagrand, S is the N × 6N ±1 sign matrix, SSᵀ = 6I and ‖QS‖_op = √6. Ledoux's Cor. 4.10 states
    P(F ≤ m)·P(F ≥ m + r) ≤ e^{−r²/4} for every m. Applied with the convex sublevel set {F ≤ M − r/√6}, it gives the lower
    tail e^{−r²/24}/P(B) as written.
* Theorem 4.5 and Corollary 4.6. From p₀(1 − Kτ) ≤ 0.01 we get p₀ ≤ 0.01/0.99.
* Necessity table. Recomputed values:

  | β | K = 1 | 2 | 10 | 100 | 1000 | ½ column |
  |---|---:|---:|---:|---:|---:|---:|
  | 406 | 13.5548 | 11.8194 | 10.3080 | 8.4127 | 6.7371 | 23.7867 |
  | 506 | 16.8577 | 14.6883 | 13.1743 | 11.2742 | 9.5913 | 26.6614 |

  These agree with Part 134's Theorem 2 (26.661 at 2%).
* Gaussian sufficiency table. ρ = 0.35322 (β = 406) and 0.44825 (β = 506). The rows reproduce to within 0.001.
* min_t Z_t ≈ 185.3, against μ = 757.5, and P(X_i = 0) = 0.3125.

**Issues and corrections.**
1. **The sufficiency threshold is mislabelled, and "essentially sharp" is overstated.** This concerns Conjecture 5.1 and the
   "Exact remaining gap" paragraph.
   * 27.4538 is Part 103's **necessary** per-block floor: below it, Cantelli forces conditional height-zero failure ≥ 1%. It
     is not "the floor needed on the sufficiency side".
   * "L ≳ 27.5 with ε(L, g) + ε_lift < 1%" is impossible. The Lean `reductionError` contains the height-zero term
     v/(v + a²), with a = L² − 1 − 1.5d. That term alone is < 1% only for L ≥ 35.112 at β = 506 (32.145 at β = 406), before
     the theta-excess terms are added. Even the Gaussian heuristic gives 29.486.
   * The rigorous necessity/sufficiency gap is therefore 16.86 vs ≥ 35.11 in radius at β = 506 (K = 1), roughly a factor of 2.
     "Theorem 4.5 shows the exploitation is essentially sharp" should read: Theorems 4.4 and 4.5 bracket plant-blind success
     between two null lower-tail statements, at radii about a factor of 2 apart.
2. **The "Consequence" in §2 is overstated.** Non-contiguity of the full laws of (A, b) does not prevent a b-dependent
   statistic from having nearly or exactly the same law under P and Q₀. For example, b₁ alone is exactly uniform under P
   whenever s ≢ 0. The correct statement: any statistic from which X can be recovered with non-negligible probability has
   law-TV close to 1 between P and Q₀, so a change of measure cannot transfer success of a b-reading reducer. Contiguity of
   other b-dependent statistics depends on the statistic.
3. **The model in Theorem 4.5 must be precise.** "Interaction with the plant consists of K SVP calls" must mean that success
   happens iff some look returns ±P_t u (then lifted and verified), with no other b-dependent post-processing. This holds for
   the fork reducer, because any other height-1 output lifts to a coset element ≠ u.
   * ℓ_K is one point of a family. Theorem 4.5 gives Pr[max_t λ1(H_t) ≤ ℓ] ≤ 0.01/(1 − K·τ_d(ℓ)) for **every** ℓ. For
     example, at K = 1 one also needs Pr[λ1 ≤ 24.81] ≤ 1.12% and Pr[λ1 ≤ 26.66] ≤ 2% (Part 134, Theorem 2).
   * So "exact remaining gap" with the single threshold ℓ_K understates the necessary statement.
4. **Ties in Corollary 4.2.** The corollary needs the convention that "decoupled SVP returns ±Pu" means ±Pu is the
   **unique** shortest pair. On τ = ∞ a horizontal vector can tie with Pu, and an SVP oracle might still return Pu.
5. **Applying `conditionalReduction` in Theorem 4.4.** The Lean theorem takes a uniform measure on a finite D and requires
   L² − 1 − 1.5d > 0, i.e. L > 27.54 at d = 505. The coins C must therefore be uniform on a finite set, or the theorem needs a
   weighted version.
6. **Smaller points.**
   * Prop. 2.2(3): 100·(KL + 1) = 359,311.7, so the required null probability is 2^−359,312, not 2^−359,313.
   * The necessary probability is 1/99 = 0.010101…, not 0.0101 (verdict, Corollary 4.6, Conjecture 5.1).
   * Some ℓ values are rounded up (16.858, 13.555, 8.413, 23.787). Thresholds of a necessity statement should be rounded down:
     16.857, 13.554, 8.412, 23.786. The effect is immaterial.
   * Conjecture 5.3 says "less than 10%". The K = 1000 gain is 8.8% at β = 506 but 10.9% at β = 406.
   * Part 101's 8.1588 is the horizontal-width-506 row. For final rank 506 (d = 505), the matching row is width 505, as Part
     101 itself notes. The conclusion (far below ℓ_K) is unchanged.
   * In PL-BKZ, "c may be size-reduced, which does not change the horizontal part" should read: size reduction changes c's
     horizontal coordinates but not (b_i), H_j or the coset π_j c + H_j. The definition should also say that no LLL swap
     involves c outside the SVP windows. The rank-2 window [N−1, N] already covers that swap.
   * Unlabelled heuristic: "its mark has norm of the order of the covering radius of H" (§2). The finite-group uniformity
     before it is correct, because W is rational and qℤ^N ⊂ L_0.
   * The heuristic and Gaussian parts are labelled adequately: §4.3 "Sufficiency side (heuristic only)", the ρ values, and
     Conjectures 5.1–5.3.
