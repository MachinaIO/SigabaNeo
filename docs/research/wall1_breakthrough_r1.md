# Breaking the circularity, round 1: what restarts buy, and why measure changes and potentials collapse onto Part 120

**Status: research note, not audited.** Every result labelled *Theorem* or *Proposition* has a complete proof here. Conjectures are labelled. Small numerical checks appear at the end. No attack parameter is optimized.

## Summary

The obligation left by `conditionalReduction` is δ ≤ 1% − ε, where δ is the fraction of designs whose reducer-selected final block H fails the plant-free test "minimum ≥ L, GS floor ≥ g". This note examines the four candidate directions of the brief and reaches one positive result and three reductions.

1. **(d) Restarts: positive, rigorous (Theorem 1).** Split the 511 rows into k disjoint blocks, run the plant-free reducer on each block, and decode with the *first* block whose final data pass the test. Failure is then at most ∏ᵢ δᵢ + ε* + (lift error). This holds **unconditionally**: there is no conditioning on s, no verification rows are needed, and ε* is paid once rather than k times. The per-block obligation relaxes from δ ≤ 0.009 to δ ≤ 0.0949 (k = 2), 0.208 (k = 3), 0.308 (k = 4), and so on. This is a non-rare-acceptance condition instead of a 1% tail. The price is fewer rows per block; the block size β needed at ⌊511/k⌋ rows is **not** evaluated here. Restarts that use only internal coins on the same rows cannot replace row splitting (Proposition 1.2).
2. **(b) Plant averaging: closed negatively (Theorem 2).** For every plant-free reducer, overall failure is at least Pr_A[λ₁(H_A)² ≤ μ − t] · t²/(v + t²). So no use of the randomness of s, e or the plant can avoid a null-only lower-tail bound on λ₁(H_A). At d = 505 this requires Pr_A[λ₁(H_A) ≤ 26.66] ≤ 2% and Pr_A[λ₁(H_A) ≤ 24.81] ≤ 1.12%. This is the design-averaged form of the fixed-H floor of Part 103 and `HeightZeroFloor`.
3. **(a) Change of measure: localized (Theorem 3).** Divergence accounting against any reference under which the last step fails with probability ≤ p behaves as follows:
   * per-state worst-case accounting is vacuous (it already pays log(1/p) ≥ 24.47 nats at the last step);
   * every typical-set refinement is equivalent to bounding the penultimate conditional failure tail Pr[Pr(F | S_{T−1}) > θ].

   That tail is exactly Part 120's last-step split.
4. **(c) Potentials: localized (Proposition 4).** Every valid supermartingale certificate dominates the Doob martingale Pr(F | S_t), so constructing one is the original problem. For the natural theta potential there is an exact one-step inequality with lift offsets. Its pathwise drift loses at least π·G_r²·(s/GH)²/(4·2^{2/r}) nats per step at every informative scale: 23.56 (s/GH)² at r = 505 and 18.96 (s/GH)² at r = 405, against a total budget of about 23.8 nats. The offset-½ vectors that cause the loss are exactly the old planes through the winner of area s·|w'|. This is Part 120's horizontal term again.

**Net.** This round does **not** break the circularity. It establishes three things.

* The obligation can be weakened rigorously from a 1% tail to a constant acceptance rate on independent row blocks (Theorem 1).
* Directions (a), (b) and (c) cannot bypass the single quantity of Part 120 in its natural formulations: the history-averaged count of small-area old planes through the final winner, together with the positive-height moment. Theorems 2–3 and Proposition 4 make this precise.
* With restarts, the budget for that quantity rises from 0.00488848 per term to about δ_k/2 (e.g. ≈ 0.047 at k = 2). That is a factor of about 10, not the 10^45 that the union bounds of Parts 124–126 miss by. Restarts are therefore a genuine relaxation for arguments that are already *nearly* tight, such as the Part 123 empirics (7/512 failures at the 0.954 target, n = 30). They give no relief to first-moment union bounds.

## 0. Setting

The setting follows [Part 47](wall1_decoupled.md), [Part 94](wall1_threshold.md) and `ConditionalReduction.lean`.

* A ∈ (ℤ/q)^{m×n} is uniform, with m = 511, n = 512, q = 3329.
* The plant X = (e, s) is CBD(3) with independent coordinates, independent of A, and u = (X, 1).
* A *plant-free reducer* is a measurable map from (A_R, coins) to final data. Here A_R is the row-restriction to a row set R, and the final data consist of:
  * a prefix basis with GS norms g₁, …, g_j;
  * the projection Q of trace d = β − 1;
  * the horizontal slice H, with a basis.
* `Acc(H, g)` is the predicate [λ₁(H) ≥ L, the GS floor of the given H-basis ≥ g, and the prefix GS norms satisfy min gᵢ ≥ g_lift].

  Every clause is a function of plant-free data. The first needs one SVP call in rank β − 1, the same oracle size as decoding.
* ε*(L, g, d) is the bound of `uniquenessProbability`: for fixed (Q, H) satisfying the first two clauses, the CBD failure of all-heights uniqueness is ≤ ε*.
* ℓ*(g_lift, j) = Σ_{i ≤ j} 2·exp(−gᵢ²/(4η)), with η = 3, bounds the Babai lift failure given D (Part 47 audit). On Acc it is at most 2j·exp(−g_lift²/12).

## 1. Restarts on disjoint rows

**Theorem 1 (row-split restart).** Let R₁, …, R_k be disjoint row sets of fixed sizes. For each i, run a plant-free reducer 𝓡ᵢ on L₀(A_{Rᵢ}) with coins Cᵢ. The coins are independent of each other, of A and of the plant. Let Accᵢ = Acc(Hᵢ, gᵢ) and δᵢ = Pr[¬Accᵢ]. Let I = min{i : Accᵢ} (I = ∞ if no block passes). On I < ∞, decode block I: call the SVP oracle on P_I L(A_{R_I}, b_{R_I}), orient the output to height one, and Babai-lift on the block-I prefix. Then

  Pr[the plant u_I = (e_{R_I}, s, 1) is not returned] ≤ ∏_{i=1}^k δᵢ + ε* + ℓ*.

In particular the secret s is recovered with at least this probability.

*Proof.* (1) **Independence.** Accᵢ is a measurable function of (A_{Rᵢ}, Cᵢ). Uniform A has independent entries, so the row restrictions A_{R₁}, …, A_{R_k} are independent, and the coins are independent of them. Hence the events ¬Accᵢ are mutually independent and Pr[I = ∞] = ∏ δᵢ.

(2) **One charge for the plant.** I is a function of D = (A, C) alone, and the plant is independent of D. Fix i and condition on D with I = i. The final data (Q_i, H_i, prefix) of block i are then fixed and satisfy Acc. The plant of block i is (e_{Rᵢ}, s), whose conditional law given D is still the product CBD law, since b is never read before I is chosen.
* By `uniquenessProbability`, the projected plant is the unique shortest pair of P_iL(A_{Rᵢ}, b_{Rᵢ}) up to sign, except with conditional probability ≤ ε*.
* When it is, the oriented oracle output is P_i u_i. By the Part 47 audit (Babai on the prefix, which is a fundamental domain of K = W ∩ L), the lift returns u_i except with conditional probability ≤ ℓ*.

Hence Pr[failure, I = i | D] ≤ ε* + ℓ* on {I = i}. Integrating over D and summing over finite i gives ≤ (ε* + ℓ*)·Pr[I < ∞]. Adding Pr[I = ∞] proves the claim. ∎

**Corollary 1.1.** If every δᵢ ≤ δ, 99% recovery follows from δ^k ≤ 0.01 − ε* − ℓ*. With ε* + ℓ* = 0.001 the per-block thresholds are:

| k | rows per block (⌊511/k⌋) | max δ |
|---|---:|---:|
| 1 | 511 | 0.009 |
| 2 | 255 | 0.0949 |
| 3 | 170 | 0.2080 |
| 4 | 127 | 0.3080 |
| 5 | 102 | 0.3898 |
| 6 | 85 | 0.4561 |

With ε* + ℓ* = 0.005 they are 0.0707, 0.1710, 0.2659, 0.3466 and 0.4135 for k = 2..6.

**Comparison with Parts 131–132.** The Part 131 audit bounded the joint failure of Part 39 blocks by E_s[f(‖s‖²)^k], conditionally on s, and then needed verification on unused rows. Theorem 1 differs in three ways:

* acceptance is *plant-free*, so independence is unconditional;
* the first-accepted rule needs no verification rows, so all 511 rows can be used;
* the plant error is charged once, not k times.

The price is unchanged from Part 131: each block sees fewer rows. Whether BKZ-β with β ≈ 406–506 reaches the acceptance regime with ⌊511/k⌋ rows is a parameter question, deliberately not evaluated here. Under GSA heuristics fewer rows need a larger β.

**Proposition 1.2 (internal-coin restarts cannot replace row splitting).** Let the same row set be used for t trials with independent coins, and let p(A) = Pr_C[Acc | A]. Then

  Pr[all t trials rejected] = E_A[(1 − p(A))^t] ≥ max(Pr_A[p(A) = 0], (1 − E p)^t).

For a deterministic reducer, such as Part 108's first tour with fixed ties, p ∈ {0, 1}, and t trials equal one trial.

*Proof.* Conditional on A, the trials are i.i.d. Bernoulli(p(A)). The first bound holds because (1 − p)^t = 1 where p = 0. The second is Jensen's inequality, since x ↦ (1 − x)^t is convex. ∎

So direction (d) on a single row set needs a lower-tail estimate Pr_A[p(A) < θ] for a reducer that is randomized in an essential way. That is again a statement about the reducer's output law. Disjoint rows are the only source of *free* independent trials. Signed permutations of rows and columns are the only Euclidean symmetries of the ensemble, and they map the reducer's output to an isometric copy of the same output.

## 2. Plant averaging cannot replace a null-only tail

**Theorem 2.** Let H_A be the final slice of any plant-free reducer on L₀(A) (coins included in A), with projection Q_A of trace d. Put μ = 1 + (3/2)d and v = (9/2)d. Then for every t > 0

  Pr_{A,plant}[all-heights uniqueness fails] ≥ Pr_A[λ₁(H_A)² ≤ μ − t] · t²/(v + t²).

*Proof.* Write R² = 1 + ‖Q_A X‖². By Part 94 (`allHeightsUniquenessCriterion`), uniqueness requires λ₁(H_A) > R; ties count as failure. By Part 47, conditional on A the vector X keeps its product CBD law. By `CBDQuadratic`, E[R² | A] = μ and Var[R² | A] ≤ v. One-sided Chebyshev (Cantelli) gives Pr[R² < μ − t | A] ≤ v/(v + t²). On {λ₁(H_A)² ≤ μ − t} the conditional failure probability is therefore ≥ Pr[R² ≥ μ − t | A] ≥ t²/(v + t²). Integrate over A. ∎

**Consequences.** A 99% guarantee with a single final block requires Pr_A[λ₁(H_A)² ≤ μ − t] ≤ 0.01·(1 + v/t²) for every t:

| d | t (in units of √v) | radius √(μ − t) | max Pr_A[λ₁(H_A) ≤ radius] |
|---|---:|---:|---:|
| 505 | 1 | 26.661 | 0.0200 |
| 505 | 2 | 25.752 | 0.0125 |
| 505 | 3 | 24.809 | 0.0111 |
| 505 | 5 | 22.807 | 0.0104 |
| 405 | 1 | 23.787 | 0.0200 |
| 405 | 3 | 21.919 | 0.0111 |

Direction (b) therefore cannot be a "terminal symmetry statement" that avoids a lower tail of the minimum of the selected block. The plant enters only through R, which concentrates around √μ independently of the design. Averaging over s and e can move the required radius by at most O(v^{1/4}), and cannot remove the requirement. Under Theorem 1 the requirement weakens accordingly: Theorem 2 applied to the accepted block only says that *Acc* must imply λ₁ > 27.45-ish, which it already does when L is chosen above the Part 103 floor.

## 3. Change of measure localizes to the penultimate state

Let (S_t) be the hidden Markov state of the reducer, for example Part 108's marked kernel (Λ_t, H_t, frame). Let Y_t be an observed statistic, and assume the failure event F is σ(Y_{1:T})-measurable. Let Q be any reference law of Y_{1:T}. The KL chain rule and convexity give the standard *state-wise accounting*

  D(P_Y ‖ Q_Y) ≤ Σ_t E_P[ D(P(Y_t | S_{t−1}) ‖ Q(Y_t | Y_{<t})) ],

and then P(F) ≤ (D(P_Y‖Q_Y) + log 2)/log(1/Q(F)). Assume the reference satisfies Q(F | y_{<T}) ≤ p for every y_{<T}. Any reference whose last step is a fresh Haar step at the 0.954 target has p ≤ 0.954^{505}/2 < 2.35·10⁻¹¹, so log(1/p) > 24.47.

**Theorem 3.**

(i) **Worst-case accounting is vacuous.** Take a reference whose last step fails with the *constant* conditional probability Q(F | y_{<T}) = p, for example a fresh Haar last step; then Q(F) = p. Suppose the last-step term is bounded by a supremum over reachable states, and some reachable s* has P(F | S_{T−1} = s*) = 1. Part 109 supplies such states: reachable histories force terminal ratios < 0.21 with one draw left. Then that supremum is ≥ log(1/p), and the resulting bound on P(F) is ≥ 1. The same holds for Rényi accounting of any order α > 1, through P(F) ≤ (Q(F)e^{D_α})^{(α−1)/α}.

(ii) **Typical-set accounting is equivalent to a penultimate tail.** Suppose the last-step divergence is ≤ D₀ for every state in a set G. Then G ⊆ {s : P(F | S_{T−1} = s) ≤ θ₀}, where θ₀ = (D₀ + log 2)/log(1/p). Consequently

  P(F) − θ₀ ≤ P(G^c),  and conversely  P(F) ≤ θ + P(P(F | S_{T−1}) > θ) for every θ.

*Proof.* (i) By data processing to the bit 1_F, D(δ₁ ‖ Ber(Q(F | y))) = log(1/Q(F | y)) ≥ log(1/p). The accounted total is therefore D ≥ log(1/p), and the KL bound (D + log 2)/log(1/Q(F)) is ≥ 1 because Q(F) = p. For Rényi divergences, D_α(δ₁ ‖ Ber(p)) = log(1/p) for every α, so (Q(F)·e^{D_α})^{(α−1)/α} ≥ (p·p^{−1})^{(α−1)/α} = 1.

(ii) Data processing gives D(Ber(a) ‖ Ber(p')) ≤ D₀, with a = P(F | s) and p' = Q(F | y) ≤ p. Also D(Ber(a) ‖ Ber(p')) ≥ a·log(1/p') − log 2 ≥ a·log(1/p) − log 2, because the binary entropy is at most log 2. Hence a ≤ θ₀. Then P(F) = E[P(F | S_{T−1})] ≤ θ₀ + P(S_{T−1} ∉ G). The converse is Markov's inequality applied to the conditional probability. ∎

So every change-of-measure argument, at any Rényi order and with any intermediate statistic, is exactly as hard as bounding the distribution of the **penultimate conditional failure probability** under the true law. By Part 120 that probability splits into:
* the horizontal term: Pr[the old shortest line wins] × 1{it lies in an old plane of area < A}, with A ≤ 1.04144·GH(W)² at width 506;
* the positive-height term, which has an exact fiber-retaining first moment.

The circular input is the law of small-area planes in the penultimate retained lattice. Part 117's KL test (full-mark transcripts, ≥ 851 nats) is the special case Y = S. Theorem 3 covers every coarser Y.

## 4. Potentials: the Doob obstruction and the exact theta drift

**Proposition 4(a) (any certificate dominates Doob).** Suppose Φ_t ≥ 0 is a supermartingale for the reducer's filtration (E[Φ_{t+1} | S_t] ≤ Φ_t) and 1_F ≤ Φ_T. Then Φ_t ≥ P(F | S_t) almost surely, for every t.

*Proof.* Φ_t ≥ E[Φ_T | S_t] ≥ E[1_F | S_t]. ∎

A drift certificate with a contraction, E[Φ_{t+1} | S_t] ≤ a_tΦ_t + b_t, likewise gives Φ_t ≥ (P(F | S_t) − B_t)/A_t, with A_t = ∏_{s>t} a_s and B_t = Σ_{s>t} b_s·∏_{s<u≤T} a_u. Hence on every reachable state Φ must upper-bound the conditional failure probability, and its drift must be provable there. Proving the drift for the *worst* reachable state is the pathwise program of Parts 109–110. Proving it *on average* requires P(F | S_t)-type information.

**Proposition 4(b) (exact theta step).** For a lattice Γ and σ > 0 put Θ_Γ(σ) = Σ_{x∈Γ} e^{−π|x|²/σ²}. Take one Part 108 step: W = Λ + ℤ(ũ + he), the winner v has |v| = s, and Λ' = QW with Q the projection onto v^⊥. Then:

1. Θ_W(σ) = Σ_{w'∈Λ'} e^{−π|w'|²/σ²}·ϑ_{a(w')}(s/σ), where ϑ_a(x) = Σ_{j∈ℤ} e^{−πx²(j+a)²} and a(w') = ⟨w, v⟩/s² mod 1 for any lift w.
2. Θ_{Λ'}(σ) ≤ e^{πs²/(4σ²)}·Θ_W(σ). The factor is attained up to 2 by any w' with offset ½: take W ⊇ ℤv + ℤ(v/2 + w') with w' ⊥ v.
3. Θ_W(σ) = Σ_{k∈ℤ} e^{−πk²h²/σ²}·Θ_{Λ+kũ}(σ), and E_U[Θ_{Λ+kU}(σ)] = |kH|⁻¹·Σ_{x∈π⁻¹(kH)} e^{−π|x|²/σ²} exactly (`averaged_layer_count`).
4. For every lattice Γ of rank r, Θ_Γ(σ) ≥ σ^r/det Γ. So the potential Θ_{Λ_T}(σ) − 1 certifies anything only when σ < (2·det Λ_T)^{1/r}. At such σ the pathwise factor in item 2 is at least

   exp(π·G_r²·(s/GH(Λ))²/(4·2^{2/r})),

   which gives 23.56·(s/GH)² nats per step at r = 505 and 18.96·(s/GH)² nats at r = 405.

*Proof.* (1) The fiber of w' is w + ℤv, and |w + jv|² = |w'|² + (a + j)²s², because Qw = w' and ⟨w, v⟩ = a·s² modulo s². (2) Some j has |a + j| ≤ ½, so ϑ_a(s/σ) ≥ e^{−πs²/(4σ²)}. Apply this termwise in (1). For attainment, an offset-½ fiber has ϑ_{1/2}(x) ≤ 2e^{−πx²/4}·(1 + o(1)) for large x. (3) Split W by height. The height-k slice is (Λ + kũ, kh), and the average over U uniform on H is the Lean layer identity. (4) Poisson summation gives Θ_Γ(σ) = (σ^r/det Γ)·Θ_{Γ*}(1/σ), and Θ_{Γ*} ≥ 1. With GH = G_r·det^{1/r}, at σ ≤ (2det)^{1/r} we get πs²/(4σ²) ≥ πG_r²s²/(4·2^{2/r}·GH²). ∎

**Diagnosis.** The total budget at the 0.954 target is about log(1/0.954^{505}) ≈ 23.8 nats. In the first tour s/GH(Λ) ≈ 1 under GSA-type heuristics (this is not proved here), so one worst-case step already exhausts it. An *averaged* theta drift requires the law of the offsets a(w') of the short old vectors relative to the winner. An old w' with offset near ½ spans with v a plane of area s·|w'|. So the bad offsets are exactly Part 120's "old planes of area < A through the winner". The theta potential therefore collapses onto Part 120's horizontal term, and the fresh-height terms in (3) are Part 120's positive-height moment. No new information enters.

## 5. The remaining gap, stated once

After Theorems 1–3 and Proposition 4, the open obligation is the following.

> **Open problem (relaxed Part 120).** For the plant-free reducer on a single row block of size m' = ⌊511/k⌋, let F be the acceptance failure ¬Acc of the selected final block. Bound
> Pr[F] ≤ E[horizontal small-plane term] + E[positive-height moment] ≤ δ_k,
> where δ_k = (0.01 − ε* − ℓ*)^{1/k} (Corollary 1.1). For k = 2, each term may use ≈ 0.047, against 0.00488848 in Part 120.

What is **rigorous** here:
* Theorem 1, Corollary 1.1 and Proposition 1.2 (restart reduction);
* Theorem 2 (the necessity of a null-only tail);
* Theorem 3 (localization of change of measure);
* Proposition 4 (Doob domination; exact theta step, its sharp pathwise factor, and the informativeness bound).

What is **not** done:
* any bound on the relaxed Part 120 quantities;
* any evaluation of the block size at ⌊511/k⌋ rows;
* any proof that the reachable states of Part 109 attain the offset-½ configuration of Proposition 4(b)(2). Sharpness is shown on abstract states only.

**Conjecture R1 (labelled; evidence only from Parts 119/123).** For the Part 108 first tour on a uniform m'×n graph with m' ≥ 255 and width b ∈ [406, 506], the history-averaged number of saturated old planes through the final winner, with area < 0.954·s_T·GH_T and internal minimum s_T, is at most 0.05. Part 123 reports 7/512 and 3/48 failures at the 0.954 target for n = 30, 36. These are consistent with R1 at δ ≈ 0.1 but not at 0.01, so restarts are precisely what makes R1 plausible as a target. No proof strategy for R1 is known that avoids the circularity diagnosed in Part 122.

## Sanity computations

The script below was run in the scratch area and is not committed. It reproduces the threshold table, the Theorem 2 table, p_ref and the theta constants.

```python
from mpmath import mp, mpf, sqrt, log, pi, gamma
mp.dps = 30
for eps in [mpf('0.001'), mpf('0.005')]:
    for k in range(1, 7):
        print(k, 511//k, (mpf('0.01')-eps)**(mpf(1)/k))   # Cor. 1.1
for d in [405, 505]:
    mu, v = 1+mpf(3)/2*d, mpf(9)/2*d
    for c in [1, 2, 3, 5]:
        t = c*sqrt(v); print(d, c, sqrt(mu-t), mpf('0.01')*(v+t*t)/(t*t))  # Thm 2
p = mpf('0.954')**505/2; print(p, log(1/p))            # 2.349e-11, 24.474
for r in [405, 505]:
    V = pi**(mpf(r)/2)/gamma(1+mpf(r)/2); G = V**(-mpf(1)/r)
    print(r, G, pi*G**2/4)   # 4.9127 / 18.956 ; 5.4774 / 23.564
```

Output, as cited above:
* δ_max: 0.0949 / 0.2080 / 0.3080 / 0.3898 / 0.4561 (ε = 0.001);
* radii: 26.661 / 25.752 / 24.809 / 22.807 at d = 505;
* p_ref = 2.349·10⁻¹¹, with log(1/p_ref) = 24.474;
* πG_r²/4 = 18.956 (r = 405) and 23.564 (r = 505).

The 2^{2/r} correction changes these by less than 0.4%.

## Audit

**Verdict: MINOR CAVEATS.** Theorem 1, Corollary 1.1, Proposition 1.2, Theorem 2, Theorem 3 and Proposition 4(a), 4(b)(1), (3) and (4) are correct as mathematics. The issues below are about overstated sharpness, overstated interpretation, small constant errors and the evidence claimed for Conjecture R1. None of them affects the main positive result (Theorem 1). The audit was independent and read-only; the numerics were recomputed with a separate mpmath script at 200 digits, kept in a scratch directory and not committed. No attack parameter was searched.

**Theorem 1 (checked, sound).**
* The reducer reads only L₀(A_{Rᵢ}), which depends on A_{Rᵢ} alone. The plant enters the full lattice only through b, and b is read only after I is fixed. Acc reads only (Hᵢ, the H-basis, the prefix GS norms), so I is σ(A, C)-measurable. The row blocks of a uniform A are independent, so Pr[I = ∞] = ∏δᵢ holds without conditioning on s.
* Selection by acceptance does not bias the plant. Conditional on D = (A, C), the plant X = (e, s) keeps its product CBD law (Part 47), and (Q_I, H_I, prefix) are D-measurable and satisfy Acc. So `uniquenessProbability` and the Part 47 Babai bound apply conditionally. The shared coordinates s across blocks do not matter, because nothing that determines I depends on s. The bound ∏δᵢ + (ε* + ℓ*)·Pr[I < ∞] is correct.
* Caveat (bookkeeping): if the blocks differ in size, d, L, g or prefix length j, then ε* and ℓ* must be read as maxima over the blocks.
* Caveat (cost): the test spends up to k SVP calls in rank β − 1 before the decoding call in rank β.

**Corollary 1.1 (recomputed).** The maximum δ values for ε* + ℓ* = 0.001 are 0.094868, 0.20801, 0.30801, 0.38981 and 0.45608. For 0.005 they are 0.070711, 0.17100, 0.26591, 0.34657 and 0.41352. All match the note.

**Proposition 1.2 (sound).** The proof is correct. The closing remark, that disjoint rows are the only free source of independence and that signed permutations are the only Euclidean symmetries, is informal and unproved. It should be labelled a remark. Part 132's negative result covers only column deletion.

**Theorem 2 (sound; scope overstated).**
* The CBD(3) variance bound v = (9/2)d is valid: Var = 2σ⁴·tr Q + κ₄·Σ Q_ii², with σ² = 3/2 and κ₄ = −3/4 < 0.
* Cantelli is applied correctly, and ties are correctly counted as failures.
* The theorem lower-bounds the failure of **all-heights uniqueness** of a single final block. It does not lower-bound recovery failure for decoders that do not need uniqueness, such as list decoding with verification (Part 131). The Summary's "overall failure is at least" should read "uniqueness failure of the single final block is at least".
* The radii 26.6614, 25.7519, 24.8090, 22.8067 (d = 505) and 23.7867, 21.9187 (d = 405) are confirmed.
* **Correction:** the c = 3 bound is 0.01·(1 + 1/9) = 0.011111, i.e. **1.11%**, not 1.12% as in the Summary. The table is correct.
* **Correction:** "averaging can move the required radius by at most O(v^{1/4})" is unproved as an upper bound, and the scale is wrong. The radius shift √μ − √(μ − c√v) is about 0.87c, which is O(1) (computed: 0.88, 1.79, 2.73, 4.73 for c = 1, 2, 3, 5 at d = 505). The shift in the *squared* radius is O(√v).
* "Acc must imply λ₁ > 27.45-ish" is loose. `uniquenessProbability` needs L > √μ = 27.5409 at d = 505. Part 103's 27.4538 is a different quantity.

**Theorem 3 (sound; content overstated).**
* The state-wise KL accounting needs the hidden-Markov hypothesis Y_t ⊥ Y_{<t} | S_{t−1}, for example Y_t a function of S_t with S Markov. This should be stated.
* In (ii), the hypothesis D₀ must hold for every y_{<T} compatible with s. One then averages P(F | s, y_{<T}) ≤ θ₀ over y_{<T}.
* The converse P(F) ≤ θ + P(Z > θ), with Z = P(F | S_{T−1}), is the pointwise bound Z ≤ θ + 1{Z > θ}, not Markov's inequality.
* p = 2.3491·10⁻¹¹, log(1/p) = 24.4744 and the budget 505·log(1/0.954) = 23.7813 are confirmed. The p bound follows from Haar calibration with ζ ≥ 1.
* **Overstatement:** because E[Z] = P(F), *any* bound P(F) ≤ ε already gives P(Z > θ) ≤ ε/θ. So "equivalence with a penultimate tail" is close to tautological, and (ii) is proved only for KL with last-step typical sets. The sentence "every change-of-measure argument, at any Rényi order and with any intermediate statistic, is exactly as hard as…" is a heuristic reading, not a theorem. Part (i) is rigorous for KL and Rényi worst-case accounting.

**Proposition 4.**
* (a) is correct. In the contraction version the index ranges are off by one. With a step t → t+1 using a_t, b_t, one has A_t = ∏_{u=t}^{T−1} a_u and B_t = Σ_{u=t}^{T−1} b_u·∏_{w=u+1}^{T−1} a_w. Here the a_u must be deterministic (or predictable) and ≥ 0.
* (b)(1) and (3) are correct, with v primitive in W and e ⊥ span(Λ, ũ). (4) is correct as an inequality. The informativeness threshold (2 det)^{1/r} is a convention: Θ − 1 < 1. Any constant other than 2 changes it by a factor c^{1/r}.
* **(b)(2) sharpness is misstated.**
  * For Θ itself (zero vector included), the ratio Θ_{Λ'}/Θ_W in the note's rank-2 example is ≈ 1, not ≈ e^{πs²/(4σ²)}/2. The k = 0 term dominates.
  * For the potential actually used, Θ − 1, the inequality Θ_{Λ'} − 1 ≤ e^{πs²/(4σ²)}(Θ_W − 1) does hold. However, the factor is attained only when the offset-½ vector has the extremal length |w'| = (√3/2)s, i.e. a hexagonal plane through the winner; λ₁(Λ') ≥ (√3/2)s always holds.
  * Computed, rank 2, s = 1, σ = 0.2, where the bound is 3.37·10⁸:
    * |w'| = √3/2: ratio 1.12·10⁸, which is the factor up to **3**, not 2;
    * |w'| = 0.9: ratio 2.97·10⁶;
    * |w'| = 1: ratio 1.
  * So "attained up to 2 by any w' with offset ½" is false. The termwise statement for one fiber is correct.
  * The Summary's "the pathwise drift **loses at least** … nats per step" should read: "the one-step worst-case factor is at most this, and it is attained up to log 3 on abstract hexagonal configurations".
* **Constants:** with the 2^{2/r} factor that the formula itself contains, the per-step constants are **23.499** (r = 505) and **18.891** (r = 405). The values 23.564 and 18.956 are πG_r²/4 alone (corrections 0.27% and 0.34%, confirmed). Since 23.50 < 23.78, one worst-case step at s/GH = 1 *nearly* exhausts the budget but does not exceed it; "already exhausts" should be softened. "s/GH" should also name the lattice whose GH is meant: σ is tied to det Λ_T at rank r, not to the step lattice Λ.

**Relation to Part 120 (overstated transfer).**
* Part 120's allocation is B(105) + 2·0.00488848 < 0.01. Its quantities are built for m = 511: the 400×105 initial graph, the 105-step freeze of Part 117, and the 0.954 ratio target at width 506.
* The relaxed budget "≈ δ_k/2 per term" assumes that this whole pipeline transfers to ⌊511/k⌋-row blocks and ignores the freeze charge. It also ignores the GS-floor and prefix clauses of Acc, which Part 120's split does not cover.
* With Part 120's own total of 0.00977696 the k = 2 per-term figure would be 0.0494. With ε* + ℓ* = 0.001 it is 0.0474 (ratio 9.70 to 0.00488848), as stated.
* Treat the "factor ≈ 10" as indicative until Parts 114/117/120 are redone at m′ rows.
* "Theorems 2–3 and Proposition 4 make this precise" overstates. The identification of each direction with Part 120's two terms is interpretive.

**Conjecture R1.** It is clearly labelled, and no rigor is claimed. The evidence sentence is partly wrong.
* 7/512 at n = 30 is **consistent** with a 1% rate: Pr[X ≥ 7 | 512, 0.01] = 0.255.
* Only 3/48 at n = 36 weighs against 1%: Pr[X ≥ 3 | 48, 0.01] = 0.012.
* Part 123 runs use m = n − 1 rows, not m′ ≈ n/2, and measure ratio-target failure, which includes positive-height failures, not R1's plane count. So they bear on R1 only indirectly.
* R1's cutoff 0.954·s_T·GH_T is not shown to imply a bound on Part 120's horizontal term, whose cutoff is A ≤ 1.04144·GH(W)².

**Status line.** "Every result labelled Theorem or Proposition has a complete proof" holds for the displayed statements, except the sharpness clause of Proposition 4(b)(2). The surrounding interpretive sentences (Proposition 1.2's remark, Theorem 2's O(v^{1/4}), Theorem 3's "every change-of-measure argument") are not proved and should be marked as remarks.
