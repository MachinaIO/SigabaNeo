# Recursive column deferral at final width 506

The zero-fresh-coordinate slice passes the **same physical radius** to every child. There is also a constraint across levels. If the final prefix is chosen on the deepest training set, all columns reserved along the way are fresh for the *same* projector. Their combined number, not just the largest batch size, enters the collision test. At width 506 the closed-ball first moment of Round 3 cannot certify 1% with a deepest quotient of rank below **89**, even granting a perfect old minimum. Rank 89 is a necessary condition for that certificate, not a successful base case. I obtain no improved certified width. The smallest width for which I can exhibit a schedule with certified total failure below 1% is **647**, using the fixed sample prefix.

## The state inherited by a child

Use the independent graph model of [Round 3, §A](wall1_idea_round3.md). Let the parent horizontal rank be d, let f columns be deferred, and put a=d−f. At final width 506 the primitive prefix K has rank 518. Before reading the f columns, choose K on the old graph. Condition on the training history, including the reducer's coins. Let Q project off K, let G be the projected old graph, and put B=G+Q(ℤ⁵¹¹ × 0), J=[B:G]. The rank of G is a. Write N_L(x) for the population including zero in the closed squared-radius-x ball of L, and c_f(j) for the number of integral f-vectors of squared length j.

For a fixed physical R<3329, write I for the indicator that G has a nonzero vector of length at most R. With independent uniform shifts in B/G, the exact expected number of competing horizontal pairs involving a fresh coordinate is

$$
 M_f(R)=\frac{1}{2J}\sum_{j=1}^{\lfloor R^2\rfloor} c_f(j)N_B(R^2-j).
$$

Every nonzero coefficient vector counted has a coordinate invertible modulo the prime. Its shift is uniform on B/G, and summing over B counts each possible lift in exactly one coset. Opposite vectors give one pair. The conditional probability bound is therefore I+(1−I)min(1,M_f). In particular, given a good old minimum, the exact condition to spend a conditional first-moment allowance ε<1 is that the displayed weighted sum before division be at most 2Jε. An average budget only requires the expectation of the capped bound. A bound on the minimum alone supplies neither J nor these counts. Only positive fresh layers earn the radius reduction to √(R²−j). If testing a multiple of the parent's own GH, evaluate R from the parent's determinant and dimension and carry that physical value downward. Replacing d by a in the plant norm threshold would change the event.

For terminal uniqueness, Part 103's necessary conditional cutoff at d=505 is
$$R_* = \sqrt{1+3d/2-\sqrt{9d/198}}\in(27.45,27.46).$$
Here 753 < R_*² < 754 by squaring the inner radical against rational endpoints. We use this optimistic test throughout the scan. It applies to the design-conditional 99% target. Its failure on a fraction of designs is not by itself that fraction of *joint* plant failures. Even passing the minimum test would leave height one, higher heights and lifting. Part 94's sufficient scalar test at the same width uses the much larger physical cutoff 909.286 rounded up. [Width scan](wall1_width_scan.md) · [Threshold](wall1_threshold.md)

## Why the schedule search reduces to one integer

Fix disjoint batches in advance and apply deferral inside the old training set with the same required prefix rank. A smaller old graph has fewer columns but still needs to supply all 518 prefix dimensions. At the leaf let G₀,B₀,J₀ be the state above and let F be the total number reserved. Its old graph uses 512−F columns and its quotient has rank a₀=505−F. Every intermediate old quotient embeds isometrically in the next. Conditional on the leaf, the parent has the graph description of Round 3 with **F** shifts into B₀/G₀. No projection is made between these appends.

More explicitly, after appending h of these columns, its superlattice is B₀ × ℤʰ. Adding the projected sample group fills each old fiber, since every realized shift already belongs to B₀. The quotient index remains J₀ by comparing the fibers at fresh coordinate zero. Hence its superlattice count is the convolution of N_B₀ with c_h, including the j=0 term. Iterating gives the same layer weights as counting the F columns at once. First-exit conditioning can change a capped probability estimate, but cannot eliminate collisions among the F columns. In particular all partitions with the same F give the same lattice law conditional on the leaf for a fixed leaf rule. The numerical first-moment exclusion below concerns the pooled Round 3 bound. Splitting its raw count into budgeted summands gives no saving. Even conditional on earlier appended columns, the newest-layer count has the same deterministic superlattice convolution on every surviving path.

If a reducer instead changes the prefix after seeing an inner batch, that batch no longer has the prescribed-shift law for the final projector. The nested isometries and the multiplication of conditional estimates would then require another theorem. Part 118 describes a prescribed rational plane and explicitly retains selection weights for adaptive planes. It does not give those weights for this modified reducer. [Prescribed projections](wall1_lit_projections.md)

## Collision and budget scan

At any node, a set of coefficient vectors of diameter ≤R with more than J distinct elements forces a collision. Equal shifts give a nonzero difference (0,z) after cancellation in the old lattice. The binary cube works when f≤R² and 2ᶠ>J. An integral ball of squared radius 188 has squared diameter at most 752, so N_ℤᶠ(188)>J also suffices here. Finally the b=0 summand alone gives M_f ≥ (N_ℤᶠ(753)−1)/(2J). This last exclusion is for a counting certificate and does not assert certain failure. In all three tests use the most favorable J≤3329ᵃ, since qB⊂G. They apply locally and also after pooling to the leaf.

| Parent rank tested at R_* | Largest f surviving binary test | Largest f surviving diameter-ball test | Largest f surviving origin term at 1% |
|---:|---:|---:|---:|
| 505 | 465 | 450 | 416 |
| 249 | 229 | 213 | 197 |

Thus splitting first at 256 leaves rank 249 and requires its minimum to clear the full 27.45 floor. Even if the local test permits 197 further columns, at most **160** further columns fit the pooled moment allowance. A rank-88 leaf already fails that allowance. A leaf below rank 55 necessarily produces a short horizontal vector by the diameter test. Neither exclusion needs a guess about GH, the leaf determinant, or the distribution of the selector.

The following integer scan checks every feasible total including the endpoints. Monotonicity also follows by embedding coefficient sets by zero padding while the group-size ceiling decreases.

```python
from math import isqrt

v = [1] * 754  # closed-ball populations in dimension zero
last = {}
for f in range(1, 506):
    v = [v[j] + 2 * sum(v[j-k*k] for k in range(1, isqrt(j)+1))
         for j in range(754)]
    for d in (505, 249):
        if f > d:
            continue
        ceiling = 3329 ** (d-f)
        for test, passes in enumerate((2**f <= ceiling, v[188] <= ceiling,
                                       50*(v[753]-1) <= ceiling)):
            if passes:
                last[d, test] = f
assert [[last[d,i] for i in range(3)] for d in (505,249)] == [
    [465,450,416], [229,213,197]]
```

## What remains at the leaf and what width is certified

The smallest moment-admissible leaf still has 96 training columns, 607 ambient dimensions, and an 89-dimensional quotient. Every admissible leaf must supply a physical minimum above 27.45 and its weighted superlattice counts on the surviving histories. Hermite gives an upper bound on the minimum for given determinant. Exact SVP at rank 89 could check a *realized* minimum but supplies no lower-tail probability over the training set. Exhausting all training matrices costs as many as 3329^(511·96) cases already at this endpoint. An exhaustive probability computation has not been made.

There is a quantitative limitation even if the leaf uses the specific first-tour rule in Parts 109–110. In their pathwise argument the branch for minimum at least one contributes a normalized certificate of 1/(G_a q^((a−1)/a)), where G_a is inverse unit-ball volume to the power 1/a. The combined worst-path certificate takes a minimum including this branch. Every projected graph has determinant at most qᵃ by completing a spanning set of projected q-axes and applying Hadamard. Even at that upper bound on own GH, the physical floor obtained from this combined formula is at most q^(1/a) < 1.10 for a≥89 (3329·10⁸⁹ < 11⁸⁹). The required radius is over **24.9 times** this optimistic ceiling. This comparison concerns the certificate; a particular leaf can have a much larger minimum. The published roughly 10⁻⁵ own-GH figures concern their original tour dimensions. [Terminal mixing](wall1_terminal_mixing.md) · [Additive tour](wall1_additive_tour.md)

At width 506 a leaf reducer can freeze one head per call in windows of size at most 506, with at most 518 freezes and one terminal call including height. Appending the reserved columns needs no oracle. This counts a single forward pass; an unrestricted reduction loop has no such count from the deferral argument. A call on the entire training graph, even the smallest moment-admissible one, exceeds the cap. Ball counts and probability averages above are proof obligations, not runtime oracles.

A schedule with a provable base is to reserve all 512 secret columns and take K from sample axes alone, retaining r sample axes. Then G₀=qℤʳ, B₀=ℤʳ and J₀=qʳ. Choosing r=134 gives final width 647. The fixed-prefix all-heights integer-ball certificate bounds joint failure by 0.00483352 rounded up, recovers the deleted errors, and uses **one** SVP call of dimension 647. Its integer scan first passes 1% there (at 646 its bound exceeds 0.0149). These figures are from [Part 39, including its exact integer recurrence](wall1_projected_reference.md). Width 647 is the best certified construction identified here. The interval from 506 through 646 has no optimality lower bound from this analysis. Even at 506 the schedules with a sufficiently large trained leaf remain unresolved; selecting their optimum would require the joint law of the leaf minimum, index and short-point counts. [Wall 1](../PROOF_GAP.md)

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT.

* **Isometric embedding.** The zero-fresh slice is exactly G × {0}. The cutoff is R_* = 27.4537594836.
* **Shared displacement group.** The index stays J_0 for a projector fixed before any deferred column is read.
* **Integer scans.** The largest surviving column counts for the binary, diameter-ball and origin-term tests are 465 / 450 / 416
  at rank 505 and 229 / 213 / 197 at rank 249. So 451 columns force a collision, 417 exhaust the budget, and at most 160 more
  fit after 256.
* **Leaf.** At rank 89 the pathwise cap is 1.0954, a factor 25.06 below R_*.
* **Width 647.** Part 39's recurrence gives failure 0.0149054 at 646 and 0.00483351 at 647, so 647 is minimal within that
  certificate family.

Width 506 stays open for a trained leaf with stronger probability estimates.
