# Final width and the height-zero probability bound

For a final block of rank β, put d = β − 1. The full horizontal rank in these notes is 1023, so the last requested width, 1023, still projects away one horizontal dimension. The empty-prefix statement has final rank 1024. Part 93 and Part 101 index their tables by horizontal width. For example, Part 101's physical lower bound 8.15876975 belongs to final rank 507 and requires Part 96's sharpened twin cap. [Part 47](wall1_decoupled.md) · [Part 93](wall1_combined_reducer.md) · [Part 101](wall1_qary_rogers.md)

## Necessary floor at every width

Condition on the design and the independent reducer coins. Let Q be the orthogonal projection matrix of rank d, and let Z = XᵀQX. Each independent CBD(3) entry of X is a sum of six independent symmetric signs divided by two. Its variance is 3/2 and its fourth cumulant is −3/4. Expanding the quadratic form and using Q² = Q gives

$$
\mathbb EZ=3d/2,\qquad
\operatorname{Var}Z=2(3/2)^2\operatorname{tr}(Q^2)
-\tfrac34\sum_i Q_{ii}^2\le 9d/2.
$$

Height-zero success requires Z < g² − 1, where g is the physical horizontal minimum. If g² − 1 is below the mean, Cantelli bounds this success probability by V/(V + (3d/2 + 1 − g²)²), with V = 9d/2. Requiring conditional success at least 0.99 and rearranging gives the necessary floor below. When g² − 1 is at or above the mean, the same necessary inequality holds immediately. A certified lower bound on g below this floor leaves the comparison undecided. [Part 94](wall1_threshold.md) · [Part 101 audit](wall1_qary_rogers.md)

The executable table prints a physical-length enclosure for every final width, valid for either lattice law. The endpoints are integers in units of 10⁻⁸. The ceiling uses the upper interval endpoint, so strict comparisons need no assumption about printing precision.

```python
from mpmath import iv

iv.dps = 50
scale = 10**8
for beta in range(450, 1024):
    d = beta - 1
    mean = iv.mpf(3) * d / 2
    variance_bound = 3 * mean
    scaled = scale * iv.sqrt(1 + mean - iv.sqrt(variance_bound / 99))
    lower = int(scaled.a)
    upper = int(scaled.b) + 1
    assert upper == lower + 1
    print(beta, d, lower, upper)
```

## What the reported probabilities cover

For a fixed width let the design meet its certificate with probability at least 1 − δ. If every such design has conditional plant failure at most ε, joint success is at least (1 − δ)(1 − ε), by conditioning. For δ = 0.009999 in Part 101, a 99% joint certificate therefore has only ε ≤ 1/990001 available using that design guarantee alone. The 99% necessary floor above tests a weaker conditional requirement. With a Haar design guarantee of exactly 0.99 as budgeted in Part 93, this accounting leaves zero conditional failure allowance. These statements concern one predetermined width. A search over deterministic theorem bounds can select a width before sampling. Choosing the width from observations of the sampled lattice requires joint control. [Part 93](wall1_combined_reducer.md) · [Part 101](wall1_qary_rogers.md)

For horizontal ranks 505 and 506, the height-one audit bounds failure by 0.00172658 and 0.00175356 respectively under g ≥ 24.66 and a GS floor of 9. Under g ≥ 61.3 alone its bounds are 0.00185397 and 0.00206404. Part 99's corresponding higher-height bounds of 0.003985 and 0.002114 apply on the norm cap and require additional multiplicity ceilings. A determinant-root benchmark controls the volume term in Part 97. The conditional first moment also contains weighted dual sums, and the probability outside the cap must be counted once. Part 95's tail-height bounds need the stated reduction hypotheses. [Height-one audit](wall1_voronoi_height1.md) · [Part 95](wall1_hkz_terminal.md) · [Part 97](wall1_dist_unique.md) · [Part 99](wall1_theta_heights.md) · [Part 100](wall1_residue_count.md)

The Haar and finite-graph design probabilities concern different probability spaces. Part 93 tabulates a Haar horizontal minimum through horizontal width 900. Its fraction column uses a GSA comparison length. Neither that fraction nor the radius alone measures conditional plant success. The height-zero table above applies unchanged after expressing both lengths in physical units. This note establishes the necessary-floor scan and the probability accounting. The extended horizontal-minimum curves, higher-height scan, and first jointly certified width are unresolved here.

## Extension of the q-ary curve past 647 (Claude, Nov 2026; corrected after audit)

This extension reruns Part 101's `row(b)` unchanged (terminal-variant branch for b ≥ 512) at widths up to 1020.

* **Rank convention.** `row(b)` certifies a horizontal lattice of rank d = b, so the final oracle rank is β = b + 1. The table
  compares each row with the Cantelli height-zero floor √(1 + 1.5d − √(4.5d/99)) for the same d.
* **Validity.** The audit checked every b in 450..1020:
  * `2t < q` holds throughout (max 2t < 898.6).
  * The Hermite caps C[r] exist down to r = 4.
  * Both oracle ranks fit the width budget.

| final rank β | certified λ1 (physical) | necessary floor | ratio |
|---:|---:|---:|---:|
| 506 | 8.088 | 27.454 | 0.295 |
| 507 | 8.159 | 27.481 | 0.297 |
| 647 | 10.621 | 31.058 | 0.342 |
| 954 | 37.715 | 37.735 | 0.999 |
| 955 | 38.148 | 37.755 | 1.010 |

* **Height zero.** The certified minimum first exceeds the necessary height-zero floor at final rank 955. Exceeding a necessary
  floor does not certify height-zero success.
* **Height one.** Part 102's profile-free bound, optimized, gives log c = (d/2)(1 − a + log a) with a = L²/(6d). At budget
  0.0025 it needs L ≥ 82.56 at d = 975 and L ≥ 83.53 at d = 1000. The first passing row is final rank 999.
* **Probability.** If the whole conditional allowance 1/990001 left by the design guarantee goes to height one, the first
  passing row is final rank 1000, with nothing left for the other failure modes.

**Conclusion.** The present Part 101 certificate gives no improvement over Part 39's dimension 647. At final rank 647 it gives
10.62, against a necessary floor of 31.06. This is a limitation of this certificate only. It gives no upper bound on the actual
minimum of the selected block, and it does not rule out other decoupled certificates.

## Audit note (Nov 2026)

Independent audit (Codex) of the first version: FLAWED. It mixed horizontal rank with final oracle rank, misplaced the height-one
crossing, and overstated the 647 conclusion. All three are corrected above. The audit confirmed the Cantelli floor
(27.45375948 at β = 506), the probability-budget remark, and the extension of Part 101 to width 1020.
