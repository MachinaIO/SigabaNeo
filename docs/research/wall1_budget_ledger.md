# Wall 1 probability ledger through Part 223

**The original Part 192 remainder of `6.515e-12` can be retained with the proved Mordell/Blichfeldt coefficients.** The existing radius-250 raw-exit certificate proves `2.35454e-12` where its exported theorem states `4.249e-12`. Changing just that numerical endpoint releases `1.89446e-12`. The prefix needs an extra `3.113715e-14`. The improved exit and the resulting prefix-explicit terminal inequality were kernel-checked in scratch. The weaker-profile prefix estimate was checked with outward intervals. Its geometric coverage and numerical sum still need to be connected in Lean. [Raw-exit certificate](../../SigabaNeo/Lib/Lattices/Research/Wall1/ControlledRawBall.lean) · [Current terminal theorem](../../SigabaNeo/Lib/Lattices/Research/Wall1/ControlledTerminalCaps.lean) · [Hermite budget script](scripts/wall1_hermite_budget.py)

| Quantity | Recommended allowance | Status |
|---|---:|---|
| Full horizontal residual, Part 192 $Z_1$ | `9e-11` | Open absolute target |
| Horizontal remainder $D$ after Parts 194 and 198 | `7.1275e-11` | More than `4.02078e-12` available for the unbounded pieces after Part 223 |
| Full vertical residual, Part 192 $Z_2$ | `9e-11` | Open absolute target |
| Vertical remainder $Z_{\rm rem}$ after Part 193 | `6.485e-11` | Includes the proved `3.75987e-11` large-$g$ charge |
| Small-$g$ portion of $Z_{\rm rem}$, $g<34.807$ | `2.72513e-11` | Open |
| Whole prefix, raw term plus flag sum | **`3.782e-14`** | Outward upper bound with proved coefficients. The maximum allowance for the original terminal theorem is **`1.901139534238e-12`** |
| Terminal remainder beyond the two full residuals | **`4.652e-12`** | Consequence on paper. Implies the original `6.515e-12` statement |

## Where the top-level number comes from

1. Parts 181–182 propose accepting a block when the shifted-ball score $C\le\tau=0.00012938$. On acceptance the failure charge is less than $0.00047835048014+\tau<0.000607731$. For the separate design rejection target $0.005$, Markov gives the sufficient mean condition $\mathbb E C\le0.005\tau=6.469\times10^{-7}$. At height zero, $C\ge0.74921186\,N_H(26)$, where the nonzero point count includes both signs. The proposed mean condition therefore **requires** $\Pr(F)\le6.469\times10^{-7}/(2\times0.74921186)<4.317204\times10^{-7}$ for $F=\{\lambda_1(H_{407})\le26\}$. The converse would require control of signed multiplicities, other lengths and shifted heights. The prefix lift is another event. [Part 181, §§4–5](wall1_test_acceptance.md) · [Part 182, score and audit](wall1_restart_passes_test.md)
2. Write $E=\{\lambda_1(P_{x^\perp}H_{406})\le26\}$ for the penultimate spacing event, with $x$ the designated shortest vector. This is $J$ in Part 183. Part 184 sets the round working target $\Pr(E)\le4\times10^{-7}$. Part 183 bounds $\Pr(F\triangle E)<3.210\times10^{-14}$ on paper. The explicit concrete Lean theorem `matrix_discrepancy_lt` supplies the weaker `5.244e-9`, which also fits the gap to `4.317204e-7`. This transfer is used only when going from $E$ back to $F$. No last-draw charge is due in a bound for $E$ itself. [Part 183](wall1_terminal_tail_047.md) · [Part 184 audit](wall1_penultimate_projection.md#audit) · [ConcreteTerminal506](../../SigabaNeo/Lib/Lattices/Research/Wall1/ConcreteTerminal506.lean)
3. Put $a=1352/\sqrt3$ and $A_i=\{\text{some saturated plane after draw }i\text{ has area}\le a\}$. For a spacing witness of length $h\le26$, shortestness and a centered lift give $\|x\|\le 2h/\sqrt3$. The primitive witness plane then has area $\|x\|h\le a$ (saturation can only decrease area). Thus $E\subseteq A_{406}$ **pathwise**. For the direct absolute target one can budget all of `4e-7` for $A_{406}$. The alternative good-event calculation uses $G$ from Part 184 and `4e-7 - 4.249e-12 - 8.147e-14 = 3.9999566953e-7` for $G\cap E$. Part 192's unconditional bound already pays these exits. [Parts 184–185](wall1_winner_alignment.md#audit) · [Part 191, scalar implication](wall1_plane_comparison.md#audit)

**The comparison conjecture has a different right-hand side.** Parts 186–187 rounded a sufficient reference exponent of about $15.06928$ down to $15$. Part 190's sharper Haar spacing probability at the determinant floor is about `9.97119e-63`; multiplying by $3329^{15}$ costs less than `6.81482e-10` and leaves over `3.99314e-7` of *conditional comparison allowance* after exits. The earlier comparison left about `1.71956e-7`. Parts 188–191 supply counting identities and reference laws. The selected-chain comparison remains open. Part 191's area **count** criterion uses the determinant-matched mean $U(D)$; Part 192's stronger area **probability** conjecture uses $p(D)$. [Part 186](wall1_quotient_slack.md) · [Part 190](wall1_rank2_transverse.md) · [Part 191](wall1_plane_comparison.md)

At $D_*$, $3329^{13.6133}p(D_*)$ lies between `1.7843192052e-10` and `1.8478163199e-10`. The latter bounds the right side from **above** over admissible determinants. Part 192's sufficient lower comparison retains $\omega=\mathbb E[(D_*/D_{406})^2]$, with coefficient `1.78431e-10`. Even the old absolute target `2 × 9e-11 + 6.515e-12 = 1.86515e-10` exceeds the floor upper endpoint. The two equal `9e-11` allocations in Parts 193–194 are proposed absolute targets. They do not follow from the Haar calculation. Meeting them would leave `3.99813485e-7` under the direct $E$ target, while establishing the determinant-matched conjecture would require additional information about the actual determinant and selected law. Part 210 also shows why its spacing and area distortion factors cannot be interchanged. [Part 192, residual and audit](wall1_rank2_tail.md#audit) · [Part 193](wall1_z2_vertical.md) · [Part 194](wall1_z1_horizontal.md) · [Part 210](wall1_distortion_sharpening.md)

## Part 192 under the actual finite law

Take the first $A_i$, imposing $G\cap A_{406}$ on the unresolved histories. $Z_1$ is the horizontal first hit on draws 155–406 on which every shortest vector of every hit plane is inherited. $Z_2$ is the positive-height first hit on draws 395–406 with winner length in $(30,R]$, $R=(\sqrt2 a)^{1/2}$. These two events are disjoint and permit intervening misses. The other summands are upper bounds from a union. The rank-506 coefficient 56.2142 and the required determinant floor are proved. [ControlledPlaneTail](../../SigabaNeo/Lib/Lattices/Research/Wall1/ControlledPlaneTail.lean) · [ControlledConcreteBounds](../../SigabaNeo/Lib/Lattices/Research/Wall1/ControlledConcreteBounds.lean) · [Rank-506 certificate](../../SigabaNeo/Lib/Lattices/Research/Wall1/HermiteSphereCertificate506.lean)

| Charge outside $Z_1+Z_2$ | Existing published or Lean upper bound | Revised charge |
|---|---:|---:|
| Raw nonzero graph vector, radius 250, first 511 columns | `4.249e-12` | **`2.35454e-12`** |
| Simultaneous dual-floor exit through draw 406, bounded by the 408-index exit of Part 172 | `8.147e-14` | `8.147e-14` |
| Positive-height winner through draw 394 at $R$ | `2.066876811e-12` | `2.066876811e-12` |
| Positive-height winner through draw 406 at radius 30 | `7.189180962e-15` | `7.189180962e-15` |
| Horizontal winner with a fresh shortest plane vector through draw 406 | `1.037844738e-13` | `1.037844738e-13` |
| **Subtotal before prefix** | **`6.508320465762e-12`** | **`4.613860465762e-12`** |
| Available for prefix under `6.515e-12` | `6.679534238e-15` | **`1.901139534238e-12`** |

The first two entries are the two terms of `bad_bound`. The three late entries are `LateEnclosures.positive394_sum`, `positive30_sum` and `horizontal406_sum`. The earlier outward ceilings, `2.067e-12`, `7.190e-15`, `1.038e-13`, left `6.540e-15` for the prefix. Re-evaluating the *same* three sums beyond today's Lean precision recovers less than `7.24e-22`. Likewise Part 183's Gaussian raw endpoint `4.24859835e-12` and Part 172's dual endpoint `8.146494523e-14` recover less than `4.07e-16` together. The larger saving comes from the inward-volume estimate already in Lean. [Late enclosures](../../SigabaNeo/Lib/Lattices/Research/Wall1/ControlledLateEnclosures.lean) · [Part 172 audit](wall1_transference.md#audit) · [Part 183 audit](wall1_terminal_tail_047.md#audit)

**Exact raw certificate.** In `ControlledRawBall.raw_numeric`, retain $d=911$, $k=455$, and $b/c=501/2$ exactly as in `raw250_numeric`. Its integer comparison bounds the probability by
$$
 B=\frac{2(501/2)^{911}(22/7)^{455}2^{456}}{911!!\,3329^{400}}
  <\frac{235454}{10^{17}}.
$$
The exact rational begins `2.3545390314544161e-12`. This bound counts both signs and needs no change to the event, the geometry or the rank-506 determinant recurrence. Reusing `good_first_moment` and then adding the two exits with this endpoint gives the revised subtotal. Direct subtraction from the already published `terminal_bound_with_prefix` would be invalid because that theorem has already discarded the individual exit charges. [Raw integer certificate](../../SigabaNeo/Lib/Lattices/Research/Wall1/ControlledRawBall.lean) · [Good-event inequality](../../SigabaNeo/Lib/Lattices/Research/Wall1/ControlledPlaneTail.lean)

**The prefix calculation.** Use the proved sharp ranks 5 and 6, $g_7=(64/3)^{1/5}$, $g_8=(64/3)^{7/30}$ and $g_{24}=(2/\pi)(13!)^{1/12}$. The outward calculation gives raw radius in $(2895.32735,2895.32737)$, raw term below `6.290e-34` and the 12,089-term flag sum in $(3.78166796205860,3.78166796205861)\times10^{-14}$. In particular the **whole** prefix costs less than `3.782e-14`. The old budget falls short by about `3.11371454e-14`. With the revised raw exit the combined terminal charge is below `4.651680465762e-12`, leaving over `1.863319534238e-12` even under the original target. The Part 197 area-preserving construction also gives a much smaller paper bound of `5.412e-36` through 154 at a larger area cutoff, but its tabulated inputs include the sharp rank-24 coefficient. [HermiteSevenTwentyFour](../../SigabaNeo/Lib/Lattices/Research/Wall1/HermiteSevenTwentyFour.lean) · [Outward calculation](scripts/wall1_hermite_budget.py) · [Part 197](wall1_enlarged_cutoff.md)

## Horizontal residual

| Step | Proved charge or open balance |
|---|---|
| Part 194, two controlled mixed classes | $S_{504}(406)+S_{505}(402)<1.3669674748\times10^{-11}$. Rounding up to `1.3670e-11` leaves `7.6330e-11` of the full `9e-11`. |
| Parts 198, 205–206, 208 | First hits on 155–171 cost at most the through-171 bound `5.055e-12` (audited upper endpoint `5.05421450e-12`). Hence $b_H=7.6330\times10^{-11}-5.055\times10^{-12}=7.1275\times10^{-11}$. This covers wholly old first hits on 172–406 and the remaining mixed class on 403–406. |
| Parts 215 and 218 | Part 218 replaces Part 215's draw-403 `2.87954220e-11` charge. The full eligible mixed charges on 403/404/405 are respectively below `2.723e-14`, `1.233e-12`, `5.536e-11`. Draw 406 unrestricted gives only `2.46814e-9`. The covered ranges on 406 and seven wholly old lookback bounds are included in a **single** joint upper bound `6.4261010401e-11`. The resulting balance exceeds `7.013989599e-12`. |
| Part 221 | Extending the paid range from $g\ge32.8$ to $g\ge32.75$ costs less than `2.99248645e-12` extra. Four terminal rank exits together cost less than `6.227e-16`, once across both surviving and replacement planes. The published conservative balance exceeds `4.02079e-12`. |
| Part 223 | Terminal hit at full-lift syndrome codimension $\le128$ costs $<10^{-505}$. Wholly old creation on 406 at old-triple codimension $\le128$ costs $<10^{-683}$. The mixed old-kernel sector at codimension $\le129$ costs $<10^{-89}$, extended through 130 for $g\ge32.68$ at cost $<10^{-36}$. The earlier creation cutoffs over 235 draws cost $<2.35\times10^{-28}$. One combined charge $<2.36\times10^{-28}$ covers these sectors. The reported remaining allowance exceeds **`4.02078e-12`**. |

The individual Part 218 draw-406 bounds in the joint sum cover height at least 5 (`2.419e-12`), large scale (`2.769e-12`), plane minimum outside $(28.22,29.2)$ (`5.362e-13`), all visits at $g\le32.22$ (`1.052e-13`) and mixed low-scale mass at $g\le32.32$ (`9.018e-13`). The seven lookback rows, in table order and units of $10^{-13}$, are bounded by 1.853, 0.6579, 5.708, 0.3236, 0.3120, 0.2430 and 0.03731. The joint total uses the unrounded sums. The remaining mixed hits require draw 406, $32.32<g<32.75$, heights 1–4, and an inherited minimum in $(28.22,29.2)$ at unpaid codimensions. The wholly old mass includes terminal replacement after the original plane collapses. The small-codimension charges bound joint events and give no upper bound on their high-codimension complements. [Part 194](wall1_z1_horizontal.md#audit) · [Part 198](wall1_flag_horizon.md#audit) · [Part 206](wall1_raw_section_compression.md#audit) · [Part 208](wall1_z1_terminal_law.md) · [Part 218](wall1_z1_remainder.md#audit) · [Part 221](wall1_z1_last_pieces.md#audit) · [Part 223](wall1_wholly_old_mass.md)

## Vertical residual

Part 193 removes draw 395, the short and the tall positive-height sectors. In units of $10^{-12}$ its four upper endpoints are 6.96162852 (draw 395), 2.19991893 ($s\le30.5$ on 396–406), 5.79448011 ($30.5<s\le0.945g$), and 10.18907221 ($k\ge13$). Overlap is safe in this upper sum. The unrounded total is below `2.51450997258e-11`, published as `2.515e-11`. Hence $b_V=9\times10^{-11}-2.515\times10^{-11}=6.485\times10^{-11}$. The eligible eleven draws have $1\le k\le12$ and $\max(30.5,0.945g)<s\le R$. [Part 193, charges and audit](wall1_z2_vertical.md#audit)

| Result | What can be charged |
|---|---|
| Part 212 | For $g\ge35.15$ the eleven-draw hit bound is below `6.574481e-12`, including exceptional prefixes. Outside a set $\mathcal X$ of probability $<10^{-749.44}$, squared frozen covolume is at least $2^{99}$ on 395–406 and terminal mark rank is at least 115. Exceptional contributions $<10^{-466.5}$ and $<10^{-95.3}$ concern the single-ball and combined *moment tests* of Part 209. For the horizontal terminal-area indicator the exceptional contribution is $<10^{-749.4}$. None is an extra debit to an unconditional hit bound already covering $\mathcal X$. |
| Part 215 | For $g\ge34.807$, the eleven-draw charge is at most `6.44697363e-11`. The `2.78189202e-12` bound on two qualifying vertical wins at $g\ge34$ is a different joint event. |
| Part 216 | For the **same** $g\ge34.807$ slice the improved bound is below `3.7598695609e-11`. Use `3.75987e-11` once. This releases `2.68710363e-11` against the rounded Part 215 charge. It grows the small-$g$ allowance from `3.802637e-13` to **`2.72513e-11`**. The latter is still an obligation. |
| Parts 216–217 | A crossing below 34.807 requires at least 100 winners above $1.10g$ in the first 405 draws. A uniform predictable ceiling 0.126 gives `2.58815e-11`. Restricted ceilings 0.126 on 11–380 or 0.1795 on 11–405 give `2.456e-11` or `2.478e-11`, respectively. These are alternative implications with open hypotheses. |
| Parts 219–220 | The covering estimate did not establish those ceilings. The two-tail hypothesis of Part 220 gives `4.21342e-14`, and its conditional fourth-moment hypothesis gives `2.69977e-11`. Neither is an unconditional crossing bound. |
| Part 222 | The three restricted hypotheses (two tails on 67–405, fourth moment on 54–405, single tail on 49–380) respectively give `2.3750e-11`, `2.4681e-11`, `2.0204e-11`. The separate `2.417e-11` exceptional-set result on 11–19 is inside the unconditional part of each argument and costs nothing extra there. |

Part 221's hypothesized long-winner ceilings for the horizontal mixed piece likewise give alternative conditional bounds; the table uses its unconditional 32.75 calculation. The other approaches in Parts 195–211 and 213–214 do not supply an absolute upper bound on either full residual. In particular the Haar benchmarks of Part 209 and the independently randomized endpoint of Part 214 have different laws from the selected finite chain. [Part 209](wall1_zrem_flag_moment.md) · [Part 212 audit](wall1_integrality_bound.md#audit) · [Part 214](wall1_hecke_gated_mixing.md) · [Part 215](wall1_fresh_mark_extension.md) · [Part 216](wall1_small_g_frequency.md#audit) · [Part 217](wall1_long_winner_ceiling.md) · [Part 219](wall1_covering_ceiling.md) · [Part 220](wall1_long_winner_routes.md) · [Part 222](wall1_long_winner_handle.md)

## Which transfers are legitimate?

* **Within the original terminal theorem.** Tightening the raw exit supplies `1.89446e-12` unconditionally. Both full residuals stay symbolic. An independent option is to use Part 193's radial bound on the **event** of a positive-height winner at $R$ for draws 1–394. Here $52/\sqrt3\le R<3329$, each positive height is invertible, and $g_i^{506}\ge e^{L_{i-1}}/V_{506}$. Summing $1.422743743939\,V_{506}R^{506}e^{-L_{i-1}}$ gives less than `1.474613e-13`, saving more than `1.9194e-12` against the Gaussian `2.066876811e-12`. This is a different first-moment majorant. Its use in Lean would require exposing the sum of event probabilities in `good_first_moment`; it cannot prove that the old Gaussian sum is smaller than its computed value. The raw-exit route already suffices. [Part 193, physical-radius estimate](wall1_z2_vertical.md#charging-the-parts-removed-in-1) · [ProjectedBallCount](../../SigabaNeo/Lib/Lattices/Research/Wall1/ProjectedBallCount.lean)
* **Across residuals in an absolute total.** Even using the old raw exit, one can transfer `1e-13` from the vertical target to the terminal remainder while retaining the old combined target `1.86515e-10`. An explicit alternative is $Z_1$ allowance `9e-11`, horizontal remainder `7.1275e-11`, $Z_2$ allowance `8.99e-11`, $Z_{\rm rem}$ allowance `6.475e-11`, small-$g$ allowance `2.71513e-11`, terminal remainder `6.615e-12`, whole-prefix allowance `1.06679534238e-13`. All the quoted conditional small-$g$ routes still fit. This changes an open residual target. It proves no unconditional saving on the small-$g$ event and preserves only the aggregate, whereas the raw-exit route preserves the literal Part 192 theorem.
* **From the direct top-level target.** With the two proposed full residual targets and the revised `4.652e-12` terminal charge the direct bound would be `1.84652e-10`, giving slack `3.99815348e-7` versus `4e-7`. For that objective alone even `6.547e-12` beyond the residuals would suffice with the old exits and the weaker-profile prefix. No bound on other score terms is needed for this direct implication. Conversely, this headroom cannot be counted as proved small mass in the score or transferred to the determinant-matched conjecture.
* **Overlaps and rounding.** Part 198 bounds *all* first hits through 171. A fresh combined first-hit proof could charge this once for the prefix and the horizontal subrange 155–171; the displayed modular ledger conservatively retains both. The alternative through-170 bound `2.413e-15` leaves draw 171 as an extra residual obligation. Part 194's mixed rounding saves less than `3.26e-16`, Part 198's through-171 rounding less than `7.86e-16`, and Part 193's controlled rounding about `4.90e-15`. These differences and the small uncovered horizontal balance refer to different levels of the ledger. [Part 198, alternative horizons](wall1_flag_horizon.md) · [Part 194 audit](wall1_z1_horizontal.md#audit) · [Part 193 audit](wall1_z2_vertical.md#audit)

## Exact statements for Lean

In namespace `SigabaNeo.Wall1.ControlledPlane`, the following are proposed names. The first statement was checked in scratch from the existing proofs, with only `propext`, `Classical.choice`, and `Quot.sound`. The second is the remaining prefix bridge. The third then follows by linear arithmetic and implies the literal `6.515 / 10^12` terminal theorem without any Hermite hypothesis.

```lean
theorem terminal_bound_with_prefix_tight_raw :
    probability terminalHit < probability residual₁ + probability residual₂
      + probability Prefix + 4.613860465762 / (10 : ℝ)^12

theorem prefix_bound_mordell_blichfeldt :
    probability Prefix < 3.782 / (10 : ℝ)^14

theorem terminal_bound_mordell_blichfeldt :
    probability terminalHit < probability residual₁ + probability residual₂
      + 4.652 / (10 : ℝ)^12
```

For the first statement, reuse the `raw250_numeric` certificate with `p := 235454`, `s := 10^17`, reprice `bad_bound`, and add it to `good_first_moment (concrete_late HermiteWitness506.Sphere.laterDeterminantFloor)` and the three current late enclosures. For the second, instantiate the suffix family with the proved rank-7/8/24 inputs, propagate that profile through the forced lengths, radii and floors, and certify its flag sum below `3.781668e-14`. Its raw radius is above 2885. The uniform cutoff 2896 is below 3329, and the same inward-volume lemma with $d=505,k=252,b/c=2897/1$ proves the initial raw term at 2896 below `7e-34` (also kernel-checked in scratch). The existing `LastCoordinateCoverage`, `initial2885_numeric`, and `FlagEnvelope.flagCharge_sum` specialize to the old profile. The comparison premises of `terminal_bound_of_numeric_caps` do not accept the unconditional coefficients. The open work is a profile-specific coverage/finite-sum certificate; the displayed terminal conclusion has no residual *hypotheses* but still has both residual *probabilities* on its right. [ControlledConcreteBounds](../../SigabaNeo/Lib/Lattices/Research/Wall1/ControlledConcreteBounds.lean) · [Suffix descent](../../SigabaNeo/Lib/Lattices/Research/Wall1/ControlledSuffixDescent.lean) · [Current flag sum](../../SigabaNeo/Lib/Lattices/Research/Wall1/ControlledFlagSum.lean) · [Terminal caps](../../SigabaNeo/Lib/Lattices/Research/Wall1/ControlledTerminalCaps.lean)

### Reproducing the numerical checks

Run the following from the repository root with Python and mpmath. The raw bound uses exact rationals; the radii, flags and optional radial sum use the repository script's outward-rounded intervals. The final budget arithmetic is exact decimal arithmetic.

```python
from decimal import Decimal as D
from fractions import Fraction as Q
from math import prod
import sys
sys.path.insert(0, "docs/research/scripts")
import wall1_hermite_budget as w

def raw(d, b):
    k = (d - 1) // 2
    return (2 * b**d * Q(22, 7)**k * 2**(k+1)
            / (prod(range(1, d+1, 2)) * 3329**400))

assert raw(911, Q(501, 2)) < Q(235454, 10**17)
assert raw(505, Q(2897)) < Q(7, 10**34)
L = w.log_floors()
radius, initial, flags = w.prefix(L, w.MORDELL_LOG_SEVEN, w.log_blichfeldt(24))
assert w.real("2895.32735") < radius < w.real("2895.32737")
assert initial < w.real("6.290e-34")
assert w.real("3.78166796205860e-14") < flags < w.real("3.78166796205861e-14")
assert flags + initial < w.real("3.782e-14")
volume = w.iv.pi**253 / w.iv.factorial(253)
radial = w.real("1.422743743939") * volume * w.WINNER**506
assert sum(radial * w.iv.exp(-l) for l in L[:394]) < w.real("1.474613e-13")

fixed = sum(map(D, ["2.35454e-12", "8.147e-14", "2.066876811e-12",
                    "7.189180962e-15", "1.037844738e-13"]))
assert fixed == D("4.613860465762e-12")
assert D("6.515e-12") - fixed == D("1.901139534238e-12")
assert fixed + D("3.782e-14") < D("4.652e-12")
assert D("9e-11") - D("1.3670e-11") - D("5.055e-12") == D("7.1275e-11")
assert D("9e-11") - D("2.515e-11") - D("3.75987e-11") == D("2.72513e-11")
```

## Audit

**Verdict.** The original Part 192 remainder survives the change of Hermite coefficients. Under the finite law, the paper bound is $\Pr(A_{406})<Z_1+Z_2+4.652\times10^{-12}$. The remaining Lean obligation is the prefix bound for the revised coefficients.

**The two raw events.** The Part 184 gate tests 511 columns at radius 250. The exact rational upper bound is $2.3545390314544161\ldots\times10^{-12}$. Replacing the exported ceiling by `2.35454e-12` releases exactly `1.89446e-12` against the old ceiling. The predicate defining $G$, the two residuals, and the determinant floor all retain their original definitions. The initial-graph branch of the prefix proof tests only 105 columns. Its required radius rises to $2895.3273590638\ldots$ because the suffix coefficients change. Rounding up to 2896 keeps every test below 3329. The inward-volume certificate at 2896 gives $5.2708430543\ldots\times10^{-34}<7\times10^{-34}$. An independent Lean run checked both raw probability inequalities and the prefix-explicit subtotal `4.613860465762e-12`. Each used only `propext`, `Classical.choice`, and `Quot.sound`. [Raw certificates](../../SigabaNeo/Lib/Lattices/Research/Wall1/ControlledRawBall.lean) · [Event definitions and first-moment decomposition](../../SigabaNeo/Lib/Lattices/Research/Wall1/ControlledPlaneTail.lean)

**Prefix and rounding.** The outward-interval assertions above passed. A separate 65-decimal-digit evaluation of the Part 192 formula, using the product of the skipped length caps and the theta factor at each test width, gave $3.7816679620586045\ldots\times10^{-14}$ for the 12,089 flag terms and $6.28915599138434\ldots\times10^{-34}$ for the initial term. The monotone suffix caps cover all horizons through 154 with one test per pair of indices. The old 2885 coverage and flag-sum certificate require replacement for this profile. The introductory `3.113715e-14` rounds up the deficit of the *evaluated majorant*. Reserving the full rounded allowance `3.782e-14` instead requires exactly `3.1140465762e-14` beyond the old balance. Adding that full allowance to the revised subtotal gives `4.651680465762e-12`, below both `4.652e-12` and `6.515e-12`. [Part 192 prefix formula](wall1_rank2_tail.md#summing-charges-along-the-tour) · [Proved coefficients](../../SigabaNeo/Lib/Lattices/Research/Wall1/HermiteSevenTwentyFour.lean)

**Residuals and overlaps.** Part 194 assigns $Z_1$ a target of `9e-11`. Its mixed charge and the Part 198 through-171 charge leave `9e-11 − 1.3670e-11 − 5.055e-12 = 7.1275e-11`, as Part 206 records. Parts 218, 221 and 223 leave more than `4.02078e-12` of that balance. Part 193 assigns $Z_2$ a target of `9e-11` and leaves `6.485e-11` after its `2.515e-11` charge. Part 216 replaces the earlier large-$g$ estimate and leaves `6.485e-11 − 3.75987e-11 = 2.72513e-11` for small $g$. Both full targets remain open. The terminal calculation pays each exit once. Overlap of the through-171 upper bound with the separately charged prefix is conservative, as is overlap among the late union bounds. No overlap is used to claim a saving. Part 184's `4e-7` is the direct spacing target for $E$. Meeting both residual targets would give $\Pr(E)\le\Pr(A_{406})<1.84652\times10^{-10}$ and leave `3.99815348e-7` of that target. [Part 184](wall1_penultimate_projection.md#audit) · [Part 194](wall1_z1_horizontal.md#audit) · [Part 206](wall1_raw_section_compression.md#audit) · [Part 223](wall1_wholly_old_mass.md) · [Part 193](wall1_z2_vertical.md#audit) · [Part 216](wall1_small_g_frequency.md#audit)
