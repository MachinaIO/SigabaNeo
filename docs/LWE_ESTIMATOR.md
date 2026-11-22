# The security function of LWE: the lattice estimator, formalized

`ModuleLWE.H`, `RingLWE.H` and `LWE.H` ([ASSUMPTIONS.md](ASSUMPTIONS.md)) are the number of bits
the lattice assumptions claim. `H p` is the integer floor of the cheapest attack of the
[lattice estimator](https://github.com/malb/lattice-estimator) on the LWE view of `p`. The attacks
are formalized as computable Lean functions in `SigabaNeo/Lib/Lattices/Estimator/`, at revision
`53da598` with its default models: the `RC.MATZOV` reduction cost, the GSA shape model, and
classical attackers.

## What is proved

| Theorem | Statement |
| --- | --- |
| `Estimator.floorBits_le`, `ModuleLWE.H_le` | for every formalized attack `a`, `H p ≤ ⌊log₂ cost_a(p)⌋`: no modelled attack refutes `H` |
| `Estimator.floorBits_tight`, `ModuleLWE.H_tight` | on the domain, when some attack is finite, one attack has `log₂ cost_a(p) < H p + 1`: any larger claim is refuted by a modelled attack |

Both hold for all parameters. They are statements about the cost models: `cost_a` is the
estimator's formula for the number of operations of attack `a`, evaluated in fixed point.

## What is not proved, and cannot be

`HardAt` quantifies over every Turing machine, so "`H` is not refuted" in that sense is LWE
hardness itself. "`H + 1` is refuted" in that sense needs a Turing machine that runs the attack
with a proven cost and success probability. The estimator's costs rest on heuristics, some of
which are false as stated or open:

| Heuristic | Used by | Status |
| --- | --- | --- |
| Geometric series assumption (GSA) for BKZ-reduced bases | all lattice attacks | empirical approximation; false in the last dimensions (HKZ tail) and for q-ary bases (Z-shape) |
| Gaussian heuristic for the projected sublattices | uSVP, BDD, hybrids | a theorem on average over random lattices, not for BKZ's projected blocks |
| 2016 estimate (BKZ-β finds the unique short vector) [ADPS16, AGVW17] | uSVP | experimentally verified at small dimensions [AGVW17, DDGR20, PV21] |
| Sieving cost `2^{0.296 β' + 20.4}`, progressive overhead `C · (d − β)` [AGPS20, MATZOV22, Kyber20] | `RC.MATZOV` | numerical fits of gate counts; the asymptotic `2^{0.292 β + o(β)}` rests on a uniform-on-the-sphere heuristic |
| Dimensions for free [Duc18] | `RC.MATZOV` | heuristic, experimentally calibrated |
| Independence of dual-vector scores [MATZOV22] | dual hybrid | shown inconsistent in some regimes [DP23]; later analyses revise it |
| Semi-regularity of the Arora–Ge system [Fröberg's conjecture] | Arora–GB | open; Arora–Ge systems are not generic |
| Babai and MITM success probabilities [Wun19, SC19] | primal hybrid | heuristic models of the projected error |
| Coded-BKW noise model [GJS15] | BKW | heuristic |

These cannot be proved here. The last column records the evidence for each. The scope of `H` is
therefore: the cheapest attack known to the estimator, in the estimator's model. Proven attacks
(`Assumption.Attack`) lower `H` further through the harness.

## Configuration: the scan range and the all-infinite case

* **`maxBeta = 16384`** (`Estimator.maxBeta`, `python/lwemodel/reduction.py: MAX_BETA`). Every
  block-size scan (`usvp`, `dual`, `dual_hybrid`, the primal hybrids' search and the BDD
  dimension `η`) stops below it. The estimator's default `conf.max_beta = 1754`
  (`RC.ADPS16(1754, 1754) ≈ 2^512`, "for security levels of at most 512 bits") is a
  configuration value; it is raised here so that large strengths can be certified
  (`RC.MATZOV(16384, 16384) ≈ 2^4673`). This is a deviation from the default configuration, in the
  direction of more attacks (a larger scan can only lower a minimum). The Kyber values below are
  unchanged, bit for bit.
* **`fallbackBits = ⌊log₂ RC.MATZOV(maxBeta, maxBeta)⌋ = 4673`** is the claim when every attack is
  infinite (formerly an arbitrary cap of 1024). A lattice attack is infinite when no block size
  below `maxBeta` succeeds, so a successful one needs `β ≥ maxBeta`. Exhaustive search is infinite
  above `2^10000` (the estimator's `Cost.sanity_check`), above `fallbackBits`. Coded-BKW keeps the
  estimator's binary64 cap `2^1024`, and Arora–GB, MITM and exhaustive search are also infinite
  when samples are lacking: on those the fallback relies on the lattice attacks.

## Large parameters

At large dimensions the attacks cannot be evaluated: the hybrids search the guessing dimension
over `[0, n)` with binomials of size `2^n`, Arora–GB iterates its Hilbert series up to degree
`2n`, the dual hybrid scans `n/10 × n/10` guessing splits when every candidate is infinite, and
the kernel refuses moduli such as `2^(2^25)`. `SigabaNeo/Lib/Lattices/Estimator/Bound/` proves
lower bounds on each attack from its definition instead (`Bound.lean` lists them):

| Attack | Lower bound | Argument |
| --- | --- | --- |
| `usvp`, `dual` | each scanned candidate | `log₂ q` passed as a number (`Usvp.costQ`, `Dual.costQ`); candidates below `β₀` evaluated by the kernel, above `β₀` the reduction cost `redLB β` (one sieve in dimension `β − d4f(β)`) |
| `dual_hybrid` | `DualHybrid.cost_ge` | the guessing part costs `≥ k + t` bits; else the reduction cost; else `v > 10` (infinite), monotone in the dimension |
| `bdd`, `bdd_hybrid`, `bdd_mitm_hybrid` | `PrimalHybrid.estimate_ge` | the reduction cost; or guessing cost plus miss probability `≥ z − 1` bits (a union bound on the binomial tail, `Binom.hit_mul_le`); or Babai's failure: the GSA profile falls below `2^{−55}` well before the last `maxBeta + 1` coordinates (AM–GM, uniform in the dimension), each such coordinate costing `29.9` bits (`Profile.lean`) |
| `bkw` | infinite (`Bkw.cost_eq_none`) | the `q^b` table exceeds `2^1024` when `log₂ q ≥ 1024` |
| `arora-gb` | `AroraGB.cost_ge`, `gb_ge` | the first `K₀` Hilbert series coefficients grow by `R` per degree, so the degree of regularity exceeds `K₀`; or the guess penalty |
| `exhaustive_search` | infinite (`Guess.exhaustiveCost_eq_none`) | more than `2^10049` candidates |
| `mitm` | evaluated | after `q` is removed (`Guess.mitmCostW`) |

`Estimator.cbd16_estimatorBits_ge` packages them for `CBD(16)` secret and error at `q = 2^e`:
closed numeric facts plus one check per block size `b < maxBeta + 2`, evaluated by
`decide +kernel` in chunks (`Params/Strength/Scan*.lean`: 8 files per instance, each a sequence of
256-block-size theorems so that the kernel's memory stays near 1.5 GB above the imports; 10–60 s
per file, about 11 minutes of kernel time for both instances; the closed facts take about 1 s).
All the bounds are about the attack models, like `H` itself.

**Ring degree `2^34`, `q = 2^(2^25)`, `CBD(16)`** (the registry's instances of the dual-use PE,
`AdvancedEncryption/PE/Impl/DualUse/Params/Strength.lean`): `2650 ≤ RingLWE.H` at `2^26 + 2` and
at `2^61 + 2^27 + 5` samples. The mirror gives `usvp` 2691.95, `bdd` 2691.95 (`β ≈ 9400`), `dual`
2691.96 and the hybrids at small `z` 2691.96, so `H ≈ 2691`; the certified bound loses about 40 bits
because the Babai-failure argument needs `β` a little below the optimum.

**The mirror at these sizes.** `python/lwemodel` evaluates `usvp` (≈ 1 min, `log₂ q` computed once),
`bdd` (0.3 s), `dual`, `mitm`, `exhaustive_search` and `bkw` at `N = 2^34`: `profile` skips the
blocks above its cut-off and sums the underflowed tail at once (equal to the block-by-block
definition, `test_fast_profile`), and exhaustive search and BKW return `None` under the conditions
of `Guess.exhaustiveCost_eq_none` and `Bkw.cost_eq_none`. Arora–GB, the primal hybrids' search over
the guessing dimension and the dual hybrid remain infeasible there; their values are only bounded.

## Faithfulness to the estimator

Each attack has a Python mirror in `python/lwemodel/` that computes the same integers as the Lean
function (`python/tests/test_lwemodel_*.py`). The mirrors are compared with the estimator itself.
Where the estimator runs a local search, the Lean function scans the same range exhaustively, so
its minimum is at most the estimator's.

| Attack (`attacks`) | Estimator function | Lean | Largest deviation from the estimator on the 75-point grid |
| --- | --- | --- | --- |
| `arora-gb` | `guess_composition(arora_gb)` | `AroraGB.cost` | 0 (at reported precision) |
| `bkw` | `coded_bkw` | `Bkw.cost` | 8.4·10⁻⁷ bit |
| `usvp` | `primal_usvp` (GSA) | `Usvp.cost` | 10⁻¹² bit (Kyber) |
| `bdd` | `primal_bdd` | `PrimalBdd.cost` | < 0.024 bit (all three primal) |
| `bdd_hybrid` | `primal_hybrid(mitm=False, babai=False)` | `PrimalHybrid.costBdd` | |
| `bdd_mitm_hybrid` | `primal_hybrid(mitm=True, babai=True)` | `PrimalHybrid.costMitm` | 0.023 bit (Kyber1024) |
| `dual` | `dual` | `Dual.cost` | 4·10⁻¹³ bit, except 4 points (below) |
| `dual_hybrid` | `dual_hybrid` (`matzov`) | `DualHybrid.cost` | < 0.1 bit (all 75 points) |
| `exhaustive_search` | `exhaustive_search` | `Guess.exhaustiveCost` | 2.7·10⁻¹² bit |
| `mitm` | `mitm` | `Guess.mitmCost` | 0 (at reported precision) |

The grid: `n ∈ {256, 512}`, `q ∈ {2^10 − 1, 2^32 − 1}`, Gaussian errors `σ ∈ {1.2, 3.2}`,
uniform, Gaussian or ternary secrets, `m ∈ {n, 2n, ∞}`, plus Kyber512/768/1024. The tests
(`python/tests/test_lwemodel_{primal,dual,misc}.py`) compare Lean with Python bit for bit, and with
the estimator when run under Sage:

```bash
SAGE_ESTIMATOR=1 LWE_ESTIMATOR_SAGE=$(which sage) PYTHONPATH=<estimator checkout> \
  sage -python -m unittest discover -s python/tests -p "test_lwemodel_*.py"
```

**The four `dual` points.** At `n = 256, q = 1023`, unlimited samples, uniform or Gaussian secret,
the Lean function finds 91.3 bits (σ = 1.2) and 121.0 bits (σ = 3.2) where the estimator reports
271.0. The estimator's own cost function gives 91.33 bits at `β = 216`, but its local search
(`local_minimum` with step 8) stops at `β = 894` between plateaus of infinite cost. The exhaustive
scan is faithful to the estimator's model, and the estimator's search misses its minimum here.

Two estimator searches raise exceptions on some points (coded-BKW with a uniform secret and
`m = n`; the primal hybrid's search bounds). There the Lean functions return `none`, except for
two `bdd_mitm_hybrid` points at ≈ 1684 bits that have no estimator value to compare with.

## Kyber

Kyber's module-LWE instances (`N = 256`, `q = 3329`, centered binomial secret and errors,
`m = rank`), without the rounding of the ciphertext:

| | Kyber512 | Kyber768 | Kyber1024 |
| --- | ---: | ---: | ---: |
| `usvp` | 143.77 | 204.91 | 275.10 |
| `bdd` | 140.20 | 200.96 | 270.72 |
| `bdd_hybrid` | 140.21 | 200.99 | 270.75 |
| `bdd_mitm_hybrid` | 262.06 | 358.23 | 495.88 |
| `dual` | 149.88 | 214.29 | 288.53 |
| `dual_hybrid` | **139.66** | **196.37** | **262.34** |
| `bkw` | 178.76 | 238.25 | 315.04 |
| `arora-gb`, `exhaustive_search`, `mitm` | ∞ | ∞ | ∞ |
| **`ModuleLWE.H`** | **139** | **196** | **262** |
| Kyber specification, classical Core-SVP (Round 3, Table 4; 183 for Kyber768 in the August 2021 revision) | 118 | 182 | 256 |
| NIST category (AES key search, gates) | 143 | 207 | 272 |
| Conservative bound `securityBits` (Gaussian proxy) | 99 | 159 | 228 |

`H` meets the specification's Core-SVP levels (`python/tests/test_kyber.py`). It does not reach the
NIST category gate counts: this is the known gap between the estimator's operation counts and
the categories, which NIST's evaluation closes with the cost of memory access, outside the model.

## The conservative bound

`Hardness.securityBits` ([LWE_HARDNESS.md](LWE_HARDNESS.md)) is an earlier, deliberately
conservative lower bound: no polynomial factors, minus the dimensions for free, minus `log₂ N`. It
is kept as a cross-check: at every parameter set listed here, `securityBits ≤ H`.

## References

* [ADPS16] Alkim, Ducas, Pöppelmann, Schwabe. Post-quantum key exchange — a new hope. USENIX 2016.
* [AGVW17] Albrecht, Göpfert, Virdia, Wunderer. Revisiting the expected cost of solving uSVP.
  ASIACRYPT 2017.
* [AGPS20] Albrecht, Gheorghiu, Postlethwaite, Schanck. Estimating quantum speedups for lattice
  sieves. ASIACRYPT 2020.
* [DDGR20] Dachman-Soled, Ducas, Gong, Rossi. LWE with side information. CRYPTO 2020.
* [DP23] Ducas, Pulles. Does the dual-sieve attack on learning with errors even work? CRYPTO 2023.
* [Duc18] Ducas. Shortest vector from lattice sieving: a few dimensions for free. EUROCRYPT 2018.
* [GJS15] Guo, Johansson, Stankovski. Coded-BKW: solving LWE using lattice codes. CRYPTO 2015.
* [Kyber20] Avanzi et al. CRYSTALS-Kyber, Round 3 specification. 2020/2021.
* [MATZOV22] MATZOV. Report on the security of LWE: improved dual lattice attack. 2022.
* [PV21] Postlethwaite, Virdia. On the success probability of solving unique SVP via BKZ. PKC 2021.
* [SC19] Son, Cheon. Revisiting the hybrid attack on sparse and ternary secret LWE. WAHC 2019.
* [Wun19] Wunderer. A detailed analysis of the hybrid lattice-reduction and meet-in-the-middle
  attack. J. Math. Cryptol. 2019.
