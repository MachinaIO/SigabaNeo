# Tight description lengths (Enc, Dec, Setup) and Setup clock — notes for integration

All new files, no existing module edited. Each builds in < 10 s (on top of existing oleans).
Axioms of every headline theorem: `propext, Classical.choice, Quot.sound`. No sorry or
native_decide.

| Theorem | Old | New | Optimal for this machine? |
|---|---|---|---|
| `EncConf.descLen_encMachine_tight` (`DescTightEnc.lean`) | 2^744 | **2^635** | yes (true ≈ 2^634.7) |
| `DecConf.descLen_decMachine_tight` (`DescTightDec.lean`) | 2^465 | **2^447** | yes (true ≈ 2^446.3) |
| `time_setupMP_conf_tight` (`SetupTight.lean`) | 2^242 | **2^241** | yes for this bound shape (≈ 2^240.63; the cap M ≥ m̄K·NK ≈ 2^97.58) |
| `descLen_setupMP_conf_tight` (`SetupTight.lean`) | 2^249 | **2^233** | ≈ 2^232.98 at the bound used |

The Setup theorems have the same hypotheses as `time_setupMP_conf` / `descLen_setupMP_conf`
(`D.e = 24`, `D.K = 2^16`, `D.b = 22`, `D.mb = 3·2^40 + 408`), in namespace
`AdvancedEncryption.ExpLUT.Prog`. (The names carry `_conf_tight` because
`DualUse.Prog.time_setupMP_tight` already exists.)

## Main slack found

`descLen = 6·S·3^k·entryBits k S 0` with `entryBits k S 0 = 4 + 4k + Nat.size S`.
The old `descLen_arithA` bounded `Nat.size S ≤ S`, i.e. the entry width by `2^112` (Enc) and
`2^28` (Dec). `DescTightBase.descTight_arith` uses `S ≤ B < 2^m → Nat.size S ≤ m`:
`descLen ≤ 6·B·3^k·(4 + 4k + m)`. This alone gives Enc ≈ 2^642, Dec 2^447, Setup 2^236.

## Enc state count (2^112 → 2^105 + 2^101)

60 states per bit for every unrolled literal reader/template (`InitOp.cost`, exact) and per bit of
input normalization. In units of 2^91 bits: public word ≈ 76.003, coin word ≈ 38.001, ciphertext
template ≈ 38.001, so the program has ≈ 60·(76+38+38+114)·2^91 ≈ 2^104.96 states. The existing
`cost_{public,coins,templates}_tight` (20, 10, 10 × 2^99) plus a new
`normalization_lengths_tight : coinLength Dc + publicLength Dc ≤ 115·2^91` give
`size_encProgram_tight : size + 4 ≤ 2^105 + 2^101`; with entry width 4 + 1304 + 106 this yields
log₂ ≈ 634.84 ≤ 635. Since 6·3^326·1413 ≈ 2^529.75, reaching 2^634 would need fewer than
≈ 2^104.25 states, below the true count — so 635 is the floor without changing the machine.

## Dec

Unchanged state bound (`size_decProgram : size + 4 ≤ 2^28`; the compiled code alone has
256728820 ≈ 2^27.94 states), entry width 4 + 1024 + 29 → log₂ ≈ 446.38. Reaching 2^446 would need
fewer than ≈ 2^27.62 states, also below the true count.

## Setup

* Clock: `setupTFn` is linear in the tape cap M (dominant `(2M+3)·22N²K²·m̄K`). With S = 2^97,
  `SetupBounds` only needs M ≥ max(S + 8K, m̄K·NK = 3·2^96 + 408·2^56), so
  M = 3·2^96 + 2^90 instead of 2^98 (`setupBounds_tight`, `setupTFn_tight` by `decide +kernel`).
* descLen: exact sizes of the fixed blocks from `decide +kernel` (detCore 28995, outP 3597,
  ucTail 1492, appendTapeP 279, coinAp 133, the coin/zero loops 208/135) instead of the slack
  constant 2·10^6, and each of the 34 `natP` counters charged at its own bit length (still
  195 per bit via `size_natP_le`), giving `size_setupP_tight : size + 4 ≤ 360000 < 2^19`.
  A further gain (→ 2^232) would need a sharper per-bit `natP` size than 195, which is about
  80% of the remaining count.

## Integration hint

Swap the uses of `EncConf.descLen_encMachine`, `DecConf.descLen_decMachine`,
`time_setupMP_conf` and `descLen_setupMP_conf` in the aggregator/submission for the `_tight`
versions; the total Enc cost then becomes max(2^253 clock, 2^635 descLen), so ≤ 2^636 for the sum.
