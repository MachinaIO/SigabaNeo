# WS2 status (depth-based noise and parameters)

Branch `t3/bp-ws2`, base `db15ea12`.

## M1 — done, commit `f248b04e`

* `SigabaNeo.Lattices.nb_fhatSLP_depth` (`Lib/Lattices/Homomorphic/GSWNoise.lean`):
  `nb WN E (fhatSLP hk p w).1 ((fhatSLP hk p w).2 b) ≤ gswFactor WN N k ^ SLP.depth p w * E`;
  through `nb_repOf_depth`, `nb_foldl_compileStep_depth`, `nb_compileSLP_depth`.
  `SLP.depth` is the existing definition of `Homomorphic/Depth.lean` (now imported by `GSWNoise`).
* `RingBTVW.noiseBound_le_depth`, `noiseBound_le_of_depth_le` (any `D ≥ depth`)
  (`RingBTVW/NoiseClosed.lean`).
* `DualUse.rnorm_rowOf_simKeyMat_le_depth`, `cnorm_simTrap_le_depth` (with `D ≥ depth`, bound
  `simTrapBound N k D`), `simTrapBound_mono` (`Params/SimTrapNorm.lean`).
* The size-based lemmas are kept.

## Stage I — commit `fefb7b09` (tree still date windows, full build green)

* `Params/NoiseGen.lean` (new): the chain over variable sizes and exponents.
* `Params/Sizes.lean`: named bounds `Dmax = 375`, `ak, an, ad, wP, eWN, eMod, eTree, eG, eGD,
  eR, eRW, eTC, eE, eNoise`; `noise_ok {Attr} (f) (hf : SLP.depth f.1 f.2 ≤ Dmax)`;
  `simTrapBound_le (hn : n ≤ Dmax)`.
* `Params/Conf.lean`: `confP.w := wP`; `depth_predC` (from `SLP.depth_le_length` and
  `length_predC`); `correct_conf`, `goodTrap_sim` through it; `eCoef`, `abortP` via `Gen.abort_prod`.
* `Params/Stat.lean`: `card_JC_le`, `card_HC_le` (over `Fin n`), `lhl_le_gen` (slack), `lhl_le`
  (`2^130`), `rpow_div_le` (width `w`), `flood_conf` in `confP.w`, slack `sP`.
* `Params/Advantage.lean`: `card_mul_le`.

## Stage II prep — commit `a4e8bb77` (`Params/SizesA.lean`, not wired)

Namespace `DualUse.Params.A`, generic in `N K k d` with hypotheses. Noise:
`4 · noise + 2 < 2^102113082`, `K = 2^27 = 134217728`, margin `32104646` bits (24 %).
Flooding gives `2^-499` (not `2^-500`: `|JC| = 2^127 (1 + 2^-27)^3 > 2^127`).

## At the switch

* `Sizes.lean`: values of `Kp, Np, dp, Eτ, Bp`, the exponent defs (from `SizesA`: `ak = 28`,
  `an = 36`, `ad = 65`, `wP = 768`, `Dmax = 1054`, `eWN = 65`, `eMod = 722`, `eTree = 66`,
  `eG = 48440`, `eGD = 51055760`, `eR = 93`, `eRW = 159`, `eTC = 31`, `eE = 869`,
  `eNoise = 102113082`); `Conf.lean`: `eCoef = 102`, `depth_predC := depth_bpPred`;
  `Stat.lean`: `sP = 500`, `card_JC` from `A.card_JC`, statement exponents (`2^-370`, `2^-499`).
* `Concrete.lean` (old instance, `Kc = 2^24`) cannot hold depth 1054 (`1054 · 16225 > 2^24`):
  delete it at the switch; `ConcreteNoise.lean` stays for its helpers.
