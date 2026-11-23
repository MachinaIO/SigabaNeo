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
