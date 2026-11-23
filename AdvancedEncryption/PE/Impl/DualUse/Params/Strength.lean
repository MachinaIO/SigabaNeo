import PE.Impl.DualUse.Params.Strength.ScanA3a
import PE.Impl.DualUse.Params.Strength.ScanA3b
import PE.Impl.DualUse.Params.Strength.ScanA3c
import PE.Impl.DualUse.Params.Strength.ScanA3d
import PE.Impl.DualUse.Params.Strength.ScanA3e
import PE.Impl.DualUse.Params.Strength.ScanA3f
import PE.Impl.DualUse.Params.Strength.ScanA3g
import PE.Impl.DualUse.Params.Strength.ScanA3h
import PE.Impl.DualUse.Params.Strength.ScanA5a
import PE.Impl.DualUse.Params.Strength.ScanA5b
import PE.Impl.DualUse.Params.Strength.ScanA5c
import PE.Impl.DualUse.Params.Strength.ScanA5d
import PE.Impl.DualUse.Params.Strength.ScanA5e
import PE.Impl.DualUse.Params.Strength.ScanA5f
import PE.Impl.DualUse.Params.Strength.ScanA5g
import PE.Impl.DualUse.Params.Strength.ScanA5h
import PE.Impl.DualUse.Params.Strength.Generic

/-!
# The Ring-LWE strength of the registry's instances at `confA` (`N = 2^36`)

The Ring-LWE instances of the reductions (`DualUse/Registry.lean`) at the parameters of `confA`
(`AdvancedEncryption/BP_PLAN.md` §4.1): ring degree `N = 2^36`, modulus `q = 2^(2^27)`,
`k = 2^27 + 1`, `d = 2^65`, `CBD(16)` errors and secret (normal form):

* hybrid 3, `params3 N q k (cbd 16)`: `2k = 2^28 + 2` samples;
* hybrid 5, `params5 N q k (Fin d) (cbd 16)`: `d + 4k + 1 = 2^65 + 2^29 + 5` samples.

**`ringLWE_H_registry3`, `ringLWE_H_registry5`: `2650 ≤ RingLWE.H`** at both, from
`Estimator.cbd16_estimatorBits_ge` through `registry3_ge`, `registry5_ge`
(`Params/Strength/Generic.lean`): the closed facts (`cbdFacts`, one kernel evaluation) and the
check of each block size `b < maxBeta + 2` (`chkA3`, `chkA5`, evaluated by the kernel in chunks,
`Params/Strength/ScanA*.lean`). The checks hold up to `kb = 2656` at both instances and fail at
`2657` (at `β = 9312`, the block size of the primal attacks' optimum).

(The instances at `N = 2^34` of the date-window scheme were removed with it.)
-/

namespace AdvancedEncryption.DualUse.Params.Strength

open SigabaNeo.Lattices SigabaNeo.Lattices.Estimator

theorem checksA3 : ∀ b < maxBeta + 2, chkA3 b = true := by
  intro b hb
  have hmb : maxBeta + 2 = 16386 := rfl
  rw [hmb] at hb
  exact range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue
    scanA3_0 scanA3_1) scanA3_2) scanA3_3) scanA3_4) scanA3_5) scanA3_6) scanA3_7 b
    (Nat.zero_le _) hb

theorem checksA5 : ∀ b < maxBeta + 2, chkA5 b = true := by
  intro b hb
  have hmb : maxBeta + 2 = 16386 := rfl
  rw [hmb] at hb
  exact range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue
    scanA5_0 scanA5_1) scanA5_2) scanA5_3) scanA5_4) scanA5_5) scanA5_6) scanA5_7 b
    (Nat.zero_le _) hb

/-- **The registry's hybrid 3 instance at `confA`: `2650 ≤ RingLWE.H`.** -/
theorem ringLWE_H_registry3 :
    2650 ≤ RingLWE.H (params3 (2 ^ 36) (2 ^ (2 ^ 27)) (2 ^ 27 + 1) (.cbd 16)) :=
  registry3_ge (M := MA3) rfl (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    checksA3

/-- **The registry's hybrid 5 instance at `confA`: `2650 ≤ RingLWE.H`.** -/
theorem ringLWE_H_registry5 :
    2650 ≤ RingLWE.H (params5 (2 ^ 36) (2 ^ (2 ^ 27)) (2 ^ 27 + 1) (Fin (2 ^ 65)) (.cbd 16)) :=
  registry5_ge (M := MA5) rfl (by norm_num) (by norm_num) (by decide +kernel) checksA5

end AdvancedEncryption.DualUse.Params.Strength
