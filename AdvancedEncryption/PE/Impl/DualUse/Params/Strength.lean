import PE.Impl.DualUse.Params.Strength.Scan3a
import PE.Impl.DualUse.Params.Strength.Scan3b
import PE.Impl.DualUse.Params.Strength.Scan3c
import PE.Impl.DualUse.Params.Strength.Scan3d
import PE.Impl.DualUse.Params.Strength.Scan3e
import PE.Impl.DualUse.Params.Strength.Scan3f
import PE.Impl.DualUse.Params.Strength.Scan3g
import PE.Impl.DualUse.Params.Strength.Scan3h
import PE.Impl.DualUse.Params.Strength.Scan5a
import PE.Impl.DualUse.Params.Strength.Scan5b
import PE.Impl.DualUse.Params.Strength.Scan5c
import PE.Impl.DualUse.Params.Strength.Scan5d
import PE.Impl.DualUse.Params.Strength.Scan5e
import PE.Impl.DualUse.Params.Strength.Scan5f
import PE.Impl.DualUse.Params.Strength.Scan5g
import PE.Impl.DualUse.Params.Strength.Scan5h
import PE.Impl.DualUse.Params.Strength.Generic

/-!
# The Ring-LWE strength of the registry's instances at `N = 2^34`

The Ring-LWE instances of the reductions (`DualUse/Registry.lean`) at ring degree `N = 2^34`,
modulus `q = 2^(2^25)`, `CBD(16)` errors and secret (normal form):

* hybrid 3, `params3 N q k (cbd 16)` with `k = 2^25 + 1`: `2k = 2^26 + 2` samples;
* hybrid 5, `params5 N q k (Fin 2^61) (cbd 16)`: `|Wd| + 4k + 1 = 2^61 + 2^27 + 5` samples.

**`ringLWE_H_params3`, `ringLWE_H_params5`: `2650 ≤ RingLWE.H`** at both. The registry's strength
`RingLWE.H = ModuleLWE.H` is the floor of the cheapest attack of the lattice estimator
(`SigabaNeo.Lib.Lattices.Estimator`, `maxBeta = 16384`); its value here is about `2691`
(`bdd`, `β ≈ 9400`, in the Python mirror). The bound is proved without evaluating the estimator,
which is infeasible at this size: `Estimator.cbd16_estimatorBits_ge` reduces it to closed numeric
facts and to a check of each block size `b < maxBeta + 2` (`Estimator.cbdCheck`), evaluated by
the kernel in chunks (`Params/Strength/Scan*.lean`).

The statements are given at explicit parameters (`ringParams3`, `ringParams5`), independently of
the configuration `confP`, and for `params3`, `params5` of the registry, through the generic
lemmas of `Params/Strength/Generic.lean`.
-/

namespace AdvancedEncryption.DualUse.Params.Strength

open SigabaNeo.Lattices SigabaNeo.Lattices.Estimator

theorem checks3 : ∀ b < maxBeta + 2, chk3 b = true := by
  intro b hb
  have hmb : maxBeta + 2 = 16386 := rfl
  rw [hmb] at hb
  exact range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue
    scan3_0 scan3_1) scan3_2) scan3_3) scan3_4) scan3_5) scan3_6) scan3_7 b
    (Nat.zero_le _) hb

theorem checks5 : ∀ b < maxBeta + 2, chk5 b = true := by
  intro b hb
  have hmb : maxBeta + 2 = 16386 := rfl
  rw [hmb] at hb
  exact range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue
    scan5_0 scan5_1) scan5_2) scan5_3) scan5_4) scan5_5) scan5_6) scan5_7 b
    (Nat.zero_le _) hb

/-- Hybrid 3's Ring-LWE instance at `N = 2^34`. -/
def ringParams3 : RingLWE.Params := ⟨2 ^ 34, 2 ^ 26 + 2, 2 ^ (2 ^ 25), .cbd 16, .cbd 16, by positivity⟩

/-- Hybrid 5's Ring-LWE instance at `N = 2^34`. -/
def ringParams5 : RingLWE.Params :=
  ⟨2 ^ 34, 2 ^ 61 + 2 ^ 27 + 5, 2 ^ (2 ^ 25), .cbd 16, .cbd 16, by positivity⟩

/-- **Hybrid 3: `2650 ≤ RingLWE.H`.** -/
theorem ringLWE_H_params3 : 2650 ≤ RingLWE.H ringParams3 :=
  H_ge_of_cbd (m := 2 ^ 26 + 2) rfl (by norm_num) (by norm_num) (by decide +kernel) checks3

/-- **Hybrid 5: `2650 ≤ RingLWE.H`.** -/
theorem ringLWE_H_params5 : 2650 ≤ RingLWE.H ringParams5 :=
  H_ge_of_cbd (m := 2 ^ 61 + 2 ^ 27 + 5) rfl (by norm_num) (by norm_num) (by decide +kernel) checks5

/-- **The registry's hybrid 3 instance at `N = 2^34`: `2650 ≤ RingLWE.H`.** -/
theorem ringLWE_H_registry3 :
    2650 ≤ RingLWE.H (params3 (2 ^ 34) (2 ^ (2 ^ 25)) (2 ^ 25 + 1) (.cbd 16)) :=
  registry3_ge (M := M3) rfl (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) checks3

/-- **The registry's hybrid 5 instance at `N = 2^34`: `2650 ≤ RingLWE.H`.** -/
theorem ringLWE_H_registry5 :
    2650 ≤ RingLWE.H (params5 (2 ^ 34) (2 ^ (2 ^ 25)) (2 ^ 25 + 1) (Fin (2 ^ 61)) (.cbd 16)) :=
  registry5_ge (M := M5) rfl (by norm_num) (by norm_num) (by decide +kernel) checks5

end AdvancedEncryption.DualUse.Params.Strength
