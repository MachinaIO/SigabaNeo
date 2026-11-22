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
import PE.Impl.DualUse.Registry

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
the configuration `confP`, and for `params3`, `params5` of the registry.
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

theorem inDomain_of {q m : ℕ} (hq0 : 0 < q) (hq : 2 ≤ q) (hm : 1 ≤ m) :
    (RingLWE.Params.toModule ⟨2 ^ 34, m, q, .cbd 16, .cbd 16, hq0⟩).inDomain = true := by
  simp only [ModuleLWE.Params.inDomain, RingLWE.Params.toModule, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨rfl, rfl⟩, decide_eq_true hm⟩, decide_eq_true hq⟩, rfl⟩, rfl⟩

theorem two_le_q : 2 ≤ 2 ^ (2 ^ 25) :=
  calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ (2 ^ 25) := pow_le_pow_right₀ (by norm_num) (by norm_num)

/-- The bound on `RingLWE.H` from the bound on the estimator at the LWE view (any modulus `q`;
the kernel never computes it). -/
theorem H_ge_of_bits {q m : ℕ} (hq0 : 0 < q) (hq : 2 ≤ q) (hm : 1 ≤ m)
    (h : 2650 ≤ estimatorBits (LWEParams.mk' (2 ^ 34 * 1) q (ND.cbd 16) (ND.cbd 16)
      (some (2 ^ 34 * m)))) :
    2650 ≤ RingLWE.H ⟨2 ^ 34, m, q, .cbd 16, .cbd 16, hq0⟩ :=
  RingLWE.H_ge_of (inDomain_of hq0 hq hm) h

/-- **Hybrid 3: `2650 ≤ RingLWE.H`.** -/
theorem ringLWE_H_params3 : 2650 ≤ RingLWE.H ringParams3 :=
  H_ge_of_bits _ two_le_q (by norm_num) (cbd16_estimatorBits_ge (by decide +kernel) checks3)

/-- **Hybrid 5: `2650 ≤ RingLWE.H`.** -/
theorem ringLWE_H_params5 : 2650 ≤ RingLWE.H ringParams5 :=
  H_ge_of_bits _ two_le_q (by norm_num) (cbd16_estimatorBits_ge (by decide +kernel) checks5)

instance : NeZero (2 ^ (2 ^ 25) : ℕ) := ⟨by positivity⟩

theorem params3_eq : params3 (2 ^ 34) (2 ^ (2 ^ 25)) (2 ^ 25 + 1) (.cbd 16) = ringParams3 := by
  unfold params3 ringParams3
  simp only [RingLWE.Params.mk.injEq, and_true, true_and]
  simp [RingBTVW.Col]

theorem params5_eq :
    params5 (2 ^ 34) (2 ^ (2 ^ 25)) (2 ^ 25 + 1) (Fin (2 ^ 61)) (.cbd 16) = ringParams5 := by
  unfold params5 ringParams5
  simp only [RingLWE.Params.mk.injEq, and_true, true_and]
  simp [Idx5, RingBTVW.Col]

/-- **The registry's hybrid 3 instance at `N = 2^34`: `2650 ≤ RingLWE.H`.** -/
theorem ringLWE_H_registry3 :
    2650 ≤ RingLWE.H (params3 (2 ^ 34) (2 ^ (2 ^ 25)) (2 ^ 25 + 1) (.cbd 16)) := by
  rw [params3_eq]; exact ringLWE_H_params3

/-- **The registry's hybrid 5 instance at `N = 2^34`: `2650 ≤ RingLWE.H`.** -/
theorem ringLWE_H_registry5 :
    2650 ≤ RingLWE.H (params5 (2 ^ 34) (2 ^ (2 ^ 25)) (2 ^ 25 + 1) (Fin (2 ^ 61)) (.cbd 16)) := by
  rw [params5_eq]; exact ringLWE_H_params5

end AdvancedEncryption.DualUse.Params.Strength
