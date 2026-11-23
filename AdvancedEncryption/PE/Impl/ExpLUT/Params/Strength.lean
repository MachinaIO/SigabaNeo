import PE.Impl.ExpLUT.Params.Strength.ScanA0
import PE.Impl.ExpLUT.Params.Strength.ScanA1
import PE.Impl.ExpLUT.Params.Strength.ScanA2
import PE.Impl.ExpLUT.Params.Strength.ScanA3
import PE.Impl.ExpLUT.Params.Strength.ScanA4
import PE.Impl.ExpLUT.Params.Strength.ScanA5
import PE.Impl.ExpLUT.Params.Strength.ScanA6
import PE.Impl.ExpLUT.Params.Strength.ScanA7
import PE.Impl.ExpLUT.Params.Strength.ScanB0
import PE.Impl.ExpLUT.Params.Strength.ScanB1
import PE.Impl.ExpLUT.Params.Strength.ScanB2
import PE.Impl.ExpLUT.Params.Strength.ScanB3
import PE.Impl.ExpLUT.Params.Strength.ScanB4
import PE.Impl.ExpLUT.Params.Strength.ScanB5
import PE.Impl.ExpLUT.Params.Strength.ScanB6
import PE.Impl.ExpLUT.Params.Strength.ScanB7
import PE.Impl.ExpLUT.Params.Strength.Generic

/-!
# The strength of ExpLUT's circular Ring-LWE assumption (`q = 2^(2^16) − 1`)

ExpLUT's assumption is circular Ring-LWE with automorphism keys
(`SigabaNeo.Lattices.CircularRingLWE`, Assumption 1 of ePrint 2026/2539), whose security function
is `RingLWE.H` of the underlying Ring-LWE parameters: ring degree `N`, modulus `q = 2^K − 1` with
`K = 2^16`, `CBD(16)` errors and secret (normal form, as `DualUse`'s `confA`), `m` plain samples.

* **`circularRingLWE_H_N24`: `1155 ≤ CircularRingLWE.H`** at `N = 2^24`,
* **`circularRingLWE_H_N23`: `495 ≤ CircularRingLWE.H`** at `N = 2^23`,

for **every** `1 ≤ m ≤ 2^50` plain samples, every list `J` of automorphism indices and every gadget
length `τ` (`ringLWE_H_N24`, `ringLWE_H_N23`: the same for `RingLWE.H`; so the Ring-LWE instance
with all `m + τ·|J|` rows has as many bits whenever `m + τ|J| ≤ 2^50`). From
`Estimator.cbd16q_estimatorBits_ge` through `circularRingLWE_H_ge` (`Params/Strength/Generic.lean`):
the closed facts (`factsA`, `factsB`, one kernel evaluation each; Arora–Ge constants `ZA = 400`,
`K₀ = 50`, `R = 2^10`) and the check of each block size `b < maxBeta + 2` (`chkA`, `chkB`,
evaluated by the kernel in chunks, `Params/Strength/Scan{A,B}*.lean`).

Both bounds are the largest targets at which every block-size check passes (`1156` and `496`
fail): they are the reduction bound `redLB` at the primal and dual attacks' block sizes. For
comparison, the estimator's uSVP and dual attacks themselves cost `2^1183`, `2^1184` at `N = 2^24`
and `2^522`, `2^522` at `N = 2^23` (`m = 2^46`).

The checks read `K` only through `log₂ q`, and the bound is not monotone in it by proof: another
`K` (or `N`) needs the scan files regenerated with the new constants (`Check.lean`); `Generic.lean`
is unchanged. At `K = 2^17` the checks pass only up to `496` bits at `N = 2^24`.
-/

namespace AdvancedEncryption.ExpLUT.Params

open SigabaNeo.Lattices SigabaNeo.Lattices.Estimator

theorem checksA : ∀ b < maxBeta + 2, chkA b = true := by
  intro b hb
  have hmb : maxBeta + 2 = 16386 := rfl
  rw [hmb] at hb
  exact range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue
    scanA_0 scanA_1) scanA_2) scanA_3) scanA_4) scanA_5) scanA_6) scanA_7 b (Nat.zero_le _) hb

theorem checksB : ∀ b < maxBeta + 2, chkB b = true := by
  intro b hb
  have hmb : maxBeta + 2 = 16386 := rfl
  rw [hmb] at hb
  exact range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue
    scanB_0 scanB_1) scanB_2) scanB_3) scanB_4) scanB_5) scanB_6) scanB_7 b (Nat.zero_le _) hb

/-- The closed facts at `N = 2^24`, `kb = 1155`, `W = 40`, `ZA = 400`, `K₀ = 50`, `R = 2^10`. -/
theorem factsA : cbdFactsQ (2 ^ 24) 1155 40 400 50 (2 ^ 10) = true := by decide +kernel

/-- The closed facts at `N = 2^23`, `kb = 495`, `W = 18`, `ZA = 400`, `K₀ = 50`, `R = 2^10`. -/
theorem factsB : cbdFactsQ (2 ^ 23) 495 18 400 50 (2 ^ 10) = true := by decide +kernel

theorem samplesA_hi {m : ℕ} (hm : m ≤ 2 ^ 50) :
    56 * (2 ^ 24 * m) ≤ (2 ^ 24 - 400) * (2 ^ 10) ^ 6 :=
  calc 56 * (2 ^ 24 * m) ≤ 56 * (2 ^ 24 * 2 ^ 50) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hm)
    _ ≤ (2 ^ 24 - 400) * (2 ^ 10) ^ 6 := by norm_num

theorem samplesB_hi {m : ℕ} (hm : m ≤ 2 ^ 50) :
    56 * (2 ^ 23 * m) ≤ (2 ^ 23 - 400) * (2 ^ 10) ^ 6 :=
  calc 56 * (2 ^ 23 * m) ≤ 56 * (2 ^ 23 * 2 ^ 50) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hm)
    _ ≤ (2 ^ 23 - 400) * (2 ^ 10) ^ 6 := by norm_num

theorem samplesA_lo (m : ℕ) : maxBeta + 1 + 40 + (1155 + 22) ≤ 2 ^ 24 * m + 2 ^ 24 := by
  have : maxBeta = 16384 := rfl
  rw [this]; omega

theorem samplesB_lo (m : ℕ) : maxBeta + 1 + 18 + (495 + 22) ≤ 2 ^ 23 * m + 2 ^ 23 := by
  have : maxBeta = 16384 := rfl
  rw [this]; omega

/-- **Ring-LWE at `N = 2^24`: `1155 ≤ RingLWE.H`** for `q = 2^(2^16) − 1`, `CBD(16)`, every
`1 ≤ m ≤ 2^50` samples. -/
theorem ringLWE_H_N24 {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 2 ^ 50) :
    1155 ≤ RingLWE.H (ringParams (2 ^ 24) (2 ^ 16) m (by norm_num)) :=
  ringLWE_H_ge (M₀ := 2 ^ 24) (W := 40) (ZA := 400) (K₀ := 50) (R := 2 ^ 10) (by norm_num) rfl hm1
    (Nat.le_mul_of_pos_right _ hm1) (samplesA_lo m) (samplesA_hi hm) factsA checksA

/-- **Ring-LWE at `N = 2^23`: `495 ≤ RingLWE.H`** for `q = 2^(2^16) − 1`, `CBD(16)`, every
`1 ≤ m ≤ 2^50` samples. -/
theorem ringLWE_H_N23 {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 2 ^ 50) :
    495 ≤ RingLWE.H (ringParams (2 ^ 23) (2 ^ 16) m (by norm_num)) :=
  ringLWE_H_ge (M₀ := 2 ^ 23) (W := 18) (ZA := 400) (K₀ := 50) (R := 2 ^ 10) (by norm_num) rfl hm1
    (Nat.le_mul_of_pos_right _ hm1) (samplesB_lo m) (samplesB_hi hm) factsB checksB

/-- **Circular Ring-LWE at `N = 2^24`: `1155 ≤ CircularRingLWE.H`** for `q = 2^(2^16) − 1`,
`CBD(16)`, every `1 ≤ m ≤ 2^50` plain samples, every `J` and `τ`. -/
theorem circularRingLWE_H_N24 {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 2 ^ 50) (J : List ℕ) (τ : ℕ) :
    1155 ≤ CircularRingLWE.H (circParams (2 ^ 24) (2 ^ 16) m (by norm_num) J τ) :=
  ringLWE_H_N24 hm1 hm

/-- **Circular Ring-LWE at `N = 2^23`: `495 ≤ CircularRingLWE.H`** for `q = 2^(2^16) − 1`,
`CBD(16)`, every `1 ≤ m ≤ 2^50` plain samples, every `J` and `τ`. -/
theorem circularRingLWE_H_N23 {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 2 ^ 50) (J : List ℕ) (τ : ℕ) :
    495 ≤ CircularRingLWE.H (circParams (2 ^ 23) (2 ^ 16) m (by norm_num) J τ) :=
  ringLWE_H_N23 hm1 hm

/-- The same as the registered assumption's security function, at `N = 2^24`. -/
theorem circularRingLWE_decision_H_N24 {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 2 ^ 50) (J : List ℕ)
    (τ : ℕ) :
    1155 ≤ CircularRingLWE.decision.H (circParams (2 ^ 24) (2 ^ 16) m (by norm_num) J τ) :=
  circularRingLWE_H_N24 hm1 hm J τ

/-- The same as the registered assumption's security function, at `N = 2^23`. -/
theorem circularRingLWE_decision_H_N23 {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 2 ^ 50) (J : List ℕ)
    (τ : ℕ) :
    495 ≤ CircularRingLWE.decision.H (circParams (2 ^ 23) (2 ^ 16) m (by norm_num) J τ) :=
  circularRingLWE_H_N23 hm1 hm J τ

end AdvancedEncryption.ExpLUT.Params
