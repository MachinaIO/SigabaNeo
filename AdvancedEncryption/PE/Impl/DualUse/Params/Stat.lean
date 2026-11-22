import PE.Impl.DualUse.Params.Conf
import PE.Impl.DualUse.AHMath

/-!
# Parameters for simulated keys: the statistical terms and Ring-LWE

For the configuration `confP` (`K = 2^25`, `N = 2^33`, `|Wd| = 2^60`, flooding width `2^512`):

* **Flooding** (`flood_conf`): the hypothesis `hflood` of `DualUse.advantage_le` holds with
  `ε = 2^{-148}` (the shift `e₀ W_j` is within `|Wd| N 16 = 2^97`, and
  `|JC| N 2^97 / 2^512 ≤ 2^{118 + 33 + 97 − 512} = 2^{-264}`).
* **Leftover hash** (`delta1_le`, `delta6_le`): `|R_q| = 2^{K N} = 2^{2^58}` and
  `|Wd| ≥ 2 K N + 600`, so `δ₁, δ₆ ≤ 2^{119} · 2^{-300} / 2 ≤ 2^{-180}`.
* **Real keys are covered** (`realCovered_conf`), the hypothesis `RealCovered` of
  `DualUse.advantage_le`.

## Ring-LWE at `q = 2^K`, `K = 2^25`, ring degree `N = 2^33` (not formalized)

The errors are centered binomial of width `16` (`σ = 2√2`), and the secret follows the same law
(normal form). The Ring-LWE instances of the reductions are `params3 Np (2^Kp) kp (cbd 16)`
(`2k` samples) and `params5 Np (2^Kp) kp (Fin dp) (cbd 16)` (`|Wd| + 4k + 1` samples) of
`DualUse/Registry.lean`.

* **Conservative bound** (`SigabaNeo/Lib/Lattices/Hardness.lean`, `Hardness.securityBits`; its
  mirror `python/lwe_hardness.py`): at both instances it gives `153` bits at `N = 2^31`, `434` at
  `N = 2^32` and `991` at `N = 2^33`. At `N = 2^33` this is the cap `bitsCap − log₂ N = 1024 − 33`:
  every modelled attack costs more than `2^{1024}`. Hence `N = 2^33`.
* **The registry's `RingLWE.H`** is `ModuleLWE.H`, the floor of the minimum over the formalized
  attacks of the lattice estimator (`SigabaNeo/Lib/Lattices/Estimator`, mirror
  `python/lwemodel`), not `Hardness.securityBits`. Its value at these sizes is not computed here.
  The mirror does not finish at `N = 2^33`: BDD, the dual hybrid, BKW and exhaustive search run
  for over two minutes each there, and Arora–Ge and the primal hybrids already take over 40 s
  each at `N = 2^15`, `q = 2^{1024}`. Nothing is proved about it here (`Params/Strength.lean`).

Heuristically, the root Hermite factor a BKZ attack must reach is about `δ` with
`log₂ δ ≈ log₂ q / (4 n)` (distinguishing attack, `q ≫ σ`): here
`log₂ δ ≈ 2^25 / 2^35 = 2^{-10}`, which requires block size `β ≈ 4041` by
`δ(β) = ((β / 2πe) (πβ)^{1/β})^{1/(2(β−1))}` (core-SVP `≈ 0.292 β ≈ 1180` bits, classical), against
`β ≈ 685` (`≈ 200` bits) at `N = 2^31`.
The modulus `K = 2^25` is the fixed point of the noise analysis: `K` must exceed
`2 · 375 · log₂ G + O(log)` with `log₂ G ≈ 62 · (2 log₂ (4k + 14) + 10 log₂ (2kN + 1)) + 61 ≈ 41477`
(`Params.noise_ok`: `2^{31109008} < 2^K`), and `K = 2^24` does not suffice.
-/

namespace AdvancedEncryption.DualUse.Params

open SigabaNeo SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow
open AdvancedEncryption.DualUse.Concrete (pow_mul_le' pow_le_pow')
open scoped ENNReal

instance : NeZero confP.d := ⟨by show dp ≠ 0; rw [dp_def]; positivity⟩

/-- **Real keys are covered.** -/
theorem realCovered_conf : RealCovered hkp confP := fun v hv w => goodTrap_real v hv w

theorem card_ctBits : Fintype.card (Sdw (N := Np) hkp).ctBits.Index ≤ 2 ^ 87 := by
  show Fintype.card (Fin 2 × Col kp × Fin kp × Fin Np) ≤ 2 ^ 87
  simp only [Fintype.card_prod, Fintype.card_fin]
  have := kp_le
  have hN := Np_le
  calc 2 * (2 * kp * (kp * Np)) ≤ 2 * (2 * 2 ^ 26 * (2 ^ 26 * 2 ^ 33)) := by gcongr
    _ = 2 ^ 87 := by norm_num

theorem card_JC : Fintype.card (JC (Sdw (N := Np) hkp)) ≤ 2 ^ 118 := by
  show Fintype.card ((Fin 10 × (Sdw (N := Np) hkp).ctBits.Index) × Col kp) ≤ 2 ^ 118
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, card_colP]
  have h1 := card_ctBits
  have h2 := kp_le
  calc 10 * Fintype.card (Sdw (N := Np) hkp).ctBits.Index * (2 * kp)
      ≤ 2 ^ 4 * 2 ^ 87 * (2 * 2 ^ 26) := by gcongr; norm_num
    _ = 2 ^ 118 := by norm_num

theorem card_HC : Fintype.card (HC (Sdw (N := Np) hkp)) ≤ 2 ^ 119 := by
  show Fintype.card ((Fin 10 × Col kp) ⊕ ((Fin 10 × (Sdw (N := Np) hkp).ctBits.Index) × Col kp))
    ≤ 2 ^ 119
  rw [Fintype.card_sum]
  have h1 := card_JC
  have h2 : Fintype.card (Fin 10 × Col kp) ≤ 2 ^ 118 := by
    rw [Fintype.card_prod, Fintype.card_fin, card_colP]
    have := kp_le
    calc 10 * (2 * kp) ≤ 10 * (2 * 2 ^ 26) := by gcongr
      _ ≤ 2 ^ 118 := by norm_num
  have h3 : Fintype.card ((Fin 10 × (Sdw (N := Np) hkp).ctBits.Index) × Col kp) ≤ 2 ^ 118 := h1
  have : (2 : ℕ) ^ 119 = 2 ^ 118 + 2 ^ 118 := by norm_num
  omega

/-- The inverse power of two in `ℝ≥0∞`. -/
theorem ofReal_inv_two_pow (n : ℕ) : ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹) = ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat]

theorem rpow_div_le {A a b : ℕ} (hA : A ≤ 2 ^ a) (h : a + b ≤ 512) :
    (A : ℝ) / ((2 ^ 512 : ℕ) : ℝ) ≤ ((2 : ℝ) ^ b)⁻¹ := by
  rw [div_le_iff₀ (by positivity), Nat.cast_pow, Nat.cast_ofNat]
  have h1 : (A : ℝ) ≤ 2 ^ a := by exact_mod_cast hA
  have e : (2 : ℝ) ^ 512 = 2 ^ (512 - b) * 2 ^ b := by rw [← pow_add]; congr 1; omega
  calc (A : ℝ) ≤ 2 ^ a := h1
    _ ≤ 2 ^ (512 - b) := pow_le_pow_right₀ (by norm_num) (by omega)
    _ = ((2 : ℝ) ^ b)⁻¹ * 2 ^ 512 := by
        rw [e, mul_comm ((2 : ℝ) ^ (512 - b)), ← mul_assoc, inv_mul_cancel₀ (by positivity),
          one_mul]

set_option exponentiation.threshold 600 in
/-- **The flooding hypothesis** with `ε = 2^{-148}`. -/
theorem flood_conf : ∀ rest ∈ (lawRestC hkp confP).support,
    ∀ w : JC (Sdw (N := Np) hkp) → (Fin confP.d → Bool),
      CloseTo ((lawEc hkp confP).map fun e j => e j + rest.2.1 * wMat w j) (lawEc hkp confP)
        ((2 : ℝ≥0∞) ^ 148)⁻¹ := by
  intro rest hrest w
  have he₀ : rnorm rest.2.1 ≤ 16 := by
    simp only [lawRestC, lawRestNF, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hrest
    obtain ⟨σ, -, u₀, -, e₀, he₀, ea, -, ez, -, Rm, -, e', -, rfl⟩ := hrest
    exact rowLaw_short (fun a ha => polyOf_short χp_short ha) he₀
  have : NeZero (2 ^ 512) := ⟨by positivity⟩
  have h := flood_hyp (S := Sdw (N := Np) hkp) (2 ^ 512) 16 rest.2.1 he₀ w
  refine CloseTo.mono h ?_
  rw [← ofReal_inv_two_pow]
  refine ENNReal.ofReal_le_ofReal ?_
  have hA : Fintype.card (JC (Sdw (N := Np) hkp)) * Np * (Fintype.card (Fin confP.d) * Np * 16)
      ≤ 2 ^ 248 := by
    have hd : Fintype.card (Fin confP.d) * Np * 16 ≤ 2 ^ 97 := by
      rw [Fintype.card_fin]
      show dp * Np * 16 ≤ 2 ^ 97
      rw [dp_def, Np_def]; norm_num
    exact pow_mul_le' (pow_mul_le' card_JC Np_le rfl) hd rfl
  have := rpow_div_le hA (show 248 + 148 ≤ 512 by norm_num)
  push_cast at this ⊢
  exact this

/-- The number of elements of the ring. -/
theorem card_Rg : Fintype.card (Rg Np Kp) = 2 ^ (Kp * Np) := by
  rw [Fintype.card_congr Negacyclic.coeffsEquiv, Fintype.card_fun, Fintype.card_fin, ZMod.card,
    ← pow_mul]

/-- The leftover hash bound: `|JC| · √(2^{a} / 2^{d}) / 2 ≤ 2^{-180}` when `a + 600 ≤ d`. -/
theorem lhl_le {C a d : ℕ} (hC : C ≤ 2 ^ 119) (had : a + 600 ≤ d) :
    (C : ℝ) * (Real.sqrt ((2 : ℝ) ^ a * ((2 : ℝ) ^ d)⁻¹) / 2) ≤ ((2 : ℝ) ^ 180)⁻¹ := by
  have h1 : (2 : ℝ) ^ a * ((2 : ℝ) ^ d)⁻¹ ≤ (((2 : ℝ) ^ 300) ^ 2)⁻¹ := by
    have e : (2 : ℝ) ^ d = 2 ^ a * 2 ^ (d - a) := by rw [← pow_add]; congr 1; omega
    rw [e, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul, ← pow_mul]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
  have h2 : Real.sqrt ((2 : ℝ) ^ a * ((2 : ℝ) ^ d)⁻¹) ≤ ((2 : ℝ) ^ 300)⁻¹ := by
    calc Real.sqrt ((2 : ℝ) ^ a * ((2 : ℝ) ^ d)⁻¹) ≤ Real.sqrt ((((2 : ℝ) ^ 300) ^ 2)⁻¹) :=
          Real.sqrt_le_sqrt h1
      _ = ((2 : ℝ) ^ 300)⁻¹ := by
          rw [Real.sqrt_inv, Real.sqrt_sq (by positivity)]
  have hC' : (C : ℝ) ≤ 2 ^ 119 := by exact_mod_cast hC
  calc (C : ℝ) * (Real.sqrt ((2 : ℝ) ^ a * ((2 : ℝ) ^ d)⁻¹) / 2)
      ≤ 2 ^ 119 * (((2 : ℝ) ^ 300)⁻¹ / 2) := by gcongr
    _ = ((2 : ℝ) ^ 182)⁻¹ := by
        have e : (2 : ℝ) ^ 300 * 2 = 2 ^ 119 * 2 ^ 182 := by rw [← pow_succ, ← pow_add]
        rw [div_eq_mul_inv, ← mul_inv, e, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity),
          one_mul]
    _ ≤ ((2 : ℝ) ^ 180)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by norm_num))

theorem KN_le : Kp * Np + 600 ≤ dp := by rw [Kp_def, Np_def, dp_def]; norm_num

theorem KN2_le : 2 * (Kp * Np) + 600 ≤ dp := by rw [Kp_def, Np_def, dp_def]; norm_num

/-- **The statistical term of hybrid 1** is at most `2^{-180}`. -/
theorem delta1_le : delta1 (Sdw (N := Np) hkp) (Fin confP.d) ≤ ((2 : ℝ≥0∞) ^ 180)⁻¹ := by
  rw [← ofReal_inv_two_pow, delta1]
  refine ENNReal.ofReal_le_ofReal ?_
  have hc : (Fintype.card (Fin 1 → Rg Np Kp) : ℝ) = (2 : ℝ) ^ (Kp * Np) := by
    rw [Fintype.card_fun, card_Rg, Fintype.card_fin, pow_one]; push_cast; rfl
  rw [hc, Fintype.card_fin]
  exact lhl_le (card_JC.trans (pow_le_pow' (by norm_num))) KN_le

/-- **The statistical term of hybrid 6** is at most `2^{-180}`. -/
theorem delta6_le : delta6 (Sdw (N := Np) hkp) (Fin confP.d) ≤ ((2 : ℝ≥0∞) ^ 180)⁻¹ := by
  rw [← ofReal_inv_two_pow, delta6]
  refine ENNReal.ofReal_le_ofReal ?_
  have hc : (Fintype.card (Fin 2 → Rg Np Kp) : ℝ) = (2 : ℝ) ^ (2 * (Kp * Np)) := by
    rw [Fintype.card_fun, card_Rg, Fintype.card_fin, ← pow_mul, mul_comm (Kp * Np) 2]
    push_cast; rfl
  rw [hc, Fintype.card_fin]
  exact lhl_le card_HC KN2_le

end AdvancedEncryption.DualUse.Params
