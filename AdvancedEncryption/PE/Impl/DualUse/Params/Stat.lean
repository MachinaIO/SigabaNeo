import PE.Impl.DualUse.Params.Conf
import PE.Impl.DualUse.AHMath

/-!
# Parameters for simulated keys: the statistical terms and Ring-LWE

For the configuration `confP` (`K = 2^25`, `N = 2^34`, `|Wd| = 2^61`, flooding width `2^512`):

* **Flooding** (`flood_conf`): the hypothesis `hflood` of `DualUse.advantage_le` holds with
  `ε = 2^{-148}` (the shift `e₀ W_j` is within `|Wd| N 16 = 2^99`, and
  `|JC| N 2^99 / 2^512 ≤ 2^{119 + 34 + 99 − 512} = 2^{-260}`).
* **Leftover hash** (`delta1_le`, `delta6_le`): `|R_q| = 2^{K N} = 2^{2^59}` and
  `|Wd| ≥ 2 K N + 600`, so `δ₁, δ₆ ≤ 2^{120} · 2^{-300} / 2 ≤ 2^{-180}`.
* **Real keys are covered** (`realCovered_conf`), the hypothesis `RealCovered` of
  `DualUse.advantage_le`.

## Ring-LWE at `q = 2^K`, `K = 2^25`, ring degree `N = 2^34` (not formalized)

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
  `python/lwemodel`), not `Hardness.securityBits`. It cannot be evaluated at these sizes (the
  hybrids, Arora–GB and the dual hybrid search spaces of size `N`), but it is bounded from below
  without evaluation (`Estimator.cbd16_estimatorBits_ge`, `docs/LWE_ESTIMATOR.md`). At ring degree
  `N = 2^34`: **`2650 ≤ RingLWE.H`** at both instances (`Params/Strength.lean`:
  `ringLWE_H_registry3`, `ringLWE_H_registry5`, at explicit parameters independent of `confP`);
  the mirror gives about `2691` (`bdd`, `β ≈ 9400`). At `N = 2^33` the uSVP estimate is about
  `1193` bits (`β ≈ 4041`), not certified here.

Heuristically, the root Hermite factor a BKZ attack must reach is about `δ` with
`log₂ δ ≈ log₂ q / (4 n)` (distinguishing attack, `q ≫ σ`): here
`log₂ δ ≈ 2^25 / 2^36 = 2^{-11}`, which requires block size `β ≈ 9312` by
`δ(β) = ((β / 2πe) (πβ)^{1/β})^{1/(2(β−1))}` (core-SVP `≈ 0.292 β ≈ 2719` bits, classical), against
`β ≈ 685` (`≈ 200` bits) at `N = 2^31`.
The modulus `K = 2^25` is the fixed point of the noise analysis: `K` must exceed
`2 · 375 · log₂ G + O(log)` with `log₂ G ≈ 63 · (2 log₂ (4k + 14) + 10 log₂ (2kN + 1)) + 62 ≈ 42776`
(`Params.noise_ok`: `2^{32083266} < 2^K`), and `K = 2^24` does not suffice.
-/

namespace AdvancedEncryption.DualUse.Params

open SigabaNeo SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow
open AdvancedEncryption.DualUse.Concrete (pow_mul_le' pow_mul_le pow_le_pow')
open AdvancedEncryption.DualUse.Params.Gen (card_col)
open scoped ENNReal

instance : NeZero confP.d := ⟨by show dp ≠ 0; rw [dp_def]; positivity⟩

/-- **Real keys are covered.** -/
theorem realCovered_conf : RealCovered hkp confP := fun v hv w => goodTrap_real v hv w

/-! ### Generic bounds

The cardinalities and the statistical bounds for variable sizes, through exponents. -/

theorem card_ctBits_eq {N q k n : ℕ} [NeZero q] (hk : q < 2 ^ k) :
    Fintype.card (ringSetting N q k hk (Fin n)).ctBits.Index = 2 * (2 * k * (k * N)) := by
  show Fintype.card (Fin 2 × Col k × Fin k × Fin N) = _
  simp only [Fintype.card_prod, Fintype.card_fin]

theorem card_JC_eq {N q k n : ℕ} [NeZero q] (hk : q < 2 ^ k) :
    Fintype.card (JC (ringSetting N q k hk (Fin n))) = n * (8 * k ^ 3) * N := by
  show Fintype.card ((Fin n × (ringSetting N q k hk (Fin n)).ctBits.Index) × Col k) = _
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, card_ctBits_eq,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  ring

/-- `|JC| = 8 n k³ N ≤ 2^e`. -/
theorem card_JC_le {N q k n en c3 eN e : ℕ} [NeZero q] (hk : q < 2 ^ k) (hn : n ≤ 2 ^ en)
    (hk3 : 8 * k ^ 3 ≤ 2 ^ c3) (hN : N ≤ 2 ^ eN) (he : en + c3 + eN ≤ e) :
    Fintype.card (JC (ringSetting N q k hk (Fin n))) ≤ 2 ^ e := by
  rw [card_JC_eq]
  exact (pow_mul_le (pow_mul_le hn hk3) hN).trans (pow_le_pow' he)

/-- `|HC| = 2 n k + |JC| ≤ 2^(c + 1)`. -/
theorem card_HC_le {N q k n c : ℕ} [NeZero q] (hk : q < 2 ^ k)
    (hJC : Fintype.card (JC (ringSetting N q k hk (Fin n))) ≤ 2 ^ c) (hn : n * (2 * k) ≤ 2 ^ c) :
    Fintype.card (HC (ringSetting N q k hk (Fin n))) ≤ 2 ^ (c + 1) := by
  show Fintype.card ((Fin n × Col k) ⊕ ((Fin n × (ringSetting N q k hk (Fin n)).ctBits.Index) ×
    Col k)) ≤ _
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_col, pow_succ]
  have h3 : Fintype.card ((Fin n × (ringSetting N q k hk (Fin n)).ctBits.Index) × Col k) ≤ 2 ^ c :=
    hJC
  omega

/-- The inverse power of two in `ℝ≥0∞`. -/
theorem ofReal_inv_two_pow (n : ℕ) : ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹) = ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat]

/-- `A / 2^w ≤ 2^{-b}` when `A ≤ 2^a` and `a + b ≤ w`. -/
theorem rpow_div_le {A a b w : ℕ} (hA : A ≤ 2 ^ a) (h : a + b ≤ w) :
    (A : ℝ) / ((2 ^ w : ℕ) : ℝ) ≤ ((2 : ℝ) ^ b)⁻¹ := by
  rw [div_le_iff₀ (by positivity), Nat.cast_pow, Nat.cast_ofNat]
  have h1 : (A : ℝ) ≤ 2 ^ a := by exact_mod_cast hA
  have e : (2 : ℝ) ^ w = 2 ^ (w - b) * 2 ^ b := by rw [← pow_add]; congr 1; omega
  calc (A : ℝ) ≤ 2 ^ a := h1
    _ ≤ 2 ^ (w - b) := pow_le_pow_right₀ (by norm_num) (by omega)
    _ = ((2 : ℝ) ^ b)⁻¹ * 2 ^ w := by
        rw [e, mul_comm ((2 : ℝ) ^ (w - b)), ← mul_assoc, inv_mul_cancel₀ (by positivity),
          one_mul]

/-- **The leftover hash bound** with a slack `s`: `C · √(2^a / 2^d) / 2 ≤ 2^{-t}` when
`C ≤ 2^c`, `a + 2 s ≤ d` and `c + t ≤ s + 1`. -/
theorem lhl_le_gen {C a d c s t : ℕ} (hC : C ≤ 2 ^ c) (had : a + 2 * s ≤ d) (hcst : c + t ≤ s + 1) :
    (C : ℝ) * (Real.sqrt ((2 : ℝ) ^ a * ((2 : ℝ) ^ d)⁻¹) / 2) ≤ ((2 : ℝ) ^ t)⁻¹ := by
  have h1 : (2 : ℝ) ^ a * ((2 : ℝ) ^ d)⁻¹ ≤ (((2 : ℝ) ^ s) ^ 2)⁻¹ := by
    have e : (2 : ℝ) ^ d = 2 ^ a * 2 ^ (d - a) := by rw [← pow_add]; congr 1; omega
    rw [e, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul, ← pow_mul]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
  have h2 : Real.sqrt ((2 : ℝ) ^ a * ((2 : ℝ) ^ d)⁻¹) ≤ ((2 : ℝ) ^ s)⁻¹ := by
    calc Real.sqrt ((2 : ℝ) ^ a * ((2 : ℝ) ^ d)⁻¹) ≤ Real.sqrt ((((2 : ℝ) ^ s) ^ 2)⁻¹) :=
          Real.sqrt_le_sqrt h1
      _ = ((2 : ℝ) ^ s)⁻¹ := by
          rw [Real.sqrt_inv, Real.sqrt_sq (by positivity)]
  have hC' : (C : ℝ) ≤ 2 ^ c := by exact_mod_cast hC
  calc (C : ℝ) * (Real.sqrt ((2 : ℝ) ^ a * ((2 : ℝ) ^ d)⁻¹) / 2)
      ≤ 2 ^ c * (((2 : ℝ) ^ s)⁻¹ / 2) := by gcongr
    _ = ((2 : ℝ) ^ (s + 1 - c))⁻¹ := by
        have e : (2 : ℝ) ^ s * 2 = 2 ^ c * 2 ^ (s + 1 - c) := by
          rw [← pow_succ, ← pow_add]; congr 1; omega
        rw [div_eq_mul_inv, ← mul_inv, e, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity),
          one_mul]
    _ ≤ ((2 : ℝ) ^ t)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))

/-- **The leftover hash bound for sets of at most `2^130` columns**: `≤ 2^{-(s - 129)}` with a
slack `s ≥ 129` (`a + 2 s ≤ d`). -/
theorem lhl_le {C a d s : ℕ} (hC : C ≤ 2 ^ 130) (had : a + 2 * s ≤ d) (hs : 129 ≤ s) :
    (C : ℝ) * (Real.sqrt ((2 : ℝ) ^ a * ((2 : ℝ) ^ d)⁻¹) / 2) ≤ ((2 : ℝ) ^ (s - 129))⁻¹ :=
  lhl_le_gen hC had (by omega)

/-! ### At `confP` -/

/-- `n ≤ 2^4` attributes (`n = 10`). -/
def eAttrBits : ℕ := 4
/-- The slack of the leftover hash lemma: `|Wd| ≥ 2 K N + 2 sP`. -/
def sP : ℕ := 300

theorem card_JC : Fintype.card (JC (Sdw (N := Np) hkp)) ≤ 2 ^ 119 :=
  card_JC_le hkp (by norm_num [eAttrBits] : 10 ≤ 2 ^ eAttrBits)
    (by have := kp_le; calc 8 * kp ^ 3 ≤ 8 * (2 ^ ak) ^ 3 := by gcongr
                            _ = 2 ^ (3 + 3 * ak) := by rw [← pow_mul, pow_add]; ring_nf
    ) Np_le (by norm_num [eAttrBits, ak, an])

theorem card_HC : Fintype.card (HC (Sdw (N := Np) hkp)) ≤ 2 ^ 120 :=
  card_HC_le hkp card_JC (by
    have := kp_le
    calc 10 * (2 * kp) ≤ 10 * (2 * 2 ^ ak) := by gcongr
      _ ≤ 2 ^ 119 := by norm_num [ak])

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
  have : NeZero (2 ^ confP.w) := ⟨by positivity⟩
  have h := flood_hyp (S := Sdw (N := Np) hkp) (2 ^ confP.w) 16 rest.2.1 he₀ w
  refine CloseTo.mono h ?_
  rw [← ofReal_inv_two_pow]
  refine ENNReal.ofReal_le_ofReal ?_
  have hA : Fintype.card (JC (Sdw (N := Np) hkp)) * Np * (Fintype.card (Fin confP.d) * Np * 16)
      ≤ 2 ^ (119 + an + (ad + an + 4)) := by
    have hd : Fintype.card (Fin confP.d) * Np * 16 ≤ 2 ^ (ad + an + 4) := by
      rw [Fintype.card_fin]
      exact pow_mul_le (pow_mul_le dp_le Np_le) (le_refl (2 ^ 4))
    exact pow_mul_le (pow_mul_le card_JC Np_le) hd
  have := rpow_div_le hA (show 119 + an + (ad + an + 4) + 148 ≤ confP.w by
    show _ ≤ wP; norm_num [an, ad, wP])
  push_cast at this ⊢
  exact this

/-- The number of elements of the ring. -/
theorem card_Rg : Fintype.card (Rg Np Kp) = 2 ^ (Kp * Np) := by
  rw [Fintype.card_congr Negacyclic.coeffsEquiv, Fintype.card_fun, Fintype.card_fin, ZMod.card,
    ← pow_mul]

theorem KN_le : Kp * Np + 2 * sP ≤ dp := by rw [Kp_def, Np_def, dp_def]; norm_num [sP]

theorem KN2_le : 2 * (Kp * Np) + 2 * sP ≤ dp := by rw [Kp_def, Np_def, dp_def]; norm_num [sP]

/-- **The statistical term of hybrid 1** is at most `2^{-180}`. -/
theorem delta1_le : delta1 (Sdw (N := Np) hkp) (Fin confP.d) ≤ ((2 : ℝ≥0∞) ^ 180)⁻¹ := by
  rw [← ofReal_inv_two_pow, delta1]
  refine ENNReal.ofReal_le_ofReal ?_
  have hc : (Fintype.card (Fin 1 → Rg Np Kp) : ℝ) = (2 : ℝ) ^ (Kp * Np) := by
    rw [Fintype.card_fun, card_Rg, Fintype.card_fin, pow_one]; push_cast; rfl
  rw [hc, Fintype.card_fin]
  exact lhl_le_gen card_JC KN_le (by norm_num [sP])

/-- **The statistical term of hybrid 6** is at most `2^{-180}`. -/
theorem delta6_le : delta6 (Sdw (N := Np) hkp) (Fin confP.d) ≤ ((2 : ℝ≥0∞) ^ 180)⁻¹ := by
  rw [← ofReal_inv_two_pow, delta6]
  refine ENNReal.ofReal_le_ofReal ?_
  have hc : (Fintype.card (Fin 2 → Rg Np Kp) : ℝ) = (2 : ℝ) ^ (2 * (Kp * Np)) := by
    rw [Fintype.card_fun, card_Rg, Fintype.card_fin, ← pow_mul, mul_comm (Kp * Np) 2]
    push_cast; rfl
  rw [hc, Fintype.card_fin]
  exact lhl_le_gen card_HC KN2_le (by norm_num [sP])

end AdvancedEncryption.DualUse.Params
