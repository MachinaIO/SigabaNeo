import PE.Impl.DualUse.Params.Conf
import PE.Impl.DualUse.AHMath

/-!
# Parameters for simulated keys: the statistical terms

For the configuration `confP` (`K = 2^27`, `N = 2^36`, `|Wd| = 2^65`, flooding width `2^768`,
`nA = 128` attribute bits):

* **Flooding** (`flood_conf`): the hypothesis `hflood` of `DualUse.advantage_le` holds with
  `ε = 2^{-499}` (the shift `e₀ W_j` is within `|Wd| N 16 = 2^105`, and
  `|JC| N 2^105 / 2^768 ≤ 2^{128 + 36 + 105 − 768}`).
* **Leftover hash** (`delta1_le`, `delta6_le`): `|R_q| = 2^{K N} = 2^{2^63}` and
  `|Wd| ≥ 2 K N + 1000`, so `δ₁, δ₆ ≤ 2^{-370}`.
* **Real keys are covered** (`realCovered_conf`), the hypothesis `RealCovered` of
  `DualUse.advantage_le`.

The Ring-LWE strength of the two instances of the reductions (`params3`, `params5` at `N = 2^36`,
`q = 2^(2^27)`) is certified in `Params/Strength.lean` (`2650 ≤ RingLWE.H`). The ratio
`log₂ q / N = 2^{-9}` is that of the earlier configuration; the modulus `K = 2^27` is fixed by the
noise of the depth-`1054` circuits (`Params.noise_ok`: `2^{102113082} < 2^K`).
-/

namespace AdvancedEncryption.DualUse.Params

open SigabaNeo SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord
open AdvancedEncryption.DualUse.Concrete (pow_mul_le' pow_mul_le pow_le_pow')
open AdvancedEncryption.DualUse.Params.Gen (card_col)
open scoped ENNReal

instance : NeZero confP.d := ⟨by show dp ≠ 0; rw [dp_def]; positivity⟩

/-- **Real keys are covered.** -/
theorem realCovered_conf : RealCovered hkp confP := fun v hv C _ => goodTrap_real v hv C

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

/-- `nA ≤ 2^7` attributes bits (`nA = 128`). -/
def eAttrBits : ℕ := 7
/-- The slack of the leftover hash lemma: `|Wd| ≥ 2 K N + 2 sP`. -/
def sP : ℕ := 500

theorem kp_le' : kp ≤ 2 ^ 27 + 1 := by rw [kp, Kp_def]

theorem k3_le : 8 * kp ^ 3 ≤ 2 ^ 85 := by
  calc 8 * kp ^ 3 ≤ 8 * (2 ^ 27 + 1) ^ 3 := by gcongr; exact kp_le'
    _ ≤ 2 ^ 85 := by norm_num

/-- `|JC| ≤ 2^128` for `128` attribute bits. -/
theorem card_JC : Fintype.card (JC (Sdw (N := Np) hkp)) ≤ 2 ^ 128 :=
  card_JC_le hkp (by norm_num : nA ≤ 2 ^ 7) k3_le Np_le (by norm_num [an])

/-- `|HC| ≤ 2^129`. -/
theorem card_HC : Fintype.card (HC (Sdw (N := Np) hkp)) ≤ 2 ^ 129 :=
  card_HC_le hkp card_JC (by
    have := kp_le
    calc nA * (2 * kp) ≤ nA * (2 * 2 ^ ak) := by gcongr
      _ ≤ 2 ^ 128 := by norm_num [ak])

set_option exponentiation.threshold 1000 in
/-- **The flooding hypothesis** with `ε = 2^{-499}`. -/
theorem flood_conf : ∀ rest ∈ (lawRestC hkp confP).support,
    ∀ w : JC (Sdw (N := Np) hkp) → (Fin confP.d → Bool),
      CloseTo ((lawEc hkp confP).map fun e j => e j + rest.2.1 * wMat w j) (lawEc hkp confP)
        ((2 : ℝ≥0∞) ^ 499)⁻¹ := by
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
      ≤ 2 ^ (128 + an + (ad + an + 4)) := by
    have hd : Fintype.card (Fin confP.d) * Np * 16 ≤ 2 ^ (ad + an + 4) := by
      rw [Fintype.card_fin]
      exact pow_mul_le (pow_mul_le dp_le Np_le) (le_refl (2 ^ 4))
    exact pow_mul_le (pow_mul_le card_JC Np_le) hd
  have := rpow_div_le hA (show 128 + an + (ad + an + 4) + 499 ≤ confP.w by
    show _ ≤ wP; norm_num [an, ad, wP])
  push_cast at this ⊢
  exact this

/-- The number of elements of the ring. -/
theorem card_Rg : Fintype.card (Rg Np Kp) = 2 ^ (Kp * Np) := by
  rw [Fintype.card_congr Negacyclic.coeffsEquiv, Fintype.card_fun, Fintype.card_fin, ZMod.card,
    ← pow_mul]

theorem KN_le : Kp * Np + 2 * sP ≤ dp := by rw [Kp_def, Np_def, dp_def]; norm_num [sP]

theorem KN2_le : 2 * (Kp * Np) + 2 * sP ≤ dp := by rw [Kp_def, Np_def, dp_def]; norm_num [sP]

/-- **The statistical term of hybrid 1** is at most `2^{-370}`. -/
theorem delta1_le : delta1 (Sdw (N := Np) hkp) (Fin confP.d) ≤ ((2 : ℝ≥0∞) ^ 370)⁻¹ := by
  rw [← ofReal_inv_two_pow, delta1]
  refine ENNReal.ofReal_le_ofReal ?_
  have hc : (Fintype.card (Fin 1 → Rg Np Kp) : ℝ) = (2 : ℝ) ^ (Kp * Np) := by
    rw [Fintype.card_fun, card_Rg, Fintype.card_fin, pow_one]; push_cast; rfl
  rw [hc, Fintype.card_fin]
  exact lhl_le_gen (c := 130) (card_JC.trans (by norm_num)) KN_le (by norm_num [sP])

/-- **The statistical term of hybrid 6** is at most `2^{-370}`. -/
theorem delta6_le : delta6 (Sdw (N := Np) hkp) (Fin confP.d) ≤ ((2 : ℝ≥0∞) ^ 370)⁻¹ := by
  rw [← ofReal_inv_two_pow, delta6]
  refine ENNReal.ofReal_le_ofReal ?_
  have hc : (Fintype.card (Fin 2 → Rg Np Kp) : ℝ) = (2 : ℝ) ^ (2 * (Kp * Np)) := by
    rw [Fintype.card_fun, card_Rg, Fintype.card_fin, ← pow_mul, mul_comm (Kp * Np) 2]
    push_cast; rfl
  rw [hc, Fintype.card_fin]
  exact lhl_le_gen (c := 130) (card_HC.trans (by norm_num)) KN2_le (by norm_num [sP])

end AdvancedEncryption.DualUse.Params
