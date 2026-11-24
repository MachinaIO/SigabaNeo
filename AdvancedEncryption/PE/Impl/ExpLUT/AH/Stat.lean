import PE.Impl.ExpLUT.AH.Conf

/-!
# The statistical terms at the concrete parameters (package G)

With `m̄ = 3 N K + 408` (P's `mbar`), `|R| ≤ 2^{NK}`, at most `2^57` programmed columns
(`lhlCols_le`), `τ = 2^16` and `ε_U = N 2^{−K} = 2^{24 − 2^16}`:

* `delta1_le`, `delta5_le`: `≤ 2^{−147}` (leftover hash lemma, seeds of 2 and 3 rows);
* `deltaT_le`: `≤ 2^{−187}`;
* `epsSetup_le`, `epsCT_le`: `≤ 2^{−150}` (the machines' near-uniform public matrices);
* `epsRed_le`: `≤ 2^{−150}` (the machines' reduction secret);
* `statW_le`: `statW Dc ε_fl ≤ 2^{−140}` for `ε_fl ≤ 2^{−148}`, so `4 · 2^128 · statW² ≤ 1`
  (`hstat_Dc`).
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Lattices Cslib Cslib.Probability AdvancedEncryption.ExpLUT.Params
open scoped ENNReal

/-- `ofReal (2^{−k}) = 2^{−k}`. -/
theorem ofReal_two_pow_inv (k : ℕ) : ENNReal.ofReal (((2 : ℝ) ^ k)⁻¹) = ((2 : ℝ≥0∞) ^ k)⁻¹ := by
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
  simp

/-- **The leftover hash term in exponents** (generic: no large number is evaluated). -/
theorem lhl_term_le {I c m e a k : ℕ} (hc : c ≤ 2 ^ e) (hm : e + 2 * a ≤ m) (hI : I ≤ 2 ^ k)
    (hk : k + 1 ≤ a) :
    ENNReal.ofReal ((I : ℝ) * (Real.sqrt ((c : ℝ) * ((2 : ℝ) ^ m)⁻¹) / 2)) ≤
      ((2 : ℝ≥0∞) ^ (a - k + 1))⁻¹ := by
  rw [← ofReal_two_pow_inv]
  refine ENNReal.ofReal_le_ofReal ?_
  have h2a : (c : ℝ) * ((2 : ℝ) ^ m)⁻¹ ≤ (((2 : ℝ) ^ a)⁻¹) ^ 2 := by
    have hc' : (c : ℝ) ≤ (2 : ℝ) ^ e := by exact_mod_cast hc
    have hm' : (2 : ℝ) ^ (e + 2 * a) ≤ (2 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    rw [inv_pow, ← pow_mul, mul_comm a 2]
    calc (c : ℝ) * ((2 : ℝ) ^ m)⁻¹ ≤ (2 : ℝ) ^ e * ((2 : ℝ) ^ (e + 2 * a))⁻¹ :=
          mul_le_mul hc' (inv_anti₀ (by positivity) hm') (by positivity) (by positivity)
      _ = ((2 : ℝ) ^ (2 * a))⁻¹ := by rw [pow_add]; field_simp
  have hs : Real.sqrt ((c : ℝ) * ((2 : ℝ) ^ m)⁻¹) ≤ ((2 : ℝ) ^ a)⁻¹ :=
    (Real.sqrt_le_sqrt h2a).trans (by rw [Real.sqrt_sq (by positivity)])
  have hI' : (I : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast hI
  have ea : (2 : ℝ) ^ a = (2 : ℝ) ^ (a - k + 1) * (2 : ℝ) ^ k / 2 := by
    rw [← pow_add, show a - k + 1 + k = a + 1 by omega, pow_succ]; ring
  calc (I : ℝ) * (Real.sqrt ((c : ℝ) * ((2 : ℝ) ^ m)⁻¹) / 2)
      ≤ (2 : ℝ) ^ k * (((2 : ℝ) ^ a)⁻¹ / 2) :=
        mul_le_mul hI' (by linarith) (by positivity) (by positivity)
    _ = ((2 : ℝ) ^ (a - k + 1))⁻¹ := by rw [ea]; field_simp

theorem card_Rg_Dc_le : Fintype.card (Rg Dc) ≤ 2 ^ (Kc * 2 ^ en) := card_Rc_le

theorem card_Wb_Dc : Fintype.card (Wb Dc) = mbar := Fintype.card_fin _

theorem card_PrI_gen (K : ℕ) : 16 * (2 * K) + (2 * K + (16 * (2 * (2 * K * K) * (2 * K)) +
    22 * (2 * (2 * K * K) * (2 * K)))) ≤ 2 * K + 16 * (2 * K) + (16 + 22) * (8 * K ^ 3) + 1 := by
  ring_nf; omega

theorem card_PrI_le : Fintype.card (PrI (setting Dc) Pos) ≤ 2 ^ 57 := by
  refine le_trans ?_ lhlCols_le
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_sum]
  simp only [Fintype.card_prod, Fintype.card_fin]
  exact card_PrI_gen Kc

theorem mbar_split_gen {M Y X a : ℕ} (hM : M = Y + 2 * (140 + 64)) (hX : X ≤ Y) (ha : a ≤ 204) :
    X + 2 * a ≤ M := by
  omega

theorem mbar_split (a : ℕ) (ha : a ≤ 204) (r : ℕ) (hr : r ≤ 3) :
    r * (Kc * 2 ^ en) + 2 * a ≤ mbar :=
  mbar_split_gen mbar_def (by rw [mul_comm Kc]; exact Nat.mul_le_mul_right _ hr) ha

theorem card_fun_le (n : ℕ) : Fintype.card (Fin n → Rg Dc) ≤ 2 ^ (n * (Kc * 2 ^ en)) := by
  rw [Fintype.card_fun, Fintype.card_fin]
  calc Fintype.card (Rg Dc) ^ n ≤ (2 ^ (Kc * 2 ^ en)) ^ n := Nat.pow_le_pow_left card_Rg_Dc_le n
    _ = 2 ^ (n * (Kc * 2 ^ en)) := by rw [← pow_mul, mul_comm]

/-- **H1**: `delta1 ≤ 2^{−147}`. -/
theorem delta1_le : delta1 (setting Dc) (Wb Dc) Pos ≤ ((2 : ℝ≥0∞) ^ (204 - 57 + 1))⁻¹ := by
  unfold delta1
  rw [card_Wb_Dc]
  exact lhl_term_le (a := 204) (k := 57) (card_fun_le 2) (mbar_split 204 le_rfl 2 (by norm_num))
    card_PrI_le (by norm_num)

/-- **H5**: `delta5 ≤ 2^{−147}`. -/
theorem delta5_le : delta5 (setting Dc) (Wb Dc) Pos ≤ ((2 : ℝ≥0∞) ^ (204 - 57 + 1))⁻¹ := by
  unfold delta5
  rw [card_Wb_Dc]
  exact lhl_term_le (a := 204) (k := 57) (card_fun_le 3) (mbar_split 204 le_rfl 3 le_rfl)
    card_PrI_le (by norm_num)

/-- **H3′, H6**: `deltaT ≤ 2^{−187}`. -/
theorem deltaT_le : deltaT (setting Dc) (Wb Dc) ≤ ((2 : ℝ≥0∞) ^ (204 - 16 + 1))⁻¹ := by
  unfold deltaT
  rw [card_Wb_Dc]
  exact lhl_term_le (a := 204) (k := 16) (card_fun_le 2) (mbar_split 204 le_rfl 2 (by norm_num))
    (by rw [Fintype.card_fin]; exact Kc_le) (by norm_num)

/-! ### The machines' near-uniform laws -/

/-- `2^a · 2^{−c} ≤ 2^{−b}` for `a + b ≤ c` (generic in the exponents). -/
theorem two_pow_mul_inv_le {a b c : ℕ} (h : a + b ≤ c) :
    (2 : ℝ≥0∞) ^ a * ((2 : ℝ≥0∞) ^ c)⁻¹ ≤ ((2 : ℝ≥0∞) ^ b)⁻¹ := by
  have h0 : (2 : ℝ≥0∞) ^ a ≠ 0 := pow_ne_zero _ two_ne_zero
  have hT : (2 : ℝ≥0∞) ^ a ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  calc (2 : ℝ≥0∞) ^ a * ((2 : ℝ≥0∞) ^ c)⁻¹ ≤ (2 : ℝ≥0∞) ^ a * ((2 : ℝ≥0∞) ^ (a + b))⁻¹ := by
        gcongr; first | exact h | norm_num
    _ = ((2 : ℝ≥0∞) ^ b)⁻¹ := by
        rw [pow_add, ENNReal.mul_inv (Or.inl h0) (Or.inl hT), ← mul_assoc,
          ENNReal.mul_inv_cancel h0 hT, one_mul]

theorem nSet_gen {M K : ℕ} (hM : M ≤ 2 ^ 42) (hK : K ≤ 2 ^ 16) :
    M + ((M + K) + (2 * 22 * (2 * (2 * K)) + (16 * (2 * K) + (2 * (2 * K) +
      (16 * (2 * (2 * K) * K * (2 * (2 * K))) + (22 * (2 * (2 * K) * K * (2 * (2 * K))) +
        2)))))) ≤ 2 ^ 63 := by
  have h3 : K ^ 3 ≤ (2 ^ 16) ^ 3 := Nat.pow_le_pow_left hK 3
  have h2 : K ^ 2 ≤ (2 ^ 16) ^ 2 := Nat.pow_le_pow_left hK 2
  ring_nf
  ring_nf at h3 h2
  omega

theorem nCT_gen {M K : ℕ} (hM : M ≤ 2 ^ 42) (hK : K ≤ 2 ^ 16) :
    (M + K) + (2 * 22 * (2 * K) + (22 * (2 * (2 * K) * K * (2 * K)) + (16 * (2 * K) +
      (16 * (2 * (2 * K) * K * (2 * K)) + (2 * K + 1))))) ≤ 2 ^ 63 := by
  have h3 : K ^ 3 ≤ (2 ^ 16) ^ 3 := Nat.pow_le_pow_left hK 3
  have h2 : K ^ 2 ≤ (2 ^ 16) ^ 2 := Nat.pow_le_pow_left hK 2
  ring_nf
  ring_nf at h3 h2
  omega

theorem Dc_mb : Dc.mb = mbar := rfl
theorem Dc_K : Dc.K = Kc := rfl

theorem mbar_le42 : mbar ≤ 2 ^ 42 := le_trans (Nat.le_add_right _ _) mbar_le

theorem epsU_Dc : epsU Dc = ((2 ^ en : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ Kc)⁻¹ := rfl

/-- `n · ε_U ≤ 2^{−150}` for `n ≤ 2^63`. -/
theorem mul_epsU_le {n : ℕ} (hn : n ≤ 2 ^ 63) : (n : ℝ≥0∞) * epsU Dc ≤ ((2 : ℝ≥0∞) ^ 150)⁻¹ := by
  rw [epsU_Dc, ← mul_assoc]
  have hn' : (n : ℝ≥0∞) * ((2 ^ en : ℕ) : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ 87 := by
    have : n * 2 ^ en ≤ 2 ^ 87 := pow_mul_le' hn le_rfl rfl
    exact_mod_cast this
  calc (n : ℝ≥0∞) * ((2 ^ en : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ Kc)⁻¹
      ≤ (2 : ℝ≥0∞) ^ 87 * ((2 : ℝ≥0∞) ^ Kc)⁻¹ := by gcongr
    _ ≤ _ := two_pow_mul_inv_le (by rw [Kc_def]; norm_num)

/-- **The machines' `Setup`**: `epsSetup ≤ 2^{−150}`. -/
theorem epsSetup_le : epsSetup Dc ≤ ((2 : ℝ≥0∞) ^ 150)⁻¹ := by
  have h := mul_epsU_le (nSet_gen (M := mbar) (K := Kc) mbar_le42 Kc_le)
  refine le_trans (le_of_eq ?_) h
  unfold epsSetup
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_Wb_Dc]
  simp only [Dc_mb, Dc_K, Dc_b, w8_len]
  push_cast
  ring

/-- **The simulator's ciphertext**: `epsCT ≤ 2^{−150}`. -/
theorem epsCT_le : epsCT Dc ≤ ((2 : ℝ≥0∞) ^ 150)⁻¹ := by
  have h := mul_epsU_le (nCT_gen (M := mbar) (K := Kc) mbar_le42 Kc_le)
  refine le_trans (le_of_eq ?_) h
  unfold epsCT
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_Wb_Dc]
  simp only [Dc_mb, Dc_K, Dc_b, w8_len]
  push_cast
  ring

theorem nRed_gen {M K : ℕ} (hM : M ≤ 2 ^ 42) (hK : K ≤ 2 ^ 16) :
    (M + K) + (22 * 2 * (2 * K) + 1) ≤ 2 ^ 63 := by
  omega

/-- **The machines' reduction secret**: `epsRed ≤ 2^{−150}`. -/
theorem epsRed_le : epsRed Dc ≤ ((2 : ℝ≥0∞) ^ 150)⁻¹ := by
  have h := mul_epsU_le (nRed_gen (M := mbar) (K := Kc) mbar_le42 Kc_le)
  refine le_trans (le_of_eq ?_) h
  unfold epsRed
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_Wb_Dc]
  simp only [Dc_mb, Dc_K, Dc_b]
  push_cast
  ring

/-! ### All the statistical terms -/

theorem inv_pow_mono {a b : ℕ} (h : a ≤ b) : ((2 : ℝ≥0∞) ^ b)⁻¹ ≤ ((2 : ℝ≥0∞) ^ a)⁻¹ :=
  ENNReal.inv_le_inv.mpr (pow_le_pow_right₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2) h)

/-- **The statistical terms at the concrete parameters**: `statW Dc ε_fl ≤ 2^{−140}` for
`ε_fl ≤ 2^{−148}`. -/
theorem statW_le {εfl : ℝ≥0∞} (hfl : εfl ≤ ((2 : ℝ≥0∞) ^ 148)⁻¹) :
    statW Dc εfl ≤ ((2 : ℝ≥0∞) ^ 140)⁻¹ := by
  set x : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ 148)⁻¹
  have hS : epsSetup Dc ≤ x := epsSetup_le.trans (inv_pow_mono (by norm_num))
  have hC : epsCT Dc ≤ x := epsCT_le.trans (inv_pow_mono (by norm_num))
  have h1 : delta1 (setting Dc) (Wb Dc) Pos ≤ x := delta1_le
  have h5 : delta5 (setting Dc) (Wb Dc) Pos ≤ x := delta5_le
  have hT : deltaT (setting Dc) (Wb Dc) ≤ x := deltaT_le.trans (inv_pow_mono (by norm_num))
  have hR : epsRed Dc ≤ x := epsRed_le.trans (inv_pow_mono (by norm_num))
  unfold statW statW0
  calc _ ≤ x + (x + x + x + x + x) + (x + x) + (x + x) := by gcongr
    _ ≤ 16 * x := by ring_nf; gcongr; norm_num
    _ ≤ _ := by
        have h0 : (2 : ℝ≥0∞) ^ 140 ≠ 0 := pow_ne_zero _ two_ne_zero
        have hT' : (2 : ℝ≥0∞) ^ 140 ≠ ⊤ := ENNReal.pow_ne_top (by simp)
        have e : x = ((2 : ℝ≥0∞) ^ 8)⁻¹ * ((2 : ℝ≥0∞) ^ 140)⁻¹ := by
          rw [← ENNReal.mul_inv (Or.inl (pow_ne_zero _ two_ne_zero))
            (Or.inl (ENNReal.pow_ne_top (by simp))), ← pow_add]
        rw [e, ← mul_assoc]
        refine mul_le_of_le_one_left (zero_le (a := ((2 : ℝ≥0∞) ^ 140)⁻¹)) ?_
        rw [show (16 : ℝ≥0∞) = 2 ^ 4 by norm_num]
        exact (two_pow_mul_inv_le (a := 4) (b := 0) (c := 8) (by norm_num)).trans (by simp)

theorem statW_ne_top {εfl : ℝ≥0∞} (hfl : εfl ≤ ((2 : ℝ≥0∞) ^ 148)⁻¹) : statW Dc εfl ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.inv_ne_top.mpr (pow_ne_zero _ two_ne_zero)) (statW_le hfl)

/-- **The quadratic-loss condition** `4 · 2^128 · statW² ≤ 1`. -/
theorem hstat_Dc {εfl : ℝ≥0∞} (hfl : εfl ≤ ((2 : ℝ≥0∞) ^ 148)⁻¹) :
    4 * (2 : ℝ) ^ 128 * (statW Dc εfl).toReal ^ 2 ≤ 1 := by
  have h := ENNReal.toReal_mono (ENNReal.inv_ne_top.mpr (pow_ne_zero _ two_ne_zero)) (statW_le hfl)
  rw [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at h
  have h0 : 0 ≤ (statW Dc εfl).toReal := ENNReal.toReal_nonneg
  have hsq : (statW Dc εfl).toReal ^ 2 ≤ (((2 : ℝ) ^ 140)⁻¹) ^ 2 := pow_le_pow_left₀ h0 h 2
  calc 4 * (2 : ℝ) ^ 128 * (statW Dc εfl).toReal ^ 2 ≤ 4 * (2 : ℝ) ^ 128 * (((2 : ℝ) ^ 140)⁻¹) ^ 2 := by
        gcongr
    _ ≤ 1 := by norm_num

end AdvancedEncryption.ExpLUT.Prog
