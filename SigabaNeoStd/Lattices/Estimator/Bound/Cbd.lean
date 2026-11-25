import SigabaNeoStd.Lattices.Estimator.Bound

/-!
# Lower bounds at a centered binomial secret and error, `q = 2^e`

`cbdP n e M` is the LWE instance of dimension `n`, modulus `2^e`, secret and error `CBD(16)` and
`M` samples. `cbd16_estimatorBits_ge` reduces `kb ≤ estimatorBits (cbdP n e M)` to closed numeric
facts (`cbdFacts`, one evaluation) and to a check per block size `b < maxBeta + 2` (`cbdCheck`,
evaluated in chunks). None of them evaluates the modulus.
-/

namespace SigabaNeo.Lattices.Estimator

open Fx

/-- The instance: dimension `n`, modulus `2^e`, `CBD(16)` secret and error, `M` samples. -/
def cbdP (n e M : ℕ) : LWEParams := LWEParams.mk' n (2 ^ e) (ND.cbd 16) (ND.cbd 16) (some M)

/-- The standard deviation of `CBD(16)`. -/
def cbdSigma : Fx := (ND.cbd 16).stddev

/-- The check of block size `b` for the scanning and hybrid attacks at the target `kb` bits. -/
def cbdCheck (n e M kb : ℕ) (b : ℕ) : Bool :=
  PrimalHybrid.check ((kb : ℤ) * ONE) (n - (kb + 22)) ((e : ℤ) * ONE) 0 (log2 cbdSigma) 90 b &&
    (decide (b < 40) || decide (maxBeta ≤ b) ||
      (Usvp.check ((kb : ℤ) * ONE) ((e : ℤ) * ONE) (cbdP n e M) b &&
        Dual.check ((kb : ℤ) * ONE) ((e : ℤ) * ONE) (cbdP n e M) b &&
        DualHybrid.check ((kb : ℤ) * ONE) n ((e : ℤ) * ONE) (log2 cbdSigma) kb b))

/-- The closed numeric facts. -/
def cbdFacts (n e M kb : ℕ) : Bool :=
  decide (kb ≤ 4673) &&
    (decide (1024 ≤ e) &&
    (decide (10050 ≤ n) &&
    (costGeB ((kb : ℤ) * ONE) (Guess.mitmCostW (cbdP n e M) true 0) &&
    (decide (Bkw.erf (div (Bkw.zOf (cbdP n e M)) (Fx.sqrt (2 * cbdSigma))) = ONE) &&
    (decide (0 ≤ Bkw.zOf (cbdP n e M)) &&
    (decide (0 ≤ DualHybrid.coeffOf cbdSigma) &&
    (decide (ONE ≤ DualHybrid.enumCostOf cbdSigma) &&
    (decide (0 ≤ DualHybrid.hOf cbdSigma) &&
    (decide (0 ≤ DualHybrid.alphaOf cbdSigma) &&
    (decide (kb ≤ n) &&
    (decide ((cbdP n e M).Xs.hammingWeight.toNat ≤ n) &&
    (decide (4 * (n - (cbdP n e M).Xs.hammingWeight.toNat) ≤ n) &&
    (decide ((kb : ℤ) * ONE + 20 * ONE ≤ (2 * (cbdP n e M).Xs.hammingWeight.toNat : ℤ) * ONE) &&
    (decide (NumPrimal.c0 * 90 ≤ -((kb : ℤ) * ONE + 21 * ONE)) &&
    (decide (maxBeta + 1 + 90 ≤ n - (kb + 22)) &&
    (decide (maxBeta + 1 + 90 + (kb + 22) ≤ M + n) &&
    (decide ((kb : ℤ) * ONE ≤ 600 * log2Nat 33) &&
    (decide (2 * (50 + 1) * (2 ^ 20 + 1) ≤ n - 600) &&
    (decide (56 * M ≤ (n - 600) * (2 ^ 20) ^ 6) &&
    (decide (0 < 33 → 8 * 33 ≤ (2 ^ 20) ^ (33 - 1)) &&
    (decide ((kb : ℤ) * ONE ≤ 2 * log2Nat (PrimalHybrid.choose (n - 600 + (50 + 1)) (50 + 1))) &&
    (decide (600 ≤ n) &&
    (decide ((cbdP n e M).Xs.isSparse = false) &&
    decide ((floor (NumMisc.width (cbdP n e M).Xs)).toNat = 33))))))))))))))))))))))))

theorem cbdP_normalize (n e M : ℕ) : (cbdP n e M).normalize = cbdP n e M := by
  unfold LWEParams.normalize
  have : ¬ (cbdP n e M).Xe.stddev < (cbdP n e M).Xs.stddev := lt_irrefl _
  simp [this]

theorem cbdP_q (n e M : ℕ) : (cbdP n e M).q = 2 ^ e := rfl

theorem mk'_cbd_normalize (n q : ℕ) (m : Option ℕ) (X Y : ND) (hX : X.kind = .cbd 16)
    (hY : Y.kind = .cbd 16) :
    (LWEParams.mk' n q X Y m).normalize = LWEParams.mk' n q X Y m := by
  unfold LWEParams.normalize
  have e1 : (LWEParams.mk' n q X Y m).Xe.stddev = cbdSigma := by
    simp only [LWEParams.mk']; split <;> simp [ND.resize, ND.stddev, hY, cbdSigma, ND.cbd]
  have e2 : (LWEParams.mk' n q X Y m).Xs.stddev = cbdSigma := by
    simp [LWEParams.mk', ND.resize, ND.stddev, hX, cbdSigma, ND.cbd]
  have : ¬ (LWEParams.mk' n q X Y m).Xe.stddev < (LWEParams.mk' n q X Y m).Xs.stddev := by
    rw [e1, e2]; exact lt_irrefl _
  simp [this]

end SigabaNeo.Lattices.Estimator

namespace SigabaNeo.Lattices.Estimator

open Fx

theorem cbdSigma_eq_Xs (n e M : ℕ) : (cbdP n e M).Xs.stddev = cbdSigma := rfl
theorem cbdSigma_eq_Xe (n e M : ℕ) : (cbdP n e M).Xe.stddev = cbdSigma := rfl

theorem cbd_log2Xi (n e M : ℕ) : Usvp.log2Xi (cbdP n e M) = 0 := by
  unfold Usvp.log2Xi; rw [cbdSigma_eq_Xs, cbdSigma_eq_Xe]; simp

/-- `single` at a `CBD(16)` instance of dimension `n'` with `M` samples costs at least the bound of
`gb_ge` at `K₀ = 50`, `R = 2^20`. -/
theorem cbd_single_ge {n' q M : ℕ} {X Y : ND} (hX : X.kind = .cbd 16) (hY : Y.kind = .cbd 16)
    {K : Fx} (hR1 : 2 * (50 + 1) * (2 ^ 20 + 1) ≤ n') (hR2 : 56 * M ≤ n' * (2 ^ 20) ^ 6)
    (hK : K ≤ 2 * log2Nat ((n' + (50 + 1)).choose (50 + 1))) :
    CostGe K (AroraGB.single (LWEParams.mk' n' q X Y (some M))) := by
  have hN := mk'_cbd_normalize n' q (some M) X Y hX hY
  have hσs : (LWEParams.mk' n' q X Y (some M)).Xs.stddev = cbdSigma := by
    simp [LWEParams.mk', ND.resize, ND.stddev, hX, cbdSigma, ND.cbd]
  have hσe : (LWEParams.mk' n' q X Y (some M)).Xe.stddev = cbdSigma := by
    simp [LWEParams.mk', ND.resize, ND.stddev, hY, cbdSigma, ND.cbd]
  have hs33 : AroraGB.sOf (LWEParams.mk' n' q X Y (some M)) = 33 := by
    unfold AroraGB.sOf
    rw [hσs, hσe]; simp only [lt_irrefl, ↓reduceIte]
    simp [LWEParams.mk', ND.resize, hX, NumMisc.width, ND.bounds]
    decide
  have hw : (floor (NumMisc.width (LWEParams.mk' n' q X Y (some M)).Xe)).toNat = 33 := by
    simp [LWEParams.mk', ND.resize, hY, NumMisc.width, ND.bounds]; decide
  have hc3 : (ceil (LWEParams.mk' n' q X Y (some M)).Xe.stddev).toNat = 3 := by
    rw [hσe]; decide +kernel
  apply AroraGB.single_ge
  · intro d m' s' hd hm hs'
    rw [hN] at hm hs' ⊢
    rw [hs33] at hs'
    subst hs'
    have hm' : m' ≤ M := hm M rfl
    have hg := AroraGB.gb_ge (n := n') (d := d) (m := m') (s := 33) (K₀ := 50) (R := 2 ^ 20)
      (by omega) (by omega) (by norm_num) (by simpa using hR1)
      (AroraGB.hmd_of (by norm_num) hm' hR2 d hd) (fun _ => by norm_num)
    exact hg.mono hK
  · rw [hN, hw]; norm_num
  · rw [hN, hc3]

theorem cbd_single_nonneg {n' q M : ℕ} {X Y : ND} (hX : X.kind = .cbd 16) (hY : Y.kind = .cbd 16) :
    CostGe 0 (AroraGB.single (LWEParams.mk' n' q X Y (some M))) := by
  have hN := mk'_cbd_normalize n' q (some M) X Y hX hY
  have hσe : (LWEParams.mk' n' q X Y (some M)).Xe.stddev = cbdSigma := by
    simp [LWEParams.mk', ND.resize, ND.stddev, hY, cbdSigma, ND.cbd]
  have hw : (floor (NumMisc.width (LWEParams.mk' n' q X Y (some M)).Xe)).toNat = 33 := by
    simp [LWEParams.mk', ND.resize, hY, NumMisc.width, ND.bounds]; decide
  have hc3 : (ceil (LWEParams.mk' n' q X Y (some M)).Xe.stddev).toNat = 3 := by
    rw [hσe]; decide +kernel
  apply AroraGB.single_ge
  · intro d m' s' _ _ _; exact AroraGB.gb_nonneg _ _ _ _
  · rw [hN, hw]; norm_num
  · rw [hN, hc3]

/-- **`kb ≤ estimatorBits (cbdP n e M)`** from the closed facts and the per-block-size checks. -/
theorem cbd16_estimatorBits_ge {n e M kb : ℕ} (hf : cbdFacts n e M kb = true)
    (hc : ∀ b < maxBeta + 2, cbdCheck n e M kb b = true) : kb ≤ estimatorBits (cbdP n e M) := by
  simp only [cbdFacts, Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨hkb, he, hn, hmitm, herf, hz, hcoeff, henum, hh, halpha, hkbn, hhn, h4, hK2, hW, hDu,
    hm, hpen, hR1, hR2, hR3, hbound, h600, hsparse, hw33⟩ := hf
  set P := cbdP n e M with hP
  have hN := cbdP_normalize n e M
  set K : Fx := (kb : ℤ) * ONE
  have hO := ONE_pos
  apply estimatorBits_ge_of hkb
  · -- arora
    have hkindXs : (cbdP n e M).Xs.kind = .cbd 16 := rfl
    have hkindXe : (cbdP n e M).Xe.kind = .cbd 16 := rfl
    have hch : ∀ n', (n' + (50 + 1)).choose (50 + 1) = PrimalHybrid.choose (n' + (50 + 1)) (50 + 1) :=
      fun n' => (PrimalHybrid.choose_eq _ _).symm
    have hK' : ∀ n', n - 600 ≤ n' → K ≤ 2 * log2Nat ((n' + (50 + 1)).choose (50 + 1)) := by
      intro n' hn'
      refine hbound.trans ?_
      rw [← hch]
      have := log2Nat_mono (Nat.choose_le_choose (50 + 1) (show n - 600 + (50 + 1) ≤ n' + (50 + 1) by omega))
      linarith
    apply AroraGB.cost_ge 600 (by rw [hN]; exact hsparse) (by rw [hN]; intro s hs; cases hs)
      (by rw [hN, hw33]; exact hpen)
    · rw [hN]
      show CostGe K (AroraGB.single (LWEParams.mk' n (2 ^ e) (ND.cbd 16) (ND.cbd 16) (some M)))
      exact cbd_single_ge (n' := n) (q := 2 ^ e) (M := M) (X := ND.cbd 16) (Y := ND.cbd 16) rfl rfl
        (le_trans hR1 (Nat.sub_le n 600)) (le_trans hR2 (Nat.mul_le_mul_right _ (Nat.sub_le n 600)))
        (hK' n (Nat.sub_le n 600))
    · intro z hz
      rw [hN]
      show CostGe K (AroraGB.single (LWEParams.mk' (n - z) (2 ^ e) (cbdP n e M).Xs (cbdP n e M).Xe
        (some M)))
      exact cbd_single_ge (n' := n - z) (q := 2 ^ e) (M := M) (X := (cbdP n e M).Xs)
        (Y := (cbdP n e M).Xe) hkindXs hkindXe (by omega)
        (le_trans hR2 (Nat.mul_le_mul_right _ (by omega))) (hK' _ (by omega))
    · intro z
      rw [hN]
      show CostGe 0 (AroraGB.single (LWEParams.mk' (n - z) (2 ^ e) (cbdP n e M).Xs (cbdP n e M).Xe
        (some M)))
      exact cbd_single_nonneg (n' := n - z) (q := 2 ^ e) (M := M) (X := (cbdP n e M).Xs)
        (Y := (cbdP n e M).Xe) hkindXs hkindXe
  · -- bkw
    rw [Bkw.cost_eq_none (e := e) rfl he (by rw [hN, cbdSigma_eq_Xs, cbdSigma_eq_Xe]; exact lt_irrefl _)
      (by rw [hN]; exact hz) (by rw [hN, cbdSigma_eq_Xe]; exact herf)]
    exact costGe_none _
  · -- usvp
    rw [Usvp.cost_eq_of_q (e := e) rfl]
    apply Usvp.costQ_ge
    intro β hβ1 hβ2
    have := hc β (by omega)
    simp only [cbdCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at this
    obtain ⟨-, h⟩ := this
    rcases h with (h | h) | h
    · omega
    · omega
    · exact Usvp.check_spec (by omega) h.1.1
  · -- bdd
    show CostGe K (PrimalHybrid.estimate P false true)
    apply PrimalHybrid.estimate_ge (Z₁ := kb + 22) (W := 90) (a := -16) (b := 16)
    · rw [hN]; intro s hs; cases hs
    · rw [hN]; rfl
    · decide
    · rw [hN]; exact hhn
    · rw [hN]; exact h4
    · rw [hN, cbdP_q, log2Nat_two_pow, cbd_log2Xi, sub_zero]
      exact mul_nonneg (Int.natCast_nonneg e) (le_of_lt ONE_pos)
    · push_cast; linarith
    · rw [hN]; exact hK2
    · exact_mod_cast hW
    · rw [hN]; exact hDu
    · rw [hN, cbdSigma_eq_Xs, cbdSigma_eq_Xe, if_pos le_rfl]
      intro M' hM'
      simp only [cbdP, LWEParams.mk', Option.map_some, Option.some.injEq] at hM'
      omega
    · intro b hb
      have := hc b hb
      simp only [cbdCheck, Bool.and_eq_true] at this
      rw [hN, cbdP_q, log2Nat_two_pow, cbd_log2Xi, cbdSigma_eq_Xe]
      exact this.1
  · -- bdd hybrid
    show CostGe K (PrimalHybrid.estimate P false false)
    apply PrimalHybrid.estimate_ge (Z₁ := kb + 22) (W := 90) (a := -16) (b := 16)
    · rw [hN]; intro s hs; cases hs
    · rw [hN]; rfl
    · decide
    · rw [hN]; exact hhn
    · rw [hN]; exact h4
    · rw [hN, cbdP_q, log2Nat_two_pow, cbd_log2Xi, sub_zero]
      exact mul_nonneg (Int.natCast_nonneg e) (le_of_lt ONE_pos)
    · push_cast; linarith
    · rw [hN]; exact hK2
    · exact_mod_cast hW
    · rw [hN]; exact hDu
    · rw [hN, cbdSigma_eq_Xs, cbdSigma_eq_Xe, if_pos le_rfl]
      intro M' hM'
      simp only [cbdP, LWEParams.mk', Option.map_some, Option.some.injEq] at hM'
      omega
    · intro b hb
      have := hc b hb
      simp only [cbdCheck, Bool.and_eq_true] at this
      rw [hN, cbdP_q, log2Nat_two_pow, cbd_log2Xi, cbdSigma_eq_Xe]
      exact this.1
  · -- mitm hybrid
    show CostGe K (PrimalHybrid.estimate P true false)
    apply PrimalHybrid.estimate_ge (Z₁ := kb + 22) (W := 90) (a := -16) (b := 16)
    · rw [hN]; intro s hs; cases hs
    · rw [hN]; rfl
    · decide
    · rw [hN]; exact hhn
    · rw [hN]; exact h4
    · rw [hN, cbdP_q, log2Nat_two_pow, cbd_log2Xi, sub_zero]
      exact mul_nonneg (Int.natCast_nonneg e) (le_of_lt ONE_pos)
    · push_cast; linarith
    · rw [hN]; exact hK2
    · exact_mod_cast hW
    · rw [hN]; exact hDu
    · rw [hN, cbdSigma_eq_Xs, cbdSigma_eq_Xe, if_pos le_rfl]
      intro M' hM'
      simp only [cbdP, LWEParams.mk', Option.map_some, Option.some.injEq] at hM'
      omega
    · intro b hb
      have := hc b hb
      simp only [cbdCheck, Bool.and_eq_true] at this
      rw [hN, cbdP_q, log2Nat_two_pow, cbd_log2Xi, cbdSigma_eq_Xe]
      exact this.1
  · -- dual
    rw [Dual.cost_eq_of_q (e := e) rfl]
    apply Dual.costQ_ge
    intro b hb1 hb2
    have := hc b (by omega)
    simp only [cbdCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at this
    obtain ⟨-, h⟩ := this
    rcases h with (h | h) | h
    · omega
    · omega
    · exact Dual.check_spec (by omega) h.1.2
  · -- dual hybrid
    apply DualHybrid.cost_ge (kb := kb) (by rw [hN]; rfl) (by rw [hN]; exact hcoeff) (by rw [hN]; exact henum)
      (by rw [hN]; exact hh) (by rw [hN]; exact halpha) le_rfl (by rw [hN]; exact hkbn)
    intro b hb1 hb2
    have := hc b (by omega)
    simp only [cbdCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at this
    obtain ⟨-, h⟩ := this
    rcases h with (h | h) | h
    · omega
    · omega
    · rw [hN, cbdP_q, log2Nat_two_pow, cbdSigma_eq_Xe]; exact h.2
  · -- exhaustive search
    rw [Guess.exhaustiveCost_eq_none (by rw [hN]; intro s hs; cases hs)
      (by rw [hN]; exact (by decide : (2 : ℤ) ≤ floor (NumMisc.width (ND.cbd 16))))
      (by rw [hN]; exact hn)]
    exact costGe_none _
  · -- mitm
    rw [Guess.mitmCost_eq (e := e) rfl
      (by rw [hN]; exact (by decide : (0 : ℤ) ≤ NumMisc.width (ND.cbd 16))) (by
      rw [hN]
      calc NumMisc.width P.Xe = 33 * ONE := rfl
        _ < 2 ^ 54 := by decide
        _ ≤ 2 ^ e := pow_le_pow_right₀ (by norm_num) (by omega)), hN]
    exact costGe_iff.mpr hmitm

end SigabaNeo.Lattices.Estimator
