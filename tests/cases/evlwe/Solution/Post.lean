import Solution.PostFacts

/-!
# The attack on Post: success probabilities

* `ev_real_rej_le`: on `postReal`, the attack rejects with probability at most
  `Pr_B[B not smooth] + k·3·2^{−m} + m·6·4^{−m} + Pr_T[some T_j near an end]`.
* `ev_rand_acc_le`: on `postRandom`, it accepts with probability at most
  `ρ + Pr_B[B has a nonzero left kernel vector] + Pr_P[P has a zero column]`,
  `ρ = (7(h + 1) + 16) / (8(h + 1))`.
-/

namespace TestCase.EvLWE

open SigabaNeo.Lattices

open TestCase TestCase.EvLWE Cslib.Probability
open scoped ENNReal Matrix

section
variable {κ : ℕ}

/-- The bound on `|e·K_j|`: `m · σ√m · τ√m = m² σ τ = m² 2^{5κ+7}`. -/
def Δn (κ : ℕ) : ℕ := m κ ^ 2 * 2 ^ (5 * κ + 7)

/-- `T_j` away from both ends of `[0, ⌊q/2⌋]`. -/
noncomputable def GoodT (κ : ℕ) (t : Fin ((q κ - 1) / 2 + 1)) : Prop := Δn κ ≤ 2 * t.val ∧ 2 * t.val + Δn κ < q κ

noncomputable instance (κ : ℕ) : DecidablePred (GoodT κ) := fun _ => by unfold GoodT; infer_instance

theorem Δn_real (κ : ℕ) : (Δn κ : ℝ) = (m κ : ℝ) ^ 2 * (σ κ * τ κ) := by
  unfold Δn σ τ; push_cast
  rw [← pow_add]; ring_nf

theorem two_tau_sqrt_lt (κ : ℕ) : 2 * (τ κ * Real.sqrt (m κ)) < q κ := by
  have hq := q_gt κ
  have hk := two_pow_ge κ
  have hm := m_le_real κ
  have hs := Real.sq_sqrt (Nat.cast_nonneg (m κ) : (0 : ℝ) ≤ m κ)
  have hs0 := Real.sqrt_nonneg (m κ : ℝ)
  set x : ℝ := 2 ^ κ
  have hx : 1 ≤ x := one_le_pow₀ (by norm_num)
  have hτ : τ κ = 8 * x := by unfold τ; rw [pow_add]; ring
  have hw8 : w κ = κ * 8 + 8 := by unfold w; ring
  have hw : (2 : ℝ) ^ w κ = 256 * x ^ 8 := by
    rw [hw8, pow_add, pow_mul]
    ring
  rw [hw] at hq
  rw [hτ]
  by_contra hc
  push Not at hc
  have hq0 : (0 : ℝ) < q κ := q_pos κ
  have h1 : (q κ : ℝ) ^ 2 ≤ (2 * (8 * x * Real.sqrt (m κ))) ^ 2 := pow_le_pow_left₀ hq0.le hc 2
  have h2 : (2 * (8 * x * Real.sqrt (m κ))) ^ 2 = 256 * x ^ 2 * m κ := by
    rw [mul_pow, mul_pow, mul_pow, hs]; ring
  have h3 : (256 * x ^ 8) ^ 2 < (q κ : ℝ) ^ 2 := pow_lt_pow_left₀ hq (by positivity) (by norm_num)
  have h4 : (κ : ℝ) + 1 ≤ x := hk
  have h5 : ((κ : ℝ) + 1) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by positivity) h4 2
  have hx2 : 1 ≤ x ^ 2 := one_le_pow₀ hx
  have hx16 : x ^ 4 ≤ x ^ 16 := pow_le_pow_right₀ hx (by norm_num)
  nlinarith

/-- The attack accepts a real sample whose `K`, `E` and `T` are good. -/
theorem real_accept (d : Draw κ) (K : Matrix (Fin (m κ)) (Fin (k κ)) ℤ)
    (E : Matrix (Fin (ell κ)) (Fin (m κ)) ℤ)
    (hBK : ∀ j, d.B *ᵥ (fun r => (K r j : ZMod (q κ))) = fun i => d.P i j)
    (hK : ∀ r j, |((K r j : ℤ) : ℝ)| < τ κ * Real.sqrt (m κ))
    (hE : ∀ i r, |((E i r : ℤ) : ℝ)| < σ κ * Real.sqrt (m κ))
    (hT : ∀ j, GoodT κ (d.T (i0 κ) j)) :
    parityOut κ (encSample κ (matVals (d.Sq * d.B + intMod (q κ) E) ++
      matVals (intMod (q κ) K) ++ matVals d.aux)) = true := by
  have hτs := two_tau_sqrt_lt κ
  have hsm : (0 : ℝ) ≤ Real.sqrt (m κ) := Real.sqrt_nonneg _
  have hsm2 := Real.sq_sqrt (Nat.cast_nonneg (m κ) : (0 : ℝ) ≤ m κ)
  -- the integer `e·K_j` is below `Δ`
  have hEK : ∀ j, |((∑ r, E (i0 κ) r * K r j : ℤ) : ℝ)| < Δn κ := by
    intro j
    rw [Δn_real]
    push_cast
    calc |∑ r, ((E (i0 κ) r : ℤ) : ℝ) * ((K r j : ℤ) : ℝ)|
        ≤ ∑ r, |((E (i0 κ) r : ℤ) : ℝ) * ((K r j : ℤ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ < ∑ _r : Fin (m κ), (σ κ * Real.sqrt (m κ)) * (τ κ * Real.sqrt (m κ)) := by
          apply Finset.sum_lt_sum_of_nonempty
          · exact ⟨⟨0, m_pos κ⟩, Finset.mem_univ _⟩
          · intro r _
            rw [abs_mul]
            exact mul_lt_mul'' (hE _ r) (hK r j) (abs_nonneg _) (abs_nonneg _)
      _ = (m κ : ℝ) ^ 2 * (σ κ * τ κ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have : (σ κ * Real.sqrt (m κ)) * (τ κ * Real.sqrt (m κ)) =
              σ κ * τ κ * Real.sqrt (m κ) ^ 2 := by ring
          rw [this, hsm2]; ring
  refine parityOut_good (Cq := d.Sq * d.B + intMod (q κ) E) (Kz := K) (Aq := d.aux)
    (fun r => E (i0 κ) r) (fun j => (d.T (i0 κ) j).val) ?_ ?_ ?_ ?_
  · intro r j
    have h := hK r j
    have : ((2 * |K r j| : ℤ) : ℝ) < q κ := by push_cast; linarith
    exact_mod_cast this
  · intro j
    have hPj : ∀ i, d.P i j = ∑ r, d.B i r * (K r j : ZMod (q κ)) := fun i =>
      (congrFun (hBK j) i).symm
    simp only [Draw.aux, Draw.Sq, Matrix.add_apply, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.smul_apply, intMod, Matrix.map_apply, hPj, add_mul, Finset.sum_add_distrib,
      Finset.sum_mul, Finset.mul_sum, smul_eq_mul]
    rw [Finset.sum_comm]
    push_cast
    ring_nf
  · intro j
    have h := hEK j
    have ht := (hT j).1
    have : (0 : ℝ) ≤ ((∑ r, E (i0 κ) r * K r j : ℤ) : ℝ) + 2 * ((d.T (i0 κ) j).val : ℝ) := by
      have : (Δn κ : ℝ) ≤ 2 * ((d.T (i0 κ) j).val : ℝ) := by exact_mod_cast ht
      have := neg_abs_le ((∑ r, E (i0 κ) r * K r j : ℤ) : ℝ)
      linarith
    exact_mod_cast this
  · intro j
    have h := hEK j
    have ht := (hT j).2
    have : ((∑ r, E (i0 κ) r * K r j : ℤ) : ℝ) + 2 * ((d.T (i0 κ) j).val : ℝ) < q κ := by
      have : 2 * ((d.T (i0 κ) j).val : ℝ) + Δn κ < q κ := by exact_mod_cast ht
      have := le_abs_self ((∑ r, E (i0 κ) r * K r j : ℤ) : ℝ)
      linarith
    exact_mod_cast this

/-! ### Marginals of `draw` -/

theorem ev_draw (F : Draw κ → ℝ≥0∞) :
    ev (draw κ) F = ev (PMF.uniformOfFintype (Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ))))
      fun B => ev (PMF.uniformOfFintype (Matrix (Fin (n κ)) (Fin (k κ)) (ZMod (q κ))))
      fun P => ev (sampleMat (gaussZ (σLWE κ) (σLWE_pos κ)) (ell κ) (n κ))
      fun S => ev (PMF.uniformOfFintype
        (Matrix (Fin (ell κ)) (Fin (k κ)) (Fin ((q κ - 1) / 2 + 1))))
      fun T => F ⟨B, P, S, T⟩ := by
  simp only [draw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, ev_bind, ev_pure]

theorem ev_draw_B (f : Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ)) → ℝ≥0∞) :
    ev (draw κ) (fun d => f d.B) =
      ev (PMF.uniformOfFintype (Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ)))) f := by
  simp only [ev_draw, ev_const]

theorem ev_draw_T (f : Matrix (Fin (ell κ)) (Fin (k κ)) (Fin ((q κ - 1) / 2 + 1)) → ℝ≥0∞) :
    ev (draw κ) (fun d => f d.T) = ev (PMF.uniformOfFintype
      (Matrix (Fin (ell κ)) (Fin (k κ)) (Fin ((q κ - 1) / 2 + 1)))) f := by
  simp only [ev_draw, ev_const]

/-! ### The real side -/

/-- The bad events of the real side. -/
noncomputable def errReal (κ : ℕ) : ℝ≥0∞ :=
  ev (PMF.uniformOfFintype (Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ))))
      (fun B => ind (¬ dualMassE B (τ κ) ≤ 1 / 2)) +
    (k κ : ℝ≥0∞) * ENNReal.ofReal (3 * (1 / 2) ^ m κ) +
    (m κ : ℝ≥0∞) * ENNReal.ofReal (6 * (1 / 4) ^ m κ) +
    ev (PMF.uniformOfFintype (Matrix (Fin (ell κ)) (Fin (k κ)) (Fin ((q κ - 1) / 2 + 1))))
      (fun T => ind (∃ j ∈ Finset.univ, T (i0 κ) j ∈ Finset.univ.filter fun t => ¬ GoodT κ t))

theorem ev_real_rej_le (κ : ℕ) :
    ev (postReal κ) (fun w => ind (¬ parityOut κ w = true)) ≤ errReal κ := by
  simp only [postReal, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, ev_bind, ev_pure]
  set εK := (k κ : ℝ≥0∞) * ENNReal.ofReal (3 * (1 / 2) ^ m κ)
  set εE := (m κ : ℝ≥0∞) * ENNReal.ofReal (6 * (1 / 4) ^ m κ)
  let badT : Draw κ → ℝ≥0∞ := fun d =>
    ind (∃ j ∈ Finset.univ, d.T (i0 κ) j ∈ Finset.univ.filter fun t => ¬ GoodT κ t)
  let badB : Draw κ → ℝ≥0∞ := fun d => ind (¬ dualMassE d.B (τ κ) ≤ 1 / 2)
  have hd : ∀ d : Draw κ, ev (preimage d) (fun K? => ev (sampleMat (gaussZ (σ κ) (σ_pos κ))
      (ell κ) (m κ)) fun E => ind (¬ parityOut κ (match K? with
        | none => []
        | some K => encSample κ (matVals (d.Sq * d.B + intMod (q κ) E) ++
            matVals (intMod (q κ) K) ++ matVals d.aux)) = true)) ≤
      badB d + εK + εE + badT d := by
    intro d
    let longK : Option (Matrix (Fin (m κ)) (Fin (k κ)) ℤ) → ℝ≥0∞ := fun K? => match K? with
      | none => 0
      | some K => ind (∃ r j, τ κ * Real.sqrt (m κ) ≤ |((K r j : ℤ) : ℝ)|)
    have hpt : ∀ K? ∈ (preimage d).support, ev (sampleMat (gaussZ (σ κ) (σ_pos κ)) (ell κ) (m κ))
        (fun E => ind (¬ parityOut κ (match K? with
          | none => []
          | some K => encSample κ (matVals (d.Sq * d.B + intMod (q κ) E) ++
              matVals (intMod (q κ) K) ++ matVals d.aux)) = true)) ≤ longK K? + εE + badT d := by
      intro K? hK?
      calc _ ≤ ev (sampleMat (gaussZ (σ κ) (σ_pos κ)) (ell κ) (m κ)) (fun E => longK K? +
            ind (∃ i r, σ κ * Real.sqrt (m κ) ≤ |((E i r : ℤ) : ℝ)|) + badT d) := by
            refine ev_mono _ fun E => ?_
            cases K? with
            | none => simp [parityOut_nil, ind_of_not]
            | some K =>
              by_cases hall : (¬ ∃ r j, τ κ * Real.sqrt (m κ) ≤ |((K r j : ℤ) : ℝ)|) ∧
                  (¬ ∃ i r, σ κ * Real.sqrt (m κ) ≤ |((E i r : ℤ) : ℝ)|) ∧
                  ¬ (∃ j ∈ Finset.univ, d.T (i0 κ) j ∈ Finset.univ.filter fun t => ¬ GoodT κ t)
              · obtain ⟨h1, h2, h3⟩ := hall
                push Not at h1 h2 h3
                have hacc := real_accept d K E (preimage_support d hK?) h1 h2 fun j => by
                  have := h3 j (Finset.mem_univ _)
                  simpa using this
                simp only [hacc, not_true_eq_false]
                rw [ind_of_not (by simp)]; exact zero_le
              · rw [not_and_or, not_and_or, not_not, not_not, not_not] at hall
                calc _ ≤ (1 : ℝ≥0∞) := ind_le_one _
                  _ ≤ _ := by
                    rcases hall with h | h | h
                    · calc (1 : ℝ≥0∞) = longK (some K) := (ind_of h).symm
                        _ ≤ _ := le_add_right (le_add_right le_rfl)
                    · calc (1 : ℝ≥0∞) = ind (∃ i r, σ κ * Real.sqrt (m κ) ≤ |((E i r : ℤ) : ℝ)|) :=
                            (ind_of h).symm
                        _ ≤ _ := le_add_right (le_add_left le_rfl)
                    · calc (1 : ℝ≥0∞) = badT d := (ind_of h).symm
                        _ ≤ _ := le_add_left le_rfl
        _ = longK K? + ev (sampleMat (gaussZ (σ κ) (σ_pos κ)) (ell κ) (m κ))
              (fun E => ind (∃ i r, σ κ * Real.sqrt (m κ) ≤ |((E i r : ℤ) : ℝ)|)) + badT d := by
            rw [ev_add, ev_add, ev_const, ev_const]
        _ ≤ _ := by gcongr; exact ev_E_long_le
    calc _ ≤ ev (preimage d) (fun K? => longK K? + εE + badT d) := ev_mono_supp _ hpt
      _ = ev (preimage d) longK + εE + badT d := by rw [ev_add, ev_add, ev_const, ev_const]
      _ ≤ badB d + εK + εE + badT d := by
          gcongr
          by_cases hB : dualMassE d.B (τ κ) ≤ 1 / 2
          · exact (ev_preimage_long_le d hB).trans le_add_self
          · calc ev (preimage d) longK ≤ 1 := ev_le_const _ fun K? => by
                  cases K? with
                  | none => exact zero_le
                  | some K => exact ind_le_one _
              _ = badB d := (ind_of hB).symm
              _ ≤ _ := le_self_add
  calc _ ≤ ev (draw κ) (fun d => badB d + εK + εE + badT d) := ev_mono _ hd
    _ = _ := by
        rw [ev_add, ev_add, ev_add, ev_const, ev_const, ev_draw_B (fun B =>
          ind (¬ dualMassE B (τ κ) ≤ 1 / 2)), ev_draw_T (fun T =>
            ind (∃ j ∈ Finset.univ, T (i0 κ) j ∈ Finset.univ.filter fun t => ¬ GoodT κ t))]
        rfl

/-! ### The random side -/

/-- `ρ = (7(h + 1) + 16) / (8(h + 1))`. -/
noncomputable def ρ (κ : ℕ) : ℝ≥0∞ :=
  ((7 * ((q κ - 1) / 2 + 1) + 16 : ℕ) : ℝ≥0∞) / ((8 * ((q κ - 1) / 2 + 1) : ℕ) : ℝ≥0∞)

theorem ev_CT_le (S : Matrix (Fin (ell κ)) (Fin (n κ)) ℤ)
    (P : Matrix (Fin (n κ)) (Fin (k κ)) (ZMod (q κ)))
    (Kq : Matrix (Fin (m κ)) (Fin (k κ)) (ZMod (q κ))) (hK : ∀ j, (fun r => Kq r j) ≠ 0) :
    ev (PMF.uniformOfFintype (Matrix (Fin (ell κ)) (Fin (k κ)) (Fin ((q κ - 1) / 2 + 1))))
      (fun T => ev (PMF.uniformOfFintype (Matrix (Fin (ell κ)) (Fin (m κ)) (ZMod (q κ))))
        fun C => ind (parityOut κ (postWord C Kq (auxOf S P T)) = true)) ≤ ρ κ := by
  classical
  have hcnt := rand_count S P Kq hK
  have hsum : ∑ T : Matrix (Fin (ell κ)) (Fin (k κ)) (Fin ((q κ - 1) / 2 + 1)),
      ∑ C : Matrix (Fin (ell κ)) (Fin (m κ)) (ZMod (q κ)),
        ind (parityOut κ (postWord C Kq (auxOf S P T)) = true) =
      ((Finset.univ.filter fun x : Matrix (Fin (ell κ)) (Fin (m κ)) (ZMod (q κ)) ×
        Matrix (Fin (ell κ)) (Fin (k κ)) (Fin ((q κ - 1) / 2 + 1)) =>
          parityOut κ (postWord x.1 Kq (auxOf S P x.2)) = true).card : ℝ≥0∞) := by
    rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
    push_cast
    refine Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun T _ => ?_
    unfold ind; split_ifs <;> simp
  simp only [ev_uniform, div_eq_mul_inv]
  rw [← Finset.sum_mul, hsum]
  generalize (Finset.univ.filter fun x : Matrix (Fin (ell κ)) (Fin (m κ)) (ZMod (q κ)) ×
        Matrix (Fin (ell κ)) (Fin (k κ)) (Fin ((q κ - 1) / 2 + 1)) =>
          parityOut κ (postWord x.1 Kq (auxOf S P x.2)) = true).card = cnt at hcnt ⊢
  have hNC : 0 < Fintype.card (Matrix (Fin (ell κ)) (Fin (m κ)) (ZMod (q κ))) := Fintype.card_pos
  have hNT : 0 < Fintype.card (Matrix (Fin (ell κ)) (Fin (k κ)) (Fin ((q κ - 1) / 2 + 1))) :=
    Fintype.card_pos
  generalize Fintype.card (Matrix (Fin (ell κ)) (Fin (m κ)) (ZMod (q κ))) = NC at hcnt hNC ⊢
  generalize Fintype.card (Matrix (Fin (ell κ)) (Fin (k κ)) (Fin ((q κ - 1) / 2 + 1))) = NT
    at hcnt hNT ⊢
  set A := 7 * ((q κ - 1) / 2 + 1) + 16
  set Bq := 8 * ((q κ - 1) / 2 + 1)
  have hB : 0 < Bq := by omega
  have hNC0 : (NC : ℝ≥0∞) ≠ 0 := by exact_mod_cast hNC.ne'
  have hNT0 : (NT : ℝ≥0∞) ≠ 0 := by exact_mod_cast hNT.ne'
  have hB0 : (Bq : ℝ≥0∞) ≠ 0 := by exact_mod_cast hB.ne'
  have htop := ENNReal.natCast_ne_top
  have hN0 : (NC : ℝ≥0∞) * NT ≠ 0 := mul_ne_zero hNC0 hNT0
  have hNt : (NC : ℝ≥0∞) * NT ≠ ⊤ := ENNReal.mul_ne_top (htop _) (htop _)
  have hc : ((cnt * Bq : ℕ) : ℝ≥0∞) ≤ ((A * (NC * NT) : ℕ) : ℝ≥0∞) := by
    exact_mod_cast (by rw [mul_comm cnt]; exact hcnt)
  push_cast at hc
  rw [mul_assoc, ← ENNReal.mul_inv (Or.inl hNC0) (Or.inl (htop _)), ← div_eq_mul_inv, ρ]
  calc (cnt : ℝ≥0∞) / (NC * NT) = (cnt * Bq) / ((NC * NT) * Bq) :=
        (ENNReal.mul_div_mul_right _ _ hB0 (htop _)).symm
    _ ≤ (A * (NC * NT)) / ((NC * NT) * Bq) := by gcongr
    _ = (A : ℝ≥0∞) / Bq := by
        rw [mul_comm (A : ℝ≥0∞)]; exact ENNReal.mul_div_mul_left _ _ hN0 hNt
    _ = _ := by simp only [A, Bq]

/-- On `postRandom`, the attack accepts with probability at most
`ρ + Pr_B[B has a nonzero left kernel vector] + Pr_P[P has a zero column]`. -/
theorem ev_rand_acc_le (κ : ℕ) :
    ev (postRandom κ) (fun w => ind (parityOut κ w = true)) ≤
      ρ κ + ev (PMF.uniformOfFintype (Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ))))
          (fun B => ind (∃ y ≠ 0, y ᵥ* B = 0)) +
        ev (PMF.uniformOfFintype (Matrix (Fin (n κ)) (Fin (k κ)) (ZMod (q κ))))
          (fun P => ind (∃ j ∈ Finset.univ, (fun i => P i j) = 0)) := by
  classical
  simp only [postRandom, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, ev_bind, ev_pure]
  rw [ev_draw]
  set UC := PMF.uniformOfFintype (Matrix (Fin (ell κ)) (Fin (m κ)) (ZMod (q κ)))
  set UT := PMF.uniformOfFintype (Matrix (Fin (ell κ)) (Fin (k κ)) (Fin ((q κ - 1) / 2 + 1)))
  have inner : ∀ B P S, ev UT (fun T => ev (preimage (⟨B, P, S, T⟩ : Draw κ)) fun K? =>
      ev UC fun C => ind (parityOut κ (match K? with
        | none => []
        | some K => encSample κ (matVals C ++ matVals (intMod (q κ) K) ++
            matVals (⟨B, P, S, T⟩ : Draw κ).aux)) = true)) ≤
      ρ κ + ind (∃ y ≠ 0, y ᵥ* B = 0) + ind (∃ j ∈ Finset.univ, (fun i => P i j) = 0) := by
    intro B P S
    have hpre : ∀ T, preimage (⟨B, P, S, T⟩ : Draw κ) = preimage (⟨B, P, S, 0⟩ : Draw κ) :=
      fun T => rfl
    simp only [hpre]
    rw [ev_comm]
    set d0 : Draw κ := ⟨B, P, S, 0⟩
    calc _ ≤ ev (preimage d0) (fun K? => ind (K? = none) + ρ κ +
          ind (∃ j ∈ Finset.univ, (fun i => P i j) = 0)) := by
          refine ev_mono_supp _ fun K? hK? => ?_
          cases K? with
          | none =>
            simp only [parityOut_nil, ind_of trivial, ev_const]
            exact le_add_right le_self_add
          | some K =>
            by_cases hP : ∃ j ∈ Finset.univ, (fun i => P i j) = 0
            · rw [ind_of hP]
              exact (ev_le_const _ fun _ => ev_le_const _ fun _ => ind_le_one _).trans le_add_self
            · have hK : ∀ j, (fun r => (intMod (q κ) K) r j) ≠ 0 := by
                intro j h0
                apply hP ⟨j, Finset.mem_univ _, ?_⟩
                have := preimage_support d0 hK? j
                rw [← this]
                have h0' : (fun r => (K r j : ZMod (q κ))) = 0 := h0
                rw [h0', Matrix.mulVec_zero]
              have := ev_CT_le S P (intMod (q κ) K) hK
              exact this.trans (le_add_right le_add_self)
      _ = ev (preimage d0) (fun K? => ind (K? = none)) + ρ κ +
            ind (∃ j ∈ Finset.univ, (fun i => P i j) = 0) := by
          rw [ev_add, ev_add, ev_const, ev_const]
      _ ≤ ind (∃ y ≠ 0, y ᵥ* B = 0) + ρ κ + ind (∃ j ∈ Finset.univ, (fun i => P i j) = 0) := by
          gcongr; exact ev_preimage_none_le d0
      _ = _ := by ring
  calc _ ≤ ev (PMF.uniformOfFintype (Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ)))) (fun B =>
        ev (PMF.uniformOfFintype (Matrix (Fin (n κ)) (Fin (k κ)) (ZMod (q κ)))) fun P =>
        ev (sampleMat (gaussZ (σLWE κ) (σLWE_pos κ)) (ell κ) (n κ)) fun _ =>
          ρ κ + ind (∃ y ≠ 0, y ᵥ* B = 0) + ind (∃ j ∈ Finset.univ, (fun i => P i j) = 0)) :=
        ev_mono _ fun B => ev_mono _ fun P => ev_mono _ fun S => inner B P S
    _ = _ := by
        simp only [ev_const, ev_add]

end

end TestCase.EvLWE
