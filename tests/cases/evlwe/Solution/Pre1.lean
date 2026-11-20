import Solution.Pre1Vec
import Solution.Pre2

/-!
# Pre1 holds (statistically)

Pre1 is `(S·B + E, S·P + E', S·P − 2T)` against `(C, C', S·P − 2T)`. Given `S ≢ 0 (mod q)`:

* `S·B` is uniform (`ev_rowmul`), so `S·B + E` is a uniform `C` (`ev_rowmul_shift`);
* `v = S·P` is uniform; writing `v = a + 2T` with `a` uniform, the real side is
  `(C, a + (2T + E'), a)` and the random side `(C, a + y, a)` for a uniform `y` (`real_S`,
  `rand_S`), so the distance is that of `2T + E'` from uniform (`closeTo_Zdist`).

`S ≡ 0` has probability at most `6/σ_LWE + 6·4^{−m}` (`ev_Sq_zero_le`). The total `δ₁` is
negligible, so `pre1Real` and `pre1Random` are indistinguishable even to unbounded distinguishers
(`pre1_holds`).
-/

namespace TestCase.EvLWE

open SigabaNeo.Lattices

open TestCase TestCase.EvLWE Cslib Cslib.Crypto Cslib.Probability
open scoped ENNReal NNReal Matrix

section
variable {α : Type*} {G : Type*} [Fintype G] [Nonempty G] [AddGroup G]

theorem ev_add_right (c : G) (g : G → ℝ≥0∞) :
    ev (PMF.uniformOfFintype G) (fun x => g (x + c)) = ev (PMF.uniformOfFintype G) g :=
  ev_uniform_equiv (Equiv.addRight c) g

theorem ev_add_left (c : G) (g : G → ℝ≥0∞) :
    ev (PMF.uniformOfFintype G) (fun x => g (c + x)) = ev (PMF.uniformOfFintype G) g :=
  ev_uniform_equiv (Equiv.addLeft c) g

end

section
variable (κ : ℕ)

abbrev RowM : Type := Matrix (Fin (ell κ)) (Fin (m κ)) (ZMod (q κ))

/-- `S` over `Z_q`. -/
noncomputable def Sqm (S : Matrix (Fin (ell κ)) (Fin (n κ)) ℤ) :
    Matrix (Fin (ell κ)) (Fin (n κ)) (ZMod (q κ)) := S.map (Int.cast : ℤ → ZMod (q κ))

/-- A nonzero row times a uniform matrix is uniform. -/
theorem ev_rowmul {c : ℕ} (Sq : Matrix (Fin (ell κ)) (Fin (n κ)) (ZMod (q κ))) (hS : Sq ≠ 0)
    (g : Matrix (Fin (ell κ)) (Fin c) (ZMod (q κ)) → ℝ≥0∞) :
    ev (PMF.uniformOfFintype (Matrix (Fin (n κ)) (Fin c) (ZMod (q κ)))) (fun B => g (Sq * B)) =
      ev (PMF.uniformOfFintype (Matrix (Fin (ell κ)) (Fin c) (ZMod (q κ)))) g := by
  classical
  obtain ⟨i0, hi0⟩ : ∃ i0, Sq default i0 ≠ 0 := by
    by_contra h
    push Not at h
    exact hS (by ext i j; obtain rfl : i = default := Subsingleton.elim _ _; exact h j)
  have hbal : ∀ δ : Matrix (Fin (ell κ)) (Fin c) (ZMod (q κ)),
      ∃ e : Matrix (Fin (n κ)) (Fin c) (ZMod (q κ)) ≃ Matrix (Fin (n κ)) (Fin c) (ZMod (q κ)),
        ∀ B, Sq * e B = Sq * B + δ := by
    intro δ
    refine ⟨Equiv.addRight (Matrix.of fun i j => if i = i0 then (Sq default i0)⁻¹ * δ default j
      else 0), fun B => ?_⟩
    rw [Equiv.coe_addRight, Matrix.mul_add]
    congr 1
    ext r j
    obtain rfl : r = default := Subsingleton.elim _ _
    simp only [Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [← mul_assoc, mul_inv_cancel₀ hi0, one_mul]
  have hmap : (PMF.uniformOfFintype (Matrix (Fin (n κ)) (Fin c) (ZMod (q κ)))).map (Sq * ·) =
      PMF.uniformOfFintype _ := by
    ext y
    have h := ev_uniform_balanced (fun B => Sq * B) hbal {y}
    rw [PMF.map_apply, PMF.uniformOfFintype_apply]
    simp only [Finset.mem_singleton, Finset.card_singleton, Nat.cast_one, one_div] at h
    rw [← h]
    unfold ev
    refine tsum_congr fun B => ?_
    by_cases hB : y = Sq * B
    · dsimp only; rw [if_pos hB, ind_of hB.symm, mul_one]
    · dsimp only; rw [if_neg hB, ind_of_not (Ne.symm hB), mul_zero]
  rw [← hmap, ev_map]; rfl

/-- `S·B + E` is uniform. -/
theorem ev_rowmul_shift (Sq : Matrix (Fin (ell κ)) (Fin (n κ)) (ZMod (q κ))) (hS : Sq ≠ 0)
    (h : RowM κ → ℝ≥0∞) :
    ev (PMF.uniformOfFintype (Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ)))) (fun B =>
      ev (sampleMat (gaussZ (σ κ) (σ_pos κ)) (ell κ) (m κ)) fun E => h (Sq * B + intMod (q κ) E)) =
      ev (PMF.uniformOfFintype (RowM κ)) h := by
  rw [ev_comm]
  refine ev_const_of_eq _ fun E => ?_
  rw [ev_rowmul κ Sq hS (fun u => h (u + intMod (q κ) E)), ev_add_right]

/-- A Pre1 word. -/
noncomputable def W1 (C : RowM κ) (C' A : Row κ) : List Bool :=
  encSample κ (matVals C ++ matVals C' ++ matVals A)

/-- Pre1 real at a fixed `S`. -/
noncomputable def RS (S : Matrix (Fin (ell κ)) (Fin (n κ)) ℤ) : PMF (List Bool) :=
  (PMF.uniformOfFintype (Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ)))).bind fun B =>
  (PMF.uniformOfFintype (PMat κ)).bind fun P =>
  (PMF.uniformOfFintype (TMat κ)).bind fun T =>
  (sampleMat (gaussZ (σ κ) (σ_pos κ)) (ell κ) (m κ)).bind fun E =>
  (sampleMat (gaussZ (σ' κ) (σ'_pos κ)) (ell κ) (k κ)).bind fun E' =>
    PMF.pure (W1 κ (Sqm κ S * B + intMod (q κ) E) (Sqm κ S * P + intMod (q κ) E')
      (Sqm κ S * P - (2 : ZMod (q κ)) • Tq κ T))

/-- Pre1 random at a fixed `S`. -/
noncomputable def QS (S : Matrix (Fin (ell κ)) (Fin (n κ)) ℤ) : PMF (List Bool) :=
  (PMF.uniformOfFintype (Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ)))).bind fun _ =>
  (PMF.uniformOfFintype (PMat κ)).bind fun P =>
  (PMF.uniformOfFintype (TMat κ)).bind fun T =>
  (PMF.uniformOfFintype (RowM κ)).bind fun C =>
  (PMF.uniformOfFintype (Row κ)).bind fun C' =>
    PMF.pure (W1 κ C C' (Sqm κ S * P - (2 : ZMod (q κ)) • Tq κ T))

theorem pre1Real_eq : pre1Real κ = (gaussMat κ (ell κ) (n κ)).bind (RS κ) := by
  refine pmf_ext_ev fun f => ?_
  unfold pre1Real draw RS gaussMat Draw.Sq Draw.aux
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind, ev_bind,
    ev_pure]
  conv_rhs => rw [ev_comm]
  congr 1; funext B
  exact ev_comm _ _ _

theorem pre1Random_eq : pre1Random κ = (gaussMat κ (ell κ) (n κ)).bind (QS κ) := by
  refine pmf_ext_ev fun f => ?_
  unfold pre1Random draw QS gaussMat Draw.aux Draw.Sq
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind, ev_bind,
    ev_pure]
  conv_rhs => rw [ev_comm]
  congr 1; funext B
  exact ev_comm _ _ _


/-- The common continuation: `(C, a + y, a)` with `a`, `C` uniform. -/
noncomputable def Kc (y : Row κ) : PMF (List Bool) :=
  (PMF.uniformOfFintype (Row κ)).bind fun a =>
    (PMF.uniformOfFintype (RowM κ)).map fun C => W1 κ C (a + y) a

set_option maxHeartbeats 1000000 in
theorem real_S (S : Matrix (Fin (ell κ)) (Fin (n κ)) ℤ) (hS : Sqm κ S ≠ 0) :
    RS κ S = (Zdist κ).bind (Kc κ) := by
  refine pmf_ext_ev fun f => ?_
  calc ev (RS κ S) f
      = ev (PMF.uniformOfFintype (Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ)))) (fun B =>
          ev (PMF.uniformOfFintype (PMat κ)) fun P =>
          ev (PMF.uniformOfFintype (TMat κ)) fun T =>
          ev (sampleMat (gaussZ (σ κ) (σ_pos κ)) (ell κ) (m κ)) fun E =>
          ev (sampleMat (gaussZ (σ' κ) (σ'_pos κ)) (ell κ) (k κ)) fun E' =>
            f (W1 κ (Sqm κ S * B + intMod (q κ) E) (Sqm κ S * P + intMod (q κ) E')
              (Sqm κ S * P - (2 : ZMod (q κ)) • Tq κ T))) := by
        unfold RS; simp only [ev_bind, ev_pure]
    _ = ev (PMF.uniformOfFintype (PMat κ)) (fun P =>
          ev (PMF.uniformOfFintype (TMat κ)) fun T =>
          ev (PMF.uniformOfFintype (Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ)))) fun B =>
          ev (sampleMat (gaussZ (σ κ) (σ_pos κ)) (ell κ) (m κ)) fun E =>
          ev (sampleMat (gaussZ (σ' κ) (σ'_pos κ)) (ell κ) (k κ)) fun E' =>
            f (W1 κ (Sqm κ S * B + intMod (q κ) E) (Sqm κ S * P + intMod (q κ) E')
              (Sqm κ S * P - (2 : ZMod (q κ)) • Tq κ T))) := by
        conv_lhs => rw [ev_comm]
        congr 1; funext P
        exact ev_comm _ _ _
    _ = ev (PMF.uniformOfFintype (PMat κ)) (fun P =>
          ev (PMF.uniformOfFintype (TMat κ)) fun T =>
          ev (PMF.uniformOfFintype (RowM κ)) fun u =>
          ev (sampleMat (gaussZ (σ' κ) (σ'_pos κ)) (ell κ) (k κ)) fun E' =>
            f (W1 κ u (Sqm κ S * P + intMod (q κ) E') (Sqm κ S * P - (2 : ZMod (q κ)) • Tq κ T))) := by
        congr 1; funext P; congr 1; funext T
        exact ev_rowmul_shift κ (Sqm κ S) hS (fun u =>
          ev (sampleMat (gaussZ (σ' κ) (σ'_pos κ)) (ell κ) (k κ)) fun E' =>
            f (W1 κ u (Sqm κ S * P + intMod (q κ) E') (Sqm κ S * P - (2 : ZMod (q κ)) • Tq κ T)))
    _ = ev (PMF.uniformOfFintype (Row κ)) (fun v =>
          ev (PMF.uniformOfFintype (TMat κ)) fun T =>
          ev (PMF.uniformOfFintype (RowM κ)) fun u =>
          ev (sampleMat (gaussZ (σ' κ) (σ'_pos κ)) (ell κ) (k κ)) fun E' =>
            f (W1 κ u (v + intMod (q κ) E') (v - (2 : ZMod (q κ)) • Tq κ T))) :=
        ev_rowmul κ (Sqm κ S) hS (fun v =>
          ev (PMF.uniformOfFintype (TMat κ)) fun T =>
          ev (PMF.uniformOfFintype (RowM κ)) fun u =>
          ev (sampleMat (gaussZ (σ' κ) (σ'_pos κ)) (ell κ) (k κ)) fun E' =>
            f (W1 κ u (v + intMod (q κ) E') (v - (2 : ZMod (q κ)) • Tq κ T)))
    _ = ev (PMF.uniformOfFintype (TMat κ)) (fun T =>
          ev (PMF.uniformOfFintype (Row κ)) fun a =>
          ev (PMF.uniformOfFintype (RowM κ)) fun u =>
          ev (sampleMat (gaussZ (σ' κ) (σ'_pos κ)) (ell κ) (k κ)) fun E' =>
            f (W1 κ u (a + (2 : ZMod (q κ)) • Tq κ T + intMod (q κ) E')
              (a + (2 : ZMod (q κ)) • Tq κ T - (2 : ZMod (q κ)) • Tq κ T))) := by
        rw [ev_comm]
        congr 1; funext T
        exact (ev_add_right ((2 : ZMod (q κ)) • Tq κ T) _).symm
    _ = ev (PMF.uniformOfFintype (TMat κ)) (fun T =>
          ev (sampleMat (gaussZ (σ' κ) (σ'_pos κ)) (ell κ) (k κ)) fun E' =>
          ev (PMF.uniformOfFintype (Row κ)) fun a =>
          ev (PMF.uniformOfFintype (RowM κ)) fun C =>
            f (W1 κ C (a + ((2 : ZMod (q κ)) • Tq κ T + intMod (q κ) E')) a)) := by
        congr 1; funext T
        conv_rhs => rw [ev_comm]
        congr 1; funext a
        rw [ev_comm]
        congr 1; funext E'
        congr 1; funext C
        rw [add_assoc, add_sub_cancel_right, ← add_assoc]
    _ = ev ((Zdist κ).bind (Kc κ)) f := by
        unfold Zdist Kc; simp only [ev_bind, ev_map, Function.comp_def]

set_option maxHeartbeats 1000000 in
theorem rand_S (S : Matrix (Fin (ell κ)) (Fin (n κ)) ℤ) (hS : Sqm κ S ≠ 0) :
    QS κ S = (PMF.uniformOfFintype (Row κ)).bind (Kc κ) := by
  refine pmf_ext_ev fun f => ?_
  calc ev (QS κ S) f
      = ev (PMF.uniformOfFintype (PMat κ)) (fun P =>
          ev (PMF.uniformOfFintype (TMat κ)) fun T =>
          ev (PMF.uniformOfFintype (RowM κ)) fun C =>
          ev (PMF.uniformOfFintype (Row κ)) fun C' =>
            f (W1 κ C C' (Sqm κ S * P - (2 : ZMod (q κ)) • Tq κ T))) := by
        unfold QS; simp only [ev_bind, ev_pure]
        exact ev_const_of_eq _ fun _ => rfl
    _ = ev (PMF.uniformOfFintype (Row κ)) (fun v =>
          ev (PMF.uniformOfFintype (TMat κ)) fun T =>
          ev (PMF.uniformOfFintype (RowM κ)) fun C =>
          ev (PMF.uniformOfFintype (Row κ)) fun C' =>
            f (W1 κ C C' (v - (2 : ZMod (q κ)) • Tq κ T))) :=
        ev_rowmul κ (Sqm κ S) hS (fun v =>
          ev (PMF.uniformOfFintype (TMat κ)) fun T =>
          ev (PMF.uniformOfFintype (RowM κ)) fun C =>
          ev (PMF.uniformOfFintype (Row κ)) fun C' =>
            f (W1 κ C C' (v - (2 : ZMod (q κ)) • Tq κ T)))
    _ = ev (PMF.uniformOfFintype (Row κ)) (fun a =>
          ev (PMF.uniformOfFintype (RowM κ)) fun C =>
          ev (PMF.uniformOfFintype (Row κ)) fun C' => f (W1 κ C C' a)) := by
        rw [ev_comm]
        refine ev_const_of_eq _ fun T => ?_
        rw [← ev_add_right ((2 : ZMod (q κ)) • Tq κ T)]
        simp only [add_sub_cancel_right]
    _ = ev ((PMF.uniformOfFintype (Row κ)).bind (Kc κ)) f := by
        unfold Kc; simp only [ev_bind, ev_map, Function.comp_def]
        conv_rhs => rw [ev_comm]
        congr 1; funext a
        conv_lhs => rw [ev_comm]
        exact (ev_add_left a (fun c' => ev (PMF.uniformOfFintype (RowM κ)) fun C =>
          f (W1 κ C c' a))).symm


/-! ### `S ≡ 0` -/

theorem n_pos : 0 < n κ := Nat.succ_pos _

/-- An entry of `S` is a draw from `D_{Z,σ_LWE}`. -/
theorem ev_entry (P : ℤ → Prop) :
    ev (gaussMat κ (ell κ) (n κ)) (fun S => ind (P (S default ⟨0, n_pos κ⟩))) =
      ev (gaussZ (σLWE κ) (σLWE_pos κ)) (fun x => ind (P x)) := by
  unfold gaussMat
  rw [sampleMat_eq, ev_map, show ell κ * n κ = κ + 1 by simp [ell, n]]
  show ev (gaussZ (σLWE κ) (σLWE_pos κ) |>.bind fun a =>
    (sampleList (gaussZ (σLWE κ) (σLWE_pos κ)) κ).map (a :: ·)) _ = _
  rw [ev_bind]
  congr 1; funext a
  rw [ev_map]
  refine ev_const_of_eq _ fun l => ?_
  simp [fin_ell_val]

theorem q_ge_σLWE : σLWE κ * Real.sqrt (m κ) ≤ q κ := by
  have hX := two_pow_ge κ
  have hX1 : (1 : ℝ) ≤ 2 ^ κ := one_le_pow₀ (by norm_num)
  have hm := m_le_real κ
  have hsq : Real.sqrt (m κ) ≤ m κ := by
    have : (1 : ℝ) ≤ m κ := by exact_mod_cast m_pos κ
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hq := q_gt κ
  set X : ℝ := 2 ^ κ
  have hσ : σLWE κ = 2 * X := by unfold σLWE; rw [pow_succ]; ring
  have hw : (2 : ℝ) ^ w κ = 256 * X ^ 8 := by
    unfold w; rw [show 8 * (κ + 1) = κ * 8 + 8 by ring, pow_add, pow_mul]; norm_num; ring
  have h3 : X ^ 3 ≤ X ^ 8 := pow_le_pow_right₀ hX1 (by norm_num)
  have hκ : ((κ : ℝ) + 1) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by positivity) hX 2
  calc σLWE κ * Real.sqrt (m κ) ≤ 2 * X * (18 * ((κ : ℝ) + 1) ^ 2) := by
        rw [hσ]; gcongr; exact hsq.trans hm
    _ ≤ 36 * X ^ 3 := by nlinarith
    _ ≤ 256 * X ^ 8 := by nlinarith
    _ ≤ q κ := by rw [← hw]; exact hq.le

theorem ev_Sq_zero_le :
    ev (gaussMat κ (ell κ) (n κ)) (fun S => ind (Sqm κ S = 0)) ≤
      ENNReal.ofReal (6 / σLWE κ) + ENNReal.ofReal (6 * (1 / 4) ^ m κ) := by
  refine (ev_mono _ fun S => ind_mono (Q := ((S default ⟨0, n_pos κ⟩ : ℤ) : ZMod (q κ)) = 0)
    fun h => by
      have := congrFun (congrFun h default) ⟨0, n_pos κ⟩
      simpa [Sqm] using this).trans ?_
  rw [ev_entry κ (fun x => (x : ZMod (q κ)) = 0)]
  have hB := q_ge_σLWE κ
  refine (ev_mono _ fun x => (ind_mono (P := ((x : ℤ) : ZMod (q κ)) = 0)
    (Q := x = 0 ∨ σLWE κ * Real.sqrt (m κ) ≤ |(x : ℝ)|) fun h => ?_).trans
      (ind_or_le _ _)).trans ?_
  · rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    by_cases hx : x = 0
    · exact Or.inl hx
    · right
      have hle := Int.natAbs_le_of_dvd_ne_zero h hx
      rw [Int.natAbs_natCast] at hle
      refine hB.trans ?_
      rw [← Int.cast_abs, ← Nat.cast_natAbs]
      exact_mod_cast hle
  · rw [ev_add]
    gcongr
    · rw [ev_point]; exact gaussZ_le (σLWE_pos κ) 0
    · exact (toOuterMeasure_eq_ev (gaussZ (σLWE κ) (σLWE_pos κ))
        {x : ℤ | σLWE κ * Real.sqrt (m κ) ≤ |(x : ℝ)|}).symm.le.trans
        (gaussZ_tail (one_le_σLWE κ) (σLWE_pos κ) (m κ))

/-! ### Pre1 -/

/-- The statistical distance of Pre1. -/
noncomputable def δ₁ : ℝ := k κ * εc κ + 6 / σLWE κ + 6 * (1 / 4) ^ m κ

theorem closeTo_pre1 : CloseTo (pre1Real κ) (pre1Random κ) (ENNReal.ofReal (δ₁ κ)) := by
  rw [pre1Real_eq, pre1Random_eq]
  refine (closeTo_bind_good _ _ _ (fun S => Sqm κ S ≠ 0) (ε := ENNReal.ofReal (k κ * εc κ))
    fun S _ hS => ?_).mono ?_
  · rw [real_S κ S hS, rand_S κ S hS]
    exact (closeTo_Zdist κ).bind_left _
  · have h := ev_Sq_zero_le κ
    have hn : ∀ S, ind (¬ Sqm κ S ≠ 0) = ind (Sqm κ S = 0) := fun S => by rw [not_not]
    simp only [hn]
    have h0 : 0 ≤ k κ * εc κ := mul_nonneg (Nat.cast_nonneg _) (εc_nonneg κ)
    have h1 : 0 ≤ 6 / σLWE κ := div_nonneg (by norm_num) (σLWE_pos κ).le
    unfold δ₁
    rw [ENNReal.ofReal_add (add_nonneg h0 h1) (by positivity), ENNReal.ofReal_add h0 h1, add_assoc]
    gcongr

theorem δ₁_le : δ₁ κ ≤ (48 * ((m κ : ℝ) + 1) ^ 2) * (1 / 2 ^ κ) := by
  have hX1 : (1 : ℝ) ≤ 2 ^ κ := one_le_pow₀ (by norm_num)
  set X : ℝ := 2 ^ κ with hXdef
  have hX0 : 0 < X := by positivity
  have hm1 : (1 : ℝ) ≤ m κ := by exact_mod_cast m_pos κ
  have hmκ : (κ : ℝ) ≤ m κ := m_ge_real κ
  have hsq : Real.sqrt (m κ) ≤ m κ + 1 := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hNT : 128 * X ^ 8 ≤ (NT κ : ℝ) := by
    have := hq1_ge κ
    have h8 : (2 : ℝ) ^ (8 * κ + 7) = 128 * X ^ 8 := by
      rw [hXdef, show 8 * κ + 7 = κ * 8 + 7 by ring, pow_add, pow_mul]; norm_num; ring
    rw [← h8]; simpa [NT] using this
  have hσ' : σ' κ = 4 * X ^ 2 := by
    unfold σ'; rw [hXdef, show 2 * κ + 2 = κ * 2 + 2 by ring, pow_add, pow_mul]; norm_num; ring
  have hσ : σLWE κ = 2 * X := by unfold σLWE; rw [pow_succ]; ring
  have hq : X ≤ q κ := q_ge_X κ
  have hk : (k κ : ℝ) = m κ + 1 := by rw [k_eq]; push_cast; ring
  have hp : (1 / 4 : ℝ) ^ m κ ≤ 1 / X := by
    rw [one_div_pow]
    apply one_div_le_one_div_of_le hX0
    calc X = 2 ^ κ := rfl
      _ ≤ 2 ^ m κ := pow_le_pow_right₀ (by norm_num) (by exact_mod_cast hmκ)
      _ ≤ 4 ^ m κ := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hX2 : X ≤ X ^ 2 := by nlinarith
  have hX8 : X ^ 2 * X ≤ X ^ 8 := by
    rw [← pow_succ]; exact pow_le_pow_right₀ hX1 (by norm_num)
  have hX8p : 0 < X ^ 8 := by positivity
  have t1 : σ' κ * Real.sqrt (m κ) / NT κ ≤ (m κ + 1) / X := by
    rw [hσ', div_le_div_iff₀ (by linarith) hX0]
    have : 4 * X ^ 2 * Real.sqrt (m κ) * X ≤ 4 * X ^ 2 * (m κ + 1) * X := by gcongr
    have h3 := mul_le_mul_of_nonneg_left hX8 (by positivity : (0 : ℝ) ≤ 4 * (m κ + 1))
    have h4 := mul_le_mul_of_nonneg_left hNT (by positivity : (0 : ℝ) ≤ m κ + 1)
    nlinarith
  have t3 : 3 / σ' κ ≤ 3 / X := by
    rw [hσ']; apply div_le_div_of_nonneg_left (by norm_num) hX0; nlinarith
  have t4 : 1 / ((q κ : ℝ) + 1) ≤ 1 / X := one_div_le_one_div_of_le hX0 (by linarith)
  have hεc : εc κ ≤ 11 * ((m κ : ℝ) + 1) * (1 / X) := by
    unfold εc
    have e1 : (m κ + 1 : ℝ) / X = (m κ + 1) * (1 / X) := by ring
    have e3 : 3 / X = 3 * (1 / X) := by ring
    have h1X : 0 ≤ 1 / X := by positivity
    have key : ((m κ : ℝ) + 1) * (1 / X) + 10 * (1 / X) ≤ 11 * ((m κ : ℝ) + 1) * (1 / X) := by
      nlinarith
    linarith
  unfold δ₁
  rw [hk, hσ]
  have h6 : 6 / (2 * X) = 3 * (1 / X) := by field_simp; ring
  rw [h6]
  have h1X : 0 ≤ 1 / X := by positivity
  have hmm : (1 : ℝ) ≤ (m κ + 1) := by linarith
  have hA : ((m κ : ℝ) + 1) * εc κ ≤ 11 * ((m κ : ℝ) + 1) ^ 2 * (1 / X) := by
    have := mul_le_mul_of_nonneg_left hεc (by positivity : (0 : ℝ) ≤ m κ + 1)
    nlinarith
  have hB : 6 * (1 / 4 : ℝ) ^ m κ ≤ 6 * (1 / X) := by linarith
  have hsq1 : (1 : ℝ) ≤ ((m κ : ℝ) + 1) ^ 2 := by nlinarith
  have hC : 1 / X ≤ ((m κ : ℝ) + 1) ^ 2 * (1 / X) := le_mul_of_one_le_left h1X hsq1
  nlinarith

theorem adv_pre1_le (D : Distinguisher) :
    (Game.advantage (distinguishingGame (pre1Real κ) (D κ))
      (distinguishingGame (pre1Random κ) (D κ)) : ℝ) ≤ δ₁ κ := by
  rw [coe_adv, gD_eq, gD_eq]
  have hδ : 0 ≤ δ₁ κ := by
    unfold δ₁
    exact add_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (εc_nonneg κ))
      (div_nonneg (by norm_num) (σLWE_pos κ).le)) (by positivity)
  have := ((closeTo_pre1 κ).bind_left fun w => ProbComp.eval (D κ w)).abs_toReal_sub_le hδ {true}
  simpa only [PMF.toOuterMeasure_apply_singleton, pt, gD] using this

end

/-- **Pre1 holds**, against every distinguisher. -/
theorem pre1_holds : ComputationallyIndistinguishable pre1Real pre1Random := by
  intro D _
  refine negligible_of_le negligible_bound fun κ => ?_
  rw [← NNReal.coe_le_coe]
  have h := adv_pre1_le κ D
  have hd := δ₁_le κ
  simp only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_div, NNReal.coe_one, NNReal.coe_pow,
    NNReal.coe_ofNat, NNReal.coe_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat]
  linarith

end TestCase.EvLWE
