import SigabaNeo.Lib.Lattices.Stat
import Solution.PostFacts

/-!
# Pre2: hybrids

`Yd κ h withE` draws `P` uniform, `S ← D_{Z,σ_LWE}^{1×n}`, `E ← D_{Z,σ_LWE}^{1×k}`, `R`, `T` uniform
and outputs the Pre2 word `(P + h·R, S·P + 2E − 2T)` (with `E = 0` unless `withE`).

* `pre2Real_eq`, `pre2Random_eq`: Pre2 is `Yd false false` against `Yd true false`.
* `closeTo_Yd`: adding the error `E` moves the word by at most `δ₂ κ` in statistical distance:
  `−2T + 2E = −2(T − E)` and `T − E` is close to `T` when `E` is short (`closeTo_shift`).
-/

namespace TestCase.EvLWE

open SigabaNeo.Lattices

open TestCase TestCase.EvLWE Cslib.Probability
open scoped ENNReal Matrix Cslib.Probability.PMF

instance (κ : ℕ) : Unique (Fin (ell κ)) := inferInstanceAs (Unique (Fin 1))

section
variable (κ : ℕ)

/-- The range of the entries of `T`. -/
noncomputable abbrev NT : ℕ := (q κ - 1) / 2 + 1
abbrev TMat : Type := Matrix (Fin (ell κ)) (Fin (k κ)) (Fin (NT κ))
abbrev RMat : Type := Matrix (Fin (n κ)) (Fin (k κ)) (Fin (κR κ + 1))
abbrev PMat : Type := Matrix (Fin (n κ)) (Fin (k κ)) (ZMod (q κ))
abbrev Row : Type := Matrix (Fin (ell κ)) (Fin (k κ)) (ZMod (q κ))

/-- A Pre2 word. -/
noncomputable def pre2Word (P : PMat κ) (aux : Row κ) : List Bool :=
  encSample κ (matVals P ++ matVals aux)

noncomputable def Rq (R : RMat κ) : PMat κ := R.map fun r => ((r : ℕ) : ZMod (q κ))
noncomputable def Tq (T : TMat κ) : Row κ := T.map fun t => ((t : ℕ) : ZMod (q κ))

/-- `(P + h·R, S·P + 2E − 2T)`. -/
noncomputable def hyb (h : Bool) (P : PMat κ) (S : Matrix (Fin (ell κ)) (Fin (n κ)) ℤ)
    (E : Matrix (Fin (ell κ)) (Fin (k κ)) ℤ) (R : RMat κ) (T : TMat κ) : List Bool :=
  pre2Word κ (P + if h then Rq κ R else 0)
    (S.map (Int.cast) * P + (2 : ZMod (q κ)) • intMod (q κ) E - (2 : ZMod (q κ)) • Tq κ T)

/-- `D_{Z,σ_LWE}^{r×c}`. -/
noncomputable def gaussMat (r c : ℕ) : PMF (Matrix (Fin r) (Fin c) ℤ) :=
  sampleMat (gaussZ (σLWE κ) (σLWE_pos κ)) r c

noncomputable def Yd (h withE : Bool) : PMF (List Bool) := do
  let P ← PMF.uniformOfFintype (PMat κ)
  let S ← gaussMat κ (ell κ) (n κ)
  let E ← gaussMat κ (ell κ) (k κ)
  let R ← PMF.uniformOfFintype (RMat κ)
  let T ← PMF.uniformOfFintype (TMat κ)
  pure (hyb κ h P S (if withE then E else 0) R T)

theorem intMod_zero {r c : ℕ} (Q : ℕ) : intMod Q (0 : Matrix (Fin r) (Fin c) ℤ) = 0 := by
  ext i j; simp [intMod]

theorem pre2Real_eq : pre2Real κ = Yd κ false false := by
  unfold pre2Real Yd draw hyb Draw.aux Draw.Sq pre2Word Tq gaussMat
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind,
    Bool.false_eq_true, ite_false, add_zero, intMod_zero, smul_zero, PMF.bind_const]

theorem pre2Random_eq : pre2Random κ = Yd κ true false := by
  unfold pre2Random Yd draw hyb Draw.aux Draw.Sq pre2Word Tq Rq gaussMat
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind,
    Bool.false_eq_true, ite_false, ite_true, add_zero, intMod_zero, smul_zero, PMF.bind_const]
  congr 1; funext P; congr 1; funext S
  exact PMF.bind_comm _ _ _

/-! ### Adding the error -/

/-- The statistical cost of adding `E`. -/
noncomputable def δ₂ : ℝ :=
  k κ * (σLWE κ * Real.sqrt (m κ)) / NT κ + k κ * (6 * (1 / 4) ^ m κ)

theorem δ₂_nonneg : 0 ≤ δ₂ κ := by unfold δ₂ σLWE; positivity

/-- The Pre2 word for the row `v = T − E`. -/
noncomputable def hybV (h : Bool) (P : PMat κ) (S : Matrix (Fin (ell κ)) (Fin (n κ)) ℤ)
    (R : RMat κ) (v : Fin (k κ) → ZMod (q κ)) : List Bool :=
  pre2Word κ (P + if h then Rq κ R else 0)
    (S.map (Int.cast) * P - (2 : ZMod (q κ)) • Matrix.of fun _ j => v j)

theorem hyb_eq_hybV (h : Bool) (P : PMat κ) (S : Matrix (Fin (ell κ)) (Fin (n κ)) ℤ)
    (E : Matrix (Fin (ell κ)) (Fin (k κ)) ℤ) (R : RMat κ) (T : TMat κ) :
    hyb κ h P S E R T =
      hybV κ h P S R fun j => ((T default j : ℕ) : ZMod (q κ)) - ((E default j : ℤ) : ZMod (q κ)) := by
  unfold hyb hybV
  congr 1
  ext i j
  obtain rfl : i = default := Subsingleton.elim _ _
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, intMod, Tq, Matrix.map_apply,
    Matrix.of_apply, smul_eq_mul]
  ring

theorem hyb_zero_eq_hybV (h : Bool) (P : PMat κ) (S : Matrix (Fin (ell κ)) (Fin (n κ)) ℤ)
    (R : RMat κ) (T : TMat κ) :
    hyb κ h P S 0 R T = hybV κ h P S R fun j => ((T default j : ℕ) : ZMod (q κ)) := by
  rw [hyb_eq_hybV]
  simp

theorem NT_pos : 0 < NT κ := Nat.succ_pos _

instance : NeZero (NT κ) := ⟨(NT_pos κ).ne'⟩

/-- For a fixed `E`, the `T` part. -/
theorem closeTo_T (h : Bool) (P : PMat κ) (S : Matrix (Fin (ell κ)) (Fin (n κ)) ℤ)
    (E : Matrix (Fin (ell κ)) (Fin (k κ)) ℤ) (R : RMat κ) :
    CloseTo ((PMF.uniformOfFintype (TMat κ)).bind fun T => PMF.pure (hyb κ h P S E R T))
      ((PMF.uniformOfFintype (TMat κ)).bind fun T => PMF.pure (hyb κ h P S 0 R T))
      (ENNReal.ofReal (∑ j, ((E default j).natAbs : ℝ) / NT κ)) := by
  let e : TMat κ ≃ (Fin (k κ) → Fin (NT κ)) := Equiv.funUnique (Fin (ell κ)) _
  have hu : (PMF.uniformOfFintype (TMat κ)).map e = PMF.uniformOfFintype _ :=
    PMF.uniformOfFintype_map_equiv e
  have h1 : ((PMF.uniformOfFintype (TMat κ)).bind fun T => PMF.pure (hyb κ h P S E R T)) =
      PMF.map (hybV κ h P S R) (PMF.map (fun (v : Fin (k κ) → Fin (NT κ)) j =>
        ((v j : ℕ) : ZMod (q κ)) - ((E default j : ℤ) : ZMod (q κ)))
        (PMF.uniformOfFintype (Fin (k κ) → Fin (NT κ)))) := by
    rw [← hu, PMF.map_comp, PMF.map_comp,
      show (fun T => PMF.pure (hyb κ h P S E R T)) = PMF.pure ∘ (fun T => hyb κ h P S E R T)
        from rfl, PMF.bind_pure_comp]
    congr 1; funext T
    simp only [Function.comp_apply, hyb_eq_hybV]
    rfl
  have h2 : ((PMF.uniformOfFintype (TMat κ)).bind fun T => PMF.pure (hyb κ h P S 0 R T)) =
      PMF.map (hybV κ h P S R) (PMF.map (fun (v : Fin (k κ) → Fin (NT κ)) j =>
        ((v j : ℕ) : ZMod (q κ))) (PMF.uniformOfFintype (Fin (k κ) → Fin (NT κ)))) := by
    rw [← hu, PMF.map_comp, PMF.map_comp,
      show (fun T => PMF.pure (hyb κ h P S 0 R T)) = PMF.pure ∘ (fun T => hyb κ h P S 0 R T)
        from rfl, PMF.bind_pure_comp]
    congr 1; funext T
    simp only [Function.comp_apply, hyb_zero_eq_hybV]
    rfl
  rw [h1, h2]
  exact (closeTo_of_dist_le_ofReal (dist_shift_vec (Q := q κ) (NT κ) (k κ)
    fun j => E default j)).map _

theorem one_le_σLWE : 1 ≤ σLWE κ := by unfold σLWE; exact one_le_pow₀ (by norm_num)

theorem ev_bad_E_le :
    ev (gaussMat κ (ell κ) (k κ))
      (fun E => ind (¬ ∀ i j, |((E i j : ℤ) : ℝ)| < σLWE κ * Real.sqrt (m κ))) ≤
      ((ell κ * k κ : ℕ) : ℝ≥0∞) * ENNReal.ofReal (6 * (1 / 4) ^ m κ) := by
  have hB : 0 < σLWE κ * Real.sqrt (m κ) :=
    mul_pos (σLWE_pos κ) (Real.sqrt_pos.mpr (by exact_mod_cast m_pos κ))
  refine (ev_mono _ fun E => ind_mono ?_).trans (ev_sampleMat_exists (gaussZ (σLWE κ) (σLWE_pos κ))
    (fun x : ℤ => σLWE κ * Real.sqrt (m κ) ≤ |(x : ℝ)|) ?_ ?_ (ell κ) (k κ))
  · intro h
    push Not at h
    exact h
  · simp only [show (default : ℤ) = 0 from rfl, Int.cast_zero, abs_zero, not_le]; exact hB
  · exact (toOuterMeasure_eq_ev (gaussZ (σLWE κ) (σLWE_pos κ))
      {x : ℤ | σLWE κ * Real.sqrt (m κ) ≤ |(x : ℝ)|}).symm.le.trans
      (gaussZ_tail (one_le_σLWE κ) (σLWE_pos κ) (m κ))

/-- Adding the error `E` to the Pre2 word. -/
theorem closeTo_Yd (h : Bool) :
    CloseTo (Yd κ h true) (Yd κ h false) (ENNReal.ofReal (δ₂ κ)) := by
  unfold Yd
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, ite_true, Bool.false_eq_true,
    ite_false]
  refine CloseTo.bind_right _ fun P _ => CloseTo.bind_right _ fun S _ => ?_
  have hgood := closeTo_bind_good (gaussMat κ (ell κ) (k κ))
    (fun E => (PMF.uniformOfFintype (RMat κ)).bind fun R =>
      (PMF.uniformOfFintype (TMat κ)).bind fun T => PMF.pure (hyb κ h P S E R T))
    (fun _ => (PMF.uniformOfFintype (RMat κ)).bind fun R =>
      (PMF.uniformOfFintype (TMat κ)).bind fun T => PMF.pure (hyb κ h P S 0 R T))
    (fun E => ∀ i j, |((E i j : ℤ) : ℝ)| < σLWE κ * Real.sqrt (m κ))
    (ε := ENNReal.ofReal (k κ * (σLWE κ * Real.sqrt (m κ)) / NT κ)) ?_
  · refine hgood.mono ?_
    have hb := ev_bad_E_le κ
    have ha : (0 : ℝ) ≤ k κ * (σLWE κ * Real.sqrt (m κ)) / NT κ := by unfold σLWE; positivity
    calc ENNReal.ofReal (k κ * (σLWE κ * Real.sqrt (m κ)) / NT κ) +
          ev (gaussMat κ (ell κ) (k κ))
            (fun E => ind (¬ ∀ i j, |((E i j : ℤ) : ℝ)| < σLWE κ * Real.sqrt (m κ)))
        ≤ ENNReal.ofReal (k κ * (σLWE κ * Real.sqrt (m κ)) / NT κ) +
          ((ell κ * k κ : ℕ) : ℝ≥0∞) * ENNReal.ofReal (6 * (1 / 4) ^ m κ) := by gcongr
      _ = ENNReal.ofReal (δ₂ κ) := by
        unfold δ₂
        rw [ENNReal.ofReal_add ha (by positivity), ENNReal.ofReal_mul (Nat.cast_nonneg (k κ)),
          ENNReal.ofReal_natCast]
        simp [ell]
  · intro E _ hE
    refine CloseTo.bind_right _ fun R _ => (closeTo_T κ h P S E R).mono ?_
    apply ENNReal.ofReal_le_ofReal
    have hle : ∑ j, ((E default j).natAbs : ℝ) / NT κ ≤
        ∑ _j : Fin (k κ), σLWE κ * Real.sqrt (m κ) / NT κ :=
      Finset.sum_le_sum fun j _ => div_le_div_of_nonneg_right
        (by rw [Nat.cast_natAbs]; exact_mod_cast (hE default j).le) (Nat.cast_nonneg _)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
    rw [mul_div_assoc]
    exact hle

end

end TestCase.EvLWE
