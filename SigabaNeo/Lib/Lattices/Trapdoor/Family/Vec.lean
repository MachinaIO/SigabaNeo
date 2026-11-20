import SigabaNeo.Lib.Lattices.Trapdoor.Family.Law1D
import CslibFrontier.Languages.Probabilistic.Repeat

/-!
# Trapdoor sampler: `m` independent draws of the `D_{Z,τ}` sampler

`sampV` runs `samp1` `m` times (cslib-frontier's `OracleComp.replicate`); its law `μV` is the
product of the one-dimensional laws (`μV_apply`). From `samp1_ge`/`samp1_le`, `μV` meets the
hypotheses of `colLawOf_close` with `a = a₁^m` and `b = b₁^m` (`μV_ge`, `μV_le`, `μV_tail`).
-/

namespace SigabaNeo.Lattices.Trapdoor.Family

open SigabaNeo.Lattices Cslib Cslib.Probability
open scoped ENNReal

theorem eval_replicate_eq {α : Type} (p : ProbComp α) :
    ∀ k, ProbComp.eval (OracleComp.replicate k p) = sampleList (ProbComp.eval p) k
  | 0 => by
    show ProbComp.eval (pure [] : ProbComp (List α)) = PMF.pure []
    rw [ProbComp.eval_pure]
  | k + 1 => by
    rw [OracleComp.replicate_succ, ProbComp.eval_bind]
    show _ = (ProbComp.eval p).bind fun a => (sampleList (ProbComp.eval p) k).map (a :: ·)
    congr 1; funext a
    rw [ProbComp.eval_map, eval_replicate_eq p k]

section
variable (κ : ℕ)

/-- `m` independent draws. -/
noncomputable def sampV : ProbComp (List ℤ) := OracleComp.replicate (m κ) (samp1 κ)

/-- The vector of a list. -/
def vecOf (l : List ℤ) : Fin (m κ) → ℤ := fun j => l.getD j default

/-- The law of the vector. -/
noncomputable def μV : PMF (Fin (m κ) → ℤ) := (ProbComp.eval (sampV κ)).map (vecOf κ)

theorem μV_apply (y : Fin (m κ) → ℤ) : μV κ y = ∏ j, ProbComp.eval (samp1 κ) (y j) := by
  unfold μV sampV
  rw [eval_replicate_eq]
  exact vecLaw_apply _ _ y

theorem gaussVec_eq_prod (y : Fin (m κ) → ℤ) :
    ENNReal.ofReal (rhoV κ y) / ENNReal.ofReal (Mz (τ κ)) ^ m κ =
      ∏ j, gaussZ (τ κ) (τ_pos κ) (y j) := by
  rw [← gaussVec_apply]; unfold gaussVec; exact vecLaw_apply _ _ y

theorem m_lt_two_pow_Lg : m κ < 2 ^ Lg κ := Nat.lt_pow_succ_log_self (by norm_num) _

/-- The enlarged box lies inside the proposals. -/
theorem BoxE_range (y : Fin (m κ) → ℤ) (hy : y ∈ BoxE κ) (j : Fin (m κ)) :
    -(2 : ℤ) ^ Aex κ ≤ y j ∧ y j < 2 ^ Aex κ := by
  have h := hy j
  have hm : ((m κ : ℕ) : ℝ) + 1 ≤ 2 ^ Lg κ := by exact_mod_cast m_lt_two_pow_Lg κ
  have hτ := one_le_τ κ
  have hmb : (mb κ : ℝ) ≤ m κ := by exact_mod_cast (show mb κ ≤ m κ by rw [m_eq_mb]; omega)
  have hA : (2 : ℝ) ^ Aex κ = τ κ * 2 ^ (Lg κ + 1) := by
    rw [τ, Aex, ← pow_add]; congr 1; ring
  have hlt : Rr κ + mb κ ≤ (2 : ℝ) ^ Aex κ := by
    rw [hA, Rr, pow_succ]
    have hm0 : (0 : ℝ) ≤ m κ := Nat.cast_nonneg _
    nlinarith
  have h2 : |((y j : ℤ) : ℝ)| < (2 : ℝ) ^ Aex κ := lt_of_lt_of_le h hlt
  have h3 : |y j| < (2 : ℤ) ^ Aex κ := by exact_mod_cast h2
  rw [abs_lt] at h3
  exact ⟨h3.1.le, h3.2⟩

theorem μV_ge (y : Fin (m κ) → ℤ) (hy : y ∈ BoxE κ) :
    a1 κ ^ m κ * (ENNReal.ofReal (rhoV κ y) / ENNReal.ofReal (Mz (τ κ)) ^ m κ) ≤ μV κ y := by
  rw [gaussVec_eq_prod, μV_apply]
  calc a1 κ ^ m κ * ∏ j, gaussZ (τ κ) (τ_pos κ) (y j)
      = ∏ j, a1 κ * gaussZ (τ κ) (τ_pos κ) (y j) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ j, ProbComp.eval (samp1 κ) (y j) :=
        Finset.prod_le_prod fun j _ => samp1_ge κ (y j) (BoxE_range κ y hy j)

theorem μV_le (y : Fin (m κ) → ℤ) :
    μV κ y ≤ b1 κ ^ m κ * (ENNReal.ofReal (rhoV κ y) / ENNReal.ofReal (Mz (τ κ)) ^ m κ) := by
  rw [gaussVec_eq_prod, μV_apply]
  calc ∏ j, ProbComp.eval (samp1 κ) (y j) ≤ ∏ j, b1 κ * gaussZ (τ κ) (τ_pos κ) (y j) :=
        Finset.prod_le_prod fun j _ => samp1_le κ (y j)
    _ = b1 κ ^ m κ * ∏ j, gaussZ (τ κ) (τ_pos κ) (y j) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem samp1_tail (S : Set ℤ) :
    (ProbComp.eval (samp1 κ)).toOuterMeasure S ≤ b1 κ * (gaussZ (τ κ) (τ_pos κ)).toOuterMeasure S := by
  rw [toOuterMeasure_eq_ev, toOuterMeasure_eq_ev, ← ev_mul_left]
  unfold ev
  refine tsum_le_tsum fun z => ?_
  calc ProbComp.eval (samp1 κ) z * ind (z ∈ S) ≤ b1 κ * gaussZ (τ κ) (τ_pos κ) z * ind (z ∈ S) :=
        mul_le_mul_left (samp1_le κ z) _
    _ = gaussZ (τ κ) (τ_pos κ) z * (b1 κ * ind (z ∈ S)) := by ring

theorem μV_tail :
    (μV κ).toOuterMeasure {y | ∃ j, τ κ * Real.sqrt (m κ) ≤ |((y j : ℤ) : ℝ)|} ≤
      (m κ : ℝ≥0∞) * (b1 κ * ENNReal.ofReal (6 * (1 / 4) ^ m κ)) := by
  rw [toOuterMeasure_eq_ev]
  unfold μV sampV
  rw [ev_map, eval_replicate_eq]
  refine (ev_mono _ fun l => ind_mono (Q := ∃ x ∈ l, τ κ * Real.sqrt (m κ) ≤ |((x : ℤ) : ℝ)|) ?_).trans
    (ev_sampleList_exists _ _ ?_ (m κ))
  · rintro ⟨j, hj⟩
    simp only [vecOf, List.getD_eq_getElem?_getD] at hj
    cases hx : l[(j : ℕ)]? with
    | none =>
      rw [hx] at hj; simp only [Option.getD_none] at hj
      have : 0 < τ κ * Real.sqrt (m κ) :=
        mul_pos (τ_pos κ) (Real.sqrt_pos.mpr (by exact_mod_cast m_pos κ))
      simp at hj; linarith
    | some x => rw [hx] at hj; exact ⟨x, List.mem_of_getElem? hx, hj⟩
  · refine (toOuterMeasure_eq_ev (ProbComp.eval (samp1 κ))
      {x : ℤ | τ κ * Real.sqrt (m κ) ≤ |(x : ℝ)|}).symm.le.trans ?_
    refine (samp1_tail κ _).trans (mul_le_mul_right ?_ _)
    exact (gaussZ_tail (one_le_τ κ) (τ_pos κ) (m κ))

end

end SigabaNeo.Lattices.Trapdoor.Family
