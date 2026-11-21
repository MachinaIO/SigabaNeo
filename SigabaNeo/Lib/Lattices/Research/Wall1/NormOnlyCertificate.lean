module

public import SigabaNeo.Lib.Lattices.Research.Wall1.HeightZeroFloor
import all SigabaNeo.Lib.Lattices.Research.Wall1.HeightZeroFloor
import Mathlib.Tactic

public section

namespace SigabaNeo.Wall1

variable {N : ℕ} (H : AddSubgroup (EuclideanSpace ℝ (Fin N))) (y : EuclideanSpace ℝ (Fin N))

/-- Strict horizontal separation at each admissible nonnegative height implies uniqueness. -/
theorem allHeightsUnique_of_normOnly
    (sep : ∀ h ∈ H, h ≠ 0 → ∀ k : ℤ, 0 ≤ k → (k : ℝ) ^ 2 ≤ ‖y‖ ^ 2 + 1 →
      (k : ℝ) * ‖y‖ + Real.sqrt (‖y‖ ^ 2 + 1 - (k : ℝ) ^ 2) < ‖h‖) :
    allHeightsUnique H y := by
  have test (h) (hh : h ∈ H) (hn : h ≠ 0) (k : ℤ) (hk : 0 ≤ k)
      (hb : (k : ℝ) ^ 2 ≤ ‖y‖ ^ 2 + 1) :
      ‖y‖ ^ 2 + 1 - (k : ℝ) ^ 2 < ‖h + k • y‖ ^ 2 := by
    have kr : (0 : ℝ) ≤ k := by exact_mod_cast hk
    have tri := norm_sub_le (h + k • y) (k • y)
    rw [add_sub_cancel_right, norm_zsmul ℝ, Real.norm_eq_abs, abs_of_nonneg kr] at tri
    have hs := sep h hh hn k hk hb
    have root := Real.sq_sqrt (sub_nonneg.mpr hb)
    rw [← root]
    exact pow_lt_pow_left₀ (by linarith) (Real.sqrt_nonneg _) (by decide)
  refine (allHeightsUniquenessCriterion H y).2 ?_
  refine ⟨fun h hh hn ↦ ?_, fun h hh hn ↦ ?_, ?_⟩
  · simpa using test h hh hn 0 (by decide) (by simp; positivity)
  · simpa using test h hh hn 1 (by decide) (by simp)
  · intro k hk hb h hh
    by_cases hz : h = 0
    · subst h
      have kr : (2 : ℝ) ≤ k := by exact_mod_cast hk
      rw [zero_add, norm_zsmul ℝ, Real.norm_eq_abs, abs_of_nonneg (by linarith), mul_pow]
      nlinarith [mul_nonneg (show 0 ≤ (k : ℝ)^2 - 1 by nlinarith [sq_nonneg ((k : ℝ)-2)])
        (sq_nonneg ‖y‖), sq_nonneg ((k : ℝ)-2)]
    · exact test h hh hz k (by omega) hb

/-- A single squared-norm bound suffices at every height. -/
theorem allHeightsUnique_of_normSq
    (sep : ∀ h ∈ H, h ≠ 0 → (‖y‖ ^ 2 + 1) ^ 2 < ‖h‖ ^ 2) :
    allHeightsUnique H y := by
  apply allHeightsUnique_of_normOnly
  intro h hh hn k _ hb
  let s := Real.sqrt (‖y‖ ^ 2 + 1 - (k : ℝ) ^ 2)
  have hs : s ^ 2 = ‖y‖ ^ 2 + 1 - (k : ℝ) ^ 2 := Real.sq_sqrt (sub_nonneg.mpr hb)
  have bound : (k : ℝ) * ‖y‖ + s ≤ ‖y‖ ^ 2 + 1 := by
    nlinarith [sq_nonneg ((k : ℝ) - ‖y‖), sq_nonneg (s - 1)]
  exact bound.trans_lt (lt_of_pow_lt_pow_left₀ 2 (norm_nonneg h) (sep h hh hn))

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.allHeightsUnique_of_normOnly
#print axioms SigabaNeo.Wall1.allHeightsUnique_of_normSq
