import PE.Impl.Game.UntilBad

/-!
# Lemmas for assembling the reductions

* `closeTo_bool`: two laws on `Bool` are as close as their probabilities of `true`.
* `closeTo_bind_avg`: continuations close pointwise give mixtures close on average.
* `pBad_bind`: the probability of the flag of a mixture is the average.
-/

namespace AdvancedEncryption.PE.Generic

open SigabaNeo Cslib Cslib.Probability
open scoped ENNReal

theorem le_add_ofReal_abs (a b : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    a ≤ b + ENNReal.ofReal |a.toReal - b.toReal| := by
  rw [← ENNReal.toReal_le_toReal ha (ENNReal.add_ne_top.mpr ⟨hb, ENNReal.ofReal_ne_top⟩),
    ENNReal.toReal_add hb ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (abs_nonneg _)]
  linarith [le_abs_self (a.toReal - b.toReal)]

/-- **Laws on `Bool`.** -/
theorem closeTo_bool (μ ν : PMF Bool) :
    CloseTo μ ν (ENNReal.ofReal |(μ true).toReal - (ν true).toReal|) := by
  have hμ : μ false = 1 - μ true := by
    have h := μ.tsum_coe; rw [tsum_bool] at h
    exact ENNReal.eq_sub_of_add_eq (PMF.apply_ne_top _ _) h
  have hν : ν false = 1 - ν true := by
    have h := ν.tsum_coe; rw [tsum_bool] at h
    exact ENNReal.eq_sub_of_add_eq (PMF.apply_ne_top _ _) h
  have hμ1 : μ true ≤ 1 := PMF.coe_le_one _ _
  have hν1 : ν true ≤ 1 := PMF.coe_le_one _ _
  have hμt := PMF.apply_ne_top μ true
  have hνt := PMF.apply_ne_top ν true
  intro E
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, tsum_bool, tsum_bool]
  by_cases ht : true ∈ E <;> by_cases hf : false ∈ E <;>
    simp only [Set.indicator, ht, hf, if_true, if_false, zero_add, add_zero]
  · rw [hμ, hν, tsub_add_cancel_of_le hμ1, tsub_add_cancel_of_le hν1]; exact le_self_add
  · exact le_add_ofReal_abs _ _ hμt hνt
  · rw [hμ, hν]
    have h := le_add_ofReal_abs (1 - μ true) (1 - ν true) (by simp) (by simp)
    rw [ENNReal.toReal_sub_of_le hμ1 ENNReal.one_ne_top,
      ENNReal.toReal_sub_of_le hν1 ENNReal.one_ne_top] at h
    rwa [show (1 : ℝ≥0∞).toReal - (μ true).toReal - ((1 : ℝ≥0∞).toReal - (ν true).toReal) =
      -((μ true).toReal - (ν true).toReal) by ring, abs_neg] at h
  · exact bot_le

/-- **Mixtures**: pointwise closeness, averaged. -/
theorem closeTo_bind_avg {α β : Type} (μ : PMF α) (f g : α → PMF β) (ε : α → ℝ≥0∞)
    (h : ∀ a, CloseTo (f a) (g a) (ε a)) :
    CloseTo (μ.bind f) (μ.bind g) (∑' a, μ a * ε a) := by
  intro E
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun a => ?_
  rw [← mul_add]
  gcongr; exact h a E

/-- The probability of the flag of a mixture. -/
theorem pBad_bind {U : Universe} {α β : Type} (μ : PMF β)
    (f : β → PMF (α × Option U.Attr × Option U.Msg × Bool)) :
    pBad (μ.bind f) = ∑' b, μ b * pBad (f b) := by
  unfold pBad
  rw [PMF.toOuterMeasure_bind_apply]

end AdvancedEncryption.PE.Generic
