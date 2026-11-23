import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonRankSix
import SigabaNeo.Lib.Lattices.Research.Wall1.ControlledLateEnclosures

/-! Scalar hypotheses for the existing Part 192 terminal estimate. -/

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane

open TerminalProjection TerminalProjection.Restart506 DualExit

local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

/-- A larger Hermite coefficient preserves the same nonzero witness in each lattice. -/
theorem IntrinsicHermite.mono {k : ℕ} {g G : ℝ} (cap : IntrinsicHermite k g)
    (le : g ≤ G) : IntrinsicHermite k G := by
  intro L _ _
  obtain ⟨w, hw, hlen⟩ := cap L
  exact ⟨w, hw, hlen.trans (mul_le_mul_of_nonneg_right le
    (Real.rpow_nonneg (ZLattice.covolume_pos L _).le _))⟩

/-- The audited profile accepts any certified coefficients within its two exceptional caps. -/
theorem terminal_bound_of_numeric_caps {g₇ g₂₄ : ℝ}
    (h₇ : IntrinsicHermite 7 g₇) (h₂₄ : IntrinsicHermite 24 g₂₄)
    (seven : g₇ ^ 7 ≤ 64) (twentyfour : g₂₄ ≤ 4) :
    probability terminalHit < probability residual₁ + probability residual₂ + 6.515 / (10:ℝ)^12 := by
  apply Watson.terminal_bound_of_seven_twentyfour _ (h₂₄.mono twentyfour)
  apply h₇.mono
  apply le_of_pow_le_pow_left₀ (by decide : 7 ≠ 0) (Real.exp_pos _).le
  change g₇ ^ 7 ≤ Real.exp (Real.log 64 / 7) ^ 7
  rw [← Real.exp_nat_mul]
  norm_num1
  rwa [show (7 : ℝ) * (Real.log 64 / 7) = Real.log 64 by ring, Real.exp_log (by norm_num)]

/-- The late enclosures and both exits, with the prefix probability left explicit. -/
theorem terminal_bound_with_prefix :
    probability terminalHit < probability residual₁ + probability residual₂ + probability Prefix
      + 6508.320465762 / (10:ℝ)^15 := by
  linarith only [terminal_first_moment (concrete_late HermiteWitness506.Sphere.laterDeterminantFloor),
    LateEnclosures.positive394_sum, LateEnclosures.positive30_sum, LateEnclosures.horizontal406_sum]

end SigabaNeo.Wall1.ControlledPlane

#print axioms SigabaNeo.Wall1.ControlledPlane.IntrinsicHermite.mono
#print axioms SigabaNeo.Wall1.ControlledPlane.terminal_bound_of_numeric_caps
#print axioms SigabaNeo.Wall1.ControlledPlane.terminal_bound_with_prefix
