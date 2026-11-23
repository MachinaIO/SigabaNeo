import SigabaNeo.Lib.Lattices.Research.Wall1.ControlledProvedFlagSum
import SigabaNeo.Lib.Lattices.Research.Wall1.ControlledTightRaw

/-! The Part 192 terminal inequality under the finite design law. -/

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane
open DualExit QaryMembership TerminalProjection TerminalProjection.Restart506 Finset
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

theorem prefix_bound_mordell_blichfeldt : probability Prefix < 3.782 / (10 : ℝ)^14 := by
  let P := fun A : Sample ↦ rawShort (designPrefix (by decide : 105 ≤ 512) A) 2896
  let Q := fun A : Sample ↦ ∃ u, flagTest ProvedProfile.radius ProvedProfile.detFloor u (history A)
  have hc : probability Prefix ≤ probability (fun A ↦ P A ∨ Q A) := by
    apply probability_mono
    rintro A ⟨t,ht,hit⟩
    exact ProvedProfile.cover A t ht (hit_shortest _ _ hit)
  have hP : probability P < 7/(10:ℝ)^34 := by
    rw [show probability P = probability (fun A : Design 400 105 3329 ↦ rawShort A 2896) from
      prefix_probability (by decide : 105 ≤ 512) (fun A ↦ rawShort A 2896)]
    exact initial2896_numeric
  have hu := probability_exists_le univ (fun u (A : Sample) ↦ flagTest ProvedProfile.radius ProvedProfile.detFloor u
    (history A))
  have hQ : probability Q ≤ ∑ u, ProvedProfile.charge u := by
    apply le_trans _ (sum_le_sum (fun u _ ↦ ProvedProfile.flag_probability u))
    simpa [Q] using hu
  have H := (hc.trans (probability_or_le P Q)).trans_lt (add_lt_add_of_lt_of_le hP hQ)
  linarith only [H, ProvedProfile.charge_sum]

theorem terminal_bound_unconditional :
    probability terminalHit < probability residual₁ + probability residual₂ + 4.652 / (10 : ℝ)^12 := by
  linarith only [terminal_bound_with_prefix_tight_raw, prefix_bound_mordell_blichfeldt]

/-- The original Part 192 remainder, with the same two residual events. -/
theorem terminal_bound_unconditional_original :
    probability terminalHit < probability residual₁ + probability residual₂ + 6.515 / (10 : ℝ)^12 := by
  linarith only [terminal_bound_unconditional]

end SigabaNeo.Wall1.ControlledPlane

#print axioms SigabaNeo.Wall1.ControlledPlane.prefix_bound_mordell_blichfeldt
#print axioms SigabaNeo.Wall1.ControlledPlane.terminal_bound_unconditional
#print axioms SigabaNeo.Wall1.ControlledPlane.terminal_bound_unconditional_original
