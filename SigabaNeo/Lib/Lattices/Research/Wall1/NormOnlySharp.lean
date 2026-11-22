module

public import SigabaNeo.Lib.Lattices.Research.Wall1.NormOnlyCertificate
import all SigabaNeo.Lib.Lattices.Research.Wall1.HeightZeroFloor
import Mathlib.Tactic

public section

namespace SigabaNeo.Wall1

/-- The antiparallel cyclic subgroup attains the height-specific threshold. Its generator
gives a nonplant point on the boundary of the closed ball. -/
theorem normOnlySharpWitness {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (y : E) (hy : y ≠ 0) (k : ℤ) (hk : 0 ≤ k) (hb : (k : ℝ)^2 ≤ ‖y‖^2 + 1) :
    let s := Real.sqrt (‖y‖^2 + 1 - (k : ℝ)^2)
    let T := (k : ℝ) * ‖y‖ + s
    let g := (-(T / ‖y‖)) • y
    g ∈ AddSubgroup.zmultiples g ∧ g ≠ 0 ∧ ‖g‖ = T ∧
      (∀ n : ℤ, ‖n • g‖ = |(n : ℝ)| * T) ∧
      (∀ h ∈ AddSubgroup.zmultiples g, h ≠ 0 → T ≤ ‖h‖) ∧
      ‖g + k • y‖ = s ∧ ‖g + k • y‖^2 + (k : ℝ)^2 = ‖y‖^2 + 1 := by
  intro s T g
  have hp := norm_pos_iff.mpr hy
  have hk' : (0 : ℝ) ≤ k := by exact_mod_cast hk
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have ht : 0 < T := by
    by_cases hz : k = 0
    · subst k
      simpa [T, s] using Real.sqrt_pos.mpr (show 0 < ‖y‖^2 + 1 by positivity)
    · have kp : 0 < k := lt_of_le_of_ne hk (Ne.symm hz)
      exact add_pos_of_pos_of_nonneg (mul_pos (by exact_mod_cast kp) hp) hs
  have hg : ‖g‖ = T := by
    dsimp only [g]
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (div_pos ht hp),
      div_mul_cancel₀ _ hp.ne']
  have hn (n : ℤ) : ‖n • g‖ = |(n : ℝ)| * T := by rw [norm_zsmul ℝ, Real.norm_eq_abs, hg]
  have he : ‖g + k • y‖ = s := by
    change ‖(-(T / ‖y‖)) • y + k • y‖ = s
    rw [← Int.cast_smul_eq_zsmul ℝ, ← add_smul, norm_smul, Real.norm_eq_abs]
    have ha : -(T / ‖y‖) + k = -(s / ‖y‖) := by
      dsimp only [T]
      field_simp
      ring
    rw [ha, abs_neg, abs_of_nonneg (div_nonneg hs hp.le), div_mul_cancel₀ _ hp.ne']
  refine ⟨AddSubgroup.mem_zmultiples _, norm_pos_iff.mp (hg ▸ ht), hg, hn, ?_, he, ?_⟩
  · intro h hh hh0
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hh
    have nz : n ≠ 0 := by rintro rfl; simp at hh0
    have one : (1 : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast (show (1 : ℤ) ≤ |n| from Int.add_one_le_iff.mpr (abs_pos.mpr nz))
    rw [hn]
    exact le_mul_of_one_le_left ht.le one
  · rw [he]
    linarith [Real.sq_sqrt (sub_nonneg.mpr hb)]

/-- Every weak lower cutoff up to the height-specific threshold admits a counterexample. -/
theorem normOnlySharp {N : ℕ} (y : EuclideanSpace ℝ (Fin N)) (hy : y ≠ 0)
    (k : ℤ) (hk : 0 ≤ k) (hb : (k : ℝ)^2 ≤ ‖y‖^2 + 1)
    (c : ℝ) (hc : c ≤ (k : ℝ) * ‖y‖ + Real.sqrt (‖y‖^2 + 1 - (k : ℝ)^2)) :
    ∃ H : AddSubgroup (EuclideanSpace ℝ (Fin N)),
      (∀ h ∈ H, h ≠ 0 → c ≤ ‖h‖) ∧ ¬ allHeightsUnique H y := by
  obtain ⟨hm, hn, _, _, hmin, _, he⟩ := normOnlySharpWitness y hy k hk hb
  exact ⟨_, fun h hh h0 ↦ hc.trans (hmin h hh h0), fun u ↦ hn (((u _ hm k).mp he.le).1)⟩

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.normOnlySharpWitness
#print axioms SigabaNeo.Wall1.normOnlySharp
