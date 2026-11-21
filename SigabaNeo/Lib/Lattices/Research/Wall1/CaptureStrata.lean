module

public import SigabaNeo.Lib.Lattices.Research.Wall1.HorizontalSelected
public import SigabaNeo.Lib.Lattices.Research.Wall1.CapturedSlide

@[expose] public section
namespace SigabaNeo.Wall1
open QAry
open scoped Matrix
noncomputable section

variable {m n q β k : ℕ} [Fact q.Prime] (pos : 0 < β) (shape : k*β = dim m n)
  (e : Fin m → ℤ) (s : Fin n → ℤ) (A : Matrix (Fin m) (Fin n) (ZMod q))

def prefixContainsPlant : Prop :=
  WithLp.toLp 2 (fun i ↦ ((Planted.plantedPoint e s (indexEquiv.symm i) : ℤ) : ℝ)) ∈
    selectedPrefixSpan pos shape e s A

/-- No lattice lift projects to the open segment from zero to either signed projection. -/
def noInteriorMultiple : Prop :=
  let W := selectedPrefixSpan pos shape e s A
  let P (z : Fin (dim m n) → ℤ) := Wᗮ.orthogonalProjectionOnto
    (WithLp.toLp 2 (fun i ↦ (z i : ℝ)))
  let c := fun i ↦ A i ⬝ᵥ (fun j ↦ (s j : ZMod q)) + e i
  let u := P (Planted.plantedPoint e s ∘ indexEquiv.symm)
  ∀ z, FinMember A c z → ∀ a : ℝ, 0 < |a| → |a| < 1 → P z ≠ a • u

theorem sameLine_strata :
    (terminal pos shape e s A).sameLine ↔
      ¬ prefixContainsPlant pos shape e s A ∧ noInteriorMultiple pos shape e s A := by
  let W := selectedPrefixSpan pos shape e s A
  let P (z : Fin (dim m n) → ℤ) := Wᗮ.orthogonalProjectionOnto
    (WithLp.toLp 2 (fun i ↦ (z i : ℝ)))
  let u := P (Planted.plantedPoint e s ∘ indexEquiv.symm)
  have zero : u = 0 ↔ prefixContainsPlant pos shape e s A := by
    dsimp [u,P,prefixContainsPlant]
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.orthogonal_orthogonal]
  constructor
  · rintro ⟨hn, h⟩
    have nz : u ≠ 0 := hn
    refine ⟨fun hc ↦ nz (zero.mpr hc), ?_⟩
    intro z hz a ha hb eq
    change P z = a • u at eq
    have small : ‖P z‖ < ‖u‖ := by
      rw [eq, norm_smul, Real.norm_eq_abs]
      exact mul_lt_of_lt_one_left (norm_pos_iff.mpr nz) hb
    have ne : P z ≠ 0 := eq ▸ smul_ne_zero (abs_pos.mp ha) nz
    rcases h z ⟨hz, ne, small.le⟩ (Submodule.mem_span_singleton.mpr ⟨a, eq.symm⟩) with hp | hm
    · exact small.ne (congrArg norm (show P z = u from hp))
    · exact small.ne (by rw [show P z = -u from hm, norm_neg])
  · rintro ⟨hc, h⟩
    have nz : u ≠ 0 := fun he ↦ hc (zero.mp he)
    refine ⟨nz, ?_⟩
    rintro z ⟨hz, hn, le⟩ line
    change P z ≠ 0 at hn
    change P z = u ∨ P z = -u
    obtain ⟨a, eq⟩ := Submodule.mem_span_singleton.mp line
    change a • u = P z at eq
    change ‖P z‖ ≤ ‖u‖ at le
    rw [← eq, norm_smul, Real.norm_eq_abs] at le
    have ha : |a| ≤ 1 := by nlinarith [norm_pos_iff.mpr nz]
    have hn' : a ≠ 0 := by
      rintro rfl
      exact hn (by simpa using eq.symm)
    have one := ha.eq_of_not_lt (fun lt ↦ h z hz a (abs_pos.mpr hn') lt eq.symm)
    rcases le_or_gt 0 a with hp | hm
    · rw [abs_of_nonneg hp] at one
      exact Or.inl (by simpa [one] using eq.symm)
    · rw [abs_of_neg hm] at one
      exact Or.inr (by simpa [show a = -1 by linarith] using eq.symm)

/-- Containment is harmless exactly when a signed output row has already recovered the plant. -/
theorem captureStrata_iff :
    (captured pos shape e s A ∨ (terminal pos shape e s A).sameLine) ↔
    (prefixContainsPlant pos shape e s A → captured pos shape e s A) ∧
    (¬ captured pos shape e s A → ¬ prefixContainsPlant pos shape e s A →
      ¬ horizontalPrefix pos shape e s A → noInteriorMultiple pos shape e s A) := by
  have horizontal := sameLine_of_horizontal pos shape e s A
  rw [sameLine_strata] at horizontal ⊢
  tauto

#print axioms captureStrata_iff
end
end SigabaNeo.Wall1
