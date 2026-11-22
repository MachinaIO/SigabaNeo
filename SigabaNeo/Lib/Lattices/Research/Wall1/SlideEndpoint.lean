module

public import SigabaNeo.Lib.Lattices.Research.Wall1.SlideCovolume
import all SigabaNeo.Lib.Lattices.Research.Wall1.SlideCovolume
public import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

/-! # The unit endpoint in a graph lattice

The extension rank here is the number of secret coordinates. No primality
assumption on the modulus is needed. -/

public section

namespace SigabaNeo.Wall1.Slide

open Matrix AttackLattice MeasureTheory
open scoped Matrix ENNReal

variable {N m n q : ℕ}

private theorem residue_of_mem (A : Fin m → Fin n → ZMod q)
    (σ : Fin N ≃ Fin n ⊕ Fin m) (z : Fin N → ℤ)
    (h : intEmb N z ∈ nullLattice A σ) : residue A σ z = 0 := by
  obtain ⟨w, hw, he⟩ := h
  have hwz : w = z := by
    funext i
    have := congrArg (fun x : EuclideanSpace ℝ (Fin N) ↦ x i) he
    change (w i : ℝ) = z i at this
    exact_mod_cast this
  subst w
  exact hw

private theorem residue_axis (A : Fin m → Fin n → ZMod q)
    (σ : Fin N ≃ Fin n ⊕ Fin m) (i : Fin N) (a : Fin m) :
    residue A σ (Pi.single i 1) a =
      (if Sum.inr a = σ i then 1 else 0) +
      ∑ j, A a j * (if Sum.inl j = σ i then 1 else 0) := by
  simp [residue_apply, Pi.single_apply, Equiv.symm_apply_eq, apply_ite]

/-- Any rank-n unit-covolume frame in the null lattice forces the whole design to vanish. -/
theorem zero_of_unit_extension [Nontrivial (ZMod q)] (A : Fin m → Fin n → ZMod q)
    (σ : Fin N ≃ Fin n ⊕ Fin m) (B : Matrix (Fin N) (Fin n) ℤ)
    (mem : ∀ j, frame B j ∈ nullLattice A σ) (unitVol : volume (frame B) = 1) :
    A = 0 := by
  obtain ⟨C, d, hi, hd, h01⟩ :=
    (gramDet_one_iff_coordinate B).mp ((volume_eq_one_iff B).mp unitVol)
  have hz (v : Fin n → ℤ) : residue A σ (B *ᵥ v) = 0 := by
    have e : B *ᵥ v = ∑ j, v j • B.col j := by
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [e, map_sum]
    exact Finset.sum_eq_zero fun j _ ↦ by rw [map_zsmul, residue_of_mem A σ _ (mem j), smul_zero]
  have hu (i : Fin N) (h : d i = 1) : residue A σ (Pi.single i 1) = 0 := by
    have h' := hz (C *ᵥ Pi.single i 1)
    rw [Matrix.mulVec_mulVec, hd, Matrix.diagonal_mulVec_single, h, one_mul] at h'
    exact h'
  have err (a : Fin m) : d (σ.symm (.inr a)) = 0 := by
    refine (h01 _).resolve_right fun he ↦ ?_
    have hh := congrFun (hu _ he) a
    rw [residue_axis] at hh
    simp at hh
  have ht : ∑ i, d i = (n : ℤ) := by
    calc _ = (B * C).trace := by simp [hd, Matrix.trace_diagonal]
         _ = (C * B).trace := Matrix.trace_mul_comm _ _
         _ = _ := by simp [hi]
  rw [← Equiv.sum_comp σ.symm d, Fintype.sum_sum_type] at ht
  simp [err] at ht
  have hsum : ∑ j : Fin n, (1 - d (σ.symm (.inl j))) = 0 := by
    rw [Finset.sum_sub_distrib]; simp [ht]
  have sec (j : Fin n) : d (σ.symm (.inl j)) = 1 := by
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦
      show 0 ≤ 1 - d (σ.symm (.inl j)) by rcases h01 (σ.symm (.inl j)) with h | h <;> omega)).mp
      hsum j (Finset.mem_univ _)
    omega
  funext a j
  have hh := congrFun (hu _ (sec j)) a
  rw [residue_axis] at hh
  simpa [mul_ite] using hh

/-- The graph lift of the secret coordinate basis using standard residue representatives. -/
def graphFrame [NeZero q] (A : Fin m → Fin n → ZMod q) (σ : Fin N ≃ Fin n ⊕ Fin m) :
    Matrix (Fin N) (Fin n) ℤ := fun i j ↦
  (σ i).elim (fun k ↦ if k = j then 1 else 0) (fun a ↦ -(A a j).val)

theorem graphFrame_mem [NeZero q] (A : Fin m → Fin n → ZMod q) (σ : Fin N ≃ Fin n ⊕ Fin m)
    (j : Fin n) : frame (graphFrame A σ) j ∈ nullLattice A σ := by
  refine ⟨_, ?_, rfl⟩
  apply (AddMonoidHom.mem_ker).mpr
  ext a
  simp [graphFrame, residue_apply, Matrix.col, apply_ite]

theorem graphFrame_zero_gram [NeZero q] (σ : Fin N ≃ Fin n ⊕ Fin m) :
    (graphFrame (q := q) 0 σ)ᵀ * graphFrame (q := q) 0 σ = 1 := by
  ext i j
  rw [Matrix.mul_apply, ← Equiv.sum_comp σ.symm]
  simp [Fintype.sum_sum_type, graphFrame, Matrix.one_apply, eq_comm]

/-- For this specified lift, unit physical covolume occurs exactly at the zero matrix. -/
theorem graphFrame_unit_iff [NeZero q] [Nontrivial (ZMod q)]
    (A : Fin m → Fin n → ZMod q) (σ : Fin N ≃ Fin n ⊕ Fin m) :
    volume (frame (graphFrame A σ)) = 1 ↔ A = 0 := by
  refine ⟨zero_of_unit_extension A σ _ (graphFrame_mem A σ), ?_⟩
  rintro rfl
  rw [volume_eq_one_iff, gramDet, graphFrame_zero_gram, Matrix.det_one]

/-- Unit covolume is attainable among all rank-n extensions exactly at the zero design. -/
theorem exists_unit_extension_iff [NeZero q] [Nontrivial (ZMod q)]
    (A : Fin m → Fin n → ZMod q) (σ : Fin N ≃ Fin n ⊕ Fin m) :
    (∃ B : Matrix (Fin N) (Fin n) ℤ, (∀ j, frame B j ∈ nullLattice A σ) ∧
      volume (frame B) = 1) ↔ A = 0 := by
  constructor
  · rintro ⟨B, hm, hu⟩
    exact zero_of_unit_extension A σ B hm hu
  · intro h
    exact ⟨_, graphFrame_mem A σ, (graphFrame_unit_iff A σ).mpr h⟩

theorem uniform_zero_mass (m n q : ℕ) [NeZero q] :
    Measure.uniformOfFinset (Finset.univ : Finset (Fin m → Fin n → ZMod q)) {0} =
      ((q : ℝ≥0∞) ^ (m*n))⁻¹ := by
  simp [Measure.uniformOfFinset_apply_singleton, Fintype.card_pi, ZMod.card, pow_mul, Nat.mul_comm m n]

end SigabaNeo.Wall1.Slide

#print axioms SigabaNeo.Wall1.Slide.zero_of_unit_extension
#print axioms SigabaNeo.Wall1.Slide.graphFrame_unit_iff
#print axioms SigabaNeo.Wall1.Slide.exists_unit_extension_iff
#print axioms SigabaNeo.Wall1.Slide.uniform_zero_mass
