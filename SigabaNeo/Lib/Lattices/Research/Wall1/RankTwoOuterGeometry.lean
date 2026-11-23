import SigabaNeo.Lib.Lattices.Research.Wall1.RankTwoOrderedIncidence

/-! The physical norm of the projection off a marked plane in transverse coordinates. -/
noncomputable section
open Matrix MeasureTheory SigabaNeo.Rogers Submodule
open scoped InnerProductSpace
namespace SigabaNeo.Wall1.RankTwo

private abbrev scale {m : ℕ} (x : E (m+1)) := ‖x‖ ^ (m : ℝ)⁻¹

private theorem axial_inner {m : ℕ} (i : Fin m) (x y : E (m+1)) :
    ⟪x,y⟫_ℝ = ‖x‖ * transverseRotation i x y 0 := by
  rw [← (transverseRotation i x).inner_map_map x y, transverseRotation_mark, real_inner_smul_left,
    EuclideanSpace.inner_single_left]
  simp

private theorem tail_inner {m : ℕ} (i : Fin m) (x u v : E (m+1)) :
    ⟪normalizedTail i x u, normalizedTail i x v⟫_ℝ =
      scale x ^ 2 * (⟪u,v⟫_ℝ - transverseRotation i x u 0 * transverseRotation i x v 0) := by
  rw [← (transverseRotation i x).inner_map_map u v, PiLp.inner_apply, PiLp.inner_apply,
    Fin.sum_univ_succ (f := fun k ↦ ⟪transverseRotation i x u k, transverseRotation i x v k⟫_ℝ)]
  simp only [Real.inner_apply, add_sub_cancel_left]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  change (scale x * _) * (scale x * _) = _
  ring

private theorem tail_norm_perp {m : ℕ} (i : Fin m) {x u : E (m+1)} (hx : x ≠ 0)
    (hu : ⟪x,u⟫_ℝ = 0) : ‖normalizedTail i x u‖ = scale x * ‖u‖ := by
  have hz := (mul_eq_zero.mp ((axial_inner i x u).symm.trans hu)).resolve_left
    (norm_ne_zero_iff.mpr hx)
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _))).mp
  rw [← real_inner_self_eq_norm_sq, tail_inner, hz, zero_mul, sub_zero, real_inner_self_eq_norm_sq,
    mul_pow]

variable {r : ℕ} (i : Fin (r+1)) (j : Fin r)
local notation "n" => (r+2)

/-- The first normalized projection of the second mark encodes the parallelogram area. -/
theorem area_mul_scale (x : Frames n) :
    area x * scale (x 0) = ‖x 0‖ * ‖normalizedTail i (x 0) (x 1)‖ := by
  have h := tail_inner i (x 0) (x 1) (x 1)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  have det : (gram ℝ x).det =
      ‖x 0‖^2 * ‖x 1‖^2 - (‖x 0‖ * transverseRotation i (x 0) (x 1) 0)^2 := by
    rw [det_fin_two]
    simp only [gram_apply, real_inner_self_eq_norm_sq]
    have h10 : ⟪x 1,x 0⟫_ℝ = _ := (show ⟪x 1,x 0⟫_ℝ = ⟪x 0,x 1⟫_ℝ from real_inner_comm ..).trans
      (axial_inner i (x 0) (x 1))
    rw [h10, axial_inner i (x 0) (x 1), pow_two (_ * _)]
  have pos := (posSemidef_gram ℝ x).det_nonneg
  apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  change (Real.sqrt (gram ℝ x).det * scale (x 0)) ^ 2 = (‖x 0‖ * _) ^ 2
  rw [mul_pow, mul_pow, Real.sq_sqrt pos, det, h]
  ring

include j in
private theorem combined_scale (x : Frames n) (hx : x 0 ≠ 0) :
    scale (normalizedTail i (x 0) (x 1)) * scale (x 0) = area x ^ (r : ℝ)⁻¹ := by
  have hs : 0 < scale (x 0) := Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) _
  have hr : (r : ℝ) ≠ 0 := by have := j.isLt; exact_mod_cast (by omega : r ≠ 0)
  have aux : scale (x 0) ^ (r+1) = ‖x 0‖ :=
    Real.rpow_inv_natCast_pow (norm_nonneg _) (by omega)
  have eqn := area_mul_scale i x
  rw [← aux, pow_succ] at eqn
  have hA : area x = ‖normalizedTail i (x 0) (x 1)‖ * scale (x 0)^r :=
    (mul_right_cancel₀ hs.ne') (eqn.trans (by ring))
  rw [hA, Real.mul_rpow (norm_nonneg _) (pow_nonneg hs.le _)]
  congr 1
  exact (Real.rpow_natCast_mul hs.le r (r : ℝ)⁻¹ |>.symm.trans (by rw [mul_inv_cancel₀ hr, Real.rpow_one])).symm

theorem outerCoordinates_norm (x : Frames n) (hx : x 0 ≠ 0)
    (hy : normalizedTail i (x 0) (x 1) ≠ 0) (v : E n) :
    ‖outerCoordinates i j x v‖ = area x ^ (r : ℝ)⁻¹ *
      ‖(span ℝ (Set.range x))ᗮ.starProjection v‖ := by
  let P := span ℝ (Set.range x)
  let z := Pᗮ.starProjection v
  have hz (k : Fin 2) : ⟪x k,z⟫_ℝ = 0 :=
    (Pᗮ.starProjection_apply_mem v) (x k) (subset_span ⟨k,rfl⟩)
  have hax := (mul_eq_zero.mp ((axial_inner i (x 0) z).symm.trans (hz 0))).resolve_left
    (norm_ne_zero_iff.mpr hx)
  have horth : ⟪normalizedTail i (x 0) (x 1), normalizedTail i (x 0) z⟫_ℝ = 0 := by
    rw [tail_inner, hz, hax]; ring
  have hker : P ≤ LinearMap.ker (outerCoordinates i j x) := by
    apply span_le.mpr
    rintro _ ⟨k,rfl⟩
    change outerCoordinates i j x (x k) = 0
    fin_cases k <;> simp [outerCoordinates, normalizedTail_self]
  have mem : v - z ∈ P := by
    simp [z]
  have he := LinearMap.mem_ker.mp (hker mem)
  rw [map_sub,sub_eq_zero] at he
  rw [he]
  change ‖normalizedTail j _ (normalizedTail i (x 0) z)‖ = _ * ‖z‖
  rw [tail_norm_perp j hy horth, tail_norm_perp i hx (hz 0), ← mul_assoc, combined_scale i j x hx]

/-- The strict minimum in unimodular coordinates is exactly the strict physical cutoff
after projecting off the real span of both marks. -/
theorem outerMinimumGeometry : OuterMinimumGeometry i j := by
  intro g p c
  let x := physical (by have := j.isLt; omega : 2 ≤ r+1) g 0 0 p
  let G := adaptedFrame j p g
  have e : columns G = x := adaptedFrame_columns j p g
  have hx : x 0 ≠ 0 := by
    rw [← e]
    change column G 0 ≠ 0
    rw [column_zero (by omega)]
    exact markedColumn_nonzero _ _
  have hy : normalizedTail i (x 0) (x 1) ≠ 0 := by
    rw [← e]
    change normalizedTail i (column G 0) (column G (0 : Fin (r+1)).succ) ≠ 0
    rw [normalizedTail_col, column_zero (by have := j.isLt; omega)]
    exact markedColumn_nonzero _ _
  have hA : 0 < area x := by
    have h := area_mul_scale i x
    exact pos_of_mul_pos_left (h ▸ mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy))
      (Real.rpow_nonneg (norm_nonneg _) _)
  have hs := Real.rpow_pos_of_pos hA (r : ℝ)⁻¹
  change (∃ y ∈ points (incidenceMark i j p g).2, 0 < ‖y‖ ∧ ‖y‖ < c * area x ^ (r : ℝ)⁻¹) ↔ _
  rw [incidenceMark_points]
  constructor
  · rintro ⟨_, ⟨_,⟨z,rfl⟩,rfl⟩,hp,hl⟩
    refine ⟨z, ?_⟩
    change 0 < ‖outerCoordinates i j x _‖ at hp
    change ‖outerCoordinates i j x _‖ < _ at hl
    rw [outerCoordinates_norm i j x hx hy] at hp hl
    exact ⟨pos_of_mul_pos_right hp hs.le, (mul_lt_mul_iff_right₀ hs).mp (hl.trans_eq (mul_comm ..))⟩
  · rintro ⟨z,hp,hl⟩
    refine ⟨_, ⟨_,⟨z,rfl⟩,rfl⟩, ?_⟩
    change 0 < ‖outerCoordinates i j x _‖ ∧ ‖outerCoordinates i j x _‖ < _
    rw [outerCoordinates_norm i j x hx hy, mul_comm c]
    exact ⟨mul_pos hs hp, mul_lt_mul_of_pos_left hl hs⟩

end SigabaNeo.Wall1.RankTwo

#print axioms SigabaNeo.Wall1.RankTwo.area_mul_scale
#print axioms SigabaNeo.Wall1.RankTwo.outerCoordinates_norm
#print axioms SigabaNeo.Wall1.RankTwo.outerMinimumGeometry
