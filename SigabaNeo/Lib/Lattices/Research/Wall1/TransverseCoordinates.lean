import SigabaNeo.Lib.Lattices.Research.Wall1.TransverseInvariance

/-! A measurable oriented choice of transverse coordinates for primitive incidence. -/

noncomputable section
open MeasureTheory ProbabilityTheory SigabaNeo.Rogers Submodule
open scoped ENNReal InnerProductSpace
namespace SigabaNeo.Wall1

abbrev basisVector {n : ℕ} (i : Fin n) : E n := EuclideanSpace.single i (1 : ℝ)

private def pole {m : ℕ} (x : E (m+1)) : E (m+1) := ‖x‖ • basisVector 0

/-- Two hyperplane reflections straighten a mark, preserving orientation. On the positive
coordinate ray (including zero) use the identity. -/
def transverseRotation {m : ℕ} (i : Fin m) (x : E (m+1)) : E (m+1) ≃ₗᵢ[ℝ] E (m+1) :=
  if x = pole x then LinearIsometryEquiv.refl ℝ _
  else (ℝ ∙ (x - pole x))ᗮ.reflection |>.trans (ℝ ∙ basisVector i.succ)ᗮ.reflection

theorem transverseRotation_mark {m : ℕ} (i : Fin m) (x : E (m+1)) :
    transverseRotation i x x = ‖x‖ • basisVector 0 := by
  unfold transverseRotation
  split_ifs with h
  · exact h
  · rw [LinearIsometryEquiv.trans_apply, reflection_sub (by simp [pole, norm_smul, PiLp.norm_single])]
    apply reflection_mem_subspace_eq_self
    rw [mem_orthogonal_singleton_iff_inner_right]
    simp [pole, EuclideanSpace.inner_single_left]

theorem transverseRotation_det {m : ℕ} (i : Fin m) (x : E (m+1)) :
    LinearMap.det (transverseRotation i x).toLinearMap = 1 := by
  unfold transverseRotation
  split_ifs with h
  · exact LinearMap.det_id
  · have hi : basisVector i.succ ≠ 0 := by
      intro e
      have := congrArg norm e
      simp [PiLp.norm_single] at this
    change LinearMap.det (_ ∘ₗ _) = _
    rw [LinearMap.det_comp, det_reflection, det_reflection]
    have rank (v : E (m+1)) (hv : v ≠ 0) :
        Module.finrank ℝ ((ℝ ∙ v)ᗮᗮ) = 1 :=
      (congrArg (fun S : Submodule ℝ (E (m+1)) ↦ Module.finrank ℝ S)
        (ℝ ∙ v).orthogonal_orthogonal).trans (finrank_span_singleton hv)
    rw [rank _ hi, rank _ (sub_ne_zero.mpr h)]
    norm_num

theorem measurable_transverseRotation {m : ℕ} (i : Fin m) :
    Measurable fun p : E (m+1) × E (m+1) ↦ transverseRotation i p.1 p.2 := by
  have hp : Measurable (pole (m := m)) := measurable_id.norm.smul measurable_const
  unfold transverseRotation
  simp_rw [show ∀ (x y : E (m+1)), (if x = pole x then LinearIsometryEquiv.refl ℝ _
      else (ℝ ∙ (x - pole x))ᗮ.reflection |>.trans (ℝ ∙ basisVector i.succ)ᗮ.reflection) y =
      if x = pole x then y else (ℝ ∙ basisVector i.succ)ᗮ.reflection
        ((ℝ ∙ (x - pole x))ᗮ.reflection y) by intro x y; split_ifs <;> rfl]
  apply Measurable.ite (measurableSet_eq_fun measurable_fst (hp.comp measurable_fst)) measurable_snd
  apply (ℝ ∙ basisVector i.succ)ᗮ.reflection.continuous.measurable.comp
  simp only [reflection_orthogonal_apply, reflection_singleton_apply]
  have hu : Measurable (fun p : E (m+1) × E (m+1) ↦ p.1 - pole p.1) := measurable_fst.sub (hp.comp measurable_fst)
  exact (((((hu.inner measurable_snd).div (hu.norm.pow_const 2)).smul hu).const_smul 2).sub
    measurable_snd).neg

/-- Straightened normalized projections have zero axial coordinate. -/
theorem transverseRotation_projection_axis {m : ℕ} (i : Fin m) (hn : 2 ≤ m+1)
    (g : SL (m+1)) (z : Fin (m+1) → ℤ) (hx : markedColumn hn g ≠ 0) :
    transverseRotation i (markedColumn hn g) (normalizedProjection hn g z) 0 = 0 := by
  let x := markedColumn hn g
  let R := transverseRotation i x
  have hmem : normalizedProjection hn g z ∈ (ℝ ∙ x)ᗮ :=
    Submodule.smul_mem _ _ (Submodule.starProjection_apply_mem _ _)
  have h := R.inner_map_map x (normalizedProjection hn g z)
  rw [mem_orthogonal_singleton_iff_inner_right.mp hmem] at h
  change inner ℝ (transverseRotation i x x) _ = 0 at h
  rw [transverseRotation_mark, real_inner_smul_left, EuclideanSpace.inner_single_left] at h
  simpa using (mul_eq_zero.mp h).resolve_left (norm_ne_zero_iff.mpr hx)

private abbrev col {n : ℕ} (g : SL n) (j : Fin n) : E n :=
  WithLp.toLp 2 (g.val.col j)

private theorem marked_eq_col {m : ℕ} (hn : 2 ≤ m+1) (g : SL (m+1)) :
    markedColumn hn g = col g 0 := by
  change WithLp.toLp 2 (g.val.mulVec _) = _
  congr 1
  rw [← Matrix.mulVec_single_one g.val 0]
  congr 1
  ext j
  by_cases h : j = 0 <;> simp [Pi.single_apply, h]

private def straightMatrix {m : ℕ} (i : Fin m) (g : SL (m+1)) :
    Matrix (Fin (m+1)) (Fin (m+1)) ℝ :=
  Matrix.of fun j k ↦ transverseRotation i (col g 0) (col g k) j

private def rotationMatrix {m : ℕ} (i : Fin m) (x : E (m+1)) : SL (m+1) :=
  let b := (EuclideanSpace.basisFun (Fin (m+1)) ℝ).toBasis
  ⟨LinearMap.toMatrix b b (transverseRotation i x).toLinearMap, by
    rw [LinearMap.det_toMatrix, transverseRotation_det]⟩

private theorem straightMatrix_factor {m : ℕ} (i : Fin m) (g : SL (m+1)) :
    straightMatrix i g = (rotationMatrix i (col g 0) * g).val := by
  let b := (EuclideanSpace.basisFun (Fin (m+1)) ℝ).toBasis
  let R := transverseRotation i (col g 0)
  ext j k
  change R (col g k) j = ((LinearMap.toMatrix b b R.toLinearMap).mulVec (g.val.col k)) j
  exact (congrFun (LinearMap.toMatrix_mulVec_repr b b R.toLinearMap (col g k)) j).symm

private theorem straightMatrix_det {m : ℕ} (i : Fin m) (g : SL (m+1)) :
    (straightMatrix i g).det = 1 := by
  rw [straightMatrix_factor]
  exact (rotationMatrix i (col g 0) * g).property

/-- A determinant-one frame for the transverse shape, in fixed Euclidean coordinates. -/
def transverseFrame {m : ℕ} (i : Fin m) (g : SL (m+1)) : SL m :=
  ⟨‖col g 0‖ ^ (m : ℝ)⁻¹ • (straightMatrix i g).submatrix Fin.succ Fin.succ, by
    have h := straightMatrix_det i g
    have head (j : Fin (m+1)) : straightMatrix i g j 0 = (‖col g 0‖ • basisVector 0) j :=
      congrArg (fun v : E (m+1) ↦ v j) (transverseRotation_mark i (col g 0))
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ] at h
    rw [Matrix.det_smul, Fintype.card_fin, Real.rpow_inv_natCast_pow (norm_nonneg _) (Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt))]
    simpa [head, PiLp.smul_apply, PiLp.single_apply] using h⟩

theorem measurable_transverseFrame {m : ℕ} (i : Fin m) :
    Measurable (transverseFrame i) := by
  let : BorelSpace (SL (m+1)) := ⟨rfl⟩
  have hc (j : Fin (m+1)) : Continuous (fun g : SL (m+1) ↦ col g j) := by
    apply (PiLp.continuous_toLp 2 _).comp
    exact continuous_pi fun k ↦ (continuous_apply j).comp
      ((continuous_apply k).comp continuous_subtype_val)
  change @Measurable _ _ _ (@borel _ (TopologicalSpace.induced Subtype.val _)) _
  rw [borel_comap, ← BorelSpace.measurable_eq (α := Matrix (Fin m) (Fin m) ℝ)]
  apply Measurable.subtype_mk
  apply Measurable.of_eval
  intro j
  apply Measurable.of_eval
  intro k
  exact ((hc 0).measurable.norm.pow_const _).mul (((EuclideanSpace.proj (𝕜 := ℝ) j.succ).continuous.measurable).comp
    ((measurable_transverseRotation i).comp ((hc 0).measurable.prodMk (hc k.succ).measurable)))

/-- Dropping the axial coordinate after straightening the normalized projection gives exactly
the lattice point with the tail integer coordinates in the transverse frame. -/
theorem transverseFrame_point {m : ℕ} (i : Fin m) (hn : 2 ≤ m+1) (g : SL (m+1))
    (z : Fin (m+1) → ℤ) (j : Fin m) :
    transverseRotation i (markedColumn hn g) (normalizedProjection hn g z) j.succ =
      latticePoint (transverseFrame i g) (fun k ↦ z k.succ) j := by
  let R := transverseRotation i (col g 0)
  have point : latticePoint g z = ∑ k, (z k : ℝ) • col g k := by
    ext k
    simp [latticePoint, Matrix.SpecialLinearGroup.smul_def, Matrix.mulVec, dotProduct,
      mul_comm]
  have axis : R (col g 0) j.succ = 0 := by
    simp [R, transverseRotation_mark, PiLp.smul_apply]
  simp only [normalizedProjection, marked_eq_col, Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_singleton, map_smul, map_sub]
  change ( _ • (R (latticePoint g z) - _ • R (col g 0))) j.succ = _
  simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, axis, mul_zero, sub_zero,
    Nat.add_sub_cancel, point, map_sum, map_smul]
  rw [Fin.sum_univ_succ]
  change _ = (transverseFrame i g).val.mulVec (fun k ↦ (z k.succ : ℝ)) j
  simp [transverseFrame, Matrix.mulVec,
    dotProduct, straightMatrix, R, transverseRotation_mark, Finset.mul_sum, mul_assoc,
    mul_comm]

/-- The fixed-coordinate lattice as a point of the arithmetic quotient. -/
def transverseShape {m : ℕ} (i : Fin m) (g : SL (m+1)) : LatticeSpace m :=
  QuotientGroup.mk (transverseFrame i g)

theorem measurable_transverseShape {m : ℕ} (i : Fin m) : Measurable (transverseShape i) :=
  measurable_quotient_mk''.comp (measurable_transverseFrame i)

/-- The point set of the quotient realization is the whole straightened projection. -/
theorem transverseShape_points {m : ℕ} (i : Fin m) (hn : 2 ≤ m+1) (g : SL (m+1)) :
    points (transverseShape i g) = Set.range (fun z ↦ WithLp.toLp 2 (fun j : Fin m ↦
      transverseRotation i (markedColumn hn g) (normalizedProjection hn g z) j.succ)) := by
  rw [transverseShape, points_mk]
  simp_rw [transverseFrame_point]
  change Set.range (latticePoint (transverseFrame i g)) =
    Set.range ((latticePoint (transverseFrame i g)) ∘ fun z : Fin (m+1) → ℤ ↦ fun k ↦ z k.succ)
  have hs : Function.Surjective (fun z : Fin (m+1) → ℤ ↦ fun k : Fin m ↦ z k.succ) :=
    fun z ↦ ⟨Fin.cons 0 z, funext fun k ↦ Fin.cons_succ _ _ _⟩
  exact (hs.range_comp _).symm

/-- Disintegration on the actual space of unimodular transverse lattices. -/
theorem transverseShape_disintegration {m : ℕ} (i : Fin m) (hn : 2 ≤ m+1)
    (D : Set (SL (m+1))) (hm : MeasurableSet D)
    (hd : IsFundamentalDomain (integerGroup (m+1)).op D (groupHaar (m+1)))
    (hp : groupHaar (m+1) D ≠ 0) (hf : groupHaar (m+1) D ≠ ⊤) :
    ∃ K : Kernel (E (m+1)) (LatticeSpace m), IsMarkovKernel K ∧
      ∀ F : E (m+1) × LatticeSpace m → ℝ≥0∞, Measurable F →
        (∫⁻ g, F (markedColumn hn g, transverseShape i g) ∂primitiveIncidence hn D) =
          (∫⁻ x, ∫⁻ L, F (x, L) ∂K x) / ∑' k, dilationWeight (m+1) k := by
  let : PolishSpace (Matrix (Fin m) (Fin m) ℝ) :=
    inferInstanceAs (PolishSpace (Fin m → Fin m → ℝ))
  let : PolishSpace (SL m) := Matrix.SpecialLinearGroup.isClosedEmbedding_val.polishSpace
  let : BorelSpace (SL m) := ⟨rfl⟩
  obtain ⟨K, hK, law⟩ := primitive_incidence_disintegration hn D hm hd hp hf
    (transverseFrame i) (measurable_transverseFrame i)
  refine ⟨K.map QuotientGroup.mk, ProbabilityTheory.Kernel.IsMarkovKernel.map K
    measurable_quotient_mk'', ?_⟩
  intro F hF
  have H := law (fun p ↦ F (p.1, QuotientGroup.mk p.2))
    (hF.comp (measurable_fst.prodMk (measurable_quotient_mk''.comp measurable_snd)))
  refine H.trans ?_
  congr 1
  apply lintegral_congr
  intro x
  exact (Kernel.lintegral_map K measurable_quotient_mk'' x
    (show Measurable (fun L ↦ F (x, L)) from hF.comp
      (measurable_const.prodMk measurable_id))).symm

private theorem markedColumn_ne {m : ℕ} (hn : 2 ≤ m+1) (g : SL (m+1)) :
    markedColumn hn g ≠ 0 := by
  intro h
  rw [marked_eq_col] at h
  have hz : g.val.col 0 = 0 := congrArg WithLp.ofLp h
  have hd := Matrix.det_succ_column_zero g.val
  simp only [show ∀ j, g.val j 0 = 0 from congrFun hz, mul_zero, zero_mul,
    Finset.sum_const_zero, g.property] at hd
  norm_num at hd

theorem transverseFrame_norm {m : ℕ} (i : Fin m) (hn : 2 ≤ m+1) (g : SL (m+1))
    (z : Fin (m+1) → ℤ) :
    ‖normalizedProjection hn g z‖ = ‖latticePoint (transverseFrame i g) (fun k ↦ z k.succ)‖ := by
  rw [← (transverseRotation i (markedColumn hn g)).norm_map (normalizedProjection hn g z)]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ,
    transverseRotation_projection_axis i hn g z (markedColumn_ne hn g)]
  simp [transverseFrame_point]

/-- Strict first-minimum event expressed without choosing a shortest vector. -/
def shortShape {m : ℕ} (c : ℝ) : Set (LatticeSpace m) :=
  {L | ∃ y ∈ points L, 0 < ‖y‖ ∧ ‖y‖ < c}

theorem transverseShape_short_iff {m : ℕ} (i : Fin m) (hn : 2 ≤ m+1) (g : SL (m+1))
    (c : ℝ) : transverseShape i g ∈ shortShape c ↔
      ∃ z, 0 < ‖normalizedProjection hn g z‖ ∧ ‖normalizedProjection hn g z‖ < c := by
  change (∃ y ∈ points (QuotientGroup.mk (transverseFrame i g)), _) ↔ _
  rw [points_mk]
  simp_rw [transverseFrame_norm i hn]
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, hz⟩
    refine ⟨Fin.cons 0 z, ?_⟩
    simp only [Fin.cons_succ]
    exact hz
  · rintro ⟨z, hz⟩
    exact ⟨_, ⟨fun k ↦ z k.succ, rfl⟩, hz⟩

/-- Every real stabilizer element acts on the positive coordinate fiber by its lower-right
block. Its free top row disappears, including for nonzero integer or real shears. -/
theorem transverseFrame_axis_stabilizer {m : ℕ} (i : Fin m) (hn : 2 ≤ m+1)
    (a g : SL (m+1)) (ha : a.val.col 0 = Pi.single 0 1)
    (hg : markedColumn hn g = ‖markedColumn hn g‖ • basisVector 0) :
    markedColumn hn (a * g) = markedColumn hn g ∧
    (transverseFrame i (a * g)).val =
      a.val.submatrix Fin.succ Fin.succ * (transverseFrame i g).val := by
  rw [marked_eq_col hn g] at hg
  have hc := congrArg WithLp.ofLp hg
  change g.val.col 0 = ‖col g 0‖ • Pi.single 0 1 at hc
  have hfix : col (a * g) 0 = col g 0 := by
    apply WithLp.ofLp_injective 2
    change (a.val * g.val).col 0 = g.val.col 0
    rw [Matrix.col_mul_eq_mulVec_col, hc, Matrix.mulVec_smul, Matrix.mulVec_single_one, ha]
  refine ⟨by simpa only [marked_eq_col] using hfix, ?_⟩
  have hr : transverseRotation i (col g 0) = LinearIsometryEquiv.refl ℝ _ := by
    exact if_pos hg
  ext j k
  have hz : a.val j.succ 0 = 0 := by simpa using congrFun ha j.succ
  change ‖col (a * g) 0‖ ^ (m : ℝ)⁻¹ *
    (transverseRotation i (col (a * g) 0) (col (a * g) k.succ)) j.succ = _
  rw [hfix, hr]
  change ‖col g 0‖ ^ (m : ℝ)⁻¹ * (a.val * g.val) j.succ k.succ = _
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, hz, zero_mul, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  change _ = a.val j.succ t.succ * (‖col g 0‖ ^ (m : ℝ)⁻¹ *
    (transverseRotation i (col g 0) (col g k.succ)) t.succ)
  rw [hr]
  change _ = a.val j.succ t.succ * (‖col g 0‖ ^ (m : ℝ)⁻¹ * g.val t.succ k.succ)
  ring

/-- For each parent transformation and each marked fiber there is one lower-dimensional
special linear transformation that works simultaneously on every frame in that fiber. -/
theorem transverseFrame_transport {m : ℕ} (i : Fin m) (hn : 2 ≤ m+1) (a g₀ : SL (m+1)) :
    ∃ h : SL m, ∀ g : SL (m+1), markedColumn hn g = markedColumn hn g₀ →
      transverseFrame i (a * g) = h * transverseFrame i g := by
  let x := col g₀ 0
  let y := col (a * g₀) 0
  let B := rotationMatrix i y * a * (rotationMatrix i x)⁻¹
  let M := B.val.submatrix Fin.succ Fin.succ
  have fac (g : SL (m+1)) (hx : col g 0 = x) :
      col (a * g) 0 = y ∧ straightMatrix i (a * g) = B.val * straightMatrix i g := by
    have hy : col (a * g) 0 = y := by
      apply WithLp.ofLp_injective 2
      change (a.val * g.val).col 0 = (a.val * g₀.val).col 0
      simp only [Matrix.col_mul_eq_mulVec_col]
      rw [show g.val.col 0 = g₀.val.col 0 from congrArg WithLp.ofLp hx]
    refine ⟨hy, ?_⟩
    rw [straightMatrix_factor, straightMatrix_factor, hx, hy]
    change _ = (B * (rotationMatrix i x * g)).val
    simp [B, mul_assoc]
  have head (g : SL (m+1)) (j : Fin (m+1)) :
      straightMatrix i g j 0 = (‖col g 0‖ • basisVector 0) j :=
    congrArg (fun v : E (m+1) ↦ v j) (transverseRotation_mark i (col g 0))
  have hcol : g₀.val.col 0 ≠ 0 := by
    intro he
    apply markedColumn_ne hn g₀
    rw [marked_eq_col]
    exact congrArg (WithLp.toLp 2) he
  have zero (j : Fin m) : B.val j.succ 0 = 0 := by
    have h := congrArg (fun A : Matrix (Fin (m+1)) (Fin (m+1)) ℝ ↦ A j.succ 0)
      (fac g₀ rfl).2
    simp [Matrix.mul_apply, Fin.sum_univ_succ, head, PiLp.smul_apply] at h
    exact h.resolve_right hcol
  let N := (‖y‖ ^ (m : ℝ)⁻¹ / ‖x‖ ^ (m : ℝ)⁻¹) • M
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr (by simpa only [marked_eq_col] using markedColumn_ne hn g₀)
  have trans (g : SL (m+1)) (hx : col g 0 = x) :
      (transverseFrame i (a * g)).val = N * (transverseFrame i g).val := by
    obtain ⟨hy, he⟩ := fac g hx
    change _ • (straightMatrix i (a * g)).submatrix Fin.succ Fin.succ =
      N * (‖col g 0‖ ^ (m : ℝ)⁻¹ • _)
    rw [hy, hx, he, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    rw [mul_comm (‖x‖ ^ (m : ℝ)⁻¹), div_mul_cancel₀ _ (Real.rpow_pos_of_pos hxpos _).ne']
    congr 1
    ext j k
    simp [Matrix.mul_apply, Fin.sum_univ_succ, M, zero]
  let h := transverseFrame i (a * g₀) * (transverseFrame i g₀)⁻¹
  have hh : h.val = N := by
    change (transverseFrame i (a * g₀)).val * _ = N
    rw [trans g₀ rfl, Matrix.mul_assoc]
    change N * ((transverseFrame i g₀ * (transverseFrame i g₀)⁻¹).val) = N
    rw [mul_inv_cancel]
    exact Matrix.mul_one _
  refine ⟨h, fun g hg ↦ Subtype.ext ?_⟩
  change _ = h.val * _
  rw [hh]
  exact trans g (by simpa only [marked_eq_col] using hg)

private def blockLift {m : ℕ} (h : SL m) : SL (m+1) :=
  let M : Matrix (Fin (m+1)) (Fin (m+1)) ℝ :=
    Matrix.of (Fin.cons (Pi.single 0 1) (fun j ↦ Fin.cons 0 (h.val j)))
  ⟨M, by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    have hz (j : Fin m) : M j.succ 0 = 0 := by simp [M]
    have hminor : M.submatrix Fin.succ Fin.succ = h.val := by ext j k; simp [M]
    have hhead : M 0 0 = 1 := by simp [M]
    simp [hz, hhead, hminor]⟩

/-- The real stabilizer of each marked fiber realizes *every* special linear transformation
of its normalized transverse frame, with one parent matrix for the whole fiber. -/
theorem transverseFrame_stabilizer_surjective {m : ℕ} (i : Fin m) (hn : 2 ≤ m+1)
    (g₀ : SL (m+1)) (h : SL m) :
    ∃ a : SL (m+1), ∀ g : SL (m+1), markedColumn hn g = markedColumn hn g₀ →
      markedColumn hn (a * g) = markedColumn hn g ∧
      transverseFrame i (a * g) = h * transverseFrame i g := by
  let R := rotationMatrix i (col g₀ 0)
  let B := blockLift h
  let a := R⁻¹ * B * R
  refine ⟨a, fun g hg ↦ ?_⟩
  have hx : col g 0 = col g₀ 0 := by simpa only [marked_eq_col] using hg
  have fac : R * (a * g) = B * (R * g) := by simp [a, mul_assoc]
  have head : (R * g).val.col 0 = ‖col g 0‖ • Pi.single 0 1 := by
    rw [show R = rotationMatrix i (col g 0) by rw [hx]]
    rw [← straightMatrix_factor]
    exact congrArg WithLp.ofLp (transverseRotation_mark i (col g 0))
  have same : (R * (a * g)).val.col 0 = (R * g).val.col 0 := by
    rw [fac]
    change (B.val * (R * g).val).col 0 = _
    rw [Matrix.col_mul_eq_mulVec_col, head, Matrix.mulVec_smul, Matrix.mulVec_single_one]
    congr 1
    funext j
    refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp [B, blockLift, Matrix.col_apply]
  change R • (a * g).val.col 0 = R • g.val.col 0 at same
  have he : col (a * g) 0 = col g 0 :=
    congrArg (WithLp.toLp 2) ((MulAction.injective R) same)
  refine ⟨by simpa only [marked_eq_col] using he, Subtype.ext ?_⟩
  have eqn : straightMatrix i (a * g) = B.val * straightMatrix i g := by
    simp only [straightMatrix_factor, he, hx]
    exact congrArg Subtype.val fac
  change _ • (straightMatrix i (a * g)).submatrix Fin.succ Fin.succ =
    h.val * (‖col g 0‖ ^ (m : ℝ)⁻¹ • _)
  rw [he, eqn, Matrix.mul_smul]
  congr 1
  ext j k
  simp [Matrix.mul_apply, Fin.sum_univ_succ, B, blockLift, Matrix.submatrix]

#print axioms transverseFrame_stabilizer_surjective
#print axioms transverseFrame_transport
#print axioms transverseFrame_axis_stabilizer
#print axioms transverseFrame_norm
#print axioms transverseShape_short_iff
#print axioms transverseShape_points
#print axioms transverseShape_disintegration
#print axioms transverseFrame_point
#print axioms transverseFrame
#print axioms measurable_transverseFrame
#print axioms transverseRotation_mark
#print axioms transverseRotation_det
#print axioms measurable_transverseRotation
#print axioms transverseRotation_projection_axis
end SigabaNeo.Wall1
