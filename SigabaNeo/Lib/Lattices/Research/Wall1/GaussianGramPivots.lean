module

public import SigabaNeo.Lib.Lattices.Research.Wall1.ThetaProfile
public import SigabaNeo.Lib.Lattices.Research.Wall1.GaussianSmoothing1D
import all SigabaNeo.Lib.Lattices.Research.Wall1.ThetaProfile
public import SigabaNeo.Lib.Lattices.Research.Wall1.ProjectedLength
import all SigabaNeo.Lib.Lattices.Research.Wall1.ProjectedLength
import Mathlib.Analysis.Matrix.PosDef
import all Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-! # Gram pivots and products of one-dimensional Gaussian masses -/

public section
namespace SigabaNeo.Wall1

open Real InnerProductSpace
open scoped Matrix

variable {N : ℕ}

/-- The leading Gram determinant of the first `j` columns of an ordered integer basis. -/
noncomputable def leadingGramDet (Q : Matrix (Fin N) (Fin N) ℝ)
    (U : Matrix (Fin N) (Fin N) ℤ) (j : ℕ) (hj : j ≤ N) : ℝ :=
  let C := (U.map (Int.castRingHom ℝ)).submatrix id (Fin.castLE hj)
  (Cᵀ * Q * C).det

/-- Consecutive Gram determinant ratios are squared lengths in the metric `Q`. -/
noncomputable def gramPivot (Q : Matrix (Fin N) (Fin N) ℝ)
    (U : Matrix (Fin N) (Fin N) ℤ) (j : Fin N) : ℝ :=
  leadingGramDet Q U (j.val + 1) j.isLt / leadingGramDet Q U j.val j.isLt.le

/-- The real projection test in (5) for one metric. Each height may have its own witness. -/
def gramProjectionTest (P : Matrix (Fin N) (Fin N) ℝ) (d : ℕ) (γ D c : ℝ) : Prop :=
  let Q := γ • (1 - P) + (γ / D) • P
  let m := γ * D ^ (-(d : ℝ) / N)
  ∃ U : Matrix (Fin N) (Fin N) ℤ, (U.det = 1 ∨ U.det = -1) ∧
    ∀ j, m/c ≤ gramPivot Q U j ∧ gramPivot Q U j ≤ c*m

/-- Product comparison at a supplied lower Gram–Schmidt profile. -/
theorem gaussianMass_le_lowerProfile {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : Module.Basis (Fin N) ℝ E) (g : Fin N → ℝ) {u : ℝ} (hu : 0 < u)
    (hg : ∀ j, 0 < g j) (floor : ∀ j, g j ≤ ‖gramSchmidt ℝ b j‖) :
    (∑' z : Fin N → ℤ, exp (-u * ‖∑ j, (z j : ℝ) • b j‖^2)) ≤
      ∏ j, thetaFactor (u * (g j)^2) := by
  apply (latticeThetaProfile b hu).2.trans
  unfold thetaFactor
  apply Finset.prod_le_prod₀ (fun j _ ↦ tsum_nonneg fun _ ↦ (exp_pos _).le)
  intro j _
  have h := (hg j).trans_le (floor j)
  apply (summable_int_gauss (mul_pos hu (sq_pos_of_pos h))).tsum_le_tsum _
    (summable_int_gauss (mul_pos hu (sq_pos_of_pos (hg j))))
  intro z
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (hg j).le (floor j) 2) hu.le)) (sq_nonneg _)

/-- Each leading Gram determinant ratio is the squared orthogonal residual. -/
theorem gramPivot_eq_residualSq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : Fin N → E) (hb : LinearIndependent ℝ b)
    (Q : Matrix (Fin N) (Fin N) ℝ) (U : Matrix (Fin N) (Fin N) ℤ)
    (gram : Matrix.gram ℝ b = (U.map (Int.castRingHom ℝ))ᵀ * Q * U.map (Int.castRingHom ℝ))
    (j : Fin N) :
    gramPivot Q U j = ‖prefixProjection (b ∘ Fin.castLE j.isLt.le) (b j)‖^2 := by
  let pre (k : ℕ) (hk : k ≤ N) := b ∘ Fin.castLE hk
  have det (k : ℕ) (hk : k ≤ N) : (Matrix.gram ℝ (pre k hk)).det = leadingGramDet Q U k hk := by
    change ((Matrix.gram ℝ b).submatrix (Fin.castLE hk) (Fin.castLE hk)).det = _
    rw [gram]
    rfl
  let W (j : Fin N) := prefixProjection (pre j j.isLt.le) (b j)
  have Kpos (k : ℕ) (hk : k ≤ N) : 0 < leadingGramDet Q U k hk := by
    rw [← det]
    exact (Matrix.posDef_gram_of_linearIndependent
      (hb.comp _ (Fin.castLE_injective hk))).det_pos
  have sqW (j : Fin N) : ‖W j‖^2 = gramPivot Q U j := by
    apply (eq_div_iff (Kpos j j.isLt.le).ne').2
    have eq : Fin.snoc (α := fun _ ↦ E) (pre j j.isLt.le) (b j) = pre (j+1) j.isLt := by
      funext i
      refine Fin.lastCases ?_ (fun i ↦ ?_) i
      · rw [Fin.snoc_last]; rfl
      · rw [Fin.snoc_castSucc]; rfl
    simpa only [eq, det] using projectedLength_sq_mul_det (pre j j.isLt.le) (b j)
  exact (sqW j).symm

/-- Equation (2) in any Euclidean realization of the Gram matrix. -/
theorem theta_le_gramPivots {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : Fin N → E) (hb : LinearIndependent ℝ b)
    (Q : Matrix (Fin N) (Fin N) ℝ) (U : Matrix (Fin N) (Fin N) ℤ)
    (gram : Matrix.gram ℝ b = (U.map (Int.castRingHom ℝ))ᵀ * Q * U.map (Int.castRingHom ℝ)) :
    (∑' z : Fin N → ℤ, exp (-‖∑ j, (z j : ℝ) • b j‖^2)) ≤ ∏ j, thetaFactor (gramPivot Q U j) := by
  let W (j : Fin N) := prefixProjection (b ∘ Fin.castLE j.isLt.le) (b j)
  have sqW (j : Fin N) : ‖W j‖^2 = gramPivot Q U j := (gramPivot_eq_residualSq b hb Q U gram j).symm
  have pos (j : Fin N) : 0 < ‖W j‖ := by
    apply norm_pos_iff.mpr
    intro hj
    let pre := b ∘ Fin.castLE j.isLt.le
    have hn : (Matrix.gram ℝ (Fin.snoc (α := fun _ ↦ E) pre (b j))).det ≠ 0 := by
      have eq : Fin.snoc (α := fun _ ↦ E) pre (b j) = b ∘ Fin.castLE j.isLt := by
        funext i
        refine Fin.lastCases ?_ (fun i ↦ ?_) i
        · rw [Fin.snoc_last]; rfl
        · rw [Fin.snoc_castSucc]; rfl
      rw [eq]
      exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr (hb.comp _ (Fin.castLE_injective _))
    apply hn
    rw [← projectedLength_sq_mul_det, show prefixProjection pre (b j) = 0 from hj]
    simp
  have diag j : inner ℝ (W j) (b j) = ‖W j‖^2 := by
    let S := (Submodule.span ℝ (Set.range (b ∘ Fin.castLE j.isLt.le)))ᗮ
    have h : W j = S.starProjection (b j) := rfl
    rw [← real_inner_self_eq_norm_sq, h]
    conv_rhs => rw [S.inner_starProjection_left_eq_right, S.starProjection_eq_self_iff.mpr
      (S.starProjection_apply_mem _)]
    rw [real_inner_comm]
  have orth (i j : Fin N) (hij : i < j) : inner ℝ (W j) (b i) = 0 := by
    let K := Submodule.span ℝ (Set.range (b ∘ Fin.castLE j.isLt.le))
    apply (Submodule.mem_orthogonal' _ _).mp (Kᗮ.starProjection_apply_mem (b j))
    exact Submodule.subset_span ⟨⟨i.val, hij⟩, rfl⟩
  simpa [sqW] using (affineThetaProfile (s := 1) one_pos b W pos diag orth 0).2

/-- The ambient integer Gaussian in (2) for any positive definite metric and unimodular basis. -/
theorem integerTheta_le_gramPivots (Q : Matrix (Fin N) (Fin N) ℝ) (hq : Q.PosDef)
    (U : Matrix (Fin N) (Fin N) ℤ) (hu : IsUnit U.det) :
    (∑' z : Fin N → ℤ, exp (-((fun j ↦ (z j : ℝ)) ⬝ᵥ (Q *ᵥ (fun j ↦ (z j : ℝ)))))) ≤
      ∏ j, thetaFactor (gramPivot Q U j) := by
  let M := U.map (Int.castRingHom ℝ)
  let := Q.toNormedAddCommGroup hq
  let := Q.toInnerProductSpace hq.posSemidef
  have hm : IsUnit M.det := by
    change IsUnit ((Int.castRingHom ℝ).mapMatrix U).det
    rw [← RingHom.map_det]
    exact hu.map _
  have gram : Matrix.gram ℝ M.col = Mᵀ * Q * M := by
    rw [Matrix.mul_assoc]
    ext i j
    change (Q *ᵥ M.col j) ⬝ᵥ star (M.col i) = _
    rw [star_trivial, dotProduct_comm]
    rfl
  have h := theta_le_gramPivots M.col
    (Matrix.linearIndependent_col_iff_isUnit.mpr (M.isUnit_iff_isUnit_det.mpr hm)) Q U gram
  let := (U.isUnit_iff_isUnit_det.mpr hu).invertible
  let e := U.toLinearEquiv' (inferInstance : Invertible U)
  rw [← e.toEquiv.tsum_eq]
  apply le_trans _ h
  apply le_of_eq
  apply tsum_congr
  intro z
  let v := ∑ j, (z j : ℝ) • M.col j
  have eq : (fun j ↦ (e z j : ℝ)) = v := by
    funext i
    change ((∑ j, U i j * z j : ℤ) : ℝ) = _
    simp [v, M, Finset.sum_apply, Matrix.col, mul_comm]
  change exp (-((fun j ↦ (e z j : ℝ)) ⬝ᵥ (Q *ᵥ (fun j ↦ (e z j : ℝ)))) ) = _
  rw [eq]
  have hnorm := @real_inner_self_eq_norm_sq _ (Q.toSeminormedAddCommGroup hq.posSemidef)
    (Q.toInnerProductSpace hq.posSemidef) v
  rw [← hnorm]
  change exp (-(v ⬝ᵥ (Q *ᵥ v))) = exp (-((Q *ᵥ v) ⬝ᵥ star v))
  rw [star_trivial, dotProduct_comm]

/-- Sum the secants of a convex function at logarithmic pivots. The mean log fixes
the total endpoint weights, including the equal-weight case of (5). -/
theorem sum_logPivot_secant (F : ℝ → ℝ) (p : Fin N → ℝ) {a b w : ℝ} (hab : a < b)
    (conv : ConvexOn ℝ (Set.Icc a b) F) (bounds : ∀ j, log (p j) ∈ Set.Icc a b)
    (mean : ∑ j, log (p j) = w*a + ((N : ℝ)-w)*b) :
    ∑ j, F (log (p j)) ≤ w*F a + ((N : ℝ)-w)*F b := by
  let x (j : Fin N) := (b - log (p j))/(b-a)
  have hba : 0 < b-a := sub_pos.mpr hab
  have point j : F (log (p j)) ≤ x j * F a + (1-x j) * F b := by
    have hx : 0 ≤ x j := div_nonneg (sub_nonneg.mpr (bounds j).2) hba.le
    have hx' : x j ≤ 1 := (div_le_one hba).2 (by linarith [(bounds j).1])
    have h := conv.2 (Set.left_mem_Icc.mpr hab.le) (Set.right_mem_Icc.mpr hab.le)
      hx (sub_nonneg.mpr hx') (show x j + (1-x j) = 1 by ring)
    have arg : x j * a + (1-x j) * b = log (p j) := by
      dsimp [x]; field_simp; ring
    simpa only [smul_eq_mul, arg] using h
  have sumx : ∑ j, x j = w := by
    simp only [x, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mean]
    field_simp
    ring
  have sy : ∑ j, (1-x j) = (N : ℝ)-w := by simp [Finset.sum_sub_distrib, sumx]
  apply (Finset.sum_le_sum fun j _ ↦ point j).trans_eq
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, sumx, sy]

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.gaussianMass_le_lowerProfile
#print axioms SigabaNeo.Wall1.theta_le_gramPivots
#print axioms SigabaNeo.Wall1.integerTheta_le_gramPivots
#print axioms SigabaNeo.Wall1.sum_logPivot_secant
