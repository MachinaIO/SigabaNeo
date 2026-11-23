import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonFiniteGram
import Mathlib.Analysis.Convex.KreinMilman

/-! A vertex certificate for the normalized rank-five Gram polytope.

The accompanying exact rational edge walk supplies 24 signed-permutation representatives.
The determinant and positive definiteness tests below are independent of that calculation.
Its completeness is the open proposition `VertexCoverage`. -/

noncomputable section
namespace SigabaNeo.Wall1.Watson

open Matrix Finset
open scoped MatrixOrder
local notation "I" => Fin 5
local notation "Mat" => Matrix I I ℝ

/-- Off-diagonal entries of the candidate orbit representatives, multiplied by four. -/
def vertexEdges : Fin 24 → Fin 10 → ℝ :=
  ![![2,2,2,2,2,2,2,2,2,2],
    ![2,2,2,2,2,2,2,2,2,0],
    ![2,2,2,2,2,2,2,2,0,0],
    ![2,2,2,2,0,2,2,0,2,0],
    ![2,0,2,2,0,2,2,0,2,0],
    ![2,2,0,2,2,0,2,2,0,-2],
    ![2,2,2,0,2,2,0,2,0,-2],
    ![2,2,0,2,0,0,2,0,2,-2],
    ![2,2,2,0,0,2,0,0,2,-2],
    ![2,2,1,2,1,2,1,2,1,-1],
    ![2,0,0,2,0,0,2,0,2,-2],
    ![2,0,2,0,0,2,0,0,2,-2],
    ![2,0,0,2,0,2,0,0,2,-2],
    ![0,0,2,0,0,0,2,0,2,-2],
    ![1,1,2,2,1,2,2,2,2,1],
    ![1,1,1,2,1,1,2,1,2,-1],
    ![2,2,2,1,1,1,2,1,-1,-1],
    ![0,0,2,2,2,0,2,2,0,0],
    ![0,0,2,2,2,0,2,0,0,0],
    ![1,1,1,2,1,1,2,1,-1,-1],
    ![2,2,2,2,0,2,0,0,2,0],
    ![2,2,2,0,0,2,2,0,0,0],
    ![1,2,1,1,-1,1,1,-1,2,-2],
    ![2,1,1,2,-1,2,1,-2,2,-1]]

/-- Unit-diagonal representatives indexed in the same order as vertexEdges. -/
def gramVertex (k : Fin 24) : Mat := (1/4 : ℝ) • Five.mat 4 (vertexEdges k)

set_option maxHeartbeats 8000000 in
private theorem shift_bound (k : Fin 24) (t : ℝ) (ht : 0 ≤ t) :
    128 ≤ (Five.mat (4+t) (vertexEdges k)).det := by
  apply sub_nonneg.mp
  simp only [Five.mat, det_succ_row_zero, Fin.sum_univ_succ, submatrix_apply, det_isEmpty,
    univ_eq_empty, sum_empty, Fin.succAbove_zero, Fin.succ_succAbove_zero, Fin.succ_succAbove_succ,
    cons_val_zero, cons_val_succ, of_apply, Fin.val_succ, Fin.val_zero, pow_zero,
    one_mul, zero_add, add_zero]
  fin_cases k <;>
    norm_num [vertexEdges, Matrix.cons_val, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    ring_nf <;> nlinarith only [ht,sq_nonneg t,pow_nonneg ht 3,pow_nonneg ht 4,pow_nonneg ht 5]

/-- The kernel checks both definiteness and determinant for every listed representative. -/
theorem gramVertex_bound (k : Fin 24) : (gramVertex k).PosDef ∧ 1 ≤ 8 * (gramVertex k).det := by
  let A := Five.mat 4 (vertexEdges k)
  have sym : A.IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have plus (t : ℝ) : A + t • (1 : Mat) = Five.mat (4+t) (vertexEdges k) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A,Five.mat, Matrix.of_apply, Matrix.cons_val]
  have pd : A.PosDef := by
    apply sym.posDef_iff_eigenvalues_pos.mpr
    intro i
    by_contra! h
    let l := sym.eigenvalues i
    have mem := sym.eigenvalues_mem_spectrum_real i
    have non : ¬ IsUnit (l • (1 : Mat) - A) := by
      simpa [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one] using mem
    have hi := shift_bound k (-l) (neg_nonneg.mpr h)
    rw [← plus] at hi
    apply non
    have eq : l • (1 : Mat) - A = -(A + -l • (1 : Mat)) := by rw [neg_smul]; abel
    rw [eq]
    exact ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (by linarith))).neg
  have hd : 128 ≤ A.det := by simpa [A] using shift_bound k 0 (by norm_num)
  refine ⟨pd.smul (by norm_num : 0 < (1/4 : ℝ)),?_⟩
  simp only [gramVertex,det_smul,Fintype.card_fin]
  change _ ≤ 8 * ((1/4 : ℝ)^5 * A.det)
  linarith

private theorem trace_gt {A : Mat} (hA : A.PosDef) (h : 1 < A.det) : 5 < A.trace := by
  have logs := Real.log_pos h
  rw [hA.1.det_eq_prod_eigenvalues] at logs
  simp only [RCLike.ofReal_real_eq_id,id_eq] at logs
  rw [Real.log_prod (fun i _ ↦ (hA.eigenvalues_pos i).ne')] at logs
  have hh := sum_le_sum (s := univ) fun i _ ↦ Real.log_le_sub_one_of_pos (hA.eigenvalues_pos i)
  rw [sum_sub_distrib] at hh
  rw [hA.1.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id,id_eq,sum_const,card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_ofNat,mul_one] at *
  linarith

/-- Convexity of the positive-definite determinant superlevel set. Whiten the candidate
convex combination to the identity. A larger determinant at both endpoints would force
both normalized traces above five by the arithmetic-geometric mean inequality. -/
private theorem good_convex : Convex ℝ {A : Mat | A.PosDef ∧ 1 ≤ 8*A.det} := by
  intro A hA B hB a b ha hb hab
  obtain ha | ha := ha.eq_or_lt
  · subst a; simp_all
  obtain hb | hb := hb.eq_or_lt
  · subst b; simp_all
  let C := a • A + b • B
  have cp : C.PosDef := (hA.1.smul ha).add (hB.1.smul hb)
  refine ⟨cp,?_⟩
  change 1 ≤ 8*C.det
  by_contra! bad
  obtain ⟨U,hu⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp cp.posSemidef.nonneg
  have uunit : IsUnit U.det := by
    have nz := cp.det_pos.ne'
    rw [hu,det_mul] at nz
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero_iff.mp nz).2
  let V := U⁻¹
  let F (X : Mat) := Vᴴ * X * V
  have fv : F C = 1 := by
    have eq : U * V = 1 := U.mul_nonsing_inv uunit
    simp only [F,hu,star_eq_conjTranspose]
    rw [← Matrix.mul_assoc,← conjTranspose_mul,eq,conjTranspose_one,one_mul,eq]
  have hc : (V.det * V.det) * C.det = 1 := by
    simpa [F,det_mul,mul_assoc,mul_left_comm,mul_comm] using congrArg det fv
  have vpos : 0 < V.det * V.det := pos_of_mul_pos_left (hc.trans_gt zero_lt_one) cp.det_pos.le
  have tr (X : Mat) (hx : X.PosDef ∧ 1 ≤ 8*X.det) : 5 < (F X).trace := by
    apply trace_gt
    · exact hx.1.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit
        ((Matrix.isUnit_iff_isUnit_det _).mpr (U.isUnit_nonsing_inv_det uunit)))
    · have lt : C.det < X.det := by linarith [hx.2]
      have h := mul_lt_mul_of_pos_left lt vpos
      rw [hc] at h
      simpa [F,det_mul,mul_comm,mul_left_comm,mul_assoc] using h
  have tf := congrArg Matrix.trace fv
  simp only [F,C,Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,trace_add,
    trace_smul,smul_eq_mul,trace_one,Fintype.card_fin,Nat.cast_ofNat] at tf
  nlinarith only [tf,hab,mul_lt_mul_of_pos_left (tr A hA) ha,mul_lt_mul_of_pos_left (tr B hB) hb]

/-- The normalized Gram polytope in symmetric coordinates. The entry box is redundant
for Gram matrices of unit vectors and makes compactness immediate. -/
def gramPolytope : Set Mat :=
  (Set.Icc (-1:ℝ) 1).matrix ∩ {A | A.IsHermitian} ∩ {A | ∀ i, A i i = 1} ∩
    {A | ∀ z : I → ℤ, z ≠ 0 → GramTest z → 1 ≤ gramValue A z}

private theorem poly_compact : IsCompact gramPolytope := by
  have closedH : IsClosed {A : Mat | A.IsHermitian} :=
    isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have closedD : IsClosed {A : Mat | ∀ i, A i i = 1} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_eq (continuous_id.matrix_elem i i) continuous_const
  have closedT : IsClosed {A : Mat | ∀ z : I → ℤ, z ≠ 0 → GramTest z → 1 ≤ gramValue A z} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun z ↦ isClosed_iInter fun _ ↦ isClosed_iInter fun _ ↦
      isClosed_le continuous_const ?_
    unfold gramValue
    fun_prop
  exact (((isCompact_Icc.matrix.inter_right closedH).inter_right closedD).inter_right closedT)

private theorem poly_convex : Convex ℝ gramPolytope := by
  intro A hA B hB a b ha hb hab
  obtain ⟨⟨⟨aBox,aSym⟩,aDiag⟩,aTest⟩ := hA
  obtain ⟨⟨⟨bBox,bSym⟩,bDiag⟩,bTest⟩ := hB
  refine ⟨⟨⟨fun i j ↦ ?_,?_⟩,fun i ↦ ?_⟩,fun z hn ht ↦ ?_⟩
  · exact convex_Icc (-1:ℝ) 1 (aBox i j) (bBox i j) ha hb hab
  · exact (IsSelfAdjoint.smul (IsSelfAdjoint.of_nonneg ha) aSym).add
      (IsSelfAdjoint.smul (IsSelfAdjoint.of_nonneg hb) bSym)
  · simp [aDiag i,bDiag i,hab]
  · have eq : gramValue (a • A + b • B) z = a*gramValue A z + b*gramValue B z := by
      simp [gramValue,add_mulVec,smul_mulVec,dotProduct_add,dotProduct_smul]
    rw [eq]
    linarith [mul_le_mul_of_nonneg_left (aTest z hn ht) ha,
      mul_le_mul_of_nonneg_left (bTest z hn ht) hb]

/-- The remaining enumeration statement: every extreme point is a signed permutation
of one of the 24 displayed matrices. -/
def VertexCoverage : Prop :=
  ∀ A ∈ gramPolytope.extremePoints ℝ, ∃ (k : Fin 24) (e : Equiv.Perm I) (s : I → ℝ),
    (∀ i, |s i| = 1) ∧ A = (diagonal s)ᴴ * (gramVertex k).submatrix e e * diagonal s

/-- Orbit coverage discharges the entire real determinant criterion. -/
theorem finite_gram_of_vertex_coverage (cover : VertexCoverage) : FiniteGramBound := by
  let : LocallyConvexSpace ℝ Mat := inferInstanceAs (LocallyConvexSpace ℝ (I → I → ℝ))
  let S := {A : Mat | A.PosDef ∧ 1 ≤ 8*A.det}
  have vertices : gramPolytope.extremePoints ℝ ⊆ S := by
    intro A hA
    obtain ⟨k,e,s,hs,rfl⟩ := cover A hA
    have hprod : |(diagonal s).det| = 1 := by simp [det_diagonal,Finset.abs_prod,hs]
    have hunit : IsUnit (diagonal s) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr
      (by intro h; simp [h] at hprod))
    obtain ⟨pd,det⟩ := gramVertex_bound k
    refine ⟨(pd.submatrix e.injective).conjTranspose_mul_mul_same (mulVec_injective_of_isUnit hunit),?_⟩
    rw [det_mul,det_mul,det_conjTranspose,star_trivial,det_submatrix_equiv_self]
    have hsquare : (diagonal s).det^2 = 1 := by rw [← sq_abs,hprod]; norm_num
    nlinarith only [det,congrArg (· * (gramVertex k).det) hsquare]
  have cov : gramPolytope ⊆ {A : Mat | 1 ≤ 8 * A.det} := by
    rw [← closure_convexHull_extremePoints poly_compact poly_convex]
    exact closure_minimal ((convexHull_min vertices good_convex).trans (fun _ h ↦ h.2))
      (isClosed_le continuous_const (by fun_prop))
  intro G pd diag tests
  apply cov
  refine ⟨⟨⟨?_,pd.1⟩,diag⟩,tests⟩
  obtain ⟨B,hB⟩ := basis_with_gram G pd
  have unit (i : I) : ‖B i‖ = 1 := by
    have hh := diag i
    rw [← hB,gram_apply,real_inner_self_eq_norm_sq] at hh
    nlinarith [norm_nonneg (B i)]
  intro i j
  rw [← hB]
  exact abs_le.mp (by simpa [gram_apply,unit] using abs_real_inner_le_norm (B i) (B j))

open ControlledPlane TerminalProjection TerminalProjection.Restart506 DualExit
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

/-- Suffix descent with the rank-five hypothesis reduced to vertex enumeration. -/
theorem terminal_bound_of_vertex_coverage (cover : VertexCoverage)
    (h6 : IntrinsicHermite 6 (flagGamma 6)) (h7 : IntrinsicHermite 7 (flagGamma 7))
    (h24 : IntrinsicHermite 24 4) :
    probability terminalHit < probability residual₁ + probability residual₂ + 6.515/(10:ℝ)^12 :=
  terminal_bound_of_finite_gram (finite_gram_of_vertex_coverage cover) h6 h7 h24

end SigabaNeo.Wall1.Watson

#print axioms SigabaNeo.Wall1.Watson.gramVertex_bound
#print axioms SigabaNeo.Wall1.Watson.finite_gram_of_vertex_coverage
#print axioms SigabaNeo.Wall1.Watson.terminal_bound_of_vertex_coverage
