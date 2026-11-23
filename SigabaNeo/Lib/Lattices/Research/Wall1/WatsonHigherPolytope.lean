import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonNumeratorBox
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonGramVertices

/-! Reduction of the rank-six and rank-seven inequalities to the extreme points of compact
residue-code Gram polytopes. The index scales the determinant threshold quadratically. -/

noncomputable section
namespace SigabaNeo.Wall1.Watson.HigherGram

open Matrix Finset Submodule Module TerminalProjection DecoupledDecoder ControlledPlane MeasureTheory
open scoped MatrixOrder
variable {n : ℕ}

theorem trace_gt {A : Mat n} (hA : A.PosDef) (h : 1 < A.det) : (n : ℝ) < A.trace := by
  have logs := Real.log_pos h
  rw [hA.1.det_eq_prod_eigenvalues] at logs
  simp only [RCLike.ofReal_real_eq_id,id_eq] at logs
  rw [Real.log_prod (fun i _ ↦ (hA.eigenvalues_pos i).ne')] at logs
  have hh := sum_le_sum (s := univ) fun i _ ↦ Real.log_le_sub_one_of_pos (hA.eigenvalues_pos i)
  rw [sum_sub_distrib] at hh
  rw [hA.1.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id,id_eq,sum_const,card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one] at *
  linarith

/-- Convexity of the positive-definite determinant superlevel set. Whiten the candidate
convex combination to the identity. A larger determinant at both endpoints would force
both normalized traces above the dimension by the arithmetic-geometric mean inequality. -/
private theorem good_convex (threshold : ℝ) : Convex ℝ {A : Mat n | A.PosDef ∧ threshold ≤ A.det} := by
  intro A hA B hB a b ha hb hab
  obtain ha | ha := ha.eq_or_lt
  · subst a; simp_all
  obtain hb | hb := hb.eq_or_lt
  · subst b; simp_all
  let C := a • A + b • B
  have cp : C.PosDef := (hA.1.smul ha).add (hB.1.smul hb)
  refine ⟨cp,?_⟩
  change threshold ≤ C.det
  by_contra! bad
  obtain ⟨U,hu⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp cp.posSemidef.nonneg
  have uunit : IsUnit U.det := by
    have nz := cp.det_pos.ne'
    rw [hu,det_mul] at nz
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero_iff.mp nz).2
  let V := U⁻¹
  let F (X : Mat n) := Vᴴ * X * V
  have fv : F C = 1 := by
    have eq : U * V = 1 := U.mul_nonsing_inv uunit
    simp only [F,hu,star_eq_conjTranspose]
    rw [← Matrix.mul_assoc,← conjTranspose_mul,eq,conjTranspose_one,one_mul,eq]
  have hc : (V.det * V.det) * C.det = 1 := by
    simpa [F,det_mul,mul_assoc,mul_left_comm,mul_comm] using congrArg det fv
  have vpos : 0 < V.det * V.det := pos_of_mul_pos_left (hc.trans_gt zero_lt_one) cp.det_pos.le
  have tr (X : Mat n) (hx : X.PosDef ∧ threshold ≤ X.det) : (n : ℝ) < (F X).trace := by
    apply trace_gt
    · exact hx.1.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit
        ((Matrix.isUnit_iff_isUnit_det _).mpr (U.isUnit_nonsing_inv_det uunit)))
    · have lt : C.det < X.det := by linarith [hx.2]
      have h := mul_lt_mul_of_pos_left lt vpos
      rw [hc] at h
      simpa [F,det_mul,mul_comm,mul_left_comm,mul_assoc] using h
  have tf := congrArg Matrix.trace fv
  simp only [F,C,Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,trace_add,
    trace_smul,smul_eq_mul,trace_one,Fintype.card_fin] at tf
  nlinarith only [tf,hab,mul_lt_mul_of_pos_left (tr A hA) ha,mul_lt_mul_of_pos_left (tr B hB) hb]

theorem poly_compact {d K : ℕ} (C : Code n d) : IsCompact (polytope d K C) := by
  have closedH : IsClosed {A : Mat n | A.IsHermitian} :=
    isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have closedD : IsClosed {A : Mat n | ∀ i, A i i = 1} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_eq (continuous_id.matrix_elem i i) continuous_const
  have closedT : IsClosed {A : Mat n | ∀ z : Fin n → ℤ, z ≠ 0 → (∀ i, |z i| ≤ (K : ℤ)) →
      (fun i ↦ (z i : ZMod d)) ∈ C → (d : ℝ)^2 ≤ value A z} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun z ↦ isClosed_iInter fun _ ↦ isClosed_iInter fun _ ↦
      isClosed_iInter fun _ ↦ isClosed_le continuous_const ?_
    unfold value
    fun_prop
  exact (((isCompact_Icc.matrix.inter_right closedH).inter_right closedD).inter_right closedT)

theorem poly_convex {d K : ℕ} (C : Code n d) : Convex ℝ (polytope d K C) := by
  intro A hA B hB a b ha hb hab
  obtain ⟨⟨⟨aBox,aSym⟩,aDiag⟩,aTest⟩ := hA
  obtain ⟨⟨⟨bBox,bSym⟩,bDiag⟩,bTest⟩ := hB
  refine ⟨⟨⟨fun i j ↦ ?_,?_⟩,fun i ↦ ?_⟩,fun z hn ht hc ↦ ?_⟩
  · exact convex_Icc (-1:ℝ) 1 (aBox i j) (bBox i j) ha hb hab
  · exact (IsSelfAdjoint.smul (IsSelfAdjoint.of_nonneg ha) aSym).add
      (IsSelfAdjoint.smul (IsSelfAdjoint.of_nonneg hb) bSym)
  · simp [aDiag i,bDiag i,hab]
  · have eq : value (a • A + b • B) z = a*value A z + b*value B z := by
      simp [value,add_mulVec,smul_mulVec,dotProduct_add,dotProduct_smul]
    rw [eq]
    have hsum := congrArg (· * (d : ℝ)^2) hab
    nlinarith only [hsum,mul_le_mul_of_nonneg_left (aTest z hn ht hc) ha,
      mul_le_mul_of_nonneg_left (bTest z hn ht hc) hb]


/-- It suffices to establish positive definiteness and the scaled determinant threshold
on the extreme points of each residue-code polytope. -/
theorem bound_of_vertices {D : ℕ} {R : ℕ → ℕ} {p : ℝ} (hp : 0 < p)
    (vertices : ∀ d, 0 < d → d ≤ D → ∀ C : Code n d, Nat.card C = d →
      ∀ G ∈ (polytope d (R d) C).extremePoints ℝ, G.PosDef ∧ (d : ℝ)^2 ≤ p * G.det) :
    Bound n D R p := by
  let : LocallyConvexSpace ℝ (Mat n) := inferInstanceAs (LocallyConvexSpace ℝ (Fin n → Fin n → ℝ))
  intro d hd hD C hC
  let b := (d : ℝ)^2 / p
  have sub : (polytope d (R d) C).extremePoints ℝ ⊆ {G | G.PosDef ∧ b ≤ G.det} := by
    intro G hG
    obtain ⟨h,det⟩ := vertices d hd hD C hC G hG
    exact ⟨h,(div_le_iff₀ hp).mpr (mul_comm p G.det ▸ det)⟩
  have all : polytope d (R d) C ⊆ {G | b ≤ G.det} := by
    rw [← closure_convexHull_extremePoints (poly_compact C) (poly_convex C)]
    exact closure_minimal ((convexHull_min sub (good_convex b)).trans (fun _ h ↦ h.2))
      (isClosed_le continuous_const (by fun_prop))
  intro G hG
  simpa [mul_comm] using (div_le_iff₀ hp).mp (all hG)

theorem intrinsic_of_power [NeZero n] {p g : ℝ} (gp : 0 ≤ g) (pg : g ^ n = p)
    (hh : ∀ (L : Submodule ℤ (CoordSpace n)) [DiscreteTopology L] [IsZLattice ℝ L]
      (v : CoordSpace n), IsShortest L v → (‖v‖^2)^n ≤ p * ZLattice.covolume L^2) :
    IntrinsicHermite n g := by
  intro L _ _
  have hn : L ≠ ⊥ := by
    intro he
    have hs := IsZLattice.span_top (K:=ℝ) (L:=L)
    simp [he] at hs
  obtain ⟨v,hv,_⟩ := exists_orderedShortest L (fun _ ↦ (0:ℕ)) hn
  refine ⟨⟨v,hv.1⟩,fun h ↦ hv.2.1 (congrArg Subtype.val h),?_⟩
  have vl := (ZLattice.covolume_pos L volume).le
  apply le_of_pow_le_pow_left₀ (NeZero.ne n) (mul_nonneg gp (Real.rpow_nonneg vl _))
  change (‖v‖^2)^n ≤ (g * ZLattice.covolume L ^ (2/(n:ℝ)))^n
  rw [mul_pow,pg,← Real.rpow_mul_natCast vl,div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne n)),
    Real.rpow_two]
  exact hh L v hv

theorem intrinsic_six (cert : Bound 6 4 (6 * ·) (64/3)) : IntrinsicHermite 6 (flagGamma 6) := by
  apply intrinsic_of_power (g := flagGamma 6) (Real.exp_pos _).le (p := 64/3)
  · change Real.exp (Real.log (64/3) / 6) ^ 6 = (64/3 : ℝ)
    rw [← Real.exp_nat_mul]
    convert Real.exp_log (by norm_num : 0 < (64/3 : ℝ)) using 2
    ring
  · intro L _ _ v hv
    exact power_of_bound (by norm_num) rank_six_minimal_index cert L hv

theorem intrinsic_seven (cert : Bound 7 10 (11 * ·) 64) : IntrinsicHermite 7 (flagGamma 7) := by
  apply intrinsic_of_power (g := flagGamma 7) (Real.exp_pos _).le (p := 64)
  · change Real.exp (Real.log 64 / 7) ^ 7 = 64
    rw [← Real.exp_nat_mul]
    convert Real.exp_log (by norm_num : (0:ℝ) < 64) using 2
    ring
  · intro L _ _ v hv
    exact power_of_bound (by norm_num) rank_seven_minimal_index cert L hv

end SigabaNeo.Wall1.Watson.HigherGram

#print axioms SigabaNeo.Wall1.Watson.HigherGram.bound_of_vertices
#print axioms SigabaNeo.Wall1.Watson.HigherGram.intrinsic_six
#print axioms SigabaNeo.Wall1.Watson.HigherGram.intrinsic_seven
