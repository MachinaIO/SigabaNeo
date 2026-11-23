import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSixPivotWitnesses

/-! A local optimality criterion at the seven perfect-form candidates.
Minimize the trace after whitening the input matrix, over integral basis changes of the
candidates. Its sublevel sets are finite. At the winner, a complete list of tangent rays
would certify optimality against the input itself. -/

noncomputable section
namespace SigabaNeo.Wall1.Watson.HigherGram.Six

open Matrix Finset Module Submodule MeasureTheory TerminalProjection ControlledPlane DecoupledDecoder
open scoped MatrixOrder

local notation "M" => Mat 6
def realMatrix : IntMat →+* M := (Int.castRingHom ℝ).mapMatrix

def pull (U : M) : M →ₗ[ℝ] M where
  toFun X := Uᴴ * X * U
  map_add' X Y := by simp [Matrix.mul_add,Matrix.add_mul]
  map_smul' c X := by simp

theorem pull_mul (A B X : M) : pull B (pull A X) = pull (A*B) X := by
  simp [pull,Matrix.mul_assoc]

theorem pull_one (X : M) : pull 1 X = X := by simp [pull]

theorem value_pull (U : IntMat) (X : M) (z : Fin 6 → ℤ) :
    value (pull (realMatrix U) X) z = value X (U *ᵥ z) := by
  have eq : (fun i ↦ ((U *ᵥ z) i : ℝ)) = realMatrix U *ᵥ fun i ↦ (z i : ℝ) :=
    funext ((Int.castRingHom ℝ).map_mulVec U z)
  simp only [value,pull,LinearMap.coe_mk,AddHom.coe_mk,Matrix.conjTranspose_eq_transpose_of_trivial,
    ← mulVec_mulVec,eq]
  rw [dotProduct_mulVec,vecMul_transpose]

/-- Only the local tangent-cone spanning assertion is needed. All changes of basis in the
stabilizer are allowed; the 32 directions and their endpoints are given by `pivot`. -/
def RayCoverage : Prop :=
  ∀ (k : Fin 7) (D : M), D.IsHermitian →
    (∀ z : Fin 6 → ℤ, z ≠ 0 → value (representative k) z = 1 → 0 ≤ value D z) →
    ∀ f : M →ₗ[ℝ] ℝ,
      (∀ (j : Fin 32), (pivot j).src = k → ∀ S : IntMat, IsUnit S →
        pull (realMatrix S) (representative k) = representative k →
        0 ≤ f (pull (realMatrix S) (realMatrix (pivot j).direction))) → 0 ≤ f D

private theorem finite_sublevel (X : M) (pos : X.PosDef) (V : M) (vunit : IsUnit V.det) (t : ℝ) :
    {U : IntMat | (pull V (pull (realMatrix U) X)).trace ≤ t}.Finite := by
  obtain ⟨A,hA⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp pos.posSemidef.nonneg
  have au : IsUnit A.det := isUnit_iff_ne_zero.mpr fun h ↦ by
    have nz := pos.det_pos.ne'
    simp [hA,det_mul,h] at nz
  let box := (Set.Icc (-(|t|+1)) (|t|+1)).matrix (m := Fin 6) (n := Fin 6)
  let undo (R : M) := A⁻¹ * R * V⁻¹
  have compact : IsCompact (undo '' box) := isCompact_Icc.matrix.image (by dsimp [undo]; fun_prop)
  have fin : (realMatrix ⁻¹' (undo '' box)).Finite :=
    isCompact_iff_finite.mp (Real.isClosedEmbedding_intCast.matrix_map.isCompact_preimage compact)
  apply fin.subset
  intro U hu
  let R := A * realMatrix U * V
  have tr : (Rᴴ * R).trace ≤ t := by
    simpa [R,pull,hA,Matrix.mul_assoc,star_eq_conjTranspose] using hu
  have hsq (i j : Fin 6) : (R i j)^2 ≤ (Rᴴ * R).trace := by
    have e (j : Fin 6) : (Rᴴ * R) j j = ∑ k, (R k j)^2 := by simp [Matrix.mul_apply,pow_two]
    simp only [Matrix.trace,Matrix.diag_apply,e]
    exact (single_le_sum (f := fun k ↦ (R k j)^2) (fun k _ ↦ sq_nonneg _) (mem_univ i)).trans
      (single_le_sum (fun k _ ↦ sum_nonneg fun i _ ↦ sq_nonneg (R i k)) (mem_univ j))
  refine ⟨R,fun i j ↦ ?_,?_⟩
  · apply abs_le.mp
    by_contra! big
    have hh := pow_lt_pow_left₀ big (by positivity : 0 ≤ |t|+1) (by decide : 2 ≠ 0)
    rw [sq_abs] at hh
    nlinarith only [(hsq i j).trans tr,hh,le_abs_self t,sq_nonneg |t|,abs_nonneg t]
  · simp [undo,R,← Matrix.mul_assoc,Matrix.nonsing_inv_mul A au]
    rw [Matrix.mul_assoc,Matrix.mul_nonsing_inv V vunit,Matrix.mul_one]

private theorem minimum (V : M) (vunit : IsUnit V.det) :
    ∃ (k : Fin 7) (U : IntMat), IsUnit U ∧ ∀ (j : Fin 7) (W : IntMat), IsUnit W →
      (pull V (pull (realMatrix U) (representative k))).trace ≤
      (pull V (pull (realMatrix W) (representative j))).trace := by
  classical
  let f (k : Fin 7) (U : IntMat) := (pull V (pull (realMatrix U) (representative k))).trace
  have per (k : Fin 7) : ∃ U, IsUnit U ∧ ∀ W, IsUnit W → f k U ≤ f k W := by
    let s := {U : IntMat | IsUnit U ∧ f k U ≤ f k 1}
    have fin : s.Finite := (finite_sublevel _ (representative_bound k).1 V vunit _).subset
      fun _ h ↦ h.2
    obtain ⟨U,hU,best⟩ := Set.exists_min_image s (f k) fin ⟨1,isUnit_one,le_rfl⟩
    refine ⟨U,hU.1,fun W hw ↦ ?_⟩
    by_cases h : f k W ≤ f k 1
    · exact best W ⟨hw,h⟩
    · exact hU.2.trans (le_of_not_ge h)
  choose U unit best using per
  obtain ⟨k,_,hk⟩ := exists_min_image univ (fun k ↦ f k (U k)) univ_nonempty
  exact ⟨k,U k,unit k,fun j W hW ↦ (hk j (mem_univ j)).trans (best j W hW)⟩

private theorem real_pivot (j : Fin 32) :
    representative (pivot j).src + (((pivot j).quarters : ℝ)/4) • realMatrix (pivot j).direction =
      pull (realMatrix (pivot j).change) (representative (pivot j).dst) := by
  let castQ : Matrix (Fin 6) (Fin 6) ℚ →+* M := (Rat.castHom ℝ).mapMatrix
  have cast_int (A : IntMat) : castQ (qmat A) = realMatrix A := by
    ext i l
    simp [castQ,realMatrix,qmat]
  have cast_trans (A : IntMat) : castQ (qmat A)ᵀ = (realMatrix A)ᴴ := by
    rw [← cast_int,conjTranspose_eq_transpose_of_trivial]
    rfl
  have h := congrArg castQ (pivot_identity j).2.2
  simp only [map_add,map_mul,cast_trans,cast_int] at h
  change _ = (realMatrix (pivot j).change)ᴴ * _ * _
  rw [← show castQ (forms (pivot j).dst) = representative (pivot j).dst from rfl,← h]
  congr 1
  ext i l
  simp [castQ,qmat,realMatrix]

/-- The determinant bound for arbitrary minimum-one forms follows from local ray coverage
alone. Integral congruence classes are compared by a positive definite trace functional. -/
theorem determinant_of_rays (cover : RayCoverage) (G : M) (pd : G.PosDef)
    (short : ∀ z : Fin 6 → ℤ, z ≠ 0 → 1 ≤ value G z) : (3:ℝ)/64 ≤ G.det := by
  obtain ⟨A,hA⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp pd.posSemidef.nonneg
  have au : IsUnit A.det := isUnit_iff_ne_zero.mpr fun h ↦ by
    have nz := pd.det_pos.ne'
    simp [hA,det_mul,h] at nz
  let V := A⁻¹
  have vu : IsUnit V.det := A.isUnit_nonsing_inv_det au
  have white : pull V G = 1 := by
    change Vᴴ * G * V = 1
    rw [hA,star_eq_conjTranspose,← Matrix.mul_assoc,← conjTranspose_mul,Matrix.mul_nonsing_inv A au,
      conjTranspose_one,one_mul,Matrix.mul_nonsing_inv A au]
  obtain ⟨k,U,unit,best⟩ := minimum V vu
  obtain ⟨u,rfl⟩ := unit
  let W := realMatrix (u : IntMat)
  let T := realMatrix (↑u⁻¹ : IntMat)
  have TW : T * W = 1 := by simp [W,T,← map_mul]
  let X := representative k
  let Y := pull T G
  let f := ((traceLinearMap (Fin 6) ℝ ℝ).comp (pull V)).comp (pull W)
  have ysym : Y.IsHermitian := (pd.posSemidef.conjTranspose_mul_mul_same T).1
  have h := cover k (Y-X) (ysym.sub (representative_bound k).1.1) (fun z nz contact ↦ by
    have inj := mulVec_injective_of_isUnit (Units.isUnit u⁻¹)
    have nonzero : (↑u⁻¹ : IntMat) *ᵥ z ≠ 0 := fun he ↦ nz (inj (he.trans (mulVec_zero _).symm))
    have hval : value Y z = value G ((↑u⁻¹ : IntMat) *ᵥ z) := value_pull _ _ _
    simp only [value,sub_mulVec,dotProduct_sub] at *
    linarith only [short _ nonzero,contact,hval]) f (fun j hj S su hs ↦ by
    let w := pivot j
    have wu : IsUnit w.change := isUnit_iff_exists_inv.mpr ⟨w.inverse,(pivot_identity j).2.1⟩
    have bound := best w.dst (w.change * S * (u : IntMat)) ((wu.mul su).mul u.isUnit)
    have eq := congrArg (fun X ↦ f (pull (realMatrix S) X)) (real_pivot j)
    simp only [map_add,map_smul,smul_eq_mul,hj,hs] at eq
    have E : f (pull (realMatrix S) (pull (realMatrix w.change) (representative w.dst))) =
        (pull V (pull (realMatrix (w.change * S * (u : IntMat))) (representative w.dst))).trace := by
      simp [f,W,pull_mul,map_mul,Matrix.mul_assoc]
    rw [← E] at bound
    change f (representative k) ≤ _ at bound
    have positive : 0 < ((pivot j).quarters : ℝ) / 4 := by
      have : 0 < ((pivot j).quarters : ℝ) := by exact_mod_cast (pivot_identity j).1
      positivity
    exact nonneg_of_mul_nonneg_right (a := ((pivot j).quarters : ℝ)/4) (by linarith only [eq,bound])
      positive)
  rw [map_sub,sub_nonneg] at h
  have fY : f Y = 6 := by simp [f,Y,pull_mul,TW,pull_one,white]
  let Z := pull V (pull W X)
  have posZ : Z.PosDef := ((representative_bound k).1.conjTranspose_mul_mul_same
    (mulVec_injective_of_isUnit (u.isUnit.map realMatrix))).conjTranspose_mul_mul_same
      (mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det V).mpr vu))
  have trZ : Z.trace ≤ 6 := h.trans_eq fY
  have detZ : Z.det ≤ 1 := by
    by_contra! large
    exact trZ.not_gt (trace_gt posZ large)
  have identity : (V.det * V.det) * G.det = 1 := by
    simpa [pull,det_mul,mul_comm,mul_assoc,mul_left_comm] using congrArg det white
  have uw : (u : IntMat).det = 1 ∨ (u : IntMat).det = -1 :=
    Int.isUnit_iff.mp ((Matrix.isUnit_iff_isUnit_det _).mp u.isUnit)
  have sq : W.det * W.det = 1 := by
    change (realMatrix (u : IntMat)).det * (realMatrix (u : IntMat)).det = 1
    simp only [realMatrix,← RingHom.map_det]
    rcases uw with hu | hu <;> simp [hu]
  have zz : Z.det = (V.det * V.det) * X.det := by
    simp only [Z,pull,LinearMap.coe_mk,AddHom.coe_mk,det_mul,det_conjTranspose,star_trivial]
    linear_combination V.det^2 * X.det * sq
  rw [zz,← identity] at detZ
  exact (representative_bound k).2.2.trans (le_of_mul_le_mul_left detZ
    (mul_self_pos.mpr (isUnit_iff_ne_zero.mp vu)))

/-- The intrinsic rank-six inequality with only the finite cone-span certificate pending. -/
theorem intrinsic_of_rays (cover : RayCoverage) : IntrinsicHermite 6 (flagGamma 6) := by
  apply intrinsic_of_power (g := flagGamma 6) (Real.exp_pos _).le (p := 64/3)
  · change Real.exp (Real.log (64/3) / 6) ^ 6 = (64/3 : ℝ)
    rw [← Real.exp_nat_mul]
    convert Real.exp_log (by norm_num : 0 < (64/3 : ℝ)) using 2
    ring
  intro L _ _ v hv
  have rk : finrank ℤ L = 6 := (ZLattice.rank ℝ L).trans (by simp [CoordSpace])
  let B := ((finBasis ℤ L).reindex (finCongr rk)).ofZLatticeBasis ℝ L
  have spanB : span ℤ (Set.range B) = L := Basis.ofZLatticeBasis_span _ _ _
  let q := ‖v‖^2
  have qp : 0 < q := sq_pos_of_pos (norm_pos_iff.mpr hv.2.1)
  have h := determinant_of_rays cover (q⁻¹ • gram ℝ B)
    ((posDef_gram_of_linearIndependent B.linearIndependent).smul (inv_pos.mpr qp)) (fun z hz ↦ by
      have mem : vec B z ∈ L := spanB ▸ ((mem_span_range_iff_exists_fun ℤ).mpr
        ⟨z,by simp only [vec,Int.cast_smul_eq_zsmul ℝ]⟩)
      have nz : vec B z ≠ 0 := by
        intro he
        apply hz
        funext i
        have eq := coord B z i
        simpa [he] using eq.symm
      have le := pow_le_pow_left₀ (norm_nonneg _) (hv.2.2 _ mem nz) 2
      have e : value (q⁻¹ • gram ℝ B) z = q⁻¹ * value (gram ℝ B) z := by
        simp [value,smul_mulVec,dotProduct_smul]
      rwa [e,energy,← div_eq_inv_mul,le_div_iff₀ qp,one_mul])
  rw [det_smul,Fintype.card_fin,inv_pow,← covolume_span_sq_eq_gram,spanB] at h
  field_simp [qp.ne'] at h
  change q^6 ≤ _
  linarith

end SigabaNeo.Wall1.Watson.HigherGram.Six

#print axioms SigabaNeo.Wall1.Watson.HigherGram.Six.determinant_of_rays

#print axioms SigabaNeo.Wall1.Watson.HigherGram.Six.intrinsic_of_rays
