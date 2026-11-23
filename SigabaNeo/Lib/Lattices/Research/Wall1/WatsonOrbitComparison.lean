import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonHigherPolytope

/-! A finite family of normalized forms gives a global determinant bound when,
at each representative, comparison with its integral neighbors suffices to minimize
every linear functional on feasible tangent directions. -/

noncomputable section
namespace SigabaNeo.Wall1.Watson.HigherGram.Orbit

open Matrix Finset Module Submodule MeasureTheory TerminalProjection ControlledPlane DecoupledDecoder
open scoped MatrixOrder

variable {n : ℕ}
local notation "M" => Mat n
local notation "IntMat" => Matrix (Fin n) (Fin n) ℤ
def realMatrix : IntMat →+* M := (Int.castRingHom ℝ).mapMatrix

def pull (U : M) : M →ₗ[ℝ] M where
  toFun X := Uᴴ * X * U
  map_add' X Y := by simp [Matrix.mul_add,Matrix.add_mul]
  map_smul' c X := by simp

theorem pull_mul (A B X : M) : pull B (pull A X) = pull (A*B) X := by
  simp [pull,Matrix.mul_assoc]

theorem pull_one (X : M) : pull 1 X = X := by simp [pull]

theorem value_pull (U : IntMat) (X : M) (z : Fin n → ℤ) :
    value (pull (realMatrix U) X) z = value X (U *ᵥ z) := by
  have eq : (fun i ↦ ((U *ᵥ z) i : ℝ)) = realMatrix U *ᵥ fun i ↦ (z i : ℝ) :=
    funext ((Int.castRingHom ℝ).map_mulVec U z)
  simp only [value,pull,LinearMap.coe_mk,AddHom.coe_mk,Matrix.conjTranspose_eq_transpose_of_trivial,
    ← mulVec_mulVec,eq]
  rw [dotProduct_mulVec,vecMul_transpose]

private theorem finite_sublevel (X : M) (pos : X.PosDef) (V : M) (vunit : IsUnit V.det) (t : ℝ) :
    {U : IntMat | (pull V (pull (realMatrix U) X)).trace ≤ t}.Finite := by
  obtain ⟨A,hA⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp pos.posSemidef.nonneg
  have au : IsUnit A.det := isUnit_iff_ne_zero.mpr fun h ↦ by
    have nz := pos.det_pos.ne'
    simp [hA,det_mul,h] at nz
  let box := (Set.Icc (-(|t|+1)) (|t|+1)).matrix (m := Fin n) (n := Fin n)
  let undo (R : M) := A⁻¹ * R * V⁻¹
  have compact : IsCompact (undo '' box) := isCompact_Icc.matrix.image (by dsimp [undo]; fun_prop)
  have fin : (realMatrix ⁻¹' (undo '' box)).Finite :=
    isCompact_iff_finite.mp (Real.isClosedEmbedding_intCast.matrix_map.isCompact_preimage compact)
  apply fin.subset
  intro U hu
  let R := A * realMatrix U * V
  have tr : (Rᴴ * R).trace ≤ t := by
    simpa [R,pull,hA,Matrix.mul_assoc,star_eq_conjTranspose] using hu
  have hsq (i j : Fin n) : (R i j)^2 ≤ (Rᴴ * R).trace := by
    have e (j : Fin n) : (Rᴴ * R) j j = ∑ k, (R k j)^2 := by simp [Matrix.mul_apply,pow_two]
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

private theorem minimum {m : ℕ} [NeZero m] (representative : Fin m → M)
    (pos : ∀ k, (representative k).PosDef) (V : M) (vunit : IsUnit V.det) :
    ∃ (k : Fin m) (U : IntMat), IsUnit U ∧ ∀ (j : Fin m) (W : IntMat), IsUnit W →
      (pull V (pull (realMatrix U) (representative k))).trace ≤
      (pull V (pull (realMatrix W) (representative j))).trace := by
  classical
  let f (k : Fin m) (U : IntMat) := (pull V (pull (realMatrix U) (representative k))).trace
  have per (k : Fin m) : ∃ U, IsUnit U ∧ ∀ W, IsUnit W → f k U ≤ f k W := by
    let s := {U : IntMat | IsUnit U ∧ f k U ≤ f k 1}
    have fin : s.Finite := (finite_sublevel _ (pos k) V vunit _).subset
      fun _ h ↦ h.2
    obtain ⟨U,hU,best⟩ := Set.exists_min_image s (f k) fin ⟨1,isUnit_one,le_rfl⟩
    refine ⟨U,hU.1,fun W hw ↦ ?_⟩
    by_cases h : f k W ≤ f k 1
    · exact best W ⟨hw,h⟩
    · exact hU.2.trans (le_of_not_ge h)
  choose U unit best using per
  obtain ⟨k,_,hk⟩ := exists_min_image univ (fun k ↦ f k (U k)) univ_nonempty
  exact ⟨k,U k,unit k,fun j W hW ↦ (hk j (mem_univ j)).trans (best j W hW)⟩

/-- Minimize the whitened trace over all integral basis changes of a finite family. -/
theorem determinant_of_comparison {m : ℕ} [NeZero m] (representative : Fin m → M)
    (pos : ∀ k, (representative k).PosDef) {b : ℝ} (floor : ∀ k, b ≤ (representative k).det)
    (compare : ∀ k (D : M), D.IsHermitian →
      (∀ z : Fin n → ℤ, z ≠ 0 → value (representative k) z = 1 → 0 ≤ value D z) →
      ∀ f : M →ₗ[ℝ] ℝ, (∀ j (U : IntMat), IsUnit U →
        f (representative k) ≤ f (pull (realMatrix U) (representative j))) → 0 ≤ f D)
    (G : M) (pd : G.PosDef) (short : ∀ z : Fin n → ℤ, z ≠ 0 → 1 ≤ value G z) :
    b ≤ G.det := by
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
  obtain ⟨k,U,unit,best⟩ := minimum representative pos V vu
  obtain ⟨u,rfl⟩ := unit
  let W := realMatrix (u : IntMat)
  let T := realMatrix (↑u⁻¹ : IntMat)
  have TW : T * W = 1 := by simp [W,T,← map_mul]
  let X := representative k
  let Y := pull T G
  let f := ((traceLinearMap (Fin n) ℝ ℝ).comp (pull V)).comp (pull W)
  have ysym : Y.IsHermitian := (pd.posSemidef.conjTranspose_mul_mul_same T).1
  have h := compare k (Y-X) (ysym.sub (pos k).1) (fun z nz contact ↦ by
    have inj := mulVec_injective_of_isUnit (Units.isUnit u⁻¹)
    have nonzero : (↑u⁻¹ : IntMat) *ᵥ z ≠ 0 := fun he ↦ nz (inj (he.trans (mulVec_zero _).symm))
    have hval : value Y z = value G ((↑u⁻¹ : IntMat) *ᵥ z) := value_pull _ _ _
    simp only [value,sub_mulVec,dotProduct_sub] at *
    linarith only [short _ nonzero,contact,hval]) f (fun j W' hu ↦ by
    have h := best j (W' * (u : IntMat)) (hu.mul u.isUnit)
    simpa [f,W,pull_mul,map_mul,Matrix.mul_assoc,X] using h)
  rw [map_sub,sub_nonneg] at h
  have fY : f Y = (n : ℝ) := by simp [f,Y,pull_mul,TW,pull_one,white]
  let Z := pull V (pull W X)
  have posZ : Z.PosDef := ((pos k).conjTranspose_mul_mul_same
    (mulVec_injective_of_isUnit (u.isUnit.map realMatrix))).conjTranspose_mul_mul_same
      (mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det V).mpr vu))
  have trZ : Z.trace ≤ (n : ℝ) := h.trans_eq fY
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
  exact (floor k).trans (le_of_mul_le_mul_left detZ
    (mul_self_pos.mpr (isUnit_iff_ne_zero.mp vu)))

end SigabaNeo.Wall1.Watson.HigherGram.Orbit
