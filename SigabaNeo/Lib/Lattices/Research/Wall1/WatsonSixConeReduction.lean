import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonOrbitComparison
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
  apply Orbit.determinant_of_comparison representative (fun k ↦ (representative_bound k).1)
    (fun k ↦ (representative_bound k).2.2) _ G pd short
  intro k D sym admissible f best
  apply cover k D sym admissible f
  intro j hj S su hs
  let w := pivot j
  have wu : IsUnit w.change := isUnit_iff_exists_inv.mpr ⟨w.inverse,(pivot_identity j).2.1⟩
  have h := best w.dst (w.change * S) (wu.mul su)
  have e := congrArg (fun X ↦ f (pull (realMatrix S) X)) (real_pivot j)
  simp only [map_add,map_smul,smul_eq_mul,hj,hs,pull_mul,← map_mul] at e
  change f (representative k) ≤ f (pull (realMatrix (w.change * S)) (representative w.dst)) at h
  have hp : 0 < ((pivot j).quarters : ℝ) := by exact_mod_cast (pivot_identity j).1
  exact nonneg_of_mul_nonneg_right (a := ((pivot j).quarters : ℝ)/4)
    (by linarith only [e,h]) (by positivity)

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
