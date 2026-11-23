import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonHigherPolytope

/-! Rank-six integral-basis representatives from the exact neighbor walk in
`docs/research/scripts/watson_perfect_neighbors.py`. Each matrix is divided by its squared
minimum. The rational upper-triangular factorizations certify all seven determinants. -/

noncomputable section
namespace SigabaNeo.Wall1.Watson.HigherGram.Six

open Matrix Finset ControlledPlane

private abbrev Q := Matrix (Fin 6) (Fin 6) ℚ
def forms : Fin 7 → Q :=
  ![!![1,1/2,1/2,1/2,1/2,1/2; 1/2,1,1/2,1/2,1/2,1/2; 1/2,1/2,1,1/2,1/2,1/2; 1/2,1/2,1/2,1,1/2,1/2; 1/2,1/2,1/2,1/2,1,1/2; 1/2,1/2,1/2,1/2,1/2,1],
    !![1,1/2,1/2,1/2,1/2,1/2; 1/2,1,0,1/2,1/2,1/2; 1/2,0,1,1/2,1/2,1/2; 1/2,1/2,1/2,1,1/2,1/2; 1/2,1/2,1/2,1/2,1,1/2; 1/2,1/2,1/2,1/2,1/2,1],
    !![1,1/2,1/4,1/4,1/4,1/4; 1/2,1,-1/4,1/2,1/2,1/2; 1/4,-1/4,1,1/4,1/4,1/4; 1/4,1/2,1/4,1,1/4,1/4; 1/4,1/2,1/4,1/4,1,1/4; 1/4,1/2,1/4,1/4,1/4,1],
    !![1,1/2,1/4,1/4,1/4,1/4; 1/2,1,-1/4,1/2,1/2,1/2; 1/4,-1/4,1,1/4,1/4,1/4; 1/4,1/2,1/4,1,1/4,1/4; 1/4,1/2,1/4,1/4,1,1/2; 1/4,1/2,1/4,1/4,1/2,1],
    !![1,1/2,1/4,1/4,1/4,1/4; 1/2,1,-1/4,1/2,1/2,1/2; 1/4,-1/4,1,1/4,1/4,1/4; 1/4,1/2,1/4,1,1/4,1/2; 1/4,1/2,1/4,1/4,1,1/2; 1/4,1/2,1/4,1/2,1/2,1],
    !![1,1/2,-1/2,-1/2,-1/2,1/2; 1/2,1,0,0,0,1/2; -1/2,0,1,0,0,0; -1/2,0,0,1,1/2,-1/2; -1/2,0,0,1/2,1,0; 1/2,1/2,0,-1/2,0,1],
    !![1,1/2,-1/2,-1/2,-1/2,1/4; 1/2,1,0,-1/4,-1/2,-1/4; -1/2,0,1,0,1/4,0; -1/2,-1/4,0,1,0,0; -1/2,-1/2,1/4,0,1,1/4; 1/4,-1/4,0,0,1/4,1]]

private def upper : Fin 7 → Q :=
  ![!![1,1/2,1/2,1/2,1/2,1/2; 0,1,1/3,1/3,1/3,1/3; 0,0,1,1/4,1/4,1/4; 0,0,0,1,1/5,1/5; 0,0,0,0,1,1/6; 0,0,0,0,0,1],
    !![1,1/2,1/2,1/2,1/2,1/2; 0,1,-1/3,1/3,1/3,1/3; 0,0,1,1/2,1/2,1/2; 0,0,0,1,0,0; 0,0,0,0,1,0; 0,0,0,0,0,1],
    !![1,1/2,1/4,1/4,1/4,1/4; 0,1,-1/2,1/2,1/2,1/2; 0,0,1,1/2,1/2,1/2; 0,0,0,1,-1/3,-1/3; 0,0,0,0,1,-1/2; 0,0,0,0,0,1],
    !![1,1/2,1/4,1/4,1/4,1/4; 0,1,-1/2,1/2,1/2,1/2; 0,0,1,1/2,1/2,1/2; 0,0,0,1,-1/3,-1/3; 0,0,0,0,1,0; 0,0,0,0,0,1],
    !![1,1/2,1/4,1/4,1/4,1/4; 0,1,-1/2,1/2,1/2,1/2; 0,0,1,1/2,1/2,1/2; 0,0,0,1,-1/3,1/9; 0,0,0,0,1,1/6; 0,0,0,0,0,1],
    !![1,1/2,-1/2,-1/2,-1/2,1/2; 0,1,1/3,1/3,1/3,1/3; 0,0,1,-1/2,-1/2,1/4; 0,0,0,1,0,-1/2; 0,0,0,0,1,1/2; 0,0,0,0,0,1],
    !![1,1/2,-1/2,-1/2,-1/2,1/4; 0,1,1/3,0,-1/3,-1/2; 0,0,1,-3/8,1/8,3/8; 0,0,0,1,-1/3,1/3; 0,0,0,0,1,1/2; 0,0,0,0,0,1]]

private def pivots : Fin 7 → (Fin 6 → ℚ) :=
  ![![1,3/4,2/3,5/8,3/5,7/12],
    ![1,3/4,2/3,1/2,1/2,1/2],
    ![1,3/4,3/4,9/16,1/2,3/8],
    ![1,3/4,3/4,9/16,1/2,1/2],
    ![1,3/4,3/4,9/16,1/2,13/24],
    ![1,3/4,2/3,1/2,1/2,3/8],
    ![1,3/4,2/3,21/32,7/12,7/16]]

def representative (k : Fin 7) : Mat 6 := (forms k).map (Rat.castHom ℝ)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
private theorem factor_entries : ∀ k i j,
    forms k i j = ((upper k)ᵀ * diagonal (pivots k) * upper k) i j := by
  intro k i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;> decide +kernel

private theorem upper_tri : ∀ k i j, j < i → upper k i j = 0 := by
  intro k i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;> decide +kernel
private theorem upper_diag : ∀ k i, upper k i i = 1 := by decide +kernel
private theorem piv_pos : ∀ k i, 0 < pivots k i := by decide +kernel

def detTable : Fin 7 → ℚ := ![7/64,1/16,243/4096,81/1024,351/4096,3/64,343/4096]

private theorem det_product : ∀ k, ∏ i, pivots k i = detTable k := by decide +kernel
private theorem det_floor : ∀ k, (3 : ℚ)/64 ≤ detTable k := by decide +kernel

/-- The seven candidate classes have the stated determinants and are positive definite. -/
theorem representative_bound (k : Fin 7) :
    (representative k).PosDef ∧ (representative k).det = (detTable k : ℝ) ∧
      (3 : ℝ)/64 ≤ (representative k).det := by
  let U := upper k
  have tri : U.IsUpperTriangular := fun i j hij ↦ upper_tri k _ _ hij
  have dU : U.det = 1 := by rw [det_of_isUpperTriangular tri]; simp [U,upper_diag]
  let V := U.map (Rat.castHom ℝ)
  have dv : V.det = 1 := by
    change ((Rat.castHom ℝ).mapMatrix U).det = _
    rw [← RingHom.map_det,dU,map_one]
  have eq : representative k = Vᴴ * diagonal (fun i ↦ (pivots k i : ℝ)) * V := by
    have h : forms k = Uᵀ * diagonal (pivots k) * U := Matrix.ext (factor_entries k)
    simp only [representative,h,Matrix.map_mul,diagonal_map (map_zero _)]
    rfl
  rw [eq]
  refine ⟨(posDef_diagonal_iff.mpr fun i ↦ (by exact_mod_cast piv_pos k i :
    0 < (pivots k i : ℝ))).conjTranspose_mul_mul_same
      (mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det V).mpr (dv ▸ isUnit_one))),?_⟩
  rw [det_mul,det_mul,det_conjTranspose,dv,star_one,one_mul,mul_one,det_diagonal]
  constructor
  · exact_mod_cast det_product k
  · have h := Rat.cast_le (K := ℝ) |>.mpr (det_floor k)
    rw [← det_product] at h
    push_cast at h
    linarith

/-- A marked shortest frame may have index d. Its determinant acquires exactly
the square of the change-of-frame determinant. -/
theorem marked_bound (k : Fin 7) (U : Mat 6) {d : ℕ} (hd : 0 < d) (hU : |U.det| = d) :
    (Uᴴ * representative k * U).PosDef ∧
      (d : ℝ)^2 ≤ 64/3 * (Uᴴ * representative k * U).det := by
  have dp : (0 : ℝ) < d := by exact_mod_cast hd
  have nz : U.det ≠ 0 := by intro h; simp [h] at hU; linarith
  obtain ⟨pos,_,det⟩ := representative_bound k
  refine ⟨pos.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det U).mpr (isUnit_iff_ne_zero.mpr nz))),?_⟩
  have sq : U.det^2 = (d : ℝ)^2 := by rw [← sq_abs,hU]
  rw [det_mul,det_mul,det_conjTranspose,star_trivial]
  calc
    (d : ℝ)^2 ≤ (64/3 * (representative k).det) * d^2 :=
      le_mul_of_one_le_left (sq_nonneg _) (by linarith)
    _ = _ := by rw [← sq]; ring

/-- The remaining rank-six coverage statement in the finite residue charts. -/
def Coverage : Prop :=
  ∀ d, 0 < d → d ≤ 4 → ∀ C : Code 6 d, Nat.card C = d →
    ∀ G ∈ (polytope d (6*d) C).extremePoints ℝ, ∃ (k : Fin 7) (U : Matrix (Fin 6) (Fin 6) ℤ),
      |U.det| = (d : ℤ) ∧
      G = (U.map (Int.castRingHom ℝ))ᴴ * representative k * U.map (Int.castRingHom ℝ)

theorem intrinsic_of_coverage (h : Coverage) : IntrinsicHermite 6 (flagGamma 6) := by
  apply intrinsic_six
  apply bound_of_vertices (by norm_num)
  intro d hd hi C hc G hG
  obtain ⟨k,U,idx,rfl⟩ := h d hd hi C hc G hG
  apply marked_bound k _ hd
  change |((Int.castRingHom ℝ).mapMatrix U).det| = _
  rw [← RingHom.map_det]
  change |(U.det : ℝ)| = (d : ℝ)
  exact_mod_cast idx

end SigabaNeo.Wall1.Watson.HigherGram.Six

#print axioms SigabaNeo.Wall1.Watson.HigherGram.Six.representative_bound
#print axioms SigabaNeo.Wall1.Watson.HigherGram.Six.marked_bound
#print axioms SigabaNeo.Wall1.Watson.HigherGram.Six.intrinsic_of_coverage
