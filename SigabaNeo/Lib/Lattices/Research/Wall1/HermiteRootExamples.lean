import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonMinimalFamily

/-! Equality examples for the proposed Hermite bounds in dimensions five through seven.
The first five, six and seven simple roots of E₇ give D₅, E₆ and E₇, respectively. -/

noncomputable section
namespace SigabaNeo.Wall1.Watson

open Matrix Finset Module Submodule TerminalProjection MeasureTheory
open scoped RealInnerProductSpace

private def simple (i : Fin 7) : CoordSpace 8 :=
  WithLp.toLp 2 (![
    ![1/2,-1/2,-1/2,-1/2,-1/2,-1/2,-1/2,1/2],
    ![1,1,0,0,0,0,0,0], ![-1,1,0,0,0,0,0,0], ![0,-1,1,0,0,0,0,0],
    ![0,0,-1,1,0,0,0,0], ![0,0,0,-1,1,0,0,0], ![0,0,0,0,-1,1,0,0]] i)

private theorem simple_inner (i j : Fin 7) : ⟪simple i,simple j⟫ = (CartanMatrix.E 7 i j : ℝ) := by
  rw [CartanMatrix.E_seven_eq, PiLp.inner_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [simple, Fin.sum_univ_succ, Matrix.cons_val, of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ']

private theorem even_norm {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {k : ℕ} (b : Fin k → V) (A : Matrix (Fin k) (Fin k) ℤ)
    (gram : ∀ i j, ⟪b i,b j⟫ = (A i j : ℝ)) (lengths : ∀ i, ‖b i‖^2 = 2)
    (a : Fin k → ℤ) (s : Finset (Fin k)) : ∃ z : ℤ, ‖∑ i ∈ s, a i • b i‖^2 = 2*z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨z,hz⟩ := ih
    refine ⟨(a i)^2 + a i * (∑ j ∈ s, a j * A i j) + z, ?_⟩
    rw [sum_insert hi,norm_add_sq_real,hz,← Int.cast_smul_eq_zsmul ℝ,norm_smul,
      Real.norm_eq_abs,mul_pow,sq_abs,lengths,real_inner_smul_left,inner_sum]
    simp only [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, gram, Int.cast_add, Int.cast_pow,
      Int.cast_mul, Int.cast_sum]
    ring

/-- Intrinsic full-rank lattices attaining squared minimum 2 and squared covolume
9 − k for each k ∈ {5,6,7}. The integer span is that of the exhibited real basis. -/
theorem root_examples (k : ℕ) (lo : 5 ≤ k) (hi : k ≤ 7) :
    ∃ B : Basis (Fin k) ℝ (CoordSpace k),
      (∀ i, DecoupledDecoder.IsShortest (span ℤ (Set.range B)) (B i) ∧ ‖B i‖^2 = 2) ∧
      ZLattice.covolume (span ℤ (Set.range B))^2 = 9 - (k : ℝ) := by
  let v (i : Fin k) := simple (i.castLE hi)
  have eq (i j : Fin k) : ⟪v i,v j⟫ = (CartanMatrix.E k i j : ℝ) := by
    rw [show ⟪v i,v j⟫ = _ from simple_inner _ _]
    simp only [CartanMatrix.E, of_apply, Fin.castLE_inj, Fin.val_castLE]
  have G : Matrix.gram ℝ v = (CartanMatrix.E k).map (fun x ↦ (x : ℝ)) := by
    ext i j
    exact eq i j
  have hd : (Matrix.gram ℝ v).det = 9 - (k : ℝ) := by
    rw [G, ← Int.cast_det,CartanMatrix.E_det (by omega)]
    push_cast
    rfl
  have ind := Matrix.linearIndependent_of_det_gram_ne_zero (𝕜 := ℝ)
    (v := v) (by rw [hd]; exact sub_ne_zero.mpr (by exact_mod_cast (show 9 ≠ k by omega)))
  let C := Basis.span ind
  let e := ChainState.coord ((finrank_eq_card_basis C).trans (Fintype.card_fin k))
  let B := C.map e.toLinearEquiv
  have gb (i j : Fin k) : ⟪B i,B j⟫ = (CartanMatrix.E k i j : ℝ) := by
    simpa [B,C] using eq i j
  have len (i : Fin k) : ‖B i‖^2 = 2 := by
    rw [← real_inner_self_eq_norm_sq, gb, CartanMatrix.E_diag]
    norm_num
  refine ⟨B,fun i ↦ ⟨⟨subset_span (Set.mem_range_self i),B.ne_zero i,?_⟩, len i⟩,?_⟩
  · intro t ht hn
    obtain ⟨a,rfl⟩ := (mem_span_range_iff_exists_fun ℤ).mp ht
    obtain ⟨z,hz⟩ := even_norm B _ gb len a univ
    have hpos := sq_pos_of_pos (norm_pos_iff.mpr hn)
    have hp : 0 < (z : ℝ) := by linarith
    have hone : (1 : ℝ) ≤ z := by exact_mod_cast (show 1 ≤ z by exact_mod_cast hp)
    exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) (by linarith only [len i,hz,hone])
  · rw [covolume_span_sq_eq_gram, ← hd]
    congr 1
    ext i j
    exact (gb i j).trans (eq i j).symm

/-- Any uniform Hermite constant must reach the ratios of the root examples. -/
theorem necessary_hermite (k : ℕ) (lo : 5 ≤ k) (hi : k ≤ 7) {g : ℝ}
    (h : ControlledPlane.IntrinsicHermite k g) : (2 : ℝ)^k ≤ g^k * (9-k) := by
  obtain ⟨B,short,vol⟩ := root_examples k lo hi
  let M := span ℤ (Set.range B)
  obtain ⟨w,hn,hw⟩ := h M
  obtain ⟨hmin,hlen⟩ := short ⟨0,by omega⟩
  have hshort := hmin.2.2 w w.property (fun eq ↦ hn (Subtype.ext eq))
  have hrad := (pow_le_pow_left₀ (norm_nonneg _) hshort 2).trans hw
  rw [hlen] at hrad
  have H := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hrad k
  rw [mul_pow,← Real.rpow_mul_natCast (ZLattice.covolume_pos M volume).le,
    div_mul_cancel₀ _ (by exact_mod_cast (show k ≠ 0 by omega)),Real.rpow_two] at H
  exact vol ▸ H

end SigabaNeo.Wall1.Watson

#print axioms SigabaNeo.Wall1.Watson.root_examples
#print axioms SigabaNeo.Wall1.Watson.necessary_hermite
