import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonFiveCertificate

/-! Sharp rank-five bound in the support-five half-coset. -/

noncomputable section
namespace SigabaNeo.Wall1.Watson

open Finset Submodule Module TerminalProjection MeasureTheory Five
open scoped RealInnerProductSpace

private theorem signed_form (q : ℝ) (t : Fin 10 → ℝ) (s : Fin 16) :
    ∑ i, ∑ j, signs s i * signs s j * mat (2*q) t i j = 8*q + 2*slack q t s := by
  fin_cases s <;>
    simp only [Fin.sum_univ_succ, mat, signs, slack, Matrix.of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_succ,
      Finset.univ_eq_empty, sum_empty, add_zero] <;> ring

/-- All five minimal vectors occur in the half-sum. The determinant bound is
stated for the Gram matrix of the five vectors before adjoining the half-sum. -/
theorem five_gram {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : Submodule ℤ V) (b : Fin 5 → V) (minimal : ∀ i, DecoupledDecoder.IsShortest L (b i))
    {x : V} (hx : x ∈ L) (out : x ∉ span ℤ (Set.range b)) (rel : ∑ i, b i = x + x) :
    ‖b 4‖^10 ≤ 2 * (Matrix.gram ℝ b).det := by
  classical
  let q := ‖b 4‖^2
  let t : Fin 10 → ℝ :=
    ![2*⟪b 0,b 1⟫, 2*⟪b 0,b 2⟫, 2*⟪b 0,b 3⟫, 2*⟪b 0,b 4⟫,
      2*⟪b 1,b 2⟫, 2*⟪b 1,b 3⟫, 2*⟪b 1,b 4⟫, 2*⟪b 2,b 3⟫, 2*⟪b 2,b 4⟫, 2*⟪b 3,b 4⟫]
  have lengths (i : Fin 5) : ‖b i‖^2 = q := by
    have h := le_antisymm ((minimal i).2.2 _ (minimal 4).1 (minimal 4).2.1)
      ((minimal 4).2.2 _ (minimal i).1 (minimal i).2.1)
    rw [h]
  have entries (i j : Fin 5) : 2 * ⟪b i, b j⟫ = mat (2*q) t i j := by
    by_cases hij : i = j
    · subst j
      rw [real_inner_self_eq_norm_sq, lengths]
      fin_cases i <;> rfl
    · fin_cases i <;> fin_cases j <;> first | rfl | exact (hij rfl).elim |
        exact congrArg (2 * ·) (real_inner_comm _ _)
  have hs (s : Fin 16) : 0 ≤ slack q t s := by
    let T := univ.filter fun i ↦ signs s i = -1
    let w := ∑ i ∈ T, b i
    let y := x - w
    have hw : w ∈ span ℤ (Set.range b) :=
      sum_mem (fun i _ ↦ subset_span (Set.mem_range_self i))
    have low : q ≤ ‖y‖^2 := pow_le_pow_left₀ (norm_nonneg _)
      ((minimal 4).2.2 y (L.sub_mem hx (L.sum_mem fun i _ ↦ (minimal i).1))
        (fun h ↦ out (sub_eq_zero.mp h ▸ hw))) 2
    have sign_cases (s : Fin 16) (i : Fin 5) : signs s i = 1 ∨ signs s i = -1 := by
      fin_cases s <;> fin_cases i <;> first | exact Or.inl rfl | exact Or.inr rfl
    have term (i : Fin 5) : signs s i • b i = b i -
        ((if i ∈ T then b i else 0) + (if i ∈ T then b i else 0)) := by
      rcases sign_cases s i with hi | hi <;> norm_num [T, hi]
    have total : ∑ i, signs s i • b i = y + y := by
      simp only [term, sum_sub_distrib, sum_add_distrib, sum_ite_mem, univ_inter, rel]
      dsimp [y, w]
      abel
    have eval : 2 * ⟪y+y,y+y⟫ =
        ∑ i, ∑ j, signs s i * signs s j * mat (2*q) t i j := by
      rw [← total]
      simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
        ← entries, mul_sum]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      rw [real_inner_comm (b j) (b i)]
      ring
    rw [signed_form, inner_add_left, inner_add_right, real_inner_self_eq_norm_sq] at eval
    linarith
  have bound := det_bound q t (sq_nonneg _) hs
  have same : mat (2*q) t = (2 : ℝ) • Matrix.gram ℝ b := by
    ext i j
    exact (entries i j).symm
  rw [same, Matrix.det_smul, Fintype.card_fin] at bound
  rw [show (10 : ℕ) = 2 * 5 by decide, pow_mul]
  change q^5 ≤ _
  linarith

/-- Sharp rank-five Hermite bound for a shortest basis with a support-five half-coset. -/
theorem five_covolume (L : Submodule ℤ (CoordSpace 5)) [DiscreteTopology L] [IsZLattice ℝ L]
    (B : Basis (Fin 5) ℝ (CoordSpace 5)) (minimal : ∀ i, DecoupledDecoder.IsShortest L (B i))
    {x : CoordSpace 5} (hx : x ∈ L) (out : x ∉ span ℤ (Set.range B))
    (rel : ∑ i, B i = x + x) : ‖B 4‖^10 ≤ 8 * ZLattice.covolume L ^ 2 := by
  let M := span ℤ (Set.range B)
  have sub : M ≤ L := span_le.mpr (Set.range_subset_iff.mpr fun i ↦ (minimal i).1)
  have h := five_gram L B minimal hx out rel
  rw [← covolume_span_sq_eq_gram] at h
  have hi := rank_five_minimal_index L B minimal
  have hr := ZLattice.covolume_div_covolume_eq_relIndex' M L sub
  have bound : ZLattice.covolume M / ZLattice.covolume L ≤ 2 := by
    rw [hr]
    exact_mod_cast hi
  have hvol := (div_le_iff₀ (ZLattice.covolume_pos L volume)).mp bound
  nlinarith only [h, pow_le_pow_left₀ (ZLattice.covolume_pos M volume).le hvol 2]

end SigabaNeo.Wall1.Watson

#print axioms SigabaNeo.Wall1.Watson.five_gram
#print axioms SigabaNeo.Wall1.Watson.five_covolume
