import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonMinimalFamily

/-! The support-four half-coset in Watson's rank-five index argument. -/

noncomputable section
namespace SigabaNeo.Wall1.Watson

open Finset Submodule Module TerminalProjection MeasureTheory
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Equality in Watson's argument for four coefficients of magnitude one.
All four neighbors of the half-sum attain the common minimum. -/
private theorem neighbors {v : Fin 4 → V} {x : V} {q : ℝ}
    (rel : ∑ i, v i = x + x) (lengths : ∀ i, ‖v i‖^2 = q)
    (lower : ∀ i, q ≤ ‖x - v i‖^2) : ∀ i, ‖x - v i‖^2 = q := by
  have hsum : ∑ i, ⟪x, v i⟫ = 2 * ‖x‖^2 := by
    rw [← inner_sum, rel, inner_add_right, real_inner_self_eq_norm_sq]
    ring
  have total : ∑ i, (‖x - v i‖^2 - q) = 0 := by
    simp only [norm_sub_sq_real, lengths, add_sub_cancel_right, sum_sub_distrib,
      sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum, hsum]
    ring
  intro i
  exact sub_eq_zero.mp ((sum_eq_zero_iff_of_nonneg
    (fun j _ ↦ sub_nonneg.mpr (lower j))).mp total i (mem_univ _))

private def flip (s : Finset (Fin 4)) (v : Fin 4 → V) (i : Fin 4) : V :=
  if i ∈ s then -v i else v i

omit [InnerProductSpace ℝ V] in
private theorem flip_sum (s : Finset (Fin 4)) (v : Fin 4 → V) :
    ∑ i, flip s v i = ∑ i, v i - ((∑ i ∈ s, v i) + ∑ i ∈ s, v i) := by
  classical
  have h (i : Fin 4) : flip s v i = v i - ((if i ∈ s then v i else 0) +
      (if i ∈ s then v i else 0)) := by by_cases hi : i ∈ s <;> simp [flip, hi]
  simp [h, sum_sub_distrib, sum_add_distrib, sum_ite_mem]

/-- All signed half-sums are shortest and the four support vectors are orthogonal. -/
theorem four_geometry (v : Fin 4 → V) (x : V) (q : ℝ)
    (rel : ∑ i, v i = x + x) (lengths : ∀ i, ‖v i‖^2 = q)
    (lower : ∀ s : Finset (Fin 4), q ≤ ‖x - ∑ i ∈ s, v i‖^2) :
    (∀ s : Finset (Fin 4), ‖x - ∑ i ∈ s, v i‖^2 = q) ∧
    ∀ i j, i ≠ j → ⟪v i, v j⟫ = 0 := by
  classical
  let y (s : Finset (Fin 4)) := x - ∑ i ∈ s, v i
  have step (s : Finset (Fin 4)) (i : Fin 4) :
      y s - flip s v i = y (if i ∈ s then s.erase i else insert i s) := by
    by_cases hi : i ∈ s
    · simp only [flip, hi, ite_true, y]
      rw [← add_sum_erase s v hi]
      abel
    · simp [flip, hi, y, sum_insert]
      abel
  have near (s : Finset (Fin 4)) : ∀ i, ‖y s - flip s v i‖^2 = q := by
    apply neighbors
    · rw [flip_sum, rel]
      dsimp [y]
      abel
    · intro i
      by_cases hi : i ∈ s <;> simp [flip, hi, lengths]
    · intro i
      rw [step]
      exact lower _
  have all_eq (s : Finset (Fin 4)) : ‖y s‖^2 = q := by
    by_cases h : 0 ∈ s
    · simpa [step, h] using near (s.erase 0) 0
    · simpa [step, h] using near (insert 0 s) 0
  refine ⟨all_eq, ?_⟩
  intro i j hij
  have h₀ := all_eq ∅
  have h₁ := all_eq {i}
  have h₂ := all_eq {j}
  have h₃ := all_eq {i, j}
  simp [y, hij, ← sub_sub, norm_sub_sq_real, inner_sub_left] at h₀ h₁ h₂ h₃
  linarith

/-- Determinant of a Gram matrix with four mutually orthogonal vectors of squared
length q and a fifth vector of the same squared length. -/
private theorem arrow_det (b : Fin 5 → V) (q : ℝ) (lengths : ∀ i, ‖b i‖^2 = q)
    (orth : ∀ i j : Fin 4, i ≠ j → ⟪b i.castSucc, b j.castSucc⟫ = 0) :
    (Matrix.gram ℝ b).det =
      q^5 - q^3 * ∑ i : Fin 4, ⟪b i.castSucc, b 4⟫^2 := by
  let t (i : Fin 4) := ⟪b i.castSucc, b 4⟫
  let A : Matrix (Fin 5) (Fin 5) ℝ :=
    !![q,0,0,0,t 0; 0,q,0,0,t 1; 0,0,q,0,t 2; 0,0,0,q,t 3; t 0,t 1,t 2,t 3,q]
  have h : Matrix.gram ℝ b = A := by
    ext i j
    refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · exact (real_inner_self_eq_norm_sq _).trans (lengths _)
    · fin_cases j <;> exact real_inner_comm _ _
    · fin_cases i <;> rfl
    · by_cases he : i = j
      · subst j
        fin_cases i <;> exact (real_inner_self_eq_norm_sq _).trans (lengths _)
      · have hij := orth i j he
        fin_cases i <;> fin_cases j <;> first | exact hij | exact (he rfl).elim
  rw [h]
  change A.det = q^5 - q^3 * ∑ i, (t i)^2
  rw [Fin.sum_univ_four]
  simp only [A, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix_apply,
    Matrix.det_isEmpty, Finset.univ_eq_empty, sum_empty, Fin.succAbove_zero,
    Fin.succ_succAbove_zero, Fin.succ_succAbove_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.of_apply, Fin.val_succ, Fin.val_zero, pow_zero, one_mul, zero_add, add_zero, zero_mul, mul_zero]
  ring

/-- With the fifth vector as a test direction, the support-four Gram determinant
is at least half the fifth power of the squared minimum. -/
theorem four_gram (L : Submodule ℤ V) (b : Fin 5 → V) (ind : LinearIndependent ℝ b)
    (minimal : ∀ i, DecoupledDecoder.IsShortest L (b i)) {x : V} (hx : x ∈ L)
    (out : x ∉ span ℤ (Set.range b)) (rel : ∑ i : Fin 4, b i.castSucc = x + x) :
    ‖b 4‖^10 ≤ 2 * (Matrix.gram ℝ b).det := by
  classical
  let v (i : Fin 4) := b i.castSucc
  let e := b 4
  let q := ‖e‖^2
  let M := span ℤ (Set.range b)
  have bm (i : Fin 5) : b i ∈ M := subset_span (Set.mem_range_self i)
  have sub : M ≤ L := span_le.mpr (Set.range_subset_iff.mpr fun i ↦ (minimal i).1)
  have lengths (i : Fin 5) : ‖b i‖^2 = q := by
    have h := le_antisymm ((minimal i).2.2 _ (minimal 4).1 (minimal 4).2.1)
      ((minimal 4).2.2 _ (minimal i).1 (minimal i).2.1)
    rw [h]
  have lower {w : V} (hw : w ∈ M) : q ≤ ‖x - w‖^2 :=
    pow_le_pow_left₀ (norm_nonneg _) ((minimal 4).2.2 _ (L.sub_mem hx (sub hw))
      (fun h ↦ out (sub_eq_zero.mp h ▸ hw))) 2
  have sums (s : Finset (Fin 4)) : ∑ i ∈ s, v i ∈ M := M.sum_mem fun i _ ↦ bm _
  obtain ⟨equal, orth⟩ := four_geometry v x q rel (fun i ↦ lengths _) (fun s ↦ lower (sums s))
  let t (i : Fin 4) := ⟪v i, e⟫
  have small (i : Fin 4) : |t i| ≤ q / 2 := by
    have hne : i.castSucc ≠ (4 : Fin 5) := Fin.castSucc_ne_last i
    have hp : b i.castSucc + e ≠ 0 := by
      intro h
      apply hne (ind.eq_of_smul_apply_eq_smul_apply 1 (-1) _ _ one_ne_zero ?_)
      simpa [e] using eq_neg_of_add_eq_zero_left h
    have hm : b i.castSucc - e ≠ 0 := fun h ↦ hne (ind.injective (sub_eq_zero.mp h))
    have h₁ := pow_le_pow_left₀ (norm_nonneg _) ((minimal 4).2.2 _
      (L.add_mem (minimal i.castSucc).1 (minimal 4).1) hp) 2
    have h₂ := pow_le_pow_left₀ (norm_nonneg _) ((minimal 4).2.2 _
      (L.sub_mem (minimal i.castSucc).1 (minimal 4).1) hm) 2
    rw [norm_add_sq_real, lengths i.castSucc] at h₁
    rw [norm_sub_sq_real, lengths i.castSucc] at h₂
    apply abs_le.mpr
    change - (q / 2) ≤ ⟪b i.castSucc, e⟫ ∧ ⟪b i.castSucc, e⟫ ≤ q / 2
    change q ≤ q + 2 * _ + q at h₁
    change q ≤ q - 2 * _ + q at h₂
    constructor <;> linarith
  let s := univ.filter fun i ↦ t i < 0
  have signed (i : Fin 4) : ⟪flip s v i, e⟫ = |t i| := by
    by_cases h : t i < 0
    · simp [s, flip, h, abs_of_neg h, t]
    · simp [s, flip, h, abs_of_nonneg (le_of_not_gt h), t]
  let y := x - ∑ i ∈ s, v i
  have hy : ∑ i, flip s v i = y + y := by
    rw [flip_sum, show ∑ i, v i = x + x from rel]
    dsimp [y]
    abel
  have hdot : ∑ i, |t i| = ⟪y, e⟫ + ⟪y, e⟫ := by
    simp only [← signed, ← sum_inner, hy, inner_add_left]
  have hlow := lower (M.add_mem (sums s) (bm 4))
  rw [← sub_sub] at hlow
  change q ≤ ‖y - e‖^2 at hlow
  rw [norm_sub_sq_real, show ‖y‖^2 = q from equal s] at hlow
  have h₁ : ∑ i, |t i| ≤ q := by
    rw [hdot]
    change q ≤ q - 2 * _ + q at hlow
    linarith
  have h₂ : ∑ i, (t i)^2 ≤ ∑ i, |t i| * (q / 2) := by
    apply sum_le_sum
    intro i _
    simpa [← sq, sq_abs] using mul_le_mul_of_nonneg_left (small i) (abs_nonneg (t i))
  rw [← sum_mul] at h₂
  have hq : 0 ≤ q := sq_nonneg _
  have bound := h₂.trans (mul_le_mul_of_nonneg_right h₁ (by positivity))
  rw [arrow_det b q lengths orth]
  rw [show (10 : ℕ) = 2 * 5 by decide, pow_mul]
  change (‖e‖^2)^5 ≤ 2 * (q^5 - q^3 * ∑ i, (t i)^2)
  change q^5 ≤ _
  nlinarith only [mul_le_mul_of_nonneg_left bound (pow_nonneg hq 3)]

/-- Sharp rank-five Hermite bound for a shortest basis with a support-four half-coset. -/
theorem four_covolume (L : Submodule ℤ (CoordSpace 5)) [DiscreteTopology L] [IsZLattice ℝ L]
    (B : Basis (Fin 5) ℝ (CoordSpace 5)) (minimal : ∀ i, DecoupledDecoder.IsShortest L (B i))
    {x : CoordSpace 5} (hx : x ∈ L) (out : x ∉ span ℤ (Set.range B))
    (rel : ∑ i : Fin 4, B i.castSucc = x + x) : ‖B 4‖^10 ≤ 8 * ZLattice.covolume L ^ 2 := by
  let M := span ℤ (Set.range B)
  have sub : M ≤ L := span_le.mpr (Set.range_subset_iff.mpr fun i ↦ (minimal i).1)
  have h := four_gram L B B.linearIndependent minimal hx out rel
  rw [← covolume_span_sq_eq_gram] at h
  have hi := rank_five_minimal_index L B minimal
  have hr := ZLattice.covolume_div_covolume_eq_relIndex' M L sub
  have bound : ZLattice.covolume M / ZLattice.covolume L ≤ 2 := by
    rw [hr]
    exact_mod_cast hi
  have hvol := (div_le_iff₀ (ZLattice.covolume_pos L volume)).mp bound
  nlinarith only [h, pow_le_pow_left₀ (ZLattice.covolume_pos M volume).le hvol 2]

end SigabaNeo.Wall1.Watson

#print axioms SigabaNeo.Wall1.Watson.four_geometry
#print axioms SigabaNeo.Wall1.Watson.four_gram
#print axioms SigabaNeo.Wall1.Watson.four_covolume
