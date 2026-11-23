import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonMinimalFamily

/-! Sharp determinant bounds when normalization to squared minimum two gives integral
Gram entries. In rank six the diagonal is also required to be even. -/

noncomputable section
namespace SigabaNeo.Wall1.Watson

open Matrix Finset Module Submodule MeasureTheory TerminalProjection ControlledPlane
open scoped RealInnerProductSpace

/-- A normalized integral Gram matrix for a lattice family, at squared minimum q. -/
def ScaledGram {d k : ℕ} (b : Fin k → CoordSpace d) (q : ℝ) (Z : Matrix (Fin k) (Fin k) ℤ) :=
  ∀ i j, q * (Z i j : ℝ) = 2 * ⟪b i, b j⟫

private theorem scaled_det {d k : ℕ} {b : Fin k → CoordSpace d} {q : ℝ}
    {Z : Matrix (Fin k) (Fin k) ℤ} (h : ScaledGram b q Z) :
    q^k * (Z.det : ℝ) = 2^k * (gram ℝ b).det := by
  have eq : q • Z.map (fun x ↦ (x : ℝ)) = (2 : ℝ) • gram ℝ b := by
    ext i j
    exact h i j
  simpa only [det_smul, Fintype.card_fin, ← Int.cast_det] using congrArg Matrix.det eq

private theorem normalized_lower {d k : ℕ} (hk : 2 ≤ k) {L : Submodule ℤ (CoordSpace d)}
    [DiscreteTopology L] {v : CoordSpace d} (hv : DecoupledDecoder.IsShortest L v)
    (b : RankinFamily L k) {Z : Matrix (Fin k) (Fin k) ℤ} (h : ScaledGram b.vec (‖v‖^2) Z) :
    (2 : ℝ)^k ≤ (MordellBlichfeldt.gamma k)^k * Z.det := by
  have detG := (Matrix.posSemidef_gram ℝ b.vec).det_nonneg
  have rad := MordellBlichfeldt.family k hk L hv b
  have bound := pow_le_pow_left₀ (sq_nonneg _) rad k
  rw [mul_pow, ← Real.rpow_mul_natCast (Real.sqrt_nonneg _),
    div_mul_cancel₀ _ (by exact_mod_cast (show k ≠ 0 by omega)), Real.rpow_two,
    Real.sq_sqrt detG] at bound
  apply le_of_mul_le_mul_left (a := (‖v‖^2)^k) _ (pow_pos (sq_pos_of_pos
    (norm_pos_iff.mpr hv.2.1)) _)
  have hh := mul_le_mul_of_nonneg_left bound (by positivity : (0 : ℝ) ≤ 2^k)
  have he := scaled_det h
  calc
    (‖v‖^2)^k * 2^k ≤ (MordellBlichfeldt.gamma k)^k * (2^k * (gram ℝ b.vec).det) := by
      linarith only [hh]
    _ = _ := by rw [← he]; ring

/-- Rounding the determinant of the normalized integral Gram matrix gives the
sharp rank-five bound, including integral index-one shortest bases. -/
theorem rank_five_integral {d : ℕ} {L : Submodule ℤ (CoordSpace d)} [DiscreteTopology L]
    {v : CoordSpace d} (hv : DecoupledDecoder.IsShortest L v) (b : RankinFamily L 5)
    {Z : Matrix (Fin 5) (Fin 5) ℤ} (h : ScaledGram b.vec (‖v‖^2) Z) :
    ‖v‖^10 ≤ 8 * (gram ℝ b.vec).det := by
  have hl := normalized_lower (by decide) hv b h
  have hg := pow_le_pow_left₀ (MordellBlichfeldt.gamma_pos 5).le
    MordellBlichfeldt.exceptional_enclosures.2.1 5
  have hd : 4 ≤ Z.det := by
    by_contra! bad
    have le : (Z.det : ℝ) ≤ 3 := by exact_mod_cast (show Z.det ≤ 3 by omega)
    nlinarith only [hl,hg,mul_le_mul_of_nonneg_left le
      (pow_nonneg (MordellBlichfeldt.gamma_pos 5).le 5)]
  have hd' : (4 : ℝ) ≤ Z.det := by exact_mod_cast hd
  nlinarith only [scaled_det h,mul_le_mul_of_nonneg_left hd' (pow_nonneg (sq_nonneg ‖v‖) 5)]

private def symSix (d : Fin 6 → ZMod 4) (a : Matrix (Fin 6) (Fin 6) (ZMod 4)) :
    Matrix (Fin 6) (Fin 6) (ZMod 4) :=
  !![2*d 0, a 0 1, a 0 2, a 0 3, a 0 4, a 0 5;
    a 0 1, 2*d 1, a 1 2, a 1 3, a 1 4, a 1 5;
    a 0 2, a 1 2, 2*d 2, a 2 3, a 2 4, a 2 5;
    a 0 3, a 1 3, a 2 3, 2*d 3, a 3 4, a 3 5;
    a 0 4, a 1 4, a 2 4, a 3 4, 2*d 4, a 4 5;
    a 0 5, a 1 5, a 2 5, a 3 5, a 4 5, 2*d 5]

-- Modulo four, the sign of each matching is immaterial after squaring.
private def matchingSum (a : Matrix (Fin 6) (Fin 6) (ZMod 4)) : ZMod 4 :=
  a 0 1 * a 2 3 * a 4 5 +
  a 0 1 * a 2 4 * a 3 5 +
  a 0 1 * a 2 5 * a 3 4 +
  a 0 2 * a 1 3 * a 4 5 +
  a 0 2 * a 1 4 * a 3 5 +
  a 0 2 * a 1 5 * a 3 4 +
  a 0 3 * a 1 2 * a 4 5 +
  a 0 3 * a 1 4 * a 2 5 +
  a 0 3 * a 1 5 * a 2 4 +
  a 0 4 * a 1 2 * a 3 5 +
  a 0 4 * a 1 3 * a 2 5 +
  a 0 4 * a 1 5 * a 2 3 +
  a 0 5 * a 1 2 * a 3 4 +
  a 0 5 * a 1 3 * a 2 4 +
  a 0 5 * a 1 4 * a 2 3

private theorem symSix_det (d : Fin 6 → ZMod 4) (a : Matrix (Fin 6) (Fin 6) (ZMod 4)) :
    (symSix d a).det = -(matchingSum a)^2 := by
  simp only [symSix, matchingSum, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix_apply, Matrix.det_isEmpty, Finset.univ_eq_empty, sum_empty,
    Fin.succAbove_zero, Fin.succ_succAbove_zero, Fin.succ_succAbove_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.of_apply, Fin.val_succ, Fin.val_zero, pow_zero, one_mul,
    zero_add, add_zero]
  grind only

/-- A positive determinant of an even integral symmetric six-by-six matrix is at least three. -/
theorem even_six_det {Z : Matrix (Fin 6) (Fin 6) ℤ} (symm : ∀ i j, Z i j = Z j i)
    (even : ∀ i, Even (Z i i)) (pos : 0 < Z.det) : 3 ≤ Z.det := by
  choose d hd using even
  let a := Z.map (fun z ↦ (z : ZMod 4))
  have A : a = symSix (fun i ↦ (d i : ZMod 4)) a := by
    ext i j
    by_cases hij : i = j
    · subst j
      have eq : a i i = 2 * (d i : ZMod 4) := by simp [a,hd,two_mul]
      fin_cases i <;> exact eq
    · fin_cases i <;> fin_cases j <;> first | rfl | exact (hij rfl).elim |
        exact congrArg (fun z : ℤ ↦ (z : ZMod 4)) (symm _ _)
  have eq : (Z.det : ZMod 4) = -(matchingSum a)^2 := by
    rw [Int.cast_det]
    exact (congrArg Matrix.det A).trans (symSix_det _ _)
  have residues : ∀ w : ZMod 4, -w^2 = 0 ∨ -w^2 = 3 := by decide
  by_contra! bad
  have small : Z.det = 1 ∨ Z.det = 2 := by omega
  rcases small with e | e <;> rw [e] at eq <;>
    rcases residues (matchingSum a) with r | r <;> rw [r] at eq <;> exact (by decide : ¬ _) eq

/-- Sharp rank-six determinant inequality for a normalized even integral Gram matrix. -/
theorem rank_six_even_integral {d : ℕ} {L : Submodule ℤ (CoordSpace d)}
    {v : CoordSpace d} (hv : DecoupledDecoder.IsShortest L v) (b : RankinFamily L 6)
    {Z : Matrix (Fin 6) (Fin 6) ℤ} (h : ScaledGram b.vec (‖v‖^2) Z)
    (even : ∀ i, Even (Z i i)) : 3 * ‖v‖^12 ≤ 64 * (gram ℝ b.vec).det := by
  have hq : 0 < ‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv.2.1)
  have pos : 0 < (gram ℝ b.vec).det := (Matrix.posDef_gram_of_linearIndependent b.ind).det_pos
  have detEq := scaled_det h
  have hd : 0 < (Z.det : ℝ) := pos_of_mul_pos_right (detEq.trans_gt (by positivity)) (by positivity)
  have symm (i j : Fin 6) : Z i j = Z j i := by
    have eq := (h i j).trans ((congrArg (2 * ·) (real_inner_comm _ _)).trans (h j i).symm)
    exact_mod_cast (mul_left_cancel₀ hq.ne' eq)
  have three := even_six_det symm even (by exact_mod_cast hd)
  have hh : (3 : ℝ) ≤ Z.det := by exact_mod_cast three
  nlinarith only [detEq,mul_le_mul_of_nonneg_left hh (pow_nonneg hq.le 6)]

/-- Sharp rank-seven bound when the normalized Gram matrix is integral. -/
theorem rank_seven_integral {d : ℕ} {L : Submodule ℤ (CoordSpace d)} [DiscreteTopology L]
    {v : CoordSpace d} (hv : DecoupledDecoder.IsShortest L v) (b : RankinFamily L 7)
    {Z : Matrix (Fin 7) (Fin 7) ℤ} (h : ScaledGram b.vec (‖v‖^2) Z) :
    ‖v‖^14 ≤ 64 * (gram ℝ b.vec).det := by
  have hl := normalized_lower (by decide) hv b h
  have hg := pow_le_pow_left₀ (MordellBlichfeldt.gamma_pos 7).le
    MordellBlichfeldt.exceptional_enclosures.2.2.2.2.2.1 7
  have hd : 2 ≤ Z.det := by
    by_contra! bad
    have le : (Z.det : ℝ) ≤ 1 := by exact_mod_cast (show Z.det ≤ 1 by omega)
    nlinarith only [hl,hg,mul_le_mul_of_nonneg_left le
      (pow_nonneg (MordellBlichfeldt.gamma_pos 7).le 7)]
  have hd' : (2 : ℝ) ≤ Z.det := by exact_mod_cast hd
  nlinarith only [scaled_det h,mul_le_mul_of_nonneg_left hd' (pow_nonneg (sq_nonneg ‖v‖) 7)]

end SigabaNeo.Wall1.Watson

#print axioms SigabaNeo.Wall1.Watson.rank_five_integral
#print axioms SigabaNeo.Wall1.Watson.even_six_det
#print axioms SigabaNeo.Wall1.Watson.rank_six_even_integral
#print axioms SigabaNeo.Wall1.Watson.rank_seven_integral
