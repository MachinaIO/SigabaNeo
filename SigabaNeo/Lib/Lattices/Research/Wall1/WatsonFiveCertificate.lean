import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonFourSupport

/-! A cubic positivity certificate for a five-vector half-coset.

The ten variables index the lexicographically ordered edges of the complete graph on
five vertices. There are sixteen sign choices up to simultaneous negation. For each
choice, the half-coset minimum gives a nonnegative linear form (a slack). The cubic
part of the determinant bound is a positive combination of products of three slacks.
The remaining terms are principal minors of a positive semidefinite matrix. -/

noncomputable section
namespace SigabaNeo.Wall1.Watson.Five

open Matrix Finset
open scoped NNReal
set_option maxHeartbeats 8000000

/-- Symmetric matrix with fixed diagonal and ten edge entries. -/
def mat (q : ℝ) (x : Fin 10 → ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![q, x 0, x 1, x 2, x 3;
    x 0, q, x 4, x 5, x 6;
    x 1, x 4, q, x 7, x 8;
    x 2, x 5, x 7, q, x 9;
    x 3, x 6, x 8, x 9, q]

/-- Signs up to global negation, with first coordinate positive. -/
def signs : Fin 16 → Fin 5 → ℝ :=
  ![![1, 1, 1, 1, 1],
    ![1, 1, 1, 1, -1],
    ![1, 1, 1, -1, 1],
    ![1, 1, 1, -1, -1],
    ![1, 1, -1, 1, 1],
    ![1, 1, -1, 1, -1],
    ![1, 1, -1, -1, 1],
    ![1, 1, -1, -1, -1],
    ![1, -1, 1, 1, 1],
    ![1, -1, 1, 1, -1],
    ![1, -1, 1, -1, 1],
    ![1, -1, 1, -1, -1],
    ![1, -1, -1, 1, 1],
    ![1, -1, -1, 1, -1],
    ![1, -1, -1, -1, 1],
    ![1, -1, -1, -1, -1]]

/-- Signed squared-length slacks in the half-coset. -/
def slack (q : ℝ) (x : Fin 10 → ℝ) : Fin 16 → ℝ :=
  ![q + x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7 + x 8 + x 9,
    q + x 0 + x 1 + x 2 - x 3 + x 4 + x 5 - x 6 + x 7 - x 8 - x 9,
    q + x 0 + x 1 - x 2 + x 3 + x 4 - x 5 + x 6 - x 7 + x 8 - x 9,
    q + x 0 + x 1 - x 2 - x 3 + x 4 - x 5 - x 6 - x 7 - x 8 + x 9,
    q + x 0 - x 1 + x 2 + x 3 - x 4 + x 5 + x 6 - x 7 - x 8 + x 9,
    q + x 0 - x 1 + x 2 - x 3 - x 4 + x 5 - x 6 - x 7 + x 8 - x 9,
    q + x 0 - x 1 - x 2 + x 3 - x 4 - x 5 + x 6 + x 7 - x 8 - x 9,
    q + x 0 - x 1 - x 2 - x 3 - x 4 - x 5 - x 6 + x 7 + x 8 + x 9,
    q - x 0 + x 1 + x 2 + x 3 - x 4 - x 5 - x 6 + x 7 + x 8 + x 9,
    q - x 0 + x 1 + x 2 - x 3 - x 4 - x 5 + x 6 + x 7 - x 8 - x 9,
    q - x 0 + x 1 - x 2 + x 3 - x 4 + x 5 - x 6 - x 7 + x 8 - x 9,
    q - x 0 + x 1 - x 2 - x 3 - x 4 + x 5 + x 6 - x 7 - x 8 + x 9,
    q - x 0 - x 1 + x 2 + x 3 + x 4 - x 5 - x 6 - x 7 - x 8 + x 9,
    q - x 0 - x 1 + x 2 - x 3 + x 4 - x 5 + x 6 - x 7 + x 8 - x 9,
    q - x 0 - x 1 - x 2 + x 3 + x 4 + x 5 - x 6 + x 7 - x 8 - x 9,
    q - x 0 - x 1 - x 2 - x 3 + x 4 + x 5 + x 6 + x 7 + x 8 + x 9]

private def switch (s : Fin 16) (x : Fin 10 → ℝ) : Fin 10 → ℝ :=
  ![signs s 0 * signs s 1 * x 0,
    signs s 0 * signs s 2 * x 1,
    signs s 0 * signs s 3 * x 2,
    signs s 0 * signs s 4 * x 3,
    signs s 1 * signs s 2 * x 4,
    signs s 1 * signs s 3 * x 5,
    signs s 1 * signs s 4 * x 6,
    signs s 2 * signs s 3 * x 7,
    signs s 2 * signs s 4 * x 8,
    signs s 3 * signs s 4 * x 9]

private theorem switch_nonneg (q : ℝ) (x : Fin 10 → ℝ)
    (h : ∀ s, 0 ≤ slack q x s) (s t : Fin 16) : 0 ≤ slack q (switch s x) t := by
  let u : Fin 16 := ⟨s.val ^^^ t.val, by
    revert s t
    decide⟩
  have heq : slack q (switch s x) t = slack q x u := by
    dsimp only [u]
    fin_cases s <;> fin_cases t <;>
      simp only [Nat.reduceXor, slack, switch, signs, Matrix.cons_val,
        Matrix.cons_val_zero', Matrix.cons_val_succ', one_mul, neg_one_mul, sub_eq_add_neg, neg_neg]
  rw [heq]
  exact h _

-- Quadratic score at the all-positive pattern. The five four-edge sums are
-- the sums of the weights incident to each respective vertex.
private def score (q : ℝ) (x : Fin 10 → ℝ) : ℝ :=
  let total := x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7 + x 8 + x 9
  180*q^2 - 48*q*total + 4*total^2 + 2 * (
    (x 0 + x 1 + x 2 + x 3)^2 + (x 0 + x 4 + x 5 + x 6)^2 +
    (x 1 + x 4 + x 7 + x 8)^2 + (x 2 + x 5 + x 7 + x 9)^2 +
    (x 3 + x 6 + x 8 + x 9)^2) - 32 * (
    (x 0)^2 + (x 1)^2 + (x 2)^2 + (x 3)^2 + (x 4)^2 +
    (x 5)^2 + (x 6)^2 + (x 7)^2 + (x 8)^2 + (x 9)^2)

/-- Pairs completing a triple with the all-positive sign pattern. In projective
Hamming distance the triples with distances 1,2,2 have weight two and the triples
with distances 2,2,2 have weight three. -/
private def pairs {R : Type*} [Semiring R] (p : Fin 16 → R) : R :=
  p 1 * (2 * (p 6 + p 7 + p 10 + p 11 + p 12 + p 13)) +
  p 2 * (2 * (p 5 + p 7 + p 9 + p 11 + p 12 + p 14)) +
  p 3 * (2 * (p 4 + p 7 + p 8 + p 11 + p 12 + p 15) +
      3 * (p 5 + p 6 + p 9 + p 10 + p 13 + p 14)) +
  p 4 * (2 * (p 7 + p 9 + p 10 + p 13 + p 14)) +
  p 5 * (2 * (p 7 + p 8 + p 10 + p 13 + p 15) +
      3 * (p 6 + p 9 + p 11 + p 12 + p 14)) +
  p 6 * (2 * (p 7 + p 8 + p 9 + p 14 + p 15) + 3 * (p 10 + p 11 + p 12 + p 13)) +
  p 7 * (3 * (p 9 + p 10 + p 11 + p 12 + p 13 + p 14)) +
  p 8 * (2 * (p 11 + p 13 + p 14)) +
  p 9 * (2 * (p 11 + p 13 + p 15) + 3 * (p 10 + p 12 + p 14)) +
  p 10 * (2 * (p 11 + p 14 + p 15) + 3 * (p 12 + p 13)) +
  p 11 * (3 * (p 12 + p 13 + p 14)) +
  p 12 * (2 * (p 13 + p 14 + p 15)) +
  p 13 * (3 * p 14)

private theorem score_nonneg (q : ℝ) (x : Fin 10 → ℝ) (h : ∀ i, 0 ≤ slack q x i) :
    0 ≤ score q x := by
  let p (i : Fin 16) : ℝ≥0 := ⟨slack q x i, h i⟩
  have identity : pairs (slack q x) = score q x := by
    simp only [pairs, slack, score, Matrix.cons_val]
    ring
  rw [← identity]
  exact (pairs p).property

private def cubic (q : ℝ) (x : Fin 10 → ℝ) : ℝ :=
  10 * q^3 - 4 * q * ((x 0)^2 + (x 1)^2 + (x 2)^2 + (x 3)^2 + (x 4)^2 +
    (x 5)^2 + (x 6)^2 + (x 7)^2 + (x 8)^2 + (x 9)^2) +
    2 * (x 0 * x 1 * x 4 +
      x 0 * x 2 * x 5 +
      x 0 * x 3 * x 6 +
      x 1 * x 2 * x 7 +
      x 1 * x 3 * x 8 +
      x 2 * x 3 * x 9 +
      x 4 * x 5 * x 7 +
      x 4 * x 6 * x 8 +
      x 5 * x 6 * x 9 +
      x 7 * x 8 * x 9)

private theorem cubic_nonneg (q : ℝ) (x : Fin 10 → ℝ) (h : ∀ i, 0 ≤ slack q x i) :
    0 ≤ cubic q x := by
  have H := sum_nonneg (s := univ) (fun (i : Fin 16) _ ↦ mul_nonneg (h i)
    (score_nonneg q (switch i x) (switch_nonneg q x h i)))
  have heq : ∑ i, slack q x i * score q (switch i x) = 288 * cubic q x := by
    simp only [Fin.sum_univ_succ, slack, score, switch, signs, cubic, Matrix.cons_val,
      Matrix.cons_val_zero, Matrix.cons_val_succ, one_mul, neg_one_mul, sub_eq_add_neg, neg_neg,
      Finset.univ_eq_empty, sum_empty, add_zero]
    ring
  linarith only [H, heq]

private theorem psd (q : ℝ) (x : Fin 10 → ℝ) (h : ∀ i, 0 ≤ slack q x i) :
    (mat q x).PosSemidef := by
  have E : mat q x = ∑ s, (slack q x s / 16) • vecMulVec (signs s) (signs s) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.sum_univ_succ, mat, signs, slack, Matrix.cons_val_zero',
        Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_succ,
        vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.zero_apply,
        Matrix.of_apply, Finset.univ_eq_empty, sum_empty] <;> ring
  rw [E]
  apply Matrix.posSemidef_sum
  intro s _
  apply Matrix.PosSemidef.smul _ (div_nonneg (h s) (by norm_num))
  simpa using posSemidef_vecMulVec_self_star (signs s)

/-- The signed half-sum inequalities alone imply the support-five determinant bound. -/
theorem det_bound (q : ℝ) (x : Fin 10 → ℝ) (hq : 0 ≤ q) (h : ∀ i, 0 ≤ slack q x i) :
    16 * q^5 ≤ (mat (2*q) x).det := by
  let A := mat q x
  let minor (i : Fin 5) := (A.submatrix i.succAbove i.succAbove).det
  have hp := psd q x h
  have hm (i : Fin 5) : 0 ≤ minor i := (hp.submatrix i.succAbove).det_nonneg
  have heq : (mat (2*q) x).det - 16*q^5 =
      q^2 * cubic q x + q * ∑ i, minor i + A.det := by
    simp only [minor, A, mat, cubic, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
      Matrix.submatrix_apply, Matrix.det_isEmpty, Finset.univ_eq_empty, sum_empty,
      Fin.succAbove_zero, Fin.succ_succAbove_zero, Fin.succ_succAbove_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.of_apply, Fin.val_succ, Fin.val_zero, pow_zero, one_mul,
      zero_add, add_zero]
    ring
  exact sub_nonneg.mp (heq ▸ add_nonneg
    (add_nonneg (mul_nonneg (sq_nonneg _) (cubic_nonneg q x h))
      (mul_nonneg hq (sum_nonneg (fun i _ ↦ hm i)))) hp.det_nonneg)

end SigabaNeo.Wall1.Watson.Five

#print axioms SigabaNeo.Wall1.Watson.Five.det_bound
