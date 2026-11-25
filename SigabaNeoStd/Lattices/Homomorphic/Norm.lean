import Mathlib.Data.ZMod.ValMinAbs
import CslibFrontier.Foundations.Algebra.Negacyclic

/-!
# The coefficient norm of `ℤ_q[X]/(X^N + 1)`

`cnorm a` is the largest absolute value of the centered representatives of the coefficients of
`a` (cslib-frontier's `Cslib.Negacyclic (ZMod q) N`). It is subadditive (`cnorm_add_le`,
`cnorm_sum_le`), invariant under negation (`cnorm_neg`), and submultiplicative up to the degree:
`cnorm (a * b) ≤ N · cnorm a · cnorm b` (`cnorm_mul_le`).
-/

namespace SigabaNeo.Lattices

open Cslib

/-- The absolute value of the centered representative. -/
def zabs {q : ℕ} (x : ZMod q) : ℕ := x.valMinAbs.natAbs

variable {q : ℕ}

/-- An integer reduced mod `q` has a centered representative no larger than itself. -/
theorem zabs_intCast_le [NeZero q] (z : ℤ) : zabs (z : ZMod q) ≤ z.natAbs :=
  ZMod.natAbs_min_of_le_div_two q _ z (ZMod.coe_valMinAbs _) (ZMod.natAbs_valMinAbs_le _)

theorem zabs_add_le (x y : ZMod q) : zabs (x + y) ≤ zabs x + zabs y :=
  (ZMod.natAbs_valMinAbs_add_le x y).trans (Int.natAbs_add_le _ _)

theorem zabs_neg (x : ZMod q) : zabs (-x) = zabs x := ZMod.natAbs_valMinAbs_neg x

theorem zabs_sub_le (x y : ZMod q) : zabs (x - y) ≤ zabs x + zabs y := by
  rw [sub_eq_add_neg]; exact (zabs_add_le _ _).trans (by rw [zabs_neg])

theorem zabs_mul_le [NeZero q] (x y : ZMod q) : zabs (x * y) ≤ zabs x * zabs y := by
  have h : x * y = ((x.valMinAbs * y.valMinAbs : ℤ) : ZMod q) := by
    rw [Int.cast_mul, ZMod.coe_valMinAbs, ZMod.coe_valMinAbs]
  rw [h]
  exact (zabs_intCast_le _).trans (le_of_eq (Int.natAbs_mul _ _))

theorem zabs_zero : zabs (0 : ZMod q) = 0 := by simp [zabs]

theorem zabs_one_le [NeZero q] : zabs (1 : ZMod q) ≤ 1 := by
  have := zabs_intCast_le (q := q) 1
  simpa using this

theorem zabs_sum_le {ι : Type*} (s : Finset ι) (f : ι → ZMod q) :
    zabs (∑ i ∈ s, f i) ≤ ∑ i ∈ s, zabs (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zabs_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (zabs_add_le _ _).trans (Nat.add_le_add_left ih _)

variable {N : ℕ}

/-- The coefficient norm: the largest centered coefficient. -/
def cnorm (a : Negacyclic (ZMod q) N) : ℕ := Finset.univ.sup fun j => zabs (a.coeffs j)

theorem zabs_coeffs_le_cnorm (a : Negacyclic (ZMod q) N) (j : Fin N) : zabs (a.coeffs j) ≤ cnorm a :=
  Finset.le_sup (f := fun j => zabs (a.coeffs j)) (Finset.mem_univ j)

theorem cnorm_le_iff (a : Negacyclic (ZMod q) N) (B : ℕ) :
    cnorm a ≤ B ↔ ∀ j, zabs (a.coeffs j) ≤ B := by
  simp [cnorm, Finset.sup_le_iff]

theorem cnorm_zero : cnorm (0 : Negacyclic (ZMod q) N) = 0 := by
  apply le_antisymm _ (Nat.zero_le _)
  rw [cnorm_le_iff]; intro j; simp [zabs_zero]

theorem cnorm_add_le (a b : Negacyclic (ZMod q) N) : cnorm (a + b) ≤ cnorm a + cnorm b := by
  rw [cnorm_le_iff]; intro j
  rw [Negacyclic.coeffs_add, Pi.add_apply]
  exact (zabs_add_le _ _).trans (Nat.add_le_add (zabs_coeffs_le_cnorm a j) (zabs_coeffs_le_cnorm b j))

theorem cnorm_neg (a : Negacyclic (ZMod q) N) : cnorm (-a) = cnorm a := by
  simp [cnorm, zabs_neg]

theorem cnorm_sub_le (a b : Negacyclic (ZMod q) N) : cnorm (a - b) ≤ cnorm a + cnorm b := by
  rw [sub_eq_add_neg]; exact (cnorm_add_le _ _).trans (by rw [cnorm_neg])

theorem cnorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → Negacyclic (ZMod q) N) :
    cnorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, cnorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cnorm_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (cnorm_add_le _ _).trans (Nat.add_le_add_left ih _)

/-- An entry of the negacyclic matrix of `a` is `± a_j`. -/
theorem zabs_rotMatrix_le (a : Negacyclic (ZMod q) N) (i j : Fin N) :
    zabs (rotMatrix a.coeffs i j) ≤ cnorm a := by
  unfold rotMatrix
  simp only [Matrix.of_apply]
  split_ifs
  · exact zabs_coeffs_le_cnorm a _
  · rw [zabs_neg]; exact zabs_coeffs_le_cnorm a _

/-- **Submultiplicativity**: `cnorm (a * b) ≤ N · cnorm a · cnorm b`. -/
theorem cnorm_mul_le [NeZero q] (a b : Negacyclic (ZMod q) N) : cnorm (a * b) ≤ N * cnorm a * cnorm b := by
  rw [cnorm_le_iff]; intro i
  rw [Negacyclic.coeffs_mul, ← rotMatrix_mulVec]
  simp only [Matrix.mulVec, dotProduct]
  refine (zabs_sum_le _ _).trans ?_
  calc ∑ j, zabs (rotMatrix a.coeffs i j * b.coeffs j)
      ≤ ∑ _j : Fin N, cnorm a * cnorm b := Finset.sum_le_sum fun j _ =>
        (zabs_mul_le _ _).trans (Nat.mul_le_mul (zabs_rotMatrix_le a i j) (zabs_coeffs_le_cnorm b j))
    _ = N * cnorm a * cnorm b := by simp [mul_assoc]

end SigabaNeo.Lattices
