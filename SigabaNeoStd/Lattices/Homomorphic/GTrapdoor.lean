import SigabaNeoStd.Lattices.Homomorphic.Gadget
import Mathlib.Tactic.Abel
import Mathlib.Algebra.BigOperators.Fin

/-!
# A gadget trapdoor over a ring

The trapdoor of Micciancio–Peikert ([MP12]) for one row over a commutative ring `R`, with gadget
digits `D`: for `A₀ ∈ R^{1×k}` and a short `T ∈ R^{k×k}`,

  `B = [A₀ | g − A₀ T] ∈ R^{1 × (2·k)}`   (`gTrapdoorMatrix`),

so `B · [T; I] = g`. A preimage of any `y ∈ R` is then `[T; I] · g⁻¹(y)` (`gTrapdoorSolve`,
`gTrapdoorMatrix_mul_solve`). Its two blocks are indexed by `Fin 2 × Fin k`, the columns of the
Ring-GSW gadget (`SigabaNeoStd.Lattices.Homomorphic.Gadget`).

This solver is exact, which is what correctness needs. It is not the Gaussian preimage sampler that
hides `T` (MP12's perturbation sampler), which security needs.
-/

namespace SigabaNeo.Lattices

variable {R : Type*} [CommRing R] {k : ℕ}

/-- `B = [A₀ | g − A₀ T]`. -/
def gTrapdoorMatrix (D : GadgetDigits R k) (A₀ : Fin k → R) (T : Matrix (Fin k) (Fin k) R) :
    Matrix (Fin 1) (Fin 2 × Fin k) R :=
  Matrix.of fun _ c => if c.1 = 0 then A₀ c.2 else D.g c.2 - ∑ i, A₀ i * T i c.2

/-- The preimage `[T; I] · g⁻¹(y)` of `y`. -/
def gTrapdoorSolve (D : GadgetDigits R k) (T : Matrix (Fin k) (Fin k) R) (y : R) :
    Matrix (Fin 2 × Fin k) (Fin 1) R :=
  Matrix.of fun c _ => if c.1 = 0 then ∑ j, T c.2 j * D.d y j else D.d y c.2

/-- **The trapdoor inverts `B`.** `B · [T; I] g⁻¹(y) = y`. -/
theorem gTrapdoorMatrix_mul_solve (D : GadgetDigits R k) (A₀ : Fin k → R)
    (T : Matrix (Fin k) (Fin k) R) (y : R) :
    gTrapdoorMatrix D A₀ T * gTrapdoorSolve D T y = Matrix.of fun _ _ => y := by
  have h10 : ((1 : Fin 2) = 0) ↔ False := by decide
  ext a b
  simp only [gTrapdoorMatrix, gTrapdoorSolve, Matrix.mul_apply, Matrix.of_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Fin.isValue, ite_true, h10, ite_false]
  have key : ∑ x, A₀ x * ∑ j, T x j * D.d y j = ∑ j, (∑ i, A₀ i * T i j) * D.d y j := by
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  rw [key, ← Finset.sum_add_distrib]
  conv_rhs => rw [← D.recompose y]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end SigabaNeo.Lattices
