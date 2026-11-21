import SigabaNeo.Lib.Lattices.Gaussian
import CslibFrontier.Foundations.Algebra.Negacyclic

/-!
# Gaussian preimages of a ring row

The solutions `z` of `∑_c L_c z_c = y` in `ℤ_q[X]/(X^N + 1)` (cslib-frontier's `Cslib.Negacyclic`),
drawn from the discrete Gaussian on their coset ([GPV08]). In coefficients the equation is
`rowRot L · coeffs(z) = coeffs(y)` over `ℤ_q` (`rowRot_mulVec`), with `rowRot L` the negacyclic
matrices of the `L_c` side by side; `gaussPreimage L y τ` is `cosetGauss` of that system, read back
as ring elements. It is defined exactly when a solution exists (`gaussPreimage_isSome`), and every
point it draws is a solution (`gaussPreimage_mem`).
-/

namespace SigabaNeo.Lattices

open Cslib
open scoped Matrix

variable {N q : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The coefficient matrix of `z ↦ ∑_c L_c z_c`. -/
def rowRot (L : ι → Negacyclic (ZMod q) N) : Matrix (Fin N) (ι × Fin N) (ZMod q) :=
  Matrix.of fun i cj => rotMatrix (L cj.1).coeffs i cj.2

omit [DecidableEq ι] in
/-- The coefficients of `∑_c L_c z_c`. -/
theorem rowRot_mulVec (L z : ι → Negacyclic (ZMod q) N) :
    rowRot L *ᵥ (fun cj => (z cj.1).coeffs cj.2) = (∑ c, L c * z c).coeffs := by
  ext i
  simp only [Matrix.mulVec, dotProduct, rowRot, Matrix.of_apply, Fintype.sum_prod_type,
    Negacyclic.coeffs_sum, Finset.sum_apply, Negacyclic.coeffs_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← rotMatrix_mulVec]
  rfl

/-- The system over `Fin m`. -/
noncomputable def rowRotFin (L : ι → Negacyclic (ZMod q) N) :
    Matrix (Fin N) (Fin (Fintype.card (ι × Fin N))) (ZMod q) :=
  Matrix.of fun i t => rowRot L i ((Fintype.equivFin (ι × Fin N)).symm t)

/-- Ring elements from integer coefficients indexed by `Fin m`. -/
noncomputable def ofIntCoeffs (x : Fin (Fintype.card (ι × Fin N)) → ℤ) : ι → Negacyclic (ZMod q) N :=
  fun c => Negacyclic.ofCoeffs fun j => (x (Fintype.equivFin (ι × Fin N) (c, j)) : ZMod q)

theorem rowRotFin_mulVec (L : ι → Negacyclic (ZMod q) N) (x : Fin (Fintype.card (ι × Fin N)) → ℤ) :
    rowRotFin L *ᵥ (fun t => (x t : ZMod q)) = (∑ c, L c * ofIntCoeffs x c).coeffs := by
  rw [← rowRot_mulVec]
  ext i
  simp only [Matrix.mulVec, dotProduct, rowRotFin, Matrix.of_apply, ofIntCoeffs,
    Negacyclic.coeffs_ofCoeffs]
  exact Fintype.sum_equiv (Fintype.equivFin (ι × Fin N)).symm _ _ fun t => by simp

/-- **Gaussian preimages**: the discrete Gaussian of width `τ` on the solutions of
`∑_c L_c z_c = y`, or `none` if there are none. -/
noncomputable def gaussPreimage (L : ι → Negacyclic (ZMod q) N) (y : Negacyclic (ZMod q) N)
    (τ : ℝ) (hτ : 0 < τ) : Option (PMF (ι → Negacyclic (ZMod q) N)) :=
  (cosetGauss (rowRotFin L) y.coeffs τ hτ).map fun d => d.map ofIntCoeffs

/-- Every point drawn is a solution. -/
theorem gaussPreimage_mem (L : ι → Negacyclic (ZMod q) N) (y : Negacyclic (ZMod q) N) {τ : ℝ}
    (hτ : 0 < τ) {d : PMF (ι → Negacyclic (ZMod q) N)} (hd : gaussPreimage L y τ hτ = some d)
    {z : ι → Negacyclic (ZMod q) N} (hz : z ∈ d.support) : ∑ c, L c * z c = y := by
  unfold gaussPreimage at hd
  obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp hd
  rw [PMF.support_map] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  have h := cosetGauss_mem_coset _ _ τ hτ hd' hx
  rw [rowRotFin_mulVec] at h
  exact Negacyclic.ext h

/-- Preimages exist exactly when solutions do. -/
theorem gaussPreimage_isSome (L : ι → Negacyclic (ZMod q) N) (y : Negacyclic (ZMod q) N) {τ : ℝ}
    (hτ : 0 < τ) (h : ∃ z : ι → Negacyclic (ZMod q) N, ∑ c, L c * z c = y) [NeZero q] :
    (gaussPreimage L y τ hτ).isSome := by
  obtain ⟨z, hz⟩ := h
  unfold gaussPreimage
  rw [Option.isSome_map, cosetGauss_isSome_iff]
  refine ⟨fun t => ((z ((Fintype.equivFin (ι × Fin N)).symm t).1).coeffs
    ((Fintype.equivFin (ι × Fin N)).symm t).2).val, ?_⟩
  rw [rowRotFin_mulVec, ← hz]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  ext j
  simp [ofIntCoeffs]

end SigabaNeo.Lattices
