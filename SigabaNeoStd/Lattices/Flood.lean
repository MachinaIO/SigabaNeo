import SigabaNeoStd.Lattices.Stat
import SigabaNeoStd.Lattices.LeftoverHash
import CslibFrontier.Foundations.Algebra.Negacyclic
import Mathlib.Data.ZMod.ValMinAbs

/-!
# Noise flooding over `ℤ_q[X]/(X^N + 1)`

`floodLaw ι W` draws a family of ring elements indexed by `ι` whose coefficients are independent and
uniform in `{0, …, W − 1}`. Adding a fixed family `δ` moves this law by at most
`∑ᵢ ∑ⱼ |δᵢⱼ| / W` in statistical distance, with `|δᵢⱼ|` the centered absolute value of the
coefficients (`closeTo_floodLaw_add`): wide uniform errors hide small ones.
-/

namespace SigabaNeo.Lattices

open Cslib Cslib.Probability
open scoped ENNReal Cslib.Probability.PMF

variable {N Q : ℕ} [NeZero Q]

/-- Ring elements with independent coefficients uniform in `{0, …, W − 1}`. -/
noncomputable def floodLaw (ι : Type) [Fintype ι] [DecidableEq ι] (W : ℕ) [NeZero W] :
    PMF (ι → Negacyclic (ZMod Q) N) :=
  (PMF.uniformOfFintype (ι × Fin N → Fin W)).map fun T i =>
    Negacyclic.ofCoeffs fun j => ((T (i, j) : ℕ) : ZMod Q)

/-- **Flooding.** -/
theorem closeTo_floodLaw_add (ι : Type) [Fintype ι] [DecidableEq ι] (W : ℕ) [NeZero W]
    (δ : ι → Negacyclic (ZMod Q) N) :
    CloseTo ((floodLaw (N := N) (Q := Q) ι W).map fun e i => e i + δ i)
      (floodLaw (N := N) (Q := Q) ι W)
      (ENNReal.ofReal (∑ ij : ι × Fin N, ((ZMod.valMinAbs ((δ ij.1).coeffs ij.2 : ZMod Q)).natAbs : ℝ) / W)) := by
  set c : ι × Fin N → ℤ := fun ij => -ZMod.valMinAbs ((δ ij.1).coeffs ij.2 : ZMod Q)
  have h := dist_shift_pi (Q := Q) (ι := ι × Fin N) W c
  have hc := closeTo_of_dist h
  have hm := hc.map fun v : ι × Fin N → ZMod Q => fun i => Negacyclic.ofCoeffs fun j => v (i, j)
  rw [PMF.map_comp, PMF.map_comp] at hm
  unfold floodLaw
  rw [PMF.map_comp]
  convert hm using 2
  · funext T i
    apply Negacyclic.ext
    funext j
    simp only [Function.comp_apply, Negacyclic.coeffs_add, Pi.add_apply, c, Int.cast_neg,
      sub_neg_eq_add, ZMod.coe_valMinAbs]
  · rfl
  · exact Finset.sum_congr rfl fun ij _ => by simp only [c, Int.natAbs_neg]

end SigabaNeo.Lattices
