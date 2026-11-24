import SigabaNeo.Lib.Lattices.Flood
import SigabaNeo.Lib.Lattices.Homomorphic.Norm

/-!
# Noise flooding of one ring element and of independent families

`floodRing N Q W`: one element of `ℤ_Q[X]/(X^N + 1)` with independent coefficients uniform in
`{0, …, W − 1}` (the one-element case of `floodLaw`). Adding a fixed `δ` moves it by at most
`∑ⱼ |δⱼ| / W` (`closeTo_floodRing_add`), hence by at most `N B / W` when `cnorm δ ≤ B`
(`closeTo_floodRing_add_le`); independent families of such elements, shifted entrywise, move by at
most the number of entries times `N B / W` (`closeTo_pi_floodRing_add_le`).
-/

namespace SigabaNeo.Lattices

open Cslib Cslib.Probability
open scoped ENNReal

variable {N Q : ℕ} [NeZero Q]

/-- One ring element with independent coefficients uniform in `{0, …, W − 1}`. -/
noncomputable def floodRing (N Q W : ℕ) [NeZero Q] [NeZero W] : PMF (Negacyclic (ZMod Q) N) :=
  (PMF.uniformOfFintype (Fin N → Fin W)).map fun T =>
    Negacyclic.ofCoeffs fun j => ((T j : ℕ) : ZMod Q)

/-- **Flooding of one ring element.** -/
theorem closeTo_floodRing_add (W : ℕ) [NeZero W] (δ : Negacyclic (ZMod Q) N) :
    CloseTo ((floodRing N Q W).map (· + δ)) (floodRing N Q W)
      (ENNReal.ofReal (∑ j : Fin N, (zabs (δ.coeffs j) : ℝ) / W)) := by
  set c : Fin N → ℤ := fun j => -ZMod.valMinAbs (δ.coeffs j)
  have h := dist_shift_pi (Q := Q) (ι := Fin N) W c
  have hc := closeTo_of_dist h
  have hm := hc.map fun v : Fin N → ZMod Q => Negacyclic.ofCoeffs v
  rw [PMF.map_comp, PMF.map_comp] at hm
  unfold floodRing
  rw [PMF.map_comp]
  convert hm using 2
  · funext T
    apply Negacyclic.ext
    funext j
    simp only [Function.comp_apply, Negacyclic.coeffs_add, Negacyclic.coeffs_ofCoeffs, c,
      Int.cast_neg, sub_neg_eq_add, ZMod.coe_valMinAbs, Pi.add_apply]
  · rfl
  · exact Finset.sum_congr rfl fun j _ => by simp only [c, Int.natAbs_neg, zabs]

omit [NeZero Q] in
/-- `∑ⱼ |δⱼ| / W ≤ N B / W` for `cnorm δ ≤ B`. -/
theorem ofReal_sum_zabs_le (W : ℕ) [NeZero W] (δ : Negacyclic (ZMod Q) N) {B : ℕ}
    (hδ : cnorm δ ≤ B) :
    ENNReal.ofReal (∑ j : Fin N, (zabs (δ.coeffs j) : ℝ) / W) ≤ ((N * B : ℕ) : ℝ≥0∞) / W := by
  have hW : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hs : ∑ j : Fin N, (zabs (δ.coeffs j) : ℝ) / W ≤ ((N * B : ℕ) : ℝ) / W := by
    rw [← Finset.sum_div]
    refine div_le_div_of_nonneg_right ?_ hW.le
    calc ∑ j : Fin N, (zabs (δ.coeffs j) : ℝ) ≤ ∑ _j : Fin N, (B : ℝ) :=
          Finset.sum_le_sum fun j _ => by exact_mod_cast (zabs_coeffs_le_cnorm δ j).trans hδ
      _ = ((N * B : ℕ) : ℝ) := by simp
  refine (ENNReal.ofReal_le_ofReal hs).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_div_of_pos hW, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

/-- **Flooding of one ring element**, for a shift of norm at most `B`: within `N B / W`. -/
theorem closeTo_floodRing_add_le (W : ℕ) [NeZero W] (δ : Negacyclic (ZMod Q) N) {B : ℕ}
    (hδ : cnorm δ ≤ B) :
    CloseTo ((floodRing N Q W).map (· + δ)) (floodRing N Q W) (((N * B : ℕ) : ℝ≥0∞) / W) :=
  (closeTo_floodRing_add W δ).mono (ofReal_sum_zabs_le W δ hδ)

/-- **Flooding of independent families**: each entry shifted by at most `B` in norm; within the
number of entries times `N B / W`. -/
theorem closeTo_pi_floodRing_add_le {ι : Type} [Fintype ι] [DecidableEq ι] (W : ℕ) [NeZero W]
    (δ : ι → Negacyclic (ZMod Q) N) {B : ℕ} (hδ : ∀ i, cnorm (δ i) ≤ B) :
    CloseTo ((PMF.pi fun _ : ι => floodRing N Q W).map (· + δ))
      (PMF.pi fun _ : ι => floodRing N Q W) (Fintype.card ι * (((N * B : ℕ) : ℝ≥0∞) / W)) := by
  have e : (PMF.pi fun _ : ι => floodRing N Q W).map (· + δ) =
      PMF.pi fun i => (floodRing N Q W).map (· + δ i) := by
    rw [PMF.pi_map]; rfl
  rw [e]
  have h := closeTo_pi (fun i => (floodRing N Q W).map (· + δ i)) (fun _ => floodRing N Q W)
    (fun _ => ((N * B : ℕ) : ℝ≥0∞) / W) fun i => closeTo_floodRing_add_le W (δ i) (hδ i)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h

end SigabaNeo.Lattices
