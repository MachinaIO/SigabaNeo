import SigabaNeo.Lib.Lattices.Gaussian.Tail
import SigabaNeo.Lib.Lattices.Gaussian.Bounds

/-!
# The tail of `D_{Z,σ}`

`gaussZ_tail`: for `σ ≥ 1`, `Pr_{x ← D_{Z,σ}}[|x| ≥ σ √M] ≤ 6 · 4^{−M}`. The lattice of `gaussZ` is
`Λ^⊥` of the empty matrix, i.e. `Z ⊂ R^1`; its nonzero dual mass at width `1/σ` is at most
`3 e^{−π σ²} ≤ 1/2`, and `gauss_tail_gen` applies.
-/

namespace SigabaNeo.Lattices

open SigabaNeo.Lattices ProbabilityTheory ZLattice MeasureTheory
open scoped ENNReal

/-- The matrix whose `Λ^⊥` is `Z`. -/
abbrev B0 : Matrix (Fin 0) (Fin 1) (ZMod 1) := 0

theorem exp_neg_three_le : Real.exp (-3) ≤ 1 / 6 := by
  have h := Real.quadratic_le_exp_of_nonneg (x := 3) (by norm_num)
  have hinv : Real.exp (-3) * Real.exp 3 = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-3)]

open Classical in
theorem dualMassE_B0 {σ : ℝ} (hσ : 1 ≤ σ) : dualMassE B0 σ ≤ 1 / 2 := by
  refine (dualMassE_le B0 σ).trans ?_
  have h1 : ∑' v : Fin 1 → ℤ, (if v ≠ 0 ∧ Orth B0 v then wt σ 1 v else 0) ≤
      ∑' u : Fin 1 → ℤ, wt1 σ u := by
    refine ENNReal.tsum_le_tsum fun v => ?_
    split_ifs with h
    · unfold wt wt1; rw [if_neg h.1]; simp
    · exact zero_le
  refine h1.trans ?_
  set x := Real.pi * σ ^ 2
  set R := Real.exp (-x)
  have hx : 3 ≤ x := by
    have h1 : 1 ≤ σ ^ 2 := by nlinarith
    have := mul_le_mul (le_of_lt Real.pi_gt_three) h1 (by norm_num) Real.pi_pos.le
    linarith
  have hR0 : 0 ≤ R := (Real.exp_pos _).le
  have hR : R ≤ 1 / 6 := (Real.exp_le_exp.mpr (by linarith)).trans exp_neg_three_le
  have hA : ∑' k : ℤ, g1 x k ≤ ENNReal.ofReal (1 + 3 * R) := by
    refine le_trans (tsum_g1_le_large (by positivity)) ?_
    rw [geom_eq hR0 (by linarith)]
    exact ENNReal.ofReal_le_ofReal (ratio_le hR0 (by linarith))
  have hZ := tsum_wt1_add_one (m := 1) σ
  rw [pow_one] at hZ
  have h2 : ∑' u : Fin 1 → ℤ, wt1 σ u + 1 ≤ ENNReal.ofReal (1 / 2) + 1 := by
    rw [hZ, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    exact hA.trans (ENNReal.ofReal_le_ofReal (by linarith))
  rw [half_ennreal]
  exact ENNReal.le_of_add_le_add_right ENNReal.one_ne_top h2

/-- A coordinate is at most the norm. -/
theorem abs_le_norm_embed {m : ℕ} (y : Fin m → ℤ) (i : Fin m) : |((y i : ℤ) : ℝ)| ≤ ‖embed m y‖ := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  have := Finset.single_le_sum (f := fun j => ‖(embed m y) j‖ ^ 2) (fun j _ => by positivity)
    (Finset.mem_univ i)
  simpa [embed] using this

theorem norm_embed_one (y : Fin 1 → ℤ) : ‖embed 1 y‖ = |((y 0 : ℤ) : ℝ)| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, ← Real.sqrt_sq_eq_abs]
  simp [embed]

theorem gaussZ_tail {σ : ℝ} (hσ : 1 ≤ σ) (hs : 0 < σ) (M : ℕ) :
    (gaussZ σ hs).toOuterMeasure {x : ℤ | σ * Real.sqrt M ≤ |(x : ℝ)|} ≤
      ENNReal.ofReal (6 * (1 / 4) ^ M) := by
  unfold gaussZ
  have hb : (ZLattice.discreteGaussian (perp B0) σ hs 0 >>= fun a =>
      pure (a : EuclideanSpace ℝ (Fin 1))) =
      (ZLattice.discreteGaussian (perp B0) σ hs 0).map Subtype.val := rfl
  have hnum : ENNReal.ofReal (3 * 2 ^ 1 * (1 / 4) ^ M) = ENNReal.ofReal (6 * (1 / 4) ^ M) := by
    congr 1; ring
  rw [PMF.toOuterMeasure_map_apply, hb, PMF.toOuterMeasure_map_apply, ← hnum]
  refine le_trans (measure_mono ?_) (gauss_tail_gen B0 hs (dualMassE_B0 hσ) 0 M)
  intro z hz
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hz ⊢
  obtain ⟨y, -, hy⟩ := Submodule.mem_map.mp z.2
  rw [sub_zero, ← hy, norm_embed_one]
  rw [← hy, toInt_embed] at hz
  exact hz

end SigabaNeo.Lattices
