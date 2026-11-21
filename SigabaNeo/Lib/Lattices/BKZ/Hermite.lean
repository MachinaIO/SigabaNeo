module

public import Mathlib

/-! # Minkowski's cube bound

For full lattices in real coordinate space the squared Euclidean length of some nonzero
vector is at most k times the squared covolume root. Uses Minkowski's convex body theorem
with a closed cube. This bound need not give the optimal Hermite constant.
-/

open MeasureTheory Metric Module ZSpan
public section

namespace SigabaNeo.BKZ

theorem hermite_cube {k : ℕ} [NeZero k] (L : Submodule ℤ (Fin k → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ v : L, v ≠ 0 ∧ ∑ i, (v.val i)^2 ≤
      k * (ZLattice.covolume L ^ (1/(k:ℝ)))^2 := by
  let D := ZLattice.covolume L
  let R := D ^ (1/(k:ℝ))
  have hp : 0 < D := ZLattice.covolume_pos L volume
  have hk : (k:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne k
  have hr : 0 ≤ R := Real.rpow_nonneg hp.le _
  have hrk : R^k = D := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
    simp [hk]
  let b := Free.chooseBasis ℤ L
  have fund := ZLattice.isAddFundamentalDomain b volume
  have vol : volume (fundamentalDomain (b.ofZLatticeBasis ℝ)) = ENNReal.ofReal D := by
    rw [show D = _ from ZLattice.covolume_eq_measure_fundamentalDomain L volume fund]
    exact (ENNReal.ofReal_toReal (fundamentalDomain_isBounded _).measure_lt_top.ne).symm
  have dim : Module.finrank ℝ (Fin k → ℝ) = k := by simp
  have size : volume (fundamentalDomain (b.ofZLatticeBasis ℝ)) * 2 ^ Module.finrank ℝ (Fin k → ℝ) ≤
      volume (closedBall (0 : Fin k → ℝ) R) := by
    rw [vol, dim, Real.volume_pi_closedBall _ hr, Fintype.card_fin, mul_pow, hrk,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
    simp [mul_comm]
  let : Countable L.toAddSubgroup := (inferInstance : Countable L)
  let : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
  obtain ⟨v,hv,hm⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (L := L.toAddSubgroup) fund (fun x hx ↦ by simpa using hx)
    (convex_closedBall _ _) (isCompact_closedBall _ _) size
  refine ⟨v,hv,?_⟩
  have bound : ‖(v.val : Fin k → ℝ)‖ ≤ R := by simpa using hm
  calc
    _ ≤ ∑ _ : Fin k, R^2 := Finset.sum_le_sum fun i _ ↦ by
      have hi := (norm_le_pi_norm v.val i).trans bound
      simpa [Real.norm_eq_abs] using (sq_le_sq₀ (abs_nonneg _) hr).mpr hi
    _ = _ := by simp [R,D]

end SigabaNeo.BKZ
