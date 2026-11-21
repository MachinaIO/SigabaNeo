module

public import Mathlib

/-! # Minkowski's cube bound

For full lattices in real coordinate space the squared Euclidean length of some nonzero
vector is at most k times the squared covolume root. Uses Minkowski's convex body theorem
with a closed cube. The Euclidean ball gives a second bound in terms of its unit volume.
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

/-- The Minkowski ball radius in dimension k, expressed using the exact unit ball volume. -/
theorem hermite_ball {k : ℕ} [NeZero k] (L : Submodule ℤ (EuclideanSpace ℝ (Fin k)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ v : L, v ≠ 0 ∧ ‖v.val‖ ≤ 2 * (ZLattice.covolume L /
      (Real.sqrt Real.pi ^ k / Real.Gamma ((k:ℝ)/2 + 1))) ^ (1/(k:ℝ)) := by
  let U := Real.sqrt Real.pi ^ k / Real.Gamma ((k:ℝ)/2 + 1)
  let D := ZLattice.covolume L
  let R := (D/U) ^ (1/(k:ℝ))
  have hU : 0 < U := div_pos (pow_pos (Real.sqrt_pos.2 Real.pi_pos) _)
    (Real.Gamma_pos_of_pos (by positivity))
  have hD : 0 < D := ZLattice.covolume_pos L volume
  have hk : (k:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne k
  have hR : 0 < R := Real.rpow_pos_of_pos (div_pos hD hU) _
  have powR : R^k = D/U := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_pos hD hU).le]
    simp [hk]
  let b := Free.chooseBasis ℤ L
  have fund := ZLattice.isAddFundamentalDomain b volume
  have vol : volume (fundamentalDomain (b.ofZLatticeBasis ℝ)) = ENNReal.ofReal D := by
    rw [show D = _ from ZLattice.covolume_eq_measure_fundamentalDomain L volume fund]
    exact (ENNReal.ofReal_toReal (fundamentalDomain_isBounded _).measure_lt_top.ne).symm
  have size : volume (fundamentalDomain (b.ofZLatticeBasis ℝ)) *
      2 ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) ≤
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) (2*R)) := by
    rw [vol, EuclideanSpace.volume_closedBall, finrank_euclideanSpace, Fintype.card_fin]
    change ENNReal.ofReal D * 2^k ≤ ENNReal.ofReal (2*R)^k * ENNReal.ofReal U
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
      mul_pow, powR, mul_assoc, div_mul_cancel₀ D hU.ne',
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
    simp [mul_comm]
  let : Countable L.toAddSubgroup := (inferInstance : Countable L)
  let : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
  obtain ⟨v,hv,hm⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (L := L.toAddSubgroup) fund (fun x hx ↦ by simpa using hx)
    (convex_closedBall _ _) (isCompact_closedBall _ _) size
  exact ⟨v,hv,by simpa [R,U,D] using hm⟩

end SigabaNeo.BKZ
