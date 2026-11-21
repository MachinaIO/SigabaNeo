module

public import SigabaNeo.Lib.Lattices.BKZ.Profile
public import SigabaNeo.Lib.Lattices.BKZ.Hermite

/-! # Fully reduced block profiles

Minkowski's cube bound and a logPrefix-sum comparison bound the first vector given projected
block data. See Hanrot–Pujol–Stehlé (2011) for finite-tour analysis.
-/

public section

namespace SigabaNeo.BKZ

/-- Coordinate data required of each projected block. The covolume identity and the
comparison with every nonzero vector are the geometric obligations of the caller. -/
structure ProjectedBlock (r : ℕ → ℝ) (i k : ℕ) where
  lattice : Submodule ℤ (Fin k → ℝ)
  discrete : DiscreteTopology lattice
  full : IsZLattice ℝ lattice
  shortest : ∀ v : lattice, v ≠ 0 → Real.exp (2*r i) ≤ ∑ j, (v.val j)^2
  logCovol : Real.log (ZLattice.covolume lattice) = logPrefix r (i+k) - logPrefix r i

theorem projected_profile {r : ℕ → ℝ} {n β : ℕ} (hb : 2 ≤ β)
    (blocks : ∀ i < n, ProjectedBlock r i (min β (n-i))) :
    BlockProfile r n β (Real.log β / 2) := by
  intro i hi
  let k := min β (n-i)
  have hk : 0 < k := by dsimp [k]; omega
  have : NeZero k := ⟨hk.ne'⟩
  let b : ProjectedBlock r i k := blocks i hi
  let _ := b.discrete
  let _ := b.full
  obtain ⟨v,hv,hs⟩ := hermite_cube b.lattice
  have hd := ZLattice.covolume_pos b.lattice MeasureTheory.volume
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hβ : (0:ℝ) < β := by exact_mod_cast (show 0 < β by omega)
  have hkβ : (k:ℝ) ≤ β := by exact_mod_cast min_le_left β (n-i)
  have hx := Real.log_le_log (Real.exp_pos _) ((b.shortest v hv).trans hs)
  rw [Real.log_exp, Real.log_mul hk'.ne' (pow_ne_zero _ (Real.rpow_pos_of_pos hd _).ne'),
    Real.log_pow, Real.log_rpow hd, b.logCovol] at hx
  have hl := Real.log_le_log hk' hkβ
  change (k:ℝ)*r i ≤ k*(Real.log β/2) + logPrefix r (i+k) - logPrefix r i
  field_simp at hx
  norm_num at hx
  nlinarith [mul_le_mul_of_nonneg_left hl hk'.le]

/-- First-vector estimate when the caller identifies log lengths, determinant and blocks. -/
theorem first_norm_bound {E : Type*} [NormedAddCommGroup E] {v : E} {D : ℝ}
    {r : ℕ → ℝ} {n β : ℕ} (hb : 2 ≤ β) (hn : β ≤ n)
    (blocks : ∀ i < n, ProjectedBlock r i (min β (n-i)))
    (hv : ‖v‖ = Real.exp (r 0)) (hd : D = Real.exp (logPrefix r n)) :
    ‖v‖ ≤ (β:ℝ) ^ (((n:ℝ)-1)/(2*((β:ℝ)-1))+1/2) * D ^ (1/(n:ℝ)) := by
  have hβ : (1:ℝ) ≤ β := by exact_mod_cast (show 1 ≤ β by omega)
  have h := first_log_bound hb hn (div_nonneg (Real.log_nonneg hβ) (by norm_num))
    (projected_profile hb blocks)
  rw [hv, hd, Real.rpow_def_of_pos (by linarith : (0:ℝ) < β), ← Real.exp_mul,
    ← Real.exp_add, Real.exp_le_exp]
  linarith only [show r 0 - logPrefix r n / n ≤
      Real.log β * (((n:ℝ)-1)/(2*((β:ℝ)-1))+1/2) by
        convert h using 1
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring,
    show logPrefix r n * (1/(n:ℝ)) = logPrefix r n / n by ring]

end SigabaNeo.BKZ
