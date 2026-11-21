module

public import SigabaNeo.Lib.Lattices.BKZ.Profile
public import SigabaNeo.Lib.Lattices.BKZ.Hermite
public import SigabaNeo.Lib.Lattices.BKZ.Geometry

/-! # Fully reduced block profiles

Minkowski's cube bound and a logPrefix-sum comparison bound the first vector given projected
block data. For a reduced basis the data are constructed in GSO coordinates. The final
estimate uses the cube constant. A shortest-vector approximation factor remains open. See Hanrot–Pujol–Stehlé (2011) for finite-tour analysis.
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

noncomputable section

open InnerProductSpace

variable {n β : ℕ} (b : Fin n → EuclideanSpace ℝ (Fin n)) (hb : LinearIndependent ℝ b)

/-- Fully reduced means the leading GSO vector is shortest in each projected block,
with Euclidean squared length computed in orthonormal coordinates. -/
def Reduced (β : ℕ) : Prop :=
  ∀ (i : Fin n) (v : blockLattice b hb
    (i := i.val) (k := min β (n-i.val)) (by omega)), v ≠ 0 →
    ‖gramSchmidt ℝ b i‖ ^ 2 ≤ ∑ j, (v.val j)^2

def basisLog (j : ℕ) : ℝ :=
  if h : j < n then Real.log ‖gramSchmidt ℝ b ⟨j,h⟩‖ else 0

private theorem block_log (i k : ℕ) (h : i+k ≤ n) :
    Real.log (ZLattice.covolume (blockLattice b hb h)) =
      logPrefix (basisLog b) (i+k) - logPrefix (basisLog b) i := by
  rw [blockLattice_covolume, Real.log_prod (fun j _ ↦
    norm_ne_zero_iff.mpr (gramSchmidt_ne_zero _ hb))]
  simp only [logPrefix, Finset.sum_range_add, add_sub_cancel_left]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp [basisLog, blockIndex, show i+j.val < n by omega]

/-- Concrete projected-block data for a reduced family. -/
def reducedProjectedBlock (hr : Reduced b hb β) (i : ℕ) (hi : i < n) :
    ProjectedBlock (basisLog b) i (min β (n-i)) where
  lattice := blockLattice b hb (i := i) (by omega)
  discrete := inferInstance
  full := inferInstance
  logCovol := block_log b hb _ _ _
  shortest := by
    intro v hv
    have hp := norm_pos_iff.mpr (gramSchmidt_ne_zero (⟨i,hi⟩ : Fin n) hb)
    simpa [basisLog, hi, two_mul, Real.exp_add, Real.exp_log hp, sq] using hr ⟨i,hi⟩ v hv

/-- First-vector estimate with the determinant expressed as the product of GSO lengths. -/
theorem reduced_first_norm_bound (hr : Reduced b hb β) (hβ : 2 ≤ β) (hn : β ≤ n) :
    ‖b ⟨0, by omega⟩‖ ≤ (β:ℝ) ^ (((n:ℝ)-1)/(2*((β:ℝ)-1))+1/2) *
      (∏ j, ‖gramSchmidt ℝ b j‖) ^ (1/(n:ℝ)) := by
  have hn' : 0 < n := by omega
  let : NeZero n := ⟨hn'.ne'⟩
  apply first_norm_bound hβ hn (reducedProjectedBlock b hb hr)
  · rw [basisLog, dite_eq_left hn', Real.exp_log (norm_pos_iff.mpr (gramSchmidt_ne_zero _ hb))]
    rw [gramSchmidt_def]
    have h : Finset.Iio (⟨0, hn'⟩ : Fin n) = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr fun j hj ↦
        Nat.not_lt_zero j.val (show j < (⟨0, hn'⟩ : Fin n) from Finset.mem_Iio.mp hj)
    rw [h, Finset.sum_empty, sub_zero]
  · rw [logPrefix, ← Fin.sum_univ_eq_sum_range, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro j _
    simp [basisLog, j.isLt, Real.exp_log (norm_pos_iff.mpr (gramSchmidt_ne_zero j hb))]

/-- First-vector estimate directly in terms of ambient lattice covolume. -/
theorem reduced_first_norm_bound_covolume
    (a : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (hr : Reduced a a.linearIndependent β) (hβ : 2 ≤ β) (hn : β ≤ n) :
    ‖a ⟨0, by omega⟩‖ ≤ (β:ℝ) ^ (((n:ℝ)-1)/(2*((β:ℝ)-1))+1/2) *
      ZLattice.covolume (Submodule.span ℤ (Set.range a)) ^ (1/(n:ℝ)) := by
  rw [basis_covolume]
  exact reduced_first_norm_bound a a.linearIndependent hr hβ hn

end

end SigabaNeo.BKZ
