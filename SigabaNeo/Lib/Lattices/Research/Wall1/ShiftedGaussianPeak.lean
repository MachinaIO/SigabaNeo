module

public import SigabaNeo.Lib.Lattices.Research.Wall1.ShiftedGaussianError
import all SigabaNeo.Lib.Lattices.Research.Wall1.ShiftedGaussianPair
import Mathlib.Tactic

/-! The old parity label of a collided pair is a mixture of translates of the new
midpoint label. This gives the shifted heaviest-class inequality at arbitrary widths. -/

@[expose] public section
noncomputable section
namespace SigabaNeo.Wall1.CVP638

open SigabaNeo.Wall1.ADRS ProbabilityTheory ZLattice Cslib.Probability.PMF MeasureTheory
open scoped ENNReal NNReal

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
variable (L : Submodule ℤ E) (b : Module.Basis ι ℤ L) {r : ℕ} (e : (ι → ZMod 2) ≃ Fin r)
variable [FiniteDimensional ℝ E] [DiscreteTopology L] {s : ℝ} (hs : 0 < s) (t : E)

theorem squared_label_le_next {p : ℝ≥0∞}
    (h : ∀ c, labelLaw L b (s := s/√2) (by positivity) t e c ≤ p) (c : Fin r) :
    squaredLabels (labelLaw L b hs t e) c ≤ p := by
  let D := discreteGaussian L (s/√2) (by positivity) t
  let H := discreteGaussian L (s/√2) (by positivity) 0
  let q := squaredLabels (labelLaw L b hs t e)
  let key := binLabel L b e
  have eqn : q = H.bind (fun z ↦ D.map fun a ↦ key (a+z)) := by
    calc q = (q.bind fun j ↦ (averageLaw L b hs t e j).map (j,·)).map Prod.fst :=
           (map_fst_bind_pair ..).symm
         _ = _ := by
           rw [show q = _ from rfl, tagged_midpoints]
           simp only [PMF.map_comp, PMF.map_bind, Function.comp_def]
           simp only [PMF.map]
           exact PMF.bind_comm ..
  change q c ≤ p
  rw [eqn, PMF.bind_apply]
  calc _ ≤ ∑' z, H z * p := by
         apply tsum_le_tsum
         intro z
         apply mul_le_mul_right
         let perm := (e.symm.trans (Equiv.addRight (coefficientMod L b 2 z))).trans e
         have he : D.map (fun a ↦ key (a+z)) = (D.map key).map perm := by
           rw [PMF.map_comp]
           congr 1
           funext a
           simp [key, binLabel, perm, Function.comp_def]
         rw [he, map_equiv_apply]
         exact h _
       _ = p := by rw [ENNReal.tsum_mul_right, H.tsum_coe, one_mul]

/-- Maximum-mass label for any nonempty finite label type. -/
def peak {C : Type*} [Finite C] [Nonempty C] (q : PMF C) : C :=
  Classical.choose (Finite.exists_max fun c ↦ (q c).toNNReal)

theorem le_peak {C : Type*} [Finite C] [Nonempty C] (q : PMF C) (c : C) :
    (q c).toNNReal ≤ (q (peak q)).toNNReal :=
  Classical.choose_spec (Finite.exists_max fun c ↦ (q c).toNNReal) c

/-- Normalized form of F² ≤ U' F', using the exact shifted collision law. -/
theorem peak_square [NeZero r] :
    let q := labelLaw L b hs t e
    let q' := labelLaw L b (s := s/√2) (by positivity) t e
    (q (peak q)).toNNReal^2 ≤ (collisionMass q).toNNReal * (q' (peak q')).toNNReal := by
  intro q q'
  have h := squared_label_le_next L b e hs t (p := q' (peak q')) (fun c ↦ by
    exact (ENNReal.toNNReal_le_toNNReal (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
      (le_peak q' c)) (peak q)
  rw [squaredLabels_apply] at h
  change q (peak q)^2 / collisionMass q ≤ q' (peak q') at h
  have H := mul_le_mul_left h (collisionMass q)
  rw [ENNReal.div_mul_cancel (collisionMass_ne_zero q) (collisionMass_ne_top q), mul_comm] at H
  have R := ENNReal.toNNReal_mono (ENNReal.mul_ne_top (collisionMass_ne_top q)
    (PMF.apply_ne_top _ _)) H
  simpa only [ENNReal.toNNReal_pow, ENNReal.toNNReal_mul] using R

end SigabaNeo.Wall1.CVP638

#print axioms SigabaNeo.Wall1.CVP638.squared_label_le_next
#print axioms SigabaNeo.Wall1.CVP638.peak_square
