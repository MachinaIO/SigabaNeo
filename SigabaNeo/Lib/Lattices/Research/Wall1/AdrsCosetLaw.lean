module

public import SigabaNeo.Lib.Lattices.Research.Wall1.AdrsMidpoint
public import CslibFrontier.Probability.PMF.Event
import Mathlib.Tactic

/-! # Disintegrating the equal-label pair law into its squared-weight bins -/

@[expose] public section

noncomputable section

namespace SigabaNeo.Wall1.ADRS

open Cslib.Probability.PMF
open scoped ENNReal

variable {V C : Type*} [Fintype C]

/-- Probability that two independent labels agree. -/
def collisionMass (q : PMF C) : ℝ≥0∞ := ∑ c, q c ^ 2

theorem collisionMass_ne_zero (q : PMF C) : collisionMass q ≠ 0 := by
  obtain ⟨c,hc⟩ := q.support_nonempty
  exact ne_of_gt ((pos_iff_ne_zero.mpr (pow_ne_zero 2 ((PMF.mem_support_iff ..).mp hc))).trans_le
    (Finset.single_le_sum (f := fun c ↦ q c ^ 2) (fun _ _ ↦ zero_le) (Finset.mem_univ c)))

theorem collisionMass_ne_top (q : PMF C) : collisionMass q ≠ ⊤ :=
  ENNReal.sum_ne_top.mpr fun c _ ↦ ENNReal.pow_ne_top (PMF.apply_ne_top q c)

/-- The input label of a random equal-label pair. -/
def squaredLabels (q : PMF C) : PMF C :=
  PMF.normalize (fun c ↦ q c ^ 2) (by rw [tsum_fintype]; exact collisionMass_ne_zero q)
    (by rw [tsum_fintype]; exact collisionMass_ne_top q)

theorem squaredLabels_apply (q : PMF C) (c : C) :
    squaredLabels q c = q c ^ 2 / collisionMass q := by
  simp only [squaredLabels, PMF.normalize_apply, tsum_fintype, div_eq_mul_inv, collisionMass]

variable (μ : PMF V) (label : V → C)
variable (hf : ∀ c, ∃ v ∈ {x | label x = c}, v ∈ μ.support)

/-- Distribution inside one (positive-probability) bin. -/
def fiberLaw (c : C) := μ.filter {x | label x = c} (hf c)

omit [Fintype C] in
theorem fiberLaw_apply [DecidableEq C] (c : C) (x : V) :
    fiberLaw μ label hf c x =
      (if label x = c then μ x else 0) / (μ.map label) c := by
  classical
  rw [fiberLaw, PMF.filter_apply, ← PMF.toOuterMeasure_apply,
    ← PMF.toOuterMeasure_apply_singleton (μ.map label), PMF.toOuterMeasure_map_apply]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, div_eq_mul_inv]
  rfl

omit [Fintype C] in
include hf in
theorem labelMass_ne_zero (c : C) : (μ.map label) c ≠ 0 := by
  obtain ⟨v,hv,hs⟩ := hf c
  exact (PMF.mem_support_iff ..).mp ((PMF.mem_support_map_iff ..).mpr ⟨v,hs,hv⟩)

/-- Mixing two independent within-bin draws with squared bin probabilities is the
conditioned independent product, as a joint law before taking averages. -/
theorem squaredLabels_pair (h : ∃ z ∈ {z : V × V | label z.1 = label z.2},
    z ∈ (independentPair μ).support) :
    (squaredLabels (μ.map label)).bind (fun c ↦ independentPair (fiberLaw μ label hf c)) =
      (independentPair μ).filter {z | label z.1 = label z.2} h := by
  classical
  let q := μ.map label
  let Q := (squaredLabels q).bind fun c ↦ independentPair (fiberLaw μ label hf c)
  let S : Set (V × V) := {z | label z.1 = label z.2}
  have hi (z : V × V) : S.indicator (independentPair μ) z = Q z * collisionMass q := by
    obtain ⟨x,y⟩ := z
    rw [show Q = (squaredLabels q).bind _ from rfl, PMF.bind_apply]
    simp only [independentPair, bind_map_prodMk_apply, fiberLaw_apply]
    rw [tsum_eq_single (label x)]
    · by_cases he : label x = label y
      · rw [Set.indicator_of_mem (show (x,y) ∈ S from he)]
        simp only [ite_eq_left he.symm, squaredLabels_apply, bind_map_prodMk_apply]
        change μ x * μ y = (q (label x)^2 / _ * (μ x / q (label x) * (μ y / q (label x)))) * _
        have hq := labelMass_ne_zero μ label hf (label x)
        have hc := collisionMass_ne_zero q
        apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
          (PMF.apply_ne_top _ _)) ?_).mp
        · simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow]
          have h₁ := (ENNReal.toReal_pos hq (PMF.apply_ne_top q _)).ne'
          have h₂ := (ENNReal.toReal_pos hc (collisionMass_ne_top q)).ne'
          change (q (label x)).toReal ≠ 0 at h₁
          field_simp [h₁,h₂]
        · apply ENNReal.mul_ne_top _ (collisionMass_ne_top q)
          apply ENNReal.mul_ne_top
          · rw [← squaredLabels_apply]; exact PMF.apply_ne_top _ _
          · apply ENNReal.mul_ne_top <;>
              exact ENNReal.div_ne_top (PMF.apply_ne_top _ _) hq
      · rw [Set.indicator_of_notMem (show (x,y) ∉ S from he)]
        simp [Ne.symm he]
    · intro c hc
      simp [Ne.symm hc]
  ext z
  rw [PMF.filter_apply]
  change Q z = S.indicator (independentPair μ) z * (∑' t, S.indicator (independentPair μ) t)⁻¹
  simp_rw [hi]
  rw [ENNReal.tsum_mul_right, Q.tsum_coe, one_mul, mul_assoc,
    ENNReal.mul_inv_cancel (collisionMass_ne_zero q) (collisionMass_ne_top q), mul_one]

end SigabaNeo.Wall1.ADRS

#print axioms SigabaNeo.Wall1.ADRS.squaredLabels_pair
