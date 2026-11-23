module

public import SigabaNeo.Lib.Lattices.Research.Wall1.AdrsGaussianBins
import all SigabaNeo.Lib.Lattices.Research.Wall1.AdrsGaussianBins
import all SigabaNeo.Lib.Lattices.Research.Wall1.AdrsMidpoint
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Tactic

/-! The shifted squared-class law from ADS §4 and the class-conditional law from ASD
Lemma 3.1. The midpoint retains the target shift and the half-difference is centered. -/

@[expose] public section
noncomputable section
namespace SigabaNeo.Wall1.CVP638

open SigabaNeo.Wall1.ADRS ProbabilityTheory ZLattice Cslib.Probability.PMF
open scoped ENNReal RealInnerProductSpace

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
variable (L : Submodule ℤ E) (b : Module.Basis ι ℤ L) [FiniteDimensional ℝ E]
variable [DiscreteTopology L] {s : ℝ} (hs : 0 < s) (t : E)

theorem shiftedMatch_possible :
    ∃ z ∈ parityMatch L b, z ∈ (independentPair (discreteGaussian L s hs t)).support := by
  refine ⟨(0,0), rfl, ?_⟩
  rw [PMF.mem_support_iff, independentPair, bind_map_prodMk_apply]
  apply mul_ne_zero <;> apply (PMF.mem_support_iff ..).mp <;> simp

/-- The unconditional product in midpoint and half-difference coordinates gives the
conditioned pair, including the normalization constant, for every shift. -/
theorem shifted_pair_law :
    (independentPair (discreteGaussian L s hs t)).filter (parityMatch L b)
      (shiftedMatch_possible L b hs t) =
    ((discreteGaussian L (s/√2) (by positivity) t).bind fun u ↦
      (discreteGaussian L (s/√2) (by positivity) 0).map (u,·)).map (endpoints L) := by
  classical
  let w := s / √2
  have hw : 0 < w := by dsimp [w]; positivity
  let P := independentPair (discreteGaussian L s hs t)
  let Q := ((discreteGaussian L w hw t).bind fun u ↦
    (discreteGaussian L w hw 0).map (u,·)).map (endpoints L)
  let a := gaussianMass L w t * gaussianMass L w 0 / (gaussianMass L s t)^2
  have ha : 0 < a := div_pos (mul_pos (gaussianMass_pos L _ hw _) (gaussianMass_pos L _ hw _))
    (sq_pos_of_pos (gaussianMass_pos L _ hs _))
  have factor (z : L × L) : (parityMatch L b).indicator P z = Q z * ENNReal.ofReal a := by
    by_cases hz : z ∈ parityMatch L b
    · rw [Set.indicator_of_mem hz]
      rw [← endpoints_range] at hz
      obtain ⟨⟨u,v⟩,rfl⟩ := hz
      unfold Q
      rw [map_apply_of_injective _ (endpoints_injective L)]
      apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (ENNReal.mul_ne_top
        (PMF.apply_ne_top _ _) ENNReal.ofReal_ne_top)).mp
      simp only [P, independentPair, bind_map_prodMk_apply, ENNReal.toReal_mul,
        discreteGaussian_apply_toReal, ENNReal.toReal_ofReal ha.le, sub_zero,
        endpoints, Submodule.coe_add, Submodule.coe_sub]
      have rot := gaussianWeight_pair hs (((u:E)+v)-t) (((u:E)-v)-t)
      rw [show (1/2:ℝ) • ((((u:E)+v)-t) + ((u-v:E)-t)) = u-t by module,
        show (1/2:ℝ) • ((((u:E)+v)-t) - ((u-v:E)-t)) = v by module] at rot
      dsimp only [a]
      field_simp [(gaussianMass_pos L _ hs t).ne', (gaussianMass_pos L _ hw 0).ne',
        (gaussianMass_pos L _ hw t).ne']
      linear_combination (norm := ring) rot
    · rw [Set.indicator_of_notMem hz, (PMF.apply_eq_zero_iff Q _).mpr ?_, zero_mul]
      dsimp only [Q]
      rw [PMF.support_map]
      rintro ⟨p, _, rfl⟩
      exact hz (endpoints_range L b ▸ Set.mem_range_self p)
  have mass : P.toOuterMeasure (parityMatch L b) = ENNReal.ofReal a := by
    rw [PMF.toOuterMeasure_apply]
    simp only [factor, ENNReal.tsum_mul_right, Q.tsum_coe, one_mul]
  change P.filter _ _ = Q
  ext z
  rw [PMF.filter_apply, ← PMF.toOuterMeasure_apply, mass, factor, mul_assoc,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr ha).ne' ENNReal.ofReal_ne_top, mul_one]

variable {r : ℕ} (e : (ι → ZMod 2) ≃ Fin r)

theorem shiftedBin_possible (c : Fin r) : ∃ v ∈ {x | binLabel L b e x = c},
    v ∈ (discreteGaussian L s hs t).support := by
  obtain ⟨x,hx⟩ := coefficientMod_surjective L b 2 (e.symm c)
  exact ⟨x, by simp [binLabel,hx], by simp⟩

def restricted (c : Fin r) : PMF L :=
  fiberLaw _ (binLabel L b e) (shiftedBin_possible L b hs t e) c

def averageLaw (c : Fin r) : PMF L :=
  (independentPair (restricted L b hs t e c)).map (fun z ↦ latticeMidpoint L z.1 z.2)

def labelLaw := (discreteGaussian L s hs t).map (binLabel L b e)

private theorem tagged_midpoints :
    ((squaredLabels (labelLaw L b hs t e)).bind fun c ↦ (averageLaw L b hs t e c).map (c,·)) =
      ((discreteGaussian L (s/√2) (by positivity) t).bind fun u ↦
        (discreteGaussian L (s/√2) (by positivity) 0).map (u,·)).map (fun z ↦ (binLabel L b e (z.1 + z.2), z.1)) := by
  classical
  let μ := discreteGaussian L s hs t
  let label := binLabel L b e
  let F (z : L × L) := (label z.1, latticeMidpoint L z.1 z.2)
  have he : {z : L × L | label z.1 = label z.2} = parityMatch L b := by
    ext z
    exact e.injective.eq_iff
  have hp : ∃ z ∈ {z : L × L | label z.1 = label z.2}, z ∈ (independentPair μ).support := by
    rw [he]; exact shiftedMatch_possible L b hs t
  have hh := squaredLabels_pair μ label (shiftedBin_possible L b hs t e) hp
  simp only [he] at hh
  rw [shifted_pair_law] at hh
  have htag (c) : (independentPair (restricted L b hs t e c)).map F =
      (averageLaw L b hs t e c).map (c,·) := by
    rw [averageLaw, PMF.map_comp]
    apply map_congr_on_support
    intro z hz
    have hmem := (PMF.mem_support_bind_iff ..).mp hz
    obtain ⟨x,hx,hz'⟩ := hmem
    obtain ⟨y,_,rfl⟩ := (PMF.mem_support_map_iff ..).mp hz'
    have hx' := (PMF.mem_support_filter_iff (shiftedBin_possible L b hs t e c)).mp hx
    exact Prod.ext hx'.1 rfl
  have hh' := congrArg (PMF.map F) hh
  rw [PMF.map_bind, PMF.map_comp] at hh'
  change ((squaredLabels (labelLaw L b hs t e)).bind fun c ↦
    (independentPair (restricted L b hs t e c)).map F) = _ at hh'
  simp_rw [htag] at hh'
  convert hh' using 2
  funext z
  exact Prod.ext rfl (midpoint_endpoints L z).symm

/-- Mixing the fixed-bin averages with squared label weights gives I2. -/
theorem shifted_squared_labels :
    (squaredLabels (labelLaw L b hs t e)).bind (averageLaw L b hs t e) =
      discreteGaussian L (s/√2) (by positivity) t := by
  have h := congrArg (PMF.map Prod.snd) (tagged_midpoints L b hs t e)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at h
  convert h using 1
  · congr 1; funext c; exact (PMF.map_id _).symm
  · simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def] using
      (map_fst_bind_pair (discreteGaussian L (s/√2) (by positivity) t)
        (fun _ ↦ discreteGaussian L (s/√2) (by positivity) 0)).symm

/-- Conditional on its output label, a fixed-bin average has the narrow Gaussian
restricted to that output bin. This is the conditional independence needed by histories. -/
theorem shifted_resample (c : Fin r) :
    ((averageLaw L b hs t e c).map (binLabel L b e)).bind
      (restricted L b (s := s/√2) (by positivity) t e) = averageLaw L b hs t e c := by
  let ν := discreteGaussian L (s/√2) (by positivity) t
  let R (d : Fin r) := (discreteGaussian L (s/√2) (by positivity) 0).map
    fun v ↦ e (e.symm d + coefficientMod L b 2 v)
  apply fiber_resample (squaredLabels (labelLaw L b hs t e)) _ ν _ R
    (shiftedBin_possible L b (s := s/√2) (by positivity) t e)
  · intro j
    rw [squaredLabels_apply, div_eq_mul_inv]
    exact mul_ne_zero (pow_ne_zero _ (labelMass_ne_zero _ _ (shiftedBin_possible L b hs t e) _))
      (ENNReal.inv_ne_zero.mpr (collisionMass_ne_top _))
  · rw [tagged_midpoints]
    simp only [R, PMF.map_bind, PMF.map_comp, Function.comp_def, binLabel,
      Equiv.symm_apply_apply, map_add, ν]

end SigabaNeo.Wall1.CVP638

#print axioms SigabaNeo.Wall1.CVP638.shifted_pair_law
#print axioms SigabaNeo.Wall1.CVP638.shifted_squared_labels
#print axioms SigabaNeo.Wall1.CVP638.shifted_resample
