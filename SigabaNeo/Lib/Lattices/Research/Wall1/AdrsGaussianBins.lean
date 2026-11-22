module

public import SigabaNeo.Lib.Lattices.Research.Wall1.AdrsCosetLaw
import Mathlib.Tactic

/-! # Conditional Gaussian laws in each generation of labelled pairs -/

@[expose] public section

noncomputable section

namespace SigabaNeo.Wall1.ADRS

open Cslib.Probability.PMF ProbabilityTheory ZLattice
open scoped ENNReal NNReal

private theorem reverse_pair_apply {U V : Type*} (p : PMF U) (K : U → PMF V) (x : U) (y : V) :
    (p.bind fun u ↦ (K u).map (·,u)) (y,x) = p x * K x y := by
  let e := Equiv.prodComm U V
  have h : p.bind (fun u ↦ (K u).map (·,u)) = (p.bind fun u ↦ (K u).map (u,·)).map e := by
    simp only [PMF.map_bind, PMF.map_comp]; rfl
  rw [h, map_equiv_apply, bind_map_prodMk_apply]
  rfl

/-- Bayes' rule when the likelihood of the old label depends only on the new label. -/
private theorem fiber_resample {C V : Type*} [Fintype C] (p : PMF C) (M : C → PMF V)
    (μ : PMF V) (label : V → C) (R : C → PMF C)
    (hf : ∀ d, ∃ v ∈ {x | label x = d}, v ∈ μ.support)
    (hp : ∀ c, p c ≠ 0)
    (h : (p.bind fun c ↦ (M c).map (c,·)) =
      μ.bind fun x ↦ (R (label x)).map (·,x)) (c : C) :
    ((M c).map label).bind (fiberLaw μ label hf) = M c := by
  classical
  have hpt (x : V) : p c * M c x = μ x * R (label x) c := by
    simpa only [bind_map_prodMk_apply, reverse_pair_apply] using congrArg (· (c,x)) h
  have hlabel (d : C) : p c * (M c).map label d = (μ.map label) d * R d c := by
    simp only [PMF.map_apply, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro x
    by_cases hd : d = label x
    · simpa [hd] using hpt x
    · simp [hd]
  ext x
  rw [PMF.bind_apply, tsum_eq_single (label x)]
  · rw [fiberLaw_apply, ite_eq_left rfl]
    apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (ENNReal.div_ne_top (PMF.apply_ne_top _ _) (labelMass_ne_zero μ label hf _)))
      (PMF.apply_ne_top _ _)).mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div]
    have h₁ := congrArg ENNReal.toReal (hpt x)
    have h₂ := congrArg ENNReal.toReal (hlabel (label x))
    simp only [ENNReal.toReal_mul] at h₁ h₂
    have hp' := ENNReal.toReal_pos (hp c) (PMF.apply_ne_top p c)
    have hd := ENNReal.toReal_pos (labelMass_ne_zero μ label hf (label x)) (PMF.apply_ne_top _ _)
    field_simp [hd.ne']
    apply (mul_left_cancel₀ hp'.ne')
    linear_combination (μ x).toReal * h₂ - ((μ.map label) (label x)).toReal * h₁
  · intro d hd
    simp [fiberLaw_apply, Ne.symm hd]

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
variable (L : Submodule ℤ E) (b : Module.Basis ι ℤ L) {r : ℕ} (e : (ι → ZMod 2) ≃ Fin r)
variable [FiniteDimensional ℝ E] [DiscreteTopology L] {s : ℝ} (hs : 0 < s)

/-- Number the coefficient-parity labels with a finite index type. -/
def binLabel (x : L) : Fin r := e (coefficientMod L b 2 x)

theorem gaussianBin_possible (c : Fin r) : ∃ v ∈ {x | binLabel L b e x = c},
    v ∈ (discreteGaussian L s hs 0).support := by
  obtain ⟨x,hx⟩ := coefficientMod_surjective L b 2 (e.symm c)
  exact ⟨x, by simp [binLabel,hx], by simp⟩

/-- The individual endpoint law inside a coset. -/
def gaussianBin (c : Fin r) : PMF L :=
  fiberLaw _ (binLabel L b e) (gaussianBin_possible L b e hs) c

/-- Law of the midpoint of two independent endpoints in a specified input bin. -/
def binAverage (c : Fin r) : PMF L :=
  (independentPair (gaussianBin L b e hs c)).map (fun z ↦ latticeMidpoint L z.1 z.2)

/-- Input bin label before conditioning on a match. -/
def gaussianLabels := (discreteGaussian L s hs 0).map (binLabel L b e)

private theorem tagged_midpoints :
    ((squaredLabels (gaussianLabels L b e hs)).bind fun c ↦ (binAverage L b e hs c).map (c,·)) =
      (independentPair (discreteGaussian L (s/√2) (by positivity) 0)).map
        (fun z ↦ (binLabel L b e (z.1 + z.2), z.1)) := by
  classical
  let μ := discreteGaussian L s hs 0
  let label := binLabel L b e
  let F (z : L × L) := (label z.1, latticeMidpoint L z.1 z.2)
  have he : {z : L × L | label z.1 = label z.2} = parityMatch L b := by
    ext z
    exact e.injective.eq_iff
  have hp : ∃ z ∈ {z : L × L | label z.1 = label z.2}, z ∈ (independentPair μ).support := by
    rw [he]; exact parityMatch_possible L b hs
  have hh := squaredLabels_pair μ label (gaussianBin_possible L b e hs) hp
  simp only [he] at hh
  rw [conditional_pair_law] at hh
  have htag (c) : (independentPair (gaussianBin L b e hs c)).map F =
      (binAverage L b e hs c).map (c,·) := by
    rw [binAverage, PMF.map_comp]
    apply map_congr_on_support
    intro z hz
    have hmem := (PMF.mem_support_bind_iff ..).mp hz
    obtain ⟨x,hx,hz'⟩ := hmem
    obtain ⟨y,_,rfl⟩ := (PMF.mem_support_map_iff ..).mp hz'
    have hx' := (PMF.mem_support_filter_iff (gaussianBin_possible L b e hs c)).mp hx
    exact Prod.ext hx'.1 rfl
  have hh' := congrArg (PMF.map F) hh
  rw [PMF.map_bind, PMF.map_comp] at hh'
  change ((squaredLabels (gaussianLabels L b e hs)).bind fun c ↦
    (independentPair (gaussianBin L b e hs c)).map F) = _ at hh'
  simp_rw [htag] at hh'
  convert hh' using 2
  funext z
  exact Prod.ext rfl (midpoint_endpoints L z).symm

/-- Mixing the fixed-bin averages with squared label weights gives I2. -/
theorem squaredLabels_binAverage :
    (squaredLabels (gaussianLabels L b e hs)).bind (binAverage L b e hs) =
      discreteGaussian L (s/√2) (by positivity) 0 := by
  have h := congrArg (PMF.map Prod.snd) (tagged_midpoints L b e hs)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at h
  convert h using 1
  · congr 1; funext c; exact (PMF.map_id _).symm
  · exact (map_fst_bind_pair _ _).symm

/-- Conditional on its output label, a fixed-bin average has the narrow Gaussian
restricted to that output bin. This is the conditional independence needed by histories. -/
theorem binAverage_resample (c : Fin r) :
    ((binAverage L b e hs c).map (binLabel L b e)).bind
      (gaussianBin L b e (s := s/√2) (by positivity)) = binAverage L b e hs c := by
  let ν := discreteGaussian L (s/√2) (by positivity) 0
  let R (d : Fin r) := ν.map fun v ↦ e (e.symm d + coefficientMod L b 2 v)
  apply fiber_resample (squaredLabels (gaussianLabels L b e hs)) _ ν _ R
    (gaussianBin_possible L b e (s := s/√2) (by positivity))
  · intro j
    rw [squaredLabels_apply, div_eq_mul_inv]
    exact mul_ne_zero (pow_ne_zero _ (labelMass_ne_zero _ _ (gaussianBin_possible L b e hs) _))
      (ENNReal.inv_ne_zero.mpr (collisionMass_ne_top _))
  · rw [tagged_midpoints]
    simp only [independentPair, R, PMF.map_bind, PMF.map_comp, Function.comp_def, binLabel,
      Equiv.symm_apply_apply, map_add, ν]

end SigabaNeo.Wall1.ADRS

#print axioms SigabaNeo.Wall1.ADRS.squaredLabels_binAverage
#print axioms SigabaNeo.Wall1.ADRS.binAverage_resample
