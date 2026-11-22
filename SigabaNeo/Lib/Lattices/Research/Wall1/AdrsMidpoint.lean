module

public import SigabaNeo.Lib.Lattices.Research.Wall1.AdrsGaussian
public import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Event
import Mathlib.Tactic

/-! # The conditional Gaussian midpoint law (Part 140, I2) -/

@[expose] public section

noncomputable section

namespace SigabaNeo.Wall1.ADRS

open ProbabilityTheory ZLattice Cslib.Probability.PMF
open scoped ENNReal Pointwise RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] (L : Submodule ℤ E) (b : Module.Basis ι ℤ L)

/-- Independent draws from the same law. -/
def independentPair {V : Type*} (μ : PMF V) : PMF (V × V) :=
  μ.bind fun x ↦ μ.map (x, ·)

/-- The event that the two draws have equal coefficient labels modulo two. -/
def parityMatch : Set (L × L) :=
  {z | coefficientMod L b 2 z.1 = coefficientMod L b 2 z.2}

/-- Reconstruct the endpoints from the midpoint and half-difference. -/
def endpoints (z : L × L) : L × L := (z.1 + z.2, z.1 - z.2)

private theorem endpoints_injective : Function.Injective (endpoints L) := by
  rintro ⟨u,v⟩ ⟨w,z⟩ h
  have h₁ := congrArg (fun t : L × L ↦ (t.1 : E)) h
  have h₂ := congrArg (fun t : L × L ↦ (t.2 : E)) h
  change (u : E) + v = w + z at h₁
  change (u : E) - v = w - z at h₂
  apply Prod.ext <;> apply Subtype.ext
  · linear_combination (norm := module) (1 / 2 : ℝ) • h₁ + (1 / 2 : ℝ) • h₂
  · linear_combination (norm := module) (1 / 2 : ℝ) • h₁ - (1 / 2 : ℝ) • h₂

private theorem endpoints_range : Set.range (endpoints L) = parityMatch L b := by
  ext ⟨x,y⟩
  change (∃ p, endpoints L p = (x,y)) ↔ _
  rw [show (x,y) ∈ parityMatch L b ↔ _ from
    coefficientMod_eq_iff_sub_mem L b 2 x y, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨⟨u,v⟩, h⟩
    cases h
    refine ⟨(v : E), v.property, ?_⟩
    change (2 : ℝ) • (v : E) = (u + v) - (u - v)
    module
  · rintro ⟨v,hv,he⟩
    change (2 : ℝ) • v = (x : E) - y at he
    refine ⟨(y + ⟨v,hv⟩, ⟨v,hv⟩), Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
    · change (y : E) + v + v = x
      linear_combination (norm := module) he
    · change (y : E) + v - v = y
      abel

/-- Lattice midpoint, extended by zero off the integral-midpoint event. -/
def latticeMidpoint (x y : L) : L := by
  classical
  let u := (1 / 2 : ℝ) • ((x : E) + y)
  exact if h : u ∈ L then ⟨u,h⟩ else 0

theorem midpoint_endpoints (p : L × L) :
    latticeMidpoint L (endpoints L p).1 (endpoints L p).2 = p.1 := by
  have he : (1 / 2 : ℝ) • (((p.1 : E) + p.2) + (p.1 - p.2)) = p.1 := by module
  apply Subtype.ext
  simp only [latticeMidpoint, endpoints, Submodule.coe_add, Submodule.coe_sub, he,
    Submodule.coe_mem, ↓reduceDIte]

variable [FiniteDimensional ℝ E] [DiscreteTopology L] {s : ℝ} (hs : 0 < s)

theorem parityMatch_possible :
    ∃ z ∈ parityMatch L b, z ∈ (independentPair (discreteGaussian L s hs 0)).support := by
  refine ⟨(0,0), rfl, ?_⟩
  rw [PMF.mem_support_iff, independentPair, bind_map_prodMk_apply]
  apply mul_ne_zero <;> apply (PMF.mem_support_iff ..).mp <;> simp

private theorem parity_indicator (z : L × L) :
    (parityMatch L b).indicator (independentPair (discreteGaussian L s hs 0)) z =
      ((independentPair (discreteGaussian L (s / √2) (by positivity) 0)).map (endpoints L)) z *
        ENNReal.ofReal ((gaussianMass L (s / √2) 0 / gaussianMass L s 0)^2) := by
  classical
  let t := s / √2
  have ht : 0 < t := by dsimp [t]; positivity
  have hS := gaussianMass_pos L s hs 0
  have hT := gaussianMass_pos L t ht 0
  by_cases hz : z ∈ parityMatch L b
  · rw [Set.indicator_of_mem hz]
    rw [← endpoints_range] at hz
    obtain ⟨⟨u,v⟩,rfl⟩ := hz
    rw [map_apply_of_injective _ (endpoints_injective L)]
    apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (ENNReal.mul_ne_top
      (PMF.apply_ne_top _ _) ENNReal.ofReal_ne_top)).mp
    simp only [independentPair, bind_map_prodMk_apply, ENNReal.toReal_mul,
      discreteGaussian_apply_toReal, ENNReal.toReal_ofReal (sq_nonneg _), sub_zero,
      endpoints, Submodule.coe_add, Submodule.coe_sub]
    have hrot := gaussianWeight_pair hs ((u : E) + v) ((u : E) - v)
    rw [show (1 / 2 : ℝ) • (((u : E) + v) + (u - v)) = u by module,
      show (1 / 2 : ℝ) • (((u : E) + v) - (u - v)) = v by module] at hrot
    change _ / gaussianMass L s 0 * (_ / _) = _ / gaussianMass L t 0 * (_ / _) * (_ / _)^2
    field_simp [hS.ne', hT.ne']
    rw [hrot]
  · rw [Set.indicator_of_notMem hz, (PMF.apply_eq_zero_iff _ _).mpr ?_, zero_mul]
    rw [PMF.support_map]
    rintro ⟨p, _, rfl⟩
    exact hz (endpoints_range L b ▸ Set.mem_range_self p)

include hs in
/-- I1 supplies the sum of the squared coset probabilities used by the Poisson rate. -/
theorem sum_sq_parityProbability [DecidableEq ι] :
    (∑ c : ι → ZMod 2, ((∑' x : ParityFiber L b c, gaussianWeight s (x.val : E)) /
      gaussianMass L s 0)^2) = (gaussianMass L (s / √2) 0 / gaussianMass L s 0)^2 := by
  simp_rw [div_pow]
  rw [← Finset.sum_div]
  have h := sum_sq_parityMass L b hs (0 : E)
  simp only [sub_zero, ← sq] at h
  rw [h]

/-- The projected Gaussian point probability, in the fiber-sum form of I1. -/
theorem parityLabel_mass (c : ι → ZMod 2) :
    (((discreteGaussian L s hs 0).map (coefficientMod L b 2)) c).toReal =
      (∑' x : ParityFiber L b c, gaussianWeight s (x.val : E)) / gaussianMass L s 0 := by
  classical
  let D := discreteGaussian L s hs 0
  have h : (D.map (coefficientMod L b 2)) c = ∑' x : ParityFiber L b c, D x.val := by
    rw [PMF.map_apply]
    trans ∑' v, {w : L | coefficientMod L b 2 w = c}.indicator (fun w ↦ D w) v
    swap
    · exact (tsum_subtype {v : L | coefficientMod L b 2 v = c} (fun v ↦ D v)).symm
    apply tsum_congr
    intro v
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, D]
    by_cases hv : coefficientMod L b 2 v = c <;> simp [hv, Ne.symm]
  have hsum : Summable (fun x : ParityFiber L b c ↦ gaussianWeight s (x.val : E)) := by
    simpa only [Function.comp_def, sub_zero] using (summable_gaussianWeight L s hs 0).subtype
      (fun v : L ↦ coefficientMod L b 2 v = c)
  rw [h]
  simp only [D, discreteGaussian_apply, sub_zero, div_eq_mul_inv, ENNReal.tsum_mul_right,
    ← ENNReal.ofReal_tsum_of_nonneg (fun x : ParityFiber L b c ↦
      (gaussianWeight_pos s (x.val : E)).le) hsum, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (tsum_nonneg (fun _ ↦ (gaussianWeight_pos ..).le)),
    ENNReal.toReal_ofReal (gaussianMass_pos L s hs 0).le]

/-- Normalizing constant for conditioning on the collision event, from I1. -/
theorem parityMatch_mass :
    (independentPair (discreteGaussian L s hs 0)).toOuterMeasure (parityMatch L b) =
      ENNReal.ofReal ((gaussianMass L (s/√2) 0 / gaussianMass L s 0)^2) := by
  classical
  let μ := discreteGaussian L s hs 0
  let f := coefficientMod L b 2
  let q := μ.map f
  have h (x : L) : (μ.map (x, ·)).toOuterMeasure (parityMatch L b) = q (f x) := by
    rw [← PMF.toOuterMeasure_apply_singleton q, PMF.toOuterMeasure_map_apply,
      show q = μ.map f from rfl, PMF.toOuterMeasure_map_apply]
    congr 1
    ext y
    exact eq_comm
  have hsum : (independentPair μ).toOuterMeasure (parityMatch L b) = ∑ c, q c ^ 2 := by
    rw [independentPair, PMF.toOuterMeasure_bind_apply]
    simp only [h]
    rw [← tsum_map_mul μ f q, tsum_fintype]
    simp only [q, sq]
  apply (ENNReal.toReal_eq_toReal_iff' (toOuterMeasure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [hsum, ENNReal.toReal_sum (fun c _ ↦ ENNReal.pow_ne_top (PMF.apply_ne_top q c)),
    ENNReal.toReal_ofReal (sq_nonneg _)]
  simp only [q, f, μ, ENNReal.toReal_pow, parityLabel_mass]
  exact sum_sq_parityProbability L b hs

/-- Joint I2 law, retaining the independent half-difference for conditioning on labels. -/
theorem conditional_pair_law :
    (independentPair (discreteGaussian L s hs 0)).filter (parityMatch L b)
      (parityMatch_possible L b hs) =
      (independentPair (discreteGaussian L (s / √2) (by positivity) 0)).map (endpoints L) := by
  let D := discreteGaussian L (s / √2) (by positivity) 0
  let Q := (independentPair D).map (endpoints L)
  let c := ENNReal.ofReal ((gaussianMass L (s / √2) 0 / gaussianMass L s 0)^2)
  have hc : c ≠ 0 := (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (div_pos
    (gaussianMass_pos L _ (by positivity) _) (gaussianMass_pos L _ hs _)))).ne'
  change _ = Q
  ext z
  rw [PMF.filter_apply, ← PMF.toOuterMeasure_apply, parityMatch_mass L b hs, parity_indicator L b hs]
  change Q z * c * c⁻¹ = Q z
  rw [mul_assoc, ENNReal.mul_inv_cancel hc ENNReal.ofReal_ne_top, mul_one]

/-- I2. The pushforward of the conditioned product PMF is exactly the narrower
discrete Gaussian on the lattice, including at zero. -/
theorem conditional_midpoint_law :
    ((independentPair (discreteGaussian L s hs 0)).filter (parityMatch L b)
      (parityMatch_possible L b hs)).map (fun z ↦ latticeMidpoint L z.1 z.2) =
        discreteGaussian L (s / √2) (by positivity) 0 := by
  let D := discreteGaussian L (s / √2) (by positivity) 0
  rw [conditional_pair_law, PMF.map_comp]
  change (independentPair D).map (fun p ↦ latticeMidpoint L _ _) = D
  simp only [midpoint_endpoints]
  exact map_fst_bind_pair D _

end SigabaNeo.Wall1.ADRS

#print axioms SigabaNeo.Wall1.ADRS.conditional_midpoint_law
#print axioms SigabaNeo.Wall1.ADRS.sum_sq_parityProbability
