module

public import CslibFrontier.Foundations.Probability.Gaussian.ShiftBounds
public import CslibFrontier.Foundations.Algebra.Module.ZLattice.CoefficientFiber
import Mathlib.Tactic.Module

/-! # Gaussian pair masses for the ADRS combiner (Part 140, I1 and I3) -/

@[expose] public section

noncomputable section

namespace SigabaNeo.Wall1.ADRS

open ProbabilityTheory ZLattice MeasureTheory
open scoped Pointwise RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The independent Gaussian weights factor in midpoint and half-difference coordinates. -/
theorem gaussianWeight_pair {s : ℝ} (hs : 0 < s) (x y : E) :
    gaussianWeight s x * gaussianWeight s y =
      gaussianWeight (s / √2) ((1 / 2 : ℝ) • (x + y)) *
      gaussianWeight (s / √2) ((1 / 2 : ℝ) • (x - y)) := by
  simp only [gaussianWeight, ← Real.exp_add, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  field_simp
  linarith only [parallelogram_law_with_norm ℝ x y]

variable {ι : Type*} [Fintype ι] (L : Submodule ℤ E) (b : Module.Basis ι ℤ L)

/-- An actual fiber in the lattice of coefficient reduction modulo two. -/
abbrev ParityFiber (c : ι → ZMod 2) := {v : L // coefficientMod L b 2 v = c}

private abbrev Pairs := Σ c, ParityFiber L b c × ParityFiber L b c

private def pairFromSumDiff (p : L × L) : Pairs L b :=
  let x := p.1 + p.2
  let y := p.1 - p.2
  ⟨coefficientMod L b 2 x, ⟨x, rfl⟩, ⟨y, by
    apply (coefficientMod_eq_iff_sub_mem L b 2 y x).2
    apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).2
    refine ⟨-(p.2 : E), L.neg_mem p.2.property, ?_⟩
    change (2 : ℝ) • -(p.2 : E) = ((p.1 : E) - p.2) - (p.1 + p.2)
    module⟩⟩

omit [InnerProductSpace ℝ E] in
private theorem pairs_ext {p q : Pairs L b} (hx : p.2.1.val = q.2.1.val)
    (hy : p.2.2.val = q.2.2.val) : p = q := by
  rcases p with ⟨_, ⟨x, rfl⟩, ⟨y, hy'⟩⟩
  rcases q with ⟨_, ⟨z, rfl⟩, ⟨w, hw'⟩⟩
  cases hx
  cases hy
  rfl

/-- The bijection sends a lattice pair (u,v) to the equal-label pair (u+v,u-v). -/
private def parityPairEquiv : (L × L) ≃ Pairs L b :=
  Equiv.ofBijective (pairFromSumDiff L b) ⟨by
    rintro ⟨u,v⟩ ⟨w,z⟩ h
    have h₁ := congrArg (fun p : Pairs L b ↦ (p.2.1.val : E)) h
    have h₂ := congrArg (fun p : Pairs L b ↦ (p.2.2.val : E)) h
    change (u : E) + v = w + z at h₁
    change (u : E) - v = w - z at h₂
    apply Prod.ext <;> apply Subtype.ext
    · linear_combination (norm := module) (1 / 2 : ℝ) • h₁ + (1 / 2 : ℝ) • h₂
    · linear_combination (norm := module) (1 / 2 : ℝ) • h₁ - (1 / 2 : ℝ) • h₂,
    by
    rintro ⟨c, ⟨x, hx⟩, ⟨y, hy⟩⟩
    have hm := (coefficientMod_eq_iff_sub_mem L b 2 x y).1 (hx.trans hy.symm)
    obtain ⟨v, hv, he⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hm
    change (2 : ℝ) • v = (x : E) - y at he
    refine ⟨(y + ⟨v, hv⟩, ⟨v, hv⟩), pairs_ext L b ?_ ?_⟩ <;> apply Subtype.ext
    · change ((y : E) + v) + v = x
      linear_combination (norm := module) he
    · change ((y : E) + v) - v = y
      abel⟩

variable [FiniteDimensional ℝ E] [DiscreteTopology L]

/-- I1, including arbitrary target shift. The outer sum runs over all cosets of 2L. -/
theorem sum_sq_parityMass [DecidableEq ι] {s : ℝ} (hs : 0 < s) (t : E) :
    (∑ c : ι → ZMod 2, (∑' x : ParityFiber L b c, gaussianWeight s ((x.val : E) - t)) ^ 2) =
      gaussianMass L (s / √2) t * gaussianMass L (s / √2) 0 := by
  classical
  let f (x : L) := gaussianWeight s ((x : E) - t)
  let F (p : Pairs L b) := f p.2.1.val * f p.2.2.val
  let g (x : L) := gaussianWeight (s / √2) ((x : E) - t)
  let k (x : L) := gaussianWeight (s / √2) ((x : E) - 0)
  have hg := summable_gaussianWeight L (s / √2) (by positivity) t
  have hk := summable_gaussianWeight L (s / √2) (by positivity) 0
  have hprod : Summable (fun p : L × L ↦ g p.1 * k p.2) :=
    hg.mul_of_nonneg hk (fun _ ↦ (gaussianWeight_pos ..).le) (fun _ ↦ (gaussianWeight_pos ..).le)
  have hrot (p : L × L) : F (parityPairEquiv L b p) = g p.1 * k p.2 := by
    change gaussianWeight s (((p.1 : E) + p.2) - t) * gaussianWeight s ((p.1 - p.2 : E) - t) = _
    rw [gaussianWeight_pair hs]
    congr 1 <;> congr 1 <;> module
  have hF : Summable F := (parityPairEquiv L b).summable_iff.mp (by simpa only [Function.comp_def, hrot] using hprod)
  have hf (c) : Summable (fun x : ParityFiber L b c ↦ f x.val) :=
    (summable_gaussianWeight L s hs t).subtype _
  have hf₂ (c) : Summable (fun p : ParityFiber L b c × ParityFiber L b c ↦ F ⟨c,p⟩) :=
    (hf c).mul_of_nonneg (hf c) (fun _ ↦ (gaussianWeight_pos ..).le)
      (fun _ ↦ (gaussianWeight_pos ..).le)
  calc _ = ∑ c, ∑' p, F ⟨c,p⟩ := by
         apply Finset.sum_congr rfl
         intro c _
         exact (sq _).trans ((hf c).tsum_mul_tsum (hf c) (hf₂ c))
       _ = ∑' p, F p := by rw [hF.tsum_sigma' hf₂, tsum_fintype]
       _ = ∑' p : L × L, g p.1 * k p.2 := by rw [← (parityPairEquiv L b).tsum_eq F]; simp only [hrot]
       _ = _ := (hg.tsum_mul_tsum hk hprod).symm

omit [FiniteDimensional ℝ E] [DiscreteTopology L] in
/-- Summing over a parity fiber is a shifted Gaussian mass on L at half the width. -/
theorem parityMass_eq_rescaled {s : ℝ} (hs : 0 < s) (c : ι → ZMod 2) (t : E) :
    (∑' x : ParityFiber L b c, gaussianWeight s ((x.val : E) - t)) =
      gaussianMass L (s / 2) ((1 / 2 : ℝ) • (t - coefficientLift L b 2 c)) := by
  let dbl (z : L) : ↥((2 : ℝ) • L) :=
    ⟨(2 : ℝ) • (z : E), (Submodule.mem_smul_pointwise_iff_exists ..).2 ⟨z, z.property, rfl⟩⟩
  have hd : Function.Bijective dbl := by
    constructor
    · intro x y h
      have he := congrArg Subtype.val h
      change (2 : ℝ) • (x : E) = (2 : ℝ) • (y : E) at he
      apply Subtype.ext
      linear_combination (norm := module) (1 / 2 : ℝ) • he
    · intro z
      obtain ⟨x,hx,he⟩ := (Submodule.mem_smul_pointwise_iff_exists ..).1 z.property
      exact ⟨⟨x,hx⟩, Subtype.ext he⟩
  let e := (Equiv.ofBijective dbl hd).trans (coefficientFiberEquiv L b 2 c)
  rw [← e.tsum_eq, gaussianMass]
  apply tsum_congr
  intro x
  change gaussianWeight s ((2 : ℝ) • (x : E) + coefficientLift L b 2 c - t) = _
  rw [show (2 : ℝ) • (x : E) + coefficientLift L b 2 c - t =
    (2 : ℝ) • ((x : E) - (1 / 2 : ℝ) • (t - coefficientLift L b 2 c)) by module]
  simp only [gaussianWeight, norm_smul, Real.norm_ofNat]
  congr 1
  field_simp

variable [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L]

/-- I3 for every full-rank lattice and arbitrary shift. Apply to 2L for the combiner. -/
theorem gaussianMass_le_center {s : ℝ} (hs : 0 < s) (c : E) :
    gaussianMass L s c ≤ gaussianMass L s 0 := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  have hz : gaussianMass L s 0 = s ^ Module.finrank ℝ E / covolume L *
      gaussianMass D (1 / s) 0 := by
    apply Complex.ofReal_injective
    simpa only [inner_zero_left, neg_zero, Real.fourierChar.map_zero_eq_one, Circle.coe_one,
      mul_one, gaussianMass, sub_zero, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_tsum, D] using gaussianMass_eq_tsum_dual L s hs 0
  have hu := (le_abs_self _).trans (abs_gaussianMass_normalized_sub_one_le L s hs c)
  have hc := covolume_pos L volume
  rw [hz]
  have h : covolume L / s ^ Module.finrank ℝ E * gaussianMass L s c ≤ gaussianMass D (1 / s) 0 :=
    by dsimp [D]; linarith
  field_simp at h ⊢
  linarith

/-- I3 in the combiner's notation. Dividing by the total mass gives the coset probability. -/
theorem parityProbability_le {s : ℝ} (hs : 0 < s) (c : ι → ZMod 2) :
    (∑' x : ParityFiber L b c, gaussianWeight s (x.val : E)) / gaussianMass L s 0 ≤
      gaussianMass L (s / 2) 0 / gaussianMass L s 0 := by
  have h := parityMass_eq_rescaled L b hs c 0
  simp only [sub_zero] at h
  rw [h]
  exact div_le_div_of_nonneg_right (gaussianMass_le_center L (by positivity) _)
    (gaussianMass_pos L s hs 0).le

omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L] [FiniteDimensional ℝ E]
  [DiscreteTopology L] in
theorem zero_parityProbability {s : ℝ} (hs : 0 < s) :
    (∑' x : ParityFiber L b 0, gaussianWeight s (x.val : E)) / gaussianMass L s 0 =
      gaussianMass L (s / 2) 0 / gaussianMass L s 0 := by
  have h := parityMass_eq_rescaled L b hs 0 0
  simpa [coefficientLift] using congrArg (· / gaussianMass L s 0) h

end SigabaNeo.Wall1.ADRS

#print axioms SigabaNeo.Wall1.ADRS.gaussianWeight_pair
#print axioms SigabaNeo.Wall1.ADRS.sum_sq_parityMass
#print axioms SigabaNeo.Wall1.ADRS.gaussianMass_le_center
#print axioms SigabaNeo.Wall1.ADRS.parityMass_eq_rescaled
#print axioms SigabaNeo.Wall1.ADRS.parityProbability_le
#print axioms SigabaNeo.Wall1.ADRS.zero_parityProbability
