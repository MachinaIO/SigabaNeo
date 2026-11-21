module

public import Mathlib

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
namespace SigabaNeo.Rogers.Gram

/-- The reciprocal symmetric beta integral after the substitution t = 2u - 1. -/
def normalizer (p : ℝ) := (2 * 4 ^ p * beta (p + 1) (p + 1))⁻¹

def weight (p t : ℝ) : ℝ≥0∞ :=
  if t ∈ Ioo (-1) 1 then ENNReal.ofReal (normalizer p * (1 - t ^ 2) ^ p) else 0

theorem weight_integral {p : ℝ} (hp : -1 < p) : ∫⁻ t, weight p t = 1 := by
  have hi : (fun u : ℝ ↦ 2 * u - 1) '' univ = univ := by
    ext t
    simp only [mem_image, mem_univ, true_and, iff_true]
    exact ⟨(t + 1) / 2, by ring⟩
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := (univ : Set ℝ))
    (f := fun u ↦ 2 * u - 1) (f' := fun _ ↦ 2) MeasurableSet.univ
    (fun x _ ↦ by convert ((hasDerivAt_id x).const_mul 2 |>.sub_const 1).hasDerivWithinAt using 1 <;> simp)
    (fun x _ y _ h ↦ by dsimp at h; linarith) (weight p)
  rw [hi, setLIntegral_univ, setLIntegral_univ] at h
  rw [h, ← lintegral_betaPDF_eq_one (α := p + 1) (β := p + 1) (by linarith) (by linarith)]
  apply lintegral_congr
  intro u
  by_cases hu : 0 < u ∧ u < 1
  · have ht : 2 * u - 1 ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    rw [weight, ite_eq_left ht, betaPDF_of_pos_lt_one hu.1 hu.2, ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    rw [show 1 - (2 * u - 1)^2 = 4 * u * (1-u) by ring,
      Real.mul_rpow (mul_nonneg (by norm_num) hu.1.le) (by linarith [hu.2]),
      Real.mul_rpow (by norm_num) hu.1.le]
    simp only [normalizer, add_sub_cancel_right, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 4) p),
      ne_of_gt (beta_pos (by linarith : 0 < p+1) (by linarith : 0 < p+1))]
  · have ht : 2 * u - 1 ∉ Ioo (-1 : ℝ) 1 := fun h ↦ hu ⟨by linarith [h.1], by linarith [h.2]⟩
    simp [weight, ht, betaPDF_eq, hu]

def det3 (a b c : ℝ) := 1 + 2*a*b*c - a^2 - b^2 - c^2

theorem det3_fiber (a b t : ℝ) (ha : a ∈ Ioo (-1 : ℝ) 1) (hb : b ∈ Ioo (-1 : ℝ) 1) :
    det3 a b (a*b + Real.sqrt ((1-a^2)*(1-b^2))*t) = (1-a^2)*(1-b^2)*(1-t^2) := by
  have hpos (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) : 0 < 1-x^2 := by
    nlinarith [mul_pos (sub_pos.mpr hx.2) (show 0 < 1+x by linarith [hx.1])]
  have h := Real.sq_sqrt (mul_pos (hpos a ha) (hpos b hb)).le
  unfold det3
  linear_combination -t^2 * h

private theorem interval_pos {x : ℝ} (h : x ∈ Ioo (-1 : ℝ) 1) : 0 < 1-x^2 := by
  nlinarith [mul_pos (sub_pos.mpr h.2) (show 0 < 1+x by linarith [h.1])]

/-- Change of variables on one positive-determinant fiber for any nonnegative test. -/
theorem fiber_integral (a b p : ℝ) (ha : a ∈ Ioo (-1 : ℝ) 1) (hb : b ∈ Ioo (-1 : ℝ) 1)
    (F : ℝ → ℝ≥0∞) :
    let u := (1-a^2)*(1-b^2)
    ∫⁻ c in {c | 0 < det3 a b c}, ENNReal.ofReal (det3 a b c ^ p) * F c =
      ∫⁻ t in Ioo (-1 : ℝ) 1, ENNReal.ofReal (u ^ (p+1/2) * (1-t^2)^p) *
        F (a*b + Real.sqrt u*t) := by
  dsimp only
  let u := (1-a^2)*(1-b^2)
  have hu : 0 < u := mul_pos (interval_pos ha) (interval_pos hb)
  have hs := Real.sqrt_pos.2 hu
  let f := fun t : ℝ ↦ a*b + Real.sqrt u*t
  have hd (t : ℝ) : det3 a b (f t) = u*(1-t^2) := by
    unfold f u det3
    linear_combination -t^2 * Real.sq_sqrt hu.le
  have him : f '' Ioo (-1 : ℝ) 1 = {c | 0 < det3 a b c} := by
    ext c
    constructor
    · rintro ⟨t, ht, rfl⟩
      change 0 < det3 a b (f t)
      rw [hd]
      exact mul_pos hu (interval_pos ht)
    · intro hc
      let t := (c-a*b)/Real.sqrt u
      have he : f t = c := by dsimp [f,t]; field_simp [hs.ne']; ring
      refine ⟨t, ?_, he⟩
      change 0 < det3 a b c at hc
      rw [← he, hd] at hc
      have ht := pos_of_mul_pos_right hc hu.le
      constructor <;> nlinarith [sq_nonneg (t-1), sq_nonneg (t+1)]
  rw [← him, lintegral_image_eq_lintegral_abs_deriv_mul (f' := fun _ ↦ Real.sqrt u)
    measurableSet_Ioo (fun t _ ↦ by
      simpa [f] using (((hasDerivAt_id t).const_mul (Real.sqrt u)).const_add (a*b)).hasDerivWithinAt)
    (fun x _ y _ h ↦ by dsimp [f] at h; exact mul_left_cancel₀ hs.ne' (add_left_cancel h) )]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  rw [abs_of_pos hs, hd, ← mul_assoc, ← ENNReal.ofReal_mul hs.le,
    Real.mul_rpow hu.le (interval_pos ht).le, Real.rpow_add hu,
    Real.sqrt_eq_rpow]
  dsimp [u,f]
  simp only [Real.sqrt_eq_rpow]
  congr 2
  ring

abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Sphere (n : ℕ) := Metric.sphere (0 : Ambient n) 1

def uniform (n : ℕ) : Measure (Sphere n) :=
  let μ := (volume : Measure (Ambient n)).toSphere
  (μ univ)⁻¹ • μ

def PairLaw (n : ℕ) : Prop :=
  Measure.map (fun z : Sphere n × Sphere n ↦ inner ℝ (z.1 : Ambient n) (z.2 : Ambient n))
    ((uniform n).prod (uniform n)) = volume.withDensity (weight (((n:ℝ)-3)/2))

theorem uniform_probability {n : ℕ} (hn : 0 < n) : IsProbabilityMeasure (uniform n) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let μ := (volume : Measure (Ambient n)).toSphere
  have h : μ univ ≠ 0 := Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero _)
  constructor
  exact ENNReal.inv_mul_cancel h (measure_ne_top μ univ)

open scoped Pointwise in
/-- The remaining scalar input can be expressed entirely as volumes of solid cones. -/
theorem pairLaw_of_coneVolumes {n : ℕ} (hn : 4 ≤ n)
    (h : ∀ (x : Sphere n) (s : Set ℝ), MeasurableSet s →
      ((volume : Measure (Ambient n)).toSphere univ)⁻¹ *
        (n * volume (Ioo (0:ℝ) 1 • (Subtype.val ''
          {y : Sphere n | inner ℝ (x : Ambient n) (y : Ambient n) ∈ s}))) =
        (volume.withDensity (weight (((n:ℝ)-3)/2))) s) : PairLaw n := by
  let := uniform_probability (n := n) (by omega)
  let f := fun z : Sphere n × Sphere n ↦ inner ℝ (z.1 : Ambient n) (z.2 : Ambient n)
  have hm : Measurable f := by dsimp [f]; fun_prop
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply (hm hs)]
  have he (x : Sphere n) : uniform n (Prod.mk x ⁻¹' (f ⁻¹' s)) =
      (volume.withDensity (weight (((n:ℝ)-3)/2))) s := by
    rw [uniform, Measure.smul_apply, Measure.toSphere_apply' _ (measurable_prodMk_left (hm hs))]
    have heq : Prod.mk x ⁻¹' (f ⁻¹' s) =
        {y : Sphere n | inner ℝ (x : Ambient n) (y : Ambient n) ∈ s} := rfl
    rw [heq]
    simpa using h x s hs
  simp_rw [he]
  simp

def tripleWeight (n : ℕ) (x : ℝ × ℝ × ℝ) : ℝ≥0∞ :=
  let (a,b,c) := x
  let p := ((n:ℝ)-4)/2
  if a ∈ Ioo (-1 : ℝ) 1 ∧ b ∈ Ioo (-1 : ℝ) 1 ∧ 0 < det3 a b c then
    ENNReal.ofReal (normalizer (p+1/2)^2 * normalizer p * det3 a b c ^ p)
  else 0

private theorem normalizer_pos {p : ℝ} (hp : -1 < p) : 0 < normalizer p := by
  unfold normalizer
  exact inv_pos.mpr (mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _))
    (beta_pos (by linarith) (by linarith)))

/-- Integrating out the third coordinate gives the independent first two marginals. -/
theorem triple_marginal (n : ℕ) (hn : 5 ≤ n) (a b : ℝ) :
    ∫⁻ c, tripleWeight n (a,b,c) =
      weight (((n:ℝ)-4)/2+1/2) a * weight (((n:ℝ)-4)/2+1/2) b := by
  let p := ((n:ℝ)-4)/2
  have hp : -1 < p := by
    dsimp [p]
    have : (5:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hN := (normalizer_pos hp).le
  have hM := (normalizer_pos (show -1 < p+1/2 by linarith)).le
  by_cases ha : a ∈ Ioo (-1 : ℝ) 1
  · by_cases hb : b ∈ Ioo (-1 : ℝ) 1
    · have hu := mul_pos (interval_pos ha) (interval_pos hb)
      let K := normalizer (p+1/2)^2 * normalizer p
      have hK : 0 ≤ K := mul_nonneg (sq_nonneg _) hN
      have he : (fun c ↦ tripleWeight n (a,b,c)) = {c | 0 < det3 a b c}.indicator
          (fun c ↦ ENNReal.ofReal K * ENNReal.ofReal (det3 a b c ^ p)) := by
        funext c
        by_cases hc : 0 < det3 a b c <;> simp [tripleWeight, ha, hb, hc, indicator, K, p]
        apply ENNReal.ofReal_mul
        simpa [K,p] using hK
      rw [he, lintegral_indicator (isOpen_lt continuous_const (by unfold det3; fun_prop)).measurableSet,
        lintegral_const_mul'' _ (by unfold det3; fun_prop)]
      have hf := fiber_integral a b p ha hb (fun _ ↦ 1)
      simp only [mul_one, ENNReal.ofReal_mul (Real.rpow_pos_of_pos hu _).le] at hf
      rw [hf, lintegral_const_mul'' _ (by fun_prop)]
      have hw := weight_integral hp
      have hw' : (fun t ↦ weight p t) = (Ioo (-1 : ℝ) 1).indicator
          (fun t ↦ ENNReal.ofReal (normalizer p) * ENNReal.ofReal ((1-t^2)^p)) := by
        funext t
        simp [weight, indicator, ENNReal.ofReal_mul hN]
      rw [hw', lintegral_indicator measurableSet_Ioo, lintegral_const_mul'' _ (by fun_prop)] at hw
      change _ = weight (p+1/2) a * weight (p+1/2) b
      rw [weight, ite_eq_left ha, weight, ite_eq_left hb]
      dsimp [K]
      rw [ENNReal.ofReal_mul (sq_nonneg _), Real.mul_rpow (interval_pos ha).le (interval_pos hb).le]
      rw [ENNReal.ofReal_mul (Real.rpow_pos_of_pos (interval_pos ha) _).le]
      simp only [sq, ENNReal.ofReal_mul hM] at hw ⊢
      conv_rhs => rw [← mul_one (_ * _), ← hw]
      ac_rfl
    · simp [tripleWeight, weight, hb]
  · simp [tripleWeight, weight, ha]

theorem triple_integral (n : ℕ) (hn : 5 ≤ n) : ∫⁻ x, tripleWeight n x = 1 := by
  have hm : Measurable (tripleWeight n) := by
    unfold tripleWeight det3
    dsimp only
    apply Measurable.ite _ (by fun_prop) measurable_const
    change MeasurableSet ((Prod.fst ⁻¹' Ioo (-1:ℝ) 1) ∩
      ((fun x : ℝ × ℝ × ℝ ↦ x.2.1) ⁻¹' Ioo (-1:ℝ) 1 ∩ {x | 0 < det3 x.1 x.2.1 x.2.2}))
    apply MeasurableSet.inter (measurable_fst measurableSet_Ioo)
    apply MeasurableSet.inter ((measurable_fst.comp measurable_snd) measurableSet_Ioo)
    exact measurableSet_lt (f := fun _ ↦ (0 : ℝ))
      (g := fun x : ℝ × ℝ × ℝ ↦ det3 x.1 x.2.1 x.2.2) measurable_const (by unfold det3; fun_prop)
  rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
  have h (a : ℝ) : Measurable (fun y : ℝ × ℝ ↦ tripleWeight n (a,y)) :=
    hm.comp (measurable_const.prodMk measurable_id)
  simp_rw [Measure.volume_eq_prod (α := ℝ) (β := ℝ), lintegral_prod _ (h _).aemeasurable,
    triple_marginal n hn]
  have hw : Measurable (weight (((n:ℝ)-4)/2+1/2)) := by unfold weight; exact Measurable.ite measurableSet_Ioo (by fun_prop) measurable_const
  have hp : -1 < ((n:ℝ)-4)/2+1/2 := by
    have : (5:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  simp_rw [lintegral_const_mul'' _ hw.aemeasurable, weight_integral hp, mul_one]
  exact weight_integral hp

def TripleLaw (n : ℕ) : Prop :=
  Measure.map (fun z : Sphere n × Sphere n × Sphere n ↦
    (inner ℝ (z.1 : Ambient n) (z.2.1 : Ambient n),
     inner ℝ (z.1 : Ambient n) (z.2.2 : Ambient n),
     inner ℝ (z.2.1 : Ambient n) (z.2.2 : Ambient n)))
    ((uniform n).prod ((uniform n).prod (uniform n))) = volume.withDensity (tripleWeight n)

abbrev OffDiagonal (s : ℕ) := {ij : Fin s × Fin s // ij.1 < ij.2}

def correlation {s : ℕ} (x : OffDiagonal s → ℝ) : Matrix (Fin s) (Fin s) ℝ :=
  fun i j ↦ if h : i < j then x ⟨(i,j),h⟩ else if h : j < i then x ⟨(j,i),h⟩ else 1

/-- Product of scalar projection normalizers for the successive orthogonal complements.
The exponent s(s-1)/4 on π is the sum of the exponents j/2 below. -/
def gramConstant (n s : ℕ) : ℝ :=
  ∏ j ∈ Finset.range (s-1), Real.Gamma ((n:ℝ)/2) /
    (Real.pi ^ (((j:ℝ)+1)/2) * Real.Gamma (((n:ℝ)-(j+1))/2))

open Classical in
def SphericalGramFormula (n s : ℕ) : Prop :=
  Measure.map (fun z : Fin s → Sphere n ↦ fun ij : OffDiagonal s ↦
    inner ℝ (z ij.val.1 : Ambient n) (z ij.val.2 : Ambient n))
    (Measure.pi fun _ ↦ uniform n) = volume.withDensity (fun x ↦
      if (correlation x).PosDef then
        ENNReal.ofReal (gramConstant n s * (correlation x).det ^ (((n:ℝ)-s-1)/2)) else 0)

end SigabaNeo.Rogers.Gram
