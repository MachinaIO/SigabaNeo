module

public import SigabaNeo.Lib.Lattices.Reduction.Rogers.Gram
public import SigabaNeo.Lib.Lattices.Research.Wall1.GaussianPackingIntegral
import Mathlib.LinearAlgebra.QuadraticForm.Dual
import Mathlib.Tactic

/-! # A packing bound by lifting points of a ball to a sphere -/

public section
namespace SigabaNeo.Wall1

open MeasureTheory Set Real InnerProductSpace Metric
open scoped ENNReal RealInnerProductSpace
open SigabaNeo.Rogers.Gram

private theorem half_le_normalizer {p : ℝ} (hp : 0 ≤ p) : 1/2 ≤ normalizer p := by
  have hn : 0 ≤ normalizer p := by
    unfold normalizer
    positivity [ProbabilityTheory.beta_pos (by linarith : 0 < p+1) (by linarith : 0 < p+1)]
  have h := lintegral_mono (μ := volume) (f := weight p)
    (g := (Ioo (-1 : ℝ) 1).indicator (fun _ ↦ ENNReal.ofReal (normalizer p))) (by
      intro t
      by_cases ht : t ∈ Ioo (-1 : ℝ) 1
      · simp only [weight, ite_eq_left ht, indicator_of_mem ht]
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_of_le_one_right hn
        have hpos : 0 < 1+t := by linarith [ht.1]
        exact rpow_le_one (by nlinarith [mul_pos (sub_pos.mpr ht.2) hpos])
          (by nlinarith [sq_nonneg t]) hp
      · simp [weight, ht])
  rw [weight_integral (by linarith), lintegral_indicator measurableSet_Ioo, setLIntegral_const,
    Real.volume_Ioo] at h
  norm_num at h
  have hh := ENNReal.toReal_mono (by finiteness) h
  simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal hn] at hh
  linarith

/-- The open cap of axial threshold `t` on the unit `d`-sphere. -/
private def openCap {d : ℕ} (x : Sphere (d+1)) (t : ℝ) :=
  {y : Sphere (d+1) | t < ⟪(x : Ambient (d+1)), (y : Ambient (d+1))⟫_ℝ}

private theorem cap_meas {d : ℕ} (x : Sphere (d+1)) (t : ℝ) :
    MeasurableSet (openCap x t) := measurableSet_lt measurable_const (by fun_prop)

private theorem cap_lower {d : ℕ} (hd : 2 ≤ d) (x : Sphere (d+1)) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    (1-t^2)^((d : ℝ)/2) / (2*d) ≤ (uniform (d+1)).real (openCap x t) := by
  let p : ℝ := ((d : ℝ)-2)/2
  have hd' : 2 ≤ (d : ℝ) := by exact_mod_cast hd
  have hp : 0 ≤ p := by dsimp [p]; linarith
  have hdim : (d : ℝ) = 2*(p+1) := by dsimp [p]; ring
  have hexp : (((d : ℝ)+1-3)/2) = p := by dsimp [p]; ring
  let f := fun u : ℝ ↦ (1-u^2)^p
  have hc : Continuous f :=
    (continuous_const.sub (continuous_id.pow 2)).rpow_const fun _ ↦ Or.inr hp
  have val := capSlice_normalized_of_two_le (d := (d : ℝ)+1) (by linarith)
    (show t ∈ Icc (0 : ℝ) 1 from ⟨ht.1.le, ht.2.le⟩)
  rw [capSlice_tail_of_two_le (by linarith) ⟨ht.1.le, ht.2.le⟩, hexp] at val
  have clean : normalizer p * (((d : ℝ)+1)/((d+1)-1)) * (((d+1)-1)/(d+1) *
      ∫ u in t..1, f u) = normalizer p * ∫ u in t..1, f u := by
    field_simp [show (d : ℝ) ≠ 0 by linarith, show (d : ℝ)+1 ≠ 0 by linarith]
  rw [clean] at val
  let μ := volume.withDensity (weight p)
  have heq : μ (Ioi t) = μ (Ici t) := measure_congr ((withDensity_absolutelyContinuous volume (weight p)).ae_eq Ioi_ae_eq_Ici)
  have hf : Measurable (fun y : Sphere (d+1) ↦ ⟪(x : Ambient (d+1)), (y : Ambient (d+1))⟫_ℝ) :=
    by fun_prop
  have law := congrArg (fun ν : Measure ℝ ↦ ν (Ioi t)) (pole_law d hd x)
  simp only [Measure.map_apply hf measurableSet_Ioi, hexp] at law
  change (uniform (d+1)) (openCap x t) = μ (Ioi t) at law
  have fint : 0 ≤ ∫ u in t..1, f u := intervalIntegral.integral_nonneg ht.2.le (by
    intro u hu
    have hplus : 0 ≤ 1+u := by linarith [ht.1.trans_le hu.1]
    exact rpow_nonneg (by nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) hplus]) _)
  rw [Measure.real, law, heq, val, ENNReal.toReal_ofReal
    (mul_nonneg (by linarith [half_le_normalizer hp]) fint)]
  have primitive (z : ℝ) (hz : z ∈ Ioo t 1) :
      HasDerivAt (fun u : ℝ ↦ -(1-u^2)^(p+1)) (2*(p+1)*(z*f z)) z := by
    have hbase : 0 < 1-z^2 := by
      nlinarith [mul_pos (sub_pos.mpr hz.2) (by linarith [ht.1.trans hz.1] : 0 < 1+z)]
    convert (((hasDerivAt_const z (1 : ℝ)).sub ((hasDerivAt_id z).pow 2)).rpow_const
      (p := p+1) (Or.inl hbase.ne')).neg using 1 <;> first | rfl | (simp [f]; ring)
  have integ := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.2.le
    (f := fun u : ℝ ↦ -(1-u^2)^(p+1)) (f' := fun u ↦ 2*(p+1)*(u*f u))
    ((continuous_const.sub (continuous_id.pow 2)).rpow_const
      (fun _ ↦ Or.inr (by linarith : 0 ≤ p+1))).neg.continuousOn primitive
    ((continuous_const.mul (continuous_id.mul hc)).intervalIntegrable t 1)
  rw [intervalIntegral.integral_const_mul] at integ
  simp [zero_rpow (by linarith : p+1 ≠ 0)] at integ
  have cmp : (∫ z in t..1, z * f z) ≤ ∫ z in t..1, f z := by
    apply intervalIntegral.integral_mono_on ht.2.le ((continuous_id.mul hc).intervalIntegrable t 1)
      (hc.intervalIntegrable t 1)
    intro z hz
    have hplus : 0 ≤ 1+z := by linarith [ht.1.trans_le hz.1]
    have hb : 0 ≤ 1-z^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hz.2) hplus]
    exact mul_le_of_le_one_left (rpow_nonneg hb _) hz.2
  have bot : (1-t^2)^((d : ℝ)/2) ≤ (d : ℝ) * (∫ u in t..1, f u) := by
    rw [hdim, show 2*(p+1)/2 = p+1 by ring, ← integ]
    exact mul_le_mul_of_nonneg_left cmp (by positivity)
  apply le_trans _ (mul_le_mul_of_nonneg_right (half_le_normalizer hp) fint)
  apply (div_le_iff₀ (by positivity : 0 < 2*(d : ℝ))).2
  linarith

/-- Inside an open cap, translating by `t` times its axis gives obtuse vectors
in a common open half-space. Their number is at most the ambient dimension. -/
private theorem cap_occupancy {d : ℕ} {ι : Type*} [Fintype ι] (x : ι → Sphere (d+1))
    (y : Sphere (d+1)) {t : ℝ} (ht : 0 < t)
    (sep : Pairwise fun i j ↦ ⟪(x i : Ambient (d+1)), (x j : Ambient (d+1))⟫_ℝ ≤ t^2)
    (mem : ∀ i, y ∈ openCap (x i) t) : Fintype.card ι ≤ d+1 := by
  let v i := (x i : Ambient (d+1)) - t • (y : Ambient (d+1))
  have hy : ⟪(y : Ambient (d+1)), (y : Ambient (d+1))⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp y.property]; norm_num
  have pos i : t < ⟪(x i : Ambient (d+1)), (y : Ambient (d+1))⟫_ℝ := mem i
  have li := LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero (innerₗ (Ambient (d+1)))
    (by intro z hz; exact real_inner_self_pos.mpr hz) (innerₗ _ (y : Ambient (d+1))) v
    (by intro i; change 0 < ⟪(y : Ambient (d+1)), v i⟫_ℝ
        rw [real_inner_comm]; simp only [v, inner_sub_left, real_inner_smul_left, hy, mul_one]
        linarith [pos i]) (by
      intro i j hij
      change ⟪v i, v j⟫_ℝ ≤ 0
      simp only [v, inner_sub_left, inner_sub_right, real_inner_smul_right, real_inner_smul_left,
        hy, mul_one]
      rw [← real_inner_comm (y : Ambient (d+1)) (x j : Ambient (d+1))]
      nlinarith [sep hij, mul_pos ht (sub_pos.mpr (pos i)), mul_pos ht (sub_pos.mpr (pos j))])
  simpa [Ambient] using li.fintype_card_le_finrank

/-- Averaging open cap occupancy over the unit sphere. -/
theorem sphericalPacking_card {d : ℕ} (hd : 2 ≤ d) {ι : Type*} [Fintype ι]
    (x : ι → Sphere (d+1)) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (sep : Pairwise fun i j ↦ ⟪(x i : Ambient (d+1)), (x j : Ambient (d+1))⟫_ℝ ≤ t^2) :
    (Fintype.card ι : ℝ) * (1-t^2)^((d : ℝ)/2) ≤ 2*((d : ℝ)+1)^2 := by
  classical
  let μ := uniform (d+1)
  let : IsProbabilityMeasure μ := uniform_probability (by omega)
  let f i := (openCap (x i) t).indicator (fun _ ↦ (1 : ℝ))
  have hi i : Integrable (f i) μ := (integrable_const 1).indicator (cap_meas _ _)
  have ev i : (∫ y, f i y ∂μ) = μ.real (openCap (x i) t) := integral_indicator_one (cap_meas _ _)
  have card (y : Sphere (d+1)) : ∑ i, f i y ≤ (d : ℝ)+1 := by
    let S := Finset.univ.filter (fun i ↦ y ∈ openCap (x i) t)
    have co := cap_occupancy (fun i : S ↦ x i.val) y ht.1
      (fun _ _ hij ↦ sep (Subtype.val_injective.ne hij)) (fun i ↦ (Finset.mem_filter.mp i.2).2)
    have he : ∑ i, f i y = (S.card : ℝ) := by simp [f, S, Set.indicator]
    rw [he]
    exact_mod_cast (show S.card ≤ d+1 by simpa using co)
  have bound := integral_mono (integrable_finsetSum _ (fun i _ ↦ hi i))
    (integrable_const ((d : ℝ)+1)) card
  rw [integral_finsetSum _ (fun i _ ↦ hi i)] at bound
  simp only [integral_const, probReal_univ, one_smul, ev] at bound
  have low := (Finset.sum_le_sum (s := Finset.univ)
    (fun i _ ↦ cap_lower hd (x i) ht)).trans bound
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_div_assoc] at low
  have hd' : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have h := (div_le_iff₀ (by positivity)).mp low
  nlinarith

/-- Lift the closed unit ball to the unit sphere in one extra dimension. -/
theorem unitBallPacking_card {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {d : ℕ} (hE : Module.finrank ℝ E = d) (hd : 2 ≤ d)
    {ι : Type*} [Fintype ι] (x : ι → E) (ball : ∀ i, ‖x i‖ ≤ 1)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (sep : Pairwise fun i j ↦ 2*(1-t^2) ≤ ‖x i - x j‖^2) :
    (Fintype.card ι : ℝ) * (1-t^2)^((d : ℝ)/2) ≤ 2*((d : ℝ)+1)^2 := by
  let V := WithLp 2 (ℝ × E)
  have dimV : Module.finrank ℝ V = d+1 := by
    rw [(WithLp.linearEquiv 2 ℝ (ℝ × E)).finrank_eq, Module.finrank_prod, hE]
    simp [Nat.add_comm]
  let e := ((stdOrthonormalBasis ℝ V).reindex (finCongr dimV)).repr
  let h i := sqrt (1-‖x i‖^2)
  let v (i : ι) : V := WithLp.toLp 2 (h i, x i)
  have normv i : ‖v i‖ = 1 := by
    have hsv := WithLp.prod_norm_sq_eq_of_L2 (v i)
    change ‖v i‖^2 = ‖h i‖^2 + ‖x i‖^2 at hsv
    have hb : 0 ≤ 1-‖x i‖^2 := by
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) (ball i) 2]
    rw [Real.norm_eq_abs, sq_abs, show h i ^ 2 = _ from sq_sqrt hb] at hsv
    nlinarith [norm_nonneg (v i)]
  let lift (i : ι) : Sphere (d+1) :=
    ⟨e (v i), mem_sphere_zero_iff_norm.mpr (by rw [e.norm_map, normv])⟩
  apply sphericalPacking_card hd lift ht
  intro i j hij
  change ⟪e (v i), e (v j)⟫_ℝ ≤ t^2
  rw [e.inner_map_map]
  have hs := WithLp.prod_norm_sq_eq_of_L2 (v i-v j)
  change ‖v i-v j‖^2 = ‖h i-h j‖^2 + ‖x i-x j‖^2 at hs
  rw [norm_sub_sq_real, normv, normv] at hs
  nlinarith [sep hij, sq_nonneg ‖h i-h j‖]

/-- The nonzero Gaussian mass bound (3) for separated points outside the radius-`L`
open ball. The lattice case follows by applying the minimum to pairwise differences. -/
theorem gaussianPacking_of_separation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {d : ℕ} (hE : Module.finrank ℝ E = d) (hd : 2 ≤ d)
    {ι : Type*} (x : ι → E) {L u : ℝ} (hL : 0 < L) (hu : 0 < u)
    (floor : ∀ i, L ≤ ‖x i‖) (sep : Pairwise fun i j ↦ L ≤ ‖x i-x j‖) :
    (∑' i, exp (-(u * ‖x i‖^2))) ≤
      2*((d : ℝ)+1)^2 * Gamma (1+(d : ℝ)/2) * (2/(u*L^2))^((d : ℝ)/2) := by
  classical
  apply gaussianPackingExcess (fun i ↦ ‖x i‖^2) (fun i ↦ sq_nonneg _) d hu hL
  intro s R hR
  let S := s.filter (fun i ↦ ‖x i‖^2 < R)
  change (S.card : ℝ) ≤ _
  by_cases hRL : L^2 ≤ R
  · let a := L^2/(2*R)
    have ha : 0 < a := by dsimp [a]; positivity
    have ha' : a ≤ 1/2 := (div_le_iff₀ (by positivity)).2 (by linarith)
    let t := sqrt (1-a)
    have ht0 : 0 < t := sqrt_pos.mpr (by linarith)
    have ht : t^2 = 1-a := sq_sqrt (by linarith)
    let r := sqrt R
    have hr : 0 < r := sqrt_pos.mpr hR
    have hr2 : r^2 = R := sq_sqrt hR.le
    let y (i : S) := r⁻¹ • x i.val
    have normScale (v : E) : ‖r⁻¹ • v‖^2 = ‖v‖^2 / R := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), mul_pow, inv_pow, hr2]
      ring
    have b i : ‖y i‖ ≤ 1 := by
      have h := (Finset.mem_filter.mp i.2).2
      have hsq : ‖y i‖^2 ≤ 1 := (normScale _).le.trans ((div_le_one hR).2 h.le)
      nlinarith [norm_nonneg (y i)]
    have sp : Pairwise fun i j ↦ 2*(1-t^2) ≤ ‖y i-y j‖^2 := by
      intro i j hij
      change _ ≤ ‖r⁻¹ • x i.val-r⁻¹ • x j.val‖^2
      rw [← smul_sub, normScale, ht, le_div_iff₀ hR]
      have h := pow_le_pow_left₀ hL.le (sep (Subtype.val_injective.ne hij)) 2
      dsimp [a]
      field_simp
      nlinarith
    have hc := unitBallPacking_card hE hd y b ⟨ht0, by nlinarith⟩ sp
    simp only [ht, sub_sub_cancel, Fintype.card_coe] at hc
    have invA : 2*R/L^2 = a⁻¹ := by dsimp [a]; rw [inv_div]
    rw [invA, Real.inv_rpow ha.le, ← div_eq_mul_inv, le_div_iff₀ (rpow_pos_of_pos ha _)]
    exact hc
  · have empty : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro i hi
      exact hRL ((pow_le_pow_left₀ hL.le (floor i) 2).trans (Finset.mem_filter.mp hi).2.le))
    rw [empty, Finset.card_empty, Nat.cast_zero]
    positivity

/-- Full nonzero theta series of an additive lattice with a verified minimum. -/
theorem latticePackingExcess {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {d : ℕ} (hE : Module.finrank ℝ E = d) (hd : 2 ≤ d)
    (H : Submodule ℤ E) {L u : ℝ} (hL : 0 < L) (hu : 0 < u)
    (minimum : ∀ v ∈ H, v ≠ 0 → L ≤ ‖v‖) :
    (∑' v : {w : H // w ≠ 0}, exp (-(u * ‖(v.val : E)‖^2))) ≤
      2*((d : ℝ)+1)^2 * Gamma (1+(d : ℝ)/2) * (2/(u*L^2))^((d : ℝ)/2) := by
  apply gaussianPacking_of_separation hE hd _ hL hu
  · intro i
    exact minimum _ i.val.property (fun h ↦ i.property (Subtype.ext h))
  · intro i j hij
    exact minimum _ (H.sub_mem i.val.property j.val.property)
      (fun h ↦ hij (Subtype.ext (Subtype.ext (sub_eq_zero.mp h))))

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.sphericalPacking_card
#print axioms SigabaNeo.Wall1.unitBallPacking_card

#print axioms SigabaNeo.Wall1.gaussianPacking_of_separation
#print axioms SigabaNeo.Wall1.latticePackingExcess
