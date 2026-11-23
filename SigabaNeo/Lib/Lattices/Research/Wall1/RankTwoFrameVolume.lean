import SigabaNeo.Lib.Lattices.Research.Wall1.RankTwoAreaJacobian
import SigabaNeo.Lib.Lattices.Research.Wall1.RankTwoOuterGeometry

/-! Lebesgue measure of the two physical columns in area and planar shape coordinates. -/
noncomputable section
open Matrix MeasureTheory SigabaNeo.Rogers Set
open scoped ENNReal
namespace SigabaNeo.Wall1.RankTwo

private abbrev surface (k : ℕ) : ℝ≥0∞ := k * volume (Metric.ball (0 : E k) 1)

private theorem radial {k : ℕ} (hk : 0 < k) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x : E k, F ‖x‖) = surface k * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t^(k-1)) * F t := by
  let : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
  let μ := (volume : Measure (E k))
  let σ := μ.toSphere
  let ρ := Measure.volumeIoiPow (Module.finrank ℝ (E k) - 1)
  let H (p : Metric.sphere (0 : E k) 1 × Ioi (0 : ℝ)) := F p.2
  have hH : Measurable H := hF.comp (measurable_subtype_coe.comp measurable_snd)
  have h := μ.measurePreserving_homeomorphUnitSphereProd.lintegral_comp hH
  simp only [H,homeomorphUnitSphereProd_apply_snd_coe] at h
  change (∫⁻ x : ({0}ᶜ : Set (E k)), F ‖x.val‖ ∂μ.comap Subtype.val) =
    ∫⁻ p, H p ∂σ.prod ρ at h
  rw [lintegral_subtype_comap (measurableSet_singleton _).compl (fun x ↦ F ‖x‖),
    restrict_compl_singleton, lintegral_prod H hH.aemeasurable] at h
  change _ = ∫⁻ _y, ∫⁻ z : Ioi (0 : ℝ), F z ∂ρ ∂σ at h
  rw [lintegral_const, mul_comm] at h
  change (∫⁻ x : E k, F ‖x‖ ∂μ) = _
  rw [h]
  change μ.toSphere univ * _ = _
  rw [Measure.toSphere_apply_univ, finrank_euclideanSpace_fin]
  congr 1
  unfold ρ Measure.volumeIoiPow
  rw [finrank_euclideanSpace_fin, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
    (show Measurable (fun z : Ioi (0:ℝ) ↦ F z) from hF.comp measurable_subtype_coe)]
  exact lintegral_subtype_comap (μ := volume) (measurableSet_Ioi (a := (0:ℝ)))
    (fun t : ℝ ↦ ENNReal.ofReal (t^(k-1)) * F t)

private def splitColumn {m : ℕ} (z : E (m+1)) : ℝ × E m :=
  (z 0,WithLp.toLp 2 (fun k ↦ z k.succ))

private theorem splitColumn_measurePreserving {m : ℕ} :
    MeasurePreserving (@splitColumn m) := by
  have h := ((MeasurePreserving.id (μ := (volume : Measure ℝ))).prod
    (PiLp.volume_preserving_toLp (Fin m))).comp
      ((volume_preserving_piFinSuccAbove (fun _ : Fin (m+1) ↦ ℝ) 0).comp
        (PiLp.volume_preserving_ofLp (Fin (m+1))))
  convert h using 1
  funext z
  exact Prod.ext rfl (congrArg (WithLp.toLp 2) (funext fun k ↦ congrArg _ (Fin.zero_succAbove k).symm))

def triangular {m : ℕ} (i : Fin m) (v : Frames (m+1)) : Triple :=
  let w := splitColumn (transverseRotation i (v 0) (v 1))
  ![‖v 0‖, w.1, ‖w.2‖]

private theorem measurable_triple {X : Type*} [MeasurableSpace X] {a b c : X → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) :
    Measurable (fun x ↦ (![a x,b x,c x] : Triple)) := by
  apply Measurable.of_eval
  intro i; fin_cases i
  · exact ha
  · exact hb
  · exact hc

private theorem triple_integral (F : Triple → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p in positiveTriples, F p) =
      ∫⁻ a in Ioi (0 : ℝ), ∫⁻ s : ℝ, ∫⁻ t in Ioi (0 : ℝ), F ![a,s,t] := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).trans
    ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)))
  have he : MeasurePreserving e := (volume_preserving_piFinSuccAbove _ 0).trans
    ((MeasurePreserving.id (μ := volume)).prod (volume_preserving_piFinTwo _))
  have hfun (p : ℝ × ℝ × ℝ) : e.symm p = ![p.1,p.2.1,p.2.2] := by
    funext k; fin_cases k <;> rfl
  have himg : e.symm '' (Ioi 0 ×ˢ (univ ×ˢ Ioi 0)) = positiveTriples := by
    ext p
    rw [show e.symm '' (Ioi 0 ×ˢ (univ ×ˢ Ioi 0)) = e ⁻¹' (Ioi 0 ×ˢ (univ ×ˢ Ioi 0)) from e.toEquiv.image_symm_eq_preimage _]
    change (0 < p 0 ∧ _ ∈ univ ∧ 0 < p 2) ↔ _
    simp [positiveTriples]
  rw [← himg, ← he.symm.setLIntegral_comp_emb e.symm.measurableEmbedding,
    show (volume : Measure (ℝ × ℝ × ℝ)) = volume.prod (volume.prod volume) from rfl,
    ← Measure.prod_restrict, ← Measure.prod_restrict, Measure.restrict_univ,
    lintegral_prod (fun p ↦ F (e.symm p)) (hF.comp e.symm.measurable).aemeasurable]
  apply lintegral_congr; intro a
  rw [lintegral_prod (fun p : ℝ × ℝ ↦ F (e.symm (a,p))) ((hF.comp e.symm.measurable).comp (measurable_const.prodMk measurable_id)).aemeasurable]
  simp only [hfun]

set_option maxHeartbeats 800000 in
private theorem triangular_integral {m : ℕ} (i : Fin m) (F : Triple → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v, F (triangular i v) ∂frameVolume (m+1)) =
      surface (m+1) * surface m * ∫⁻ p in positiveTriples,
        ENNReal.ofReal ((p 0)^m * (p 2)^(m-1)) * F p := by
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  let T (a : ℝ) (q : ℝ × E m) := F ![a, q.1, ‖q.2‖]
  have mT (a : ℝ) : Measurable (T a) := hF.comp
    (measurable_triple measurable_const measurable_fst measurable_snd.norm)
  let L (a : ℝ) := ∫⁻ q : ℝ × E m, T a q
  have mL : Measurable L := Measurable.lintegral_prod_right' (hF.comp
    (measurable_triple measurable_fst (measurable_fst.comp measurable_snd)
      (measurable_snd.comp measurable_snd).norm))
  have mt : Measurable (fun v : Frames (m+1) ↦ triangular i v) := by
    have hv : Measurable (fun v : Frames (m+1) ↦ (v 0, v 1)) :=
      (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
    have hw : Measurable (fun v : Frames (m+1) ↦ transverseRotation i (v 0) (v 1)) :=
      (measurable_transverseRotation i).comp hv
    have h := (@splitColumn_measurePreserving m).measurable.comp hw
    exact measurable_triple (measurable_pi_apply 0).norm h.fst h.snd.norm
  have hsplit := (measurePreserving_finTwoArrow (volume : Measure (E (m+1)))).symm
  rw [← hsplit.lintegral_comp (f := fun v ↦ F (triangular i v)) (hF.comp mt)]
  rw [lintegral_prod (fun p ↦ F (triangular i (MeasurableEquiv.finTwoArrow.symm p)))
    ((hF.comp mt).comp MeasurableEquiv.finTwoArrow.symm.measurable).aemeasurable]
  have step (x : E (m+1)) : (∫⁻ y : E (m+1), T ‖x‖ (splitColumn (transverseRotation i x y))) =
      L ‖x‖ :=
    (splitColumn_measurePreserving.comp (transverseRotation i x).measurePreserving).lintegral_comp (mT _)
  change (∫⁻ x, ∫⁻ y, T ‖x‖ (splitColumn (transverseRotation i x y))) = _
  simp_rw [step]
  rw [radial (by omega : 0 < m+1) L mL, mul_assoc (surface (m+1)) (surface m), triple_integral _ (by fun_prop)]
  congr 1
  have w (a s : ℝ) := radial hm (fun t ↦ F ![a,s,t])
    (hF.comp (measurable_triple measurable_const measurable_const measurable_id))
  have hconst : surface m ≠ ⊤ := ENNReal.mul_ne_top (by simp) measure_ball_lt_top.ne
  rw [← lintegral_const_mul' _ _ hconst]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro a ha
  dsimp only
  change ENNReal.ofReal (a^m) * L a = _
  unfold L
  rw [show (volume : Measure (ℝ × E m)) = volume.prod volume from rfl, lintegral_prod _ (mT a).aemeasurable]
  change ENNReal.ofReal (a^m) * (∫⁻ s : ℝ, ∫⁻ v : E m, F ![a,s,‖v‖]) = _
  simp_rw [w]
  rw [lintegral_const_mul' _ _ hconst, mul_left_comm]
  congr 1
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr; intro s
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change _ = ENNReal.ofReal (a^m * t^(m-1)) * _
  rw [ENNReal.ofReal_mul (pow_nonneg ha.le _), mul_assoc]

/-- Joint Lebesgue density for area and upper half-plane coordinates of unrestricted
ordered frames. The quotient by integral basis changes is a separate restriction. -/
theorem frameVolume_areaChart {m : ℕ} (i : Fin m) (F : Triple → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v, F (areaChart (triangular i v)) ∂frameVolume (m+1)) =
      surface (m+1) * surface m / 2 * ∫⁻ q in positiveTriples,
        ENNReal.ofReal ((q 0)^m / (q 2)^2) * F q := by
  have hm : 2 ≤ m+1 := by have := i.isLt; omega
  have hC : Measurable areaChart := measurable_triple (by fun_prop) (by fun_prop) (by fun_prop)
  rw [triangular_integral i (fun p ↦ F (areaChart p)) (hF.comp hC)]
  have h := areaChart_weighted_integral (m+1) hm F
  simp only [Nat.add_sub_cancel, show m+1-2 = m-1 by omega] at h
  rw [h]
  have e (p : Triple) : ENNReal.ofReal (2*p 0^m*p 2^(m-1)) =
      2 * ENNReal.ofReal (p 0^m*p 2^(m-1)) := by
    rw [mul_assoc,ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  simp_rw [e,mul_assoc (2 : ℝ≥0∞)]
  rw [lintegral_const_mul' _ _ (by norm_num), ← mul_assoc (_ / 2) 2, ENNReal.div_mul_cancel (by norm_num) (by norm_num)]

/-- The first chart coordinate is the Gram area of the original two columns. -/
theorem areaChart_area {r : ℕ} (i : Fin (r+1)) (x : Frames (r+2)) :
    areaChart (triangular i x) 0 = area x := by
  by_cases hz : x 0 = 0
  · simp [areaChart, triangular, area, det_fin_two, gram_apply, hz]
  let a := ‖x 0‖ ^ ((r+1 : ℕ) : ℝ)⁻¹
  let w := (splitColumn (transverseRotation i (x 0) (x 1))).2
  have he : normalizedTail i (x 0) (x 1) = a • w := rfl
  have ha : 0 < a := Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) _
  apply mul_right_cancel₀ ha.ne'
  change (‖x 0‖ * ‖w‖)*a = area x * a
  rw [area_mul_scale i x, he, norm_smul, Real.norm_of_nonneg ha.le]
  ring

/-- At positive area the Gauss inequalities cut out the closed modular region. -/
theorem gaussReduced_iff_areaChart {r : ℕ} (i : Fin (r+1)) (x : Frames (r+2))
    (hx : x 0 ≠ 0) :
    let q := areaChart (triangular i x)
    GaussReduced x ↔ |q 1| ≤ 1/2 ∧ 1 ≤ (q 1)^2 + (q 2)^2 := by
  intro q
  let z := transverseRotation i (x 0) (x 1)
  let b := ‖(splitColumn z).2‖
  let a := ‖x 0‖
  have ha : 0 < a := norm_pos_iff.mpr hx
  have hs : ‖x 1‖^2 = (z 0)^2 + b^2 := by
    rw [← (transverseRotation i (x 0)).norm_map (x 1)]
    change ‖z‖^2 = (z 0)^2 + ‖(splitColumn z).2‖^2
    rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ,EuclideanSpace.real_norm_sq_eq]; rfl
  have he : inner ℝ (x 0) (x 1) = a * z 0 := by
    rw [← (transverseRotation i (x 0)).inner_map_map (x 0) (x 1), transverseRotation_mark,
      real_inner_smul_left, EuclideanSpace.inner_single_left]
    simp [a,z]
  change (a ≤ ‖x 1‖ ∧ 2 * |inner ℝ (x 0) (x 1)| ≤ a^2) ↔
    |z 0/a| ≤ 1/2 ∧ 1 ≤ (z 0/a)^2 + (b/a)^2
  rw [he, abs_mul, abs_div, abs_of_pos ha, div_le_iff₀ ha,
    div_pow, div_pow, ← add_div,le_div_iff₀ (sq_pos_of_pos ha),one_mul,← hs,
    sq_le_sq₀ ha.le (norm_nonneg _)]
  have h : 2*(a * |z 0|) ≤ a^2 ↔ |z 0| ≤ 1/2*a := by
    rw [pow_two,show 2*(a * |z 0|) = a*(2 * |z 0|) by ring, mul_le_mul_iff_right₀ ha]
    constructor <;> intro h <;> linarith
  rw [h,and_comm]

end SigabaNeo.Wall1.RankTwo

#print axioms SigabaNeo.Wall1.RankTwo.frameVolume_areaChart

#print axioms SigabaNeo.Wall1.RankTwo.areaChart_area
#print axioms SigabaNeo.Wall1.RankTwo.gaussReduced_iff_areaChart
