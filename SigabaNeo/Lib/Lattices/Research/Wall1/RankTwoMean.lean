import SigabaNeo.Lib.Lattices.Research.Wall1.RankTwoFrames
import SigabaNeo.Lib.Lattices.Research.Wall1.RankTwoDivisors
import SigabaNeo.Lib.Lattices.Reduction.Rogers.RogersOrderKJacobian

/-! The two successive content sieves for primitive ordered rank-two frames. -/

noncomputable section
open Matrix MeasureTheory SigabaNeo.Rogers
open scoped ENNReal
namespace SigabaNeo.Wall1.RankTwo

abbrev Frames (n : ℕ) := Fin 2 → E n
abbrev frameVolume (n : ℕ) := Measure.pi (fun _ : Fin 2 ↦ (volume : Measure (E n)))

variable {m : ℕ} (hm : 2 ≤ m)
local notation "n" => (m+1)

def physical (g : SL n) (a b : ℕ) (p : Core m) : Frames n :=
  ![latticePoint g (first a p), latticePoint g (second (by omega) b p)]

theorem measurable_physical (a b : ℕ) (p : Core m) :
    Measurable (fun g : SL n ↦ physical hm g a b p) := by
  let : BorelSpace (SL n) := ⟨rfl⟩
  apply Measurable.of_eval
  intro j
  have meas (z : IV n) : Measurable (fun g : SL n ↦ latticePoint g z) := by
    apply Continuous.measurable
    apply (PiLp.continuous_toLp 2 _).comp
    change Continuous (fun g : SL n ↦ g.val.mulVec _)
    unfold Matrix.mulVec dotProduct
    fun_prop
  fin_cases j <;> exact meas _

private def term (D : Set (SL n)) (F : Frames n → ℝ≥0∞) (a b : ℕ) (p : Core m) :=
  ∫⁻ g in D, F (physical hm g a b p) ∂groupHaar n

private theorem all_mean (D : Set (SL n))
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hf : groupHaar n D ≠ ⊤)
    (F : Frames n → ℝ≥0∞) (hF : Measurable F) :
    (∑' a, ∑' b, ∑' p, term hm D F a b p) =
      groupHaar n D * ∫⁻ x, F x ∂frameVolume n := by
  obtain ⟨C,hC⟩ := independentPairMeasure_proportional (by omega : 2 < n) hd hf
  rw [← independentPairMeasure_scalar_calibration (by omega : 2 < n) hd hf hC,
    ← smul_eq_mul, ← lintegral_smul_measure, ← hC, independentPairMeasure_lintegral D F hF,
    ← (Equiv.ofBijective _ (bijective_toPair (by omega : 1 ≤ m))).tsum_eq, tsum_prod']
  apply tsum_congr
  intro a
  rw [tsum_prod']
  apply tsum_congr
  intro b
  apply tsum_congr
  intro p
  apply lintegral_congr
  intro g
  apply congrArg F
  funext i
  fin_cases i <;> rfl

private def changeBasis (d a b : ℕ) (r : ℤ) :=
  frameBasisChange d !![(a+1 : ℕ), 0; (r : ℝ), (b+1 : ℕ)]

private theorem change_meas (d a b : ℕ) (r : ℤ) : Measurable (changeBasis d a b r) :=
  (changeBasis d a b r).continuous_of_finiteDimensional.measurable

private theorem change_integral (d a b : ℕ) (r : ℤ) (F : Frames d → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F (changeBasis d a b r x) ∂frameVolume d) =
      (dilationWeight d a * dilationWeight d b) * ∫⁻ x, F x ∂frameVolume d := by
  rw [← lintegral_map hF (change_meas ..)]
  unfold changeBasis
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by
    rw [frameBasisChange_det]
    exact pow_ne_zero _ (by
      simpa [Matrix.det_fin_two] using (show ((a+1 : ℕ) : ℝ) * ((b+1 : ℕ) : ℝ) ≠ 0 by positivity))),
    lintegral_smul_measure, frameBasisChange_det, Matrix.det_fin_two]
  simp [dilationWeight, mul_pow, abs_mul, ENNReal.ofReal_mul, mul_comm]

private def liftResidue (k : ℕ) (r : Fin (k+1)) (p : Core m) : Core m :=
  (p.1, p.2.1 * (k+1 : ℕ) + r.val, p.2.2)

private theorem point_int (g : SL n) (c : ℤ) (z : IV n) :
    latticePoint g (c • z) = (c : ℝ) • latticePoint g z := by
  rw [map_zsmul, Int.cast_smul_eq_zsmul]

private theorem physical_first (g : SL n) (k a b : ℕ) (p : Core m) :
    physical hm g (times k a) b p = changeBasis n k 0 0 (physical hm g a b p) := by
  have he : first (times k a) p = ((k+1 : ℕ) : ℤ) • first a p := by
    rw [first, scaled_val, times_succ, Nat.cast_mul, mul_smul]; rfl
  have hpoint := congrArg (latticePoint g) he
  rw [point_int] at hpoint
  ext i j
  fin_cases i
  · simpa [physical, changeBasis, frameBasisChange_apply, Fin.sum_univ_two, PiLp.smul_apply]
      using congrArg (fun v : E n ↦ v j) hpoint
  · simp [physical, changeBasis, frameBasisChange_apply, Fin.sum_univ_two]

private theorem physical_second (g : SL n) (k b : ℕ) (r : Fin (k+1)) (p : Core m) :
    physical hm g 0 (times k b) (liftResidue k r p) =
      changeBasis n 0 k r.val (physical hm g 0 b p) := by
  have he : second (by omega) (times k b) (liftResidue k r p) =
      (r.val : ℤ) • first 0 p + ((k+1 : ℕ) : ℤ) • second (by omega) b p := by
    have hx : first 0 p = completion (by omega) p.1 (Pi.single 0 1) := by
      rw [completion_axis, first, scaled_val]; simp
    rw [hx]
    unfold second
    change completion _ p.1 _ = _
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    funext j
    refine Fin.cases (by simp [liftResidue, mul_comm, add_comm]) (fun i ↦ ?_) j
    simp [liftResidue, scaled_val, mul_assoc]
  have hpoint := congrArg (latticePoint g) he
  rw [map_add, point_int, point_int] at hpoint
  ext i j
  fin_cases i
  · simp [physical, changeBasis, frameBasisChange_apply, Fin.sum_univ_two, first, liftResidue]
  · simpa [physical, changeBasis, frameBasisChange_apply, Fin.sum_univ_two, PiLp.add_apply,
      PiLp.smul_apply] using congrArg (fun v : E n ↦ v j) hpoint

private theorem sum_lifts (k : ℕ) (f : Core m → ℝ≥0∞) :
    (∑' p, f p) = ∑' r : Fin (k+1), ∑' p, f (liftResidue k r p) := by
  let e : (Fin (k+1) × Core m) ≃ Core m := {
    toFun := fun p ↦ liftResidue k p.1 p.2
    invFun := fun ⟨u,t,v⟩ ↦ ((Int.divModEquiv (k+1) t).2,u,(Int.divModEquiv (k+1) t).1,v)
    left_inv := by
      rintro ⟨r,u,t,v⟩
      have he := (Int.divModEquiv (k+1)).apply_symm_apply (t,r)
      change Int.divModEquiv (k+1) (t * (k+1 : ℕ) + ↑r.val) = _ at he
      exact congrArg (fun q : ℤ × Fin (k+1) ↦ (q.2,u,q.1,v)) he
    right_inv := by
      rintro ⟨u,t,v⟩
      exact congrArg (fun j : ℤ ↦ (u,j,v)) ((Int.divModEquiv (k+1)).symm_apply_apply t) }
  rw [← e.tsum_eq f, tsum_prod']
  rfl

private theorem first_mean (D : Set (SL n))
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hf : groupHaar n D ≠ ⊤)
    (F : Frames n → ℝ≥0∞) (hF : Measurable F) (hfin : ∫⁻ x, F x ∂frameVolume n ≠ ⊤) :
    (∑' b, ∑' p, term hm D F 0 b p) =
      (groupHaar n D * ∫⁻ x, F x ∂frameVolume n) / zetaFactor n := by
  apply sieve_series (by omega : 1 < n) (fun a ↦ ∑' b, ∑' p, term hm D F a b p) _
    (ENNReal.mul_ne_top hf hfin)
  intro k
  simp only [term, physical_first hm]
  have he := all_mean hm D hd hf (F ∘ changeBasis n k 0 0) (hF.comp (change_meas ..))
  unfold term at he
  simp only [Function.comp_apply] at he
  rw [he, change_integral _ _ _ _ _ hF]
  simp [dilationWeight, mul_left_comm]

/-- Unrestricted primitive ordered bases, integrated on the ambient fundamental domain.
The second positive content is computed in the quotient by the first primitive vector. -/
theorem ordered_mean_finite (D : Set (SL n))
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hf : groupHaar n D ≠ ⊤)
    (F : Frames n → ℝ≥0∞) (hF : Measurable F) (hfin : (∫⁻ x, F x ∂frameVolume n) ≠ ⊤) :
    (∫⁻ g in D, ∑' p : Core m, F (physical hm g 0 0 p) ∂groupHaar n) =
      (groupHaar n D * ∫⁻ x, F x ∂frameVolume n) / (zetaFactor n * zetaFactor m) := by
  rw [lintegral_tsum (f := fun p g ↦ F (physical hm g 0 0 p))
    (fun p ↦ (hF.comp (measurable_physical hm 0 0 p)).aemeasurable),
    show ∀ M : ℝ≥0∞, M / (zetaFactor n * zetaFactor m) = M / zetaFactor n / zetaFactor m by
      intro M
      simp [div_eq_mul_inv, ENNReal.mul_inv,
        zetaFactor_ne_top (by omega : 1 < n), zetaFactor_ne_top (by omega : 1 < m), mul_assoc]]
  apply sieve_series (by omega : 1 < m) (fun b ↦ ∑' p, term hm D F 0 b p) _
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top hf hfin)
      (ENNReal.inv_ne_top.mpr (zetaFactor_ne_zero _)))
  intro k
  conv_lhs => arg 1; intro b; rw [sum_lifts k]
  rw [tsum_comm]
  have hj (r : Fin (k+1)) := change_integral n 0 k r.val F hF
  simp only [dilationWeight, zero_add, Nat.cast_one, one_pow, inv_one, abs_one,
    ENNReal.ofReal_one, one_mul] at hj
  have eqn (r : Fin (k+1)) :
      (∑' b, ∑' p, term hm D F 0 (times k b) (liftResidue k r p)) =
        dilationWeight n k * ((groupHaar n D * ∫⁻ x, F x ∂frameVolume n) / zetaFactor n) := by
    simp only [term, physical_second hm]
    have he := first_mean hm D hd hf (F ∘ changeBasis n 0 k r.val) (hF.comp (change_meas ..))
      (by rw [show (∫⁻ x, (F ∘ changeBasis n 0 k r.val) x ∂frameVolume n) = _ from hj r]
          exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)
    unfold term at he
    simp only [Function.comp_apply] at he
    rw [he, hj r]
    unfold dilationWeight
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ac_rfl
  simp_rw [eqn]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← mul_assoc]
  congr 1
  unfold dilationWeight
  have hpos : 0 < ((k+1 : ℕ) : ℝ) := by positivity
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hpos.le]
  congr 1
  rw [pow_succ, abs_of_pos (by positivity), abs_of_pos (by positivity)]
  field_simp

/-- Campbell measure of the ordered primitive two-frames in ambient lattice coordinates. -/
def orderedMeasure (D : Set (SL n)) : Measure (Frames n) :=
  Measure.sum fun p : Core m ↦ ((groupHaar n).restrict D).map (fun g ↦ physical hm g 0 0 p)

theorem orderedMeasure_integral (D : Set (SL n)) (F : Frames n → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x ∂orderedMeasure hm D) =
      ∫⁻ g in D, ∑' p : Core m, F (physical hm g 0 0 p) ∂groupHaar n := by
  rw [orderedMeasure, lintegral_sum_measure,
    lintegral_tsum (f := fun p g ↦ F (physical hm g 0 0 p))
      (fun p ↦ (hF.comp (measurable_physical hm 0 0 p)).aemeasurable)]
  exact tsum_congr fun p ↦ lintegral_map hF (measurable_physical hm 0 0 p)

/-- Measure identity, including all nonnegative Borel tests of infinite mass. -/
theorem orderedMeasure_eq (D : Set (SL n))
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hf : groupHaar n D ≠ ⊤) :
    orderedMeasure hm D =
      (groupHaar n D / (zetaFactor n * zetaFactor m)) • frameVolume n := by
  let : SigmaFinite (frameVolume n) := Measure.pi.sigmaFinite _
  rw [Measure.ext_iff_of_iUnion_eq_univ (iUnion_spanningSets (frameVolume n))]
  intro i
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs, Measure.smul_apply, smul_eq_mul]
  let W := s ∩ spanningSets (frameVolume n) i
  have hW : MeasurableSet W := hs.inter (measurableSet_spanningSets _ _)
  have e := ordered_mean_finite hm D hd hf (W.indicator 1) (measurable_one.indicator hW)
    (by rw [lintegral_indicator_one hW]
        exact ((measure_mono Set.inter_subset_right).trans_lt (measure_spanningSets_lt_top _ i)).ne)
  rw [← orderedMeasure_integral hm D _ (measurable_one.indicator hW),
    lintegral_indicator_one hW, lintegral_indicator_one hW] at e
  exact e.trans (by simp only [div_eq_mul_inv]; ac_rfl)

end SigabaNeo.Wall1.RankTwo

#print axioms SigabaNeo.Wall1.RankTwo.ordered_mean_finite

#print axioms SigabaNeo.Wall1.RankTwo.orderedMeasure_eq
