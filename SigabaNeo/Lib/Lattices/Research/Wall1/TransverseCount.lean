import SigabaNeo.Lib.Lattices.Research.Wall1.TransverseCoordinates

/-! The primitive short-projection count as an integral of the transverse kernel. -/
noncomputable section
open MeasureTheory ProbabilityTheory SigabaNeo.Rogers
open scoped ENNReal Pointwise
namespace SigabaNeo.Wall1

theorem measurableSet_shortShape {m : ℕ} (c : ℝ) : MeasurableSet (shortShape (m := m) c) := by
  apply measurableSet_quotient.mpr
  have eqn : QuotientGroup.mk ⁻¹' shortShape (m := m) c =
      ⋃ z : Fin m → ℤ, {g : SL m | 0 < ‖latticePoint g z‖ ∧ ‖latticePoint g z‖ < c} := by
    ext g
    simp [shortShape, points_mk, latticePoint]
  rw [show Quotient.mk'' ⁻¹' shortShape (m := m) c = _ from eqn]
  apply MeasurableSet.iUnion
  intro z
  let : BorelSpace (SL m) := ⟨rfl⟩
  have h : Continuous (fun g : SL m ↦ latticePoint g z) := by
    apply (PiLp.continuous_toLp 2 _).comp
    change Continuous (fun g : SL m ↦ g.val.mulVec _)
    unfold Matrix.mulVec dotProduct
    fun_prop
  exact (measurableSet_lt measurable_const h.norm.measurable).inter
    (measurableSet_lt h.norm.measurable measurable_const)

/-- Oriented marks in the window whose normalized physical quotient has a nonzero short point. -/
def shortProjectionTest {n : ℕ} (W : Set (E n)) (c : ℝ) (x : E n) (P : Set (E n)) : ℝ≥0∞ :=
  @ite _ (x ∈ W ∧ ∃ y ∈ P, 0 < ‖‖x‖ ^ ((n-1 : ℕ) : ℝ)⁻¹ • y‖ ∧
    ‖‖x‖ ^ ((n-1 : ℕ) : ℝ)⁻¹ • y‖ < c) (Classical.propDecidable _) 1 0

/-- A single probability kernel gives the expected count for every window and every cutoff. -/
theorem shortProjection_count_disintegration {m : ℕ} (i : Fin m) (hn : 2 ≤ m+1)
    (D : Set (SL (m+1))) (hm : MeasurableSet D)
    (hd : IsFundamentalDomain (integerGroup (m+1)).op D (groupHaar (m+1)))
    (hp : groupHaar (m+1) D ≠ 0) (hf : groupHaar (m+1) D ≠ ⊤) :
    ∃ K : Kernel (E (m+1)) (LatticeSpace m), IsMarkovKernel K ∧
      ∀ W : Set (E (m+1)), MeasurableSet W → ∀ c : ℝ,
        (∫⁻ g in D, ∑' v : ContentFiber (m+1) 1, shortProjectionTest W c
          (latticePoint g v.val.val) (projectedPoints g v.val.val) ∂groupHaar (m+1)) /
          groupHaar (m+1) D =
        (∫⁻ x in W, K x (shortShape c)) / ∑' k, dilationWeight (m+1) k := by
  classical
  obtain ⟨K, hK, law⟩ := transverseShape_disintegration i hn D hm hd hp hf
  refine ⟨K, hK, ?_⟩
  intro W hW c
  let S := shortShape (m := m) c
  let F := (W ×ˢ S).indicator (1 : E (m+1) × LatticeSpace m → ℝ≥0∞)
  have hF : Measurable F := measurable_one.indicator (hW.prod (measurableSet_shortShape c))
  let e : Fin (m+1) → ℤ := Pi.single 0 1
  have eqn (g : SL (m+1)) :
      shortProjectionTest W c (latticePoint g e) (projectedPoints g e) =
      F (markedColumn hn g, transverseShape i g) := by
    simp [F, S, Set.indicator, Set.mem_prod, transverseShape_short_iff i hn, shortProjectionTest,
      projectedPoints, normalizedProjection, markedColumn, e]
  have htest : Measurable fun g ↦ shortProjectionTest W c (latticePoint g e) (projectedPoints g e) := by
    simp_rw [eqn]
    exact hF.comp ((measurable_markedColumn hn).prodMk (measurable_transverseShape i))
  rw [primitive_projected_unfolding hn D hm hd _ htest]
  have H := law F hF
  simp only [primitiveIncidence, lintegral_smul_measure, smul_eq_mul] at H
  simp_rw [← eqn] at H
  rw [div_eq_mul_inv, mul_comm]
  refine H.trans ?_
  congr 1
  rw [← lintegral_indicator hW]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ W
  · simpa [F, Set.indicator, hx, Set.mem_prod, S] using
      (lintegral_indicator_one (μ := K x) (measurableSet_shortShape c))
  · simp [F, Set.indicator, Set.mem_prod, hx]

/-- Haar calibration for precisely the quotient-space event appearing in the count identity. -/
theorem domainProbability_shortShape_le {m : ℕ} (hn : 2 ≤ m) (D : Set (SL m))
    (hm : MeasurableSet D) (hd : IsFundamentalDomain (integerGroup m).op D (groupHaar m))
    (hp : groupHaar m D ≠ 0) (hf : groupHaar m D ≠ ⊤) {c : ℝ} (hc : 0 < c) :
    domainProbability (groupHaar m) D (shortShape c) ≤
      ENNReal.ofReal (c ^ m) * volume (Metric.ball (0 : E m) 1) /
        (2 * ∑' k, dilationWeight m k) := by
  rw [domainProbability, Measure.smul_apply, Measure.map_apply measurable_quotient_mk''
    (measurableSet_shortShape c), smul_eq_mul, mul_comm, ← div_eq_mul_inv]
  refine le_trans (ENNReal.div_le_div_right (measure_mono ?_) _) (haar_short_vector_upper
    hn D hm hd hp hf hc)
  intro g hg
  change ∃ y ∈ points (QuotientGroup.mk g), _ at hg
  rw [points_mk] at hg
  obtain ⟨_, ⟨z, rfl⟩, hpos, hlt⟩ := hg
  change 0 < ‖latticePoint g z‖ at hpos
  exact ⟨⟨z, fun he ↦ by simp [he] at hpos⟩, hlt⟩

/-- In ambient dimension two the transverse arithmetic quotient is a singleton,
so its conditional law is the Haar point mass for every base window. -/
theorem transverseShape_rankOne_product (D : Set (SL 2)) (hm : MeasurableSet D)
    (hd : IsFundamentalDomain (integerGroup 2).op D (groupHaar 2))
    (hp : groupHaar 2 D ≠ 0) (hf : groupHaar 2 D ≠ ⊤)
    (F : E 2 × LatticeSpace 1 → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ g, F (markedColumn (by decide : 2 ≤ 2) g, transverseShape (m := 1) 0 g)
      ∂primitiveIncidence (by decide : 2 ≤ 2) D) =
      (∫⁻ x, F (x, QuotientGroup.mk (1 : SL 1))) / ∑' k, dilationWeight 2 k := by
  have singleton (g : SL 1) : g = 1 := by
    apply Subtype.ext
    ext j k
    fin_cases j
    fin_cases k
    simpa [Matrix.det_fin_one] using g.property
  simp only [transverseShape, singleton (transverseFrame _ _)]
  have h := congrArg (fun μ : Measure (E 2) ↦ ∫⁻ x, F (x, QuotientGroup.mk (1 : SL 1)) ∂μ)
    (primitiveIncidence_map (by decide : 2 ≤ 2) D hm hd hp hf)
  rw [lintegral_map (show Measurable (fun x : E 2 ↦ F (x, QuotientGroup.mk (1 : SL 1))) from
    hF.comp (measurable_id.prodMk measurable_const))
    (measurable_markedColumn _), lintegral_smul_measure, smul_eq_mul, mul_comm] at h
  exact h

#print axioms transverseShape_rankOne_product
#print axioms domainProbability_shortShape_le
#print axioms measurableSet_shortShape
#print axioms shortProjection_count_disintegration
end SigabaNeo.Wall1
