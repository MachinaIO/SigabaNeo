import SigabaNeo.Lib.Lattices.Research.Wall1.RankTwoPlaneMean
import SigabaNeo.Lib.Lattices.Research.Wall1.TransverseUniqueness

/-! Disintegration of plane incidence over its selected basis. The remaining Haar product
identity is stated as `HaarProduct`. Its consequences below take it as a hypothesis. -/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix SigabaNeo.Rogers
open scoped ENNReal ProbabilityTheory
namespace SigabaNeo.Wall1.RankTwo

variable {r : ℕ} (i : Fin (r+1)) (j : Fin r)
local notation "n" => (r+2)
private theorem dim (j : Fin r) : 2 ≤ r+1 := by have := j.isLt; omega

/-- Straighten and normalize the first projection, then mark the primitive tail vector and
straighten and normalize again. Adding a lift along the first column has no effect. -/
def outerFrame (p : Core (r+1)) (g : SL n) : SL r :=
  transverseFrame j (primitiveTranslate (dim j) p.2.2 •
    transverseFrame i (primitiveTranslate (by omega) p.1 • g))

theorem measurable_outerFrame (p : Core (r+1)) : Measurable (outerFrame i j p) := by
  let bor (d : ℕ) : BorelSpace (SL d) := ⟨rfl⟩
  exact (measurable_transverseFrame j).comp ((MeasurableEquiv.mulRight _).measurable.comp
    ((measurable_transverseFrame i).comp (MeasurableEquiv.mulRight _).measurable))

private def mark (p : Core (r+1)) (g : SL n) :=
  (physical (dim j) g 0 0 p, outerFrame i j p g)

private theorem measurable_mark (p : Core (r+1)) : Measurable (mark i j p) :=
  (measurable_physical (dim j) 0 0 p).prodMk (measurable_outerFrame i j p)

def planeMarginal (d : ℕ) := ((zetaFactor d * zetaFactor (d-1))⁻¹ • frameVolume d).restrict
  (basisDomain d)

private def allJoint (D : Set (SL n)) : Measure (Frames n × SL r) :=
  (groupHaar n D)⁻¹ • Measure.sum fun p ↦ ((groupHaar n).restrict D).map (mark i j p)

/-- Joint counting measure. The basis domain counts each saturated submodule once. -/
def jointFrame (D : Set (SL n)) : Measure (Frames n × SL r) :=
  (allJoint i j D).restrict (Prod.fst ⁻¹' basisDomain n)

private theorem jointFrame_fst (D : Set (SL n))
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (hf : groupHaar n D ≠ ⊤) (hp : groupHaar n D ≠ 0) :
    (jointFrame i j D).map Prod.fst = planeMarginal n := by
  rw [jointFrame, ← Measure.restrict_map measurable_fst (measurableSet_basisDomain _)]
  unfold planeMarginal
  congr 1
  rw [allJoint, Measure.map_smul _ measurable_fst.aemeasurable,
    Measure.map_sum measurable_fst.aemeasurable]
  simp_rw [Measure.map_map measurable_fst (measurable_mark i j _)]
  change (groupHaar n D)⁻¹ • orderedMeasure (dim j) D = _
  rw [orderedMeasure_eq _ D hd hf, smul_smul, div_eq_mul_inv, ← mul_assoc,
    ENNReal.inv_mul_cancel hp hf, one_mul]
  rfl

/-- Incidence of the selected basis and the arithmetic coset of the twice-normalized frame. -/
def joint (D : Set (SL n)) : Measure (Frames n × LatticeSpace r) :=
  (jointFrame i j D).map (Prod.map id QuotientGroup.mk)

theorem joint_fst (D : Set (SL n))
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (hf : groupHaar n D ≠ ⊤) (hp : groupHaar n D ≠ 0) :
    (joint i j D).map Prod.fst = planeMarginal n := by
  rw [joint, Measure.map_map measurable_fst (measurable_id.prodMap measurable_quotient_mk'')]
  exact jointFrame_fst i j D hd hf hp

/-- Evaluate joint incidence directly on the ambient fundamental domain. The summand
vanishes except at the unique selected basis of each saturated integer plane. -/
theorem joint_apply (D : Set (SL n)) (S : Set (Frames n × LatticeSpace r))
    (hS : MeasurableSet S) :
    joint i j D S = (∫⁻ g in D, ∑' p : Core (r+1),
      ((Prod.fst ⁻¹' basisDomain n) ∩ S).indicator 1
        (physical (dim j) g 0 0 p, QuotientGroup.mk (outerFrame i j p g)) ∂groupHaar n) /
          groupHaar n D := by
  let q : Frames n × SL r → Frames n × LatticeSpace r := Prod.map id QuotientGroup.mk
  have hq : Measurable q := measurable_id.prodMap measurable_quotient_mk''
  let B := (Prod.fst ⁻¹' basisDomain n : Set (Frames n × LatticeSpace r)) ∩ S
  have hB : MeasurableSet B := (measurable_fst (measurableSet_basisDomain _)).inter hS
  rw [joint, Measure.map_apply hq hS, jointFrame, Measure.restrict_apply (hq hS)]
  have eqn : q ⁻¹' S ∩ Prod.fst ⁻¹' basisDomain n = q ⁻¹' B := by
    ext p; exact and_comm
  rw [eqn, allJoint, Measure.smul_apply, Measure.sum_apply _ (hq hB), smul_eq_mul,
    div_eq_mul_inv, mul_comm]
  congr 1
  let f (p : Core (r+1)) (g : SL n) :=
    B.indicator (1 : Frames n × LatticeSpace r → ℝ≥0∞) (q (mark i j p g))
  have mf (p) : Measurable (f p) :=
    (measurable_one.indicator hB).comp (hq.comp (measurable_mark i j p))
  change _ = ∫⁻ g in D, ∑' p, f p g ∂groupHaar n
  rw [lintegral_tsum fun p ↦ (mf p).aemeasurable]
  apply tsum_congr; intro p
  rw [Measure.map_apply (measurable_mark i j p) (hq hB)]
  have hpre : MeasurableSet ((q ∘ mark i j p) ⁻¹' B) :=
    hB.preimage (hq.comp (measurable_mark i j p))
  exact (lintegral_indicator_one (μ := (groupHaar n).restrict D) hpre).symm.trans (by
    apply lintegral_congr; intro g
    by_cases h : q (mark i j p g) ∈ B <;> simp [f, Set.indicator, h, Set.mem_preimage])

private theorem planeMarginal_sigmaFinite {d : ℕ} :
    SigmaFinite (planeMarginal d) := by
  let c := (zetaFactor d * zetaFactor (d-1))⁻¹
  have hc : c ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (mul_ne_zero (zetaFactor_ne_zero _) (zetaFactor_ne_zero _))
  let : SigmaFinite (frameVolume d) := Measure.pi.sigmaFinite _
  change SigmaFinite ((c • frameVolume d).restrict _)
  lift c to NNReal using hc with a ha
  let : SigmaFinite ((a : ℝ≥0∞) • frameVolume d) := SMul.sigmaFinite a
  infer_instance

private theorem local_kernel {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y] (μ : Measure (X × Y)) (η : Measure X)
    (hm : μ.map Prod.fst = η) (W : Set X) (hW : MeasurableSet W) (hf : η W ≠ ⊤) :
    ∃ K : Kernel X Y, IsMarkovKernel K ∧
      (η.restrict W) ⊗ₘ K = μ.restrict (Prod.fst ⁻¹' W) := by
  let ν := μ.restrict (Prod.fst ⁻¹' W)
  have marg : ν.map Prod.fst = η.restrict W := by
    rw [← hm, Measure.restrict_map measurable_fst hW]
  have : IsFiniteMeasure ν := ⟨by
    have h := congrArg (fun σ : Measure X ↦ σ Set.univ) marg
    simpa [Measure.map_apply measurable_fst] using h.trans_lt (by simpa using hf.lt_top)⟩
  refine ⟨condDistrib Prod.snd Prod.fst ν, inferInstance, ?_⟩
  rw [← marg, compProd_map_condDistrib measurable_fst.aemeasurable measurable_snd.aemeasurable]
  exact Measure.map_id

private theorem sigma_kernel {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y] (μ : Measure (X × Y)) (η : Measure X)
    [SigmaFinite η] (hm : μ.map Prod.fst = η) :
    ∃ K : Kernel X Y, IsMarkovKernel K ∧ μ = η ⊗ₘ K := by
  let W := disjointed (spanningSets η)
  have hW : ∀ k, MeasurableSet (W k) := MeasurableSet.disjointed (measurableSet_spanningSets η)
  choose K hK h using fun k ↦ local_kernel μ η hm (W k) (hW k)
    (((measure_mono (disjointed_subset _ _)).trans_lt (measure_spanningSets_lt_top η k)).ne)
  let J : Kernel X Y :=
    ⟨fun x ↦ K (spanningSetsIndex η x) x,
      (measurable_from_prod_countable_left (f := fun p : X × ℕ ↦ K p.2 p.1)
        (fun k ↦ (K k).measurable)).comp (measurable_id.prodMk (measurableSet_spanningSetsIndex η))⟩
  have hJ : IsMarkovKernel J := ⟨fun x ↦ (hK _).isProbabilityMeasure x⟩
  refine ⟨J,hJ,?_⟩
  apply Measure.ext_of_lintegral
  intro F hF
  have cov : ⋃ k, W k = Set.univ := iUnion_disjointed.trans (iUnion_spanningSets η)
  have pre : (⋃ k, (Prod.fst : X × Y → X) ⁻¹' W k) = Set.univ := by
    rw [← Set.preimage_iUnion,cov,Set.preimage_univ]
  have hμ := lintegral_iUnion (μ := μ) (fun k ↦ measurable_fst (hW k))
    (fun a b hab ↦ (disjoint_disjointed _ hab).preimage Prod.fst) F
  have hη := lintegral_iUnion (μ := η) hW (disjoint_disjointed _) (fun x ↦ ∫⁻ y, F (x,y) ∂J x)
  rw [pre, Measure.restrict_univ] at hμ
  rw [cov, Measure.restrict_univ] at hη
  rw [hμ,Measure.lintegral_compProd hF,hη]
  apply tsum_congr; intro k
  rw [← h k, Measure.lintegral_compProd hF]
  apply setLIntegral_congr_fun (hW k)
  intro x hx
  change _ = ∫⁻ y, F (x,y) ∂K (spanningSetsIndex η x) x
  rw [(spanningSetsIndex_eq_iff η).mpr hx]

/-- One Markov kernel over the selected plane basis disintegrates the entire incidence
measure, including all finite windows simultaneously. -/
theorem plane_disintegration (D : Set (SL n))
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (hf : groupHaar n D ≠ ⊤) (hp : groupHaar n D ≠ 0) :
    ∃ K : Kernel (Frames n) (LatticeSpace r), IsMarkovKernel K ∧
      joint i j D = planeMarginal n ⊗ₘ K := by
  let : PolishSpace (Matrix (Fin r) (Fin r) ℝ) :=
    inferInstanceAs (PolishSpace (Fin r → Fin r → ℝ))
  let : PolishSpace (SL r) := SpecialLinearGroup.isClosedEmbedding_val.polishSpace
  let : BorelSpace (SL r) := ⟨rfl⟩
  let := planeMarginal_sigmaFinite (d := n)
  obtain ⟨K,hK,he⟩ := sigma_kernel _ _ (jointFrame_fst i j D hd hf hp)
  exact ⟨K.map QuotientGroup.mk, Kernel.IsMarkovKernel.map K measurable_quotient_mk'',
    by rw [joint, he, Measure.compProd_map measurable_quotient_mk'']⟩

/-- The remaining rank-two product identity for an outer arithmetic fundamental domain Q. -/
def HaarProduct (D : Set (SL n)) (Q : Set (SL r)) : Prop :=
  joint i j D = (planeMarginal n).prod (domainProbability (groupHaar r) Q)

/-- The remaining stabilizer obligation has a single null set for all outer group elements.
Once it holds, uniqueness of invariant probability gives the full product. -/
theorem haarProduct_of_kernel_invariant (D : Set (SL n)) (Q : Set (SL r))
    (hq : IsFundamentalDomain (integerGroup r).op Q (groupHaar r))
    (qp : groupHaar r Q ≠ 0) (qf : groupHaar r Q ≠ ⊤)
    (K : Kernel (Frames n) (LatticeSpace r)) [IsMarkovKernel K]
    (law : joint i j D = planeMarginal n ⊗ₘ K)
    (inv : ∀ᵐ x ∂planeMarginal n, SMulInvariantMeasure (SL r) (LatticeSpace r) (K x)) :
    (∀ᵐ x ∂planeMarginal n, K x = domainProbability (groupHaar r) Q) ∧ HaarProduct i j D Q := by
  have he : ∀ᵐ x ∂planeMarginal n, K x = domainProbability (groupHaar r) Q := by
    filter_upwards [inv] with x hx
    exact transverse_invariant_probability_eq Q hq qp qf (K x)
  let := planeMarginal_sigmaFinite (d := n)
  let := domainProbability_probability (groupHaar r) Q qp qf
  refine ⟨he, ?_⟩
  unfold HaarProduct
  rw [law, ← Measure.compProd_const]
  exact Measure.compProd_congr he

/-- In ambient dimension three the normalized outer lattice is the unique element of X₁.
Consequently the rank-two Haar product holds without an additional fiber hypothesis. -/
theorem haarProduct_three (i : Fin 2) (D : Set (SL 3))
    (hd : IsFundamentalDomain (integerGroup 3).op D (groupHaar 3))
    (hf : groupHaar 3 D ≠ ⊤) (hp : groupHaar 3 D ≠ 0) (Q : Set (SL 1))
    (qp : groupHaar 1 Q ≠ 0) (qf : groupHaar 1 Q ≠ ⊤) : HaarProduct i 0 D Q := by
  have hSL (g : SL 1) : g = 1 := by
    apply Subtype.ext
    ext a b; fin_cases a; fin_cases b
    simpa [Matrix.det_fin_one] using g.property
  have sub : Subsingleton (LatticeSpace 1) := ⟨fun a b ↦ by
    induction a using Quotient.inductionOn with
    | _ a =>
      induction b using Quotient.inductionOn with
      | _ b => rw [hSL a, hSL b]⟩
  let H := domainProbability (groupHaar 1) Q
  have := domainProbability_probability (groupHaar 1) Q qp qf
  obtain ⟨K,hK,he⟩ := plane_disintegration i (0 : Fin 1) D hd hf hp
  have hk (x : Frames 3) : K x = H := by
    ext s hs
    rcases s.eq_empty_or_nonempty with h | ⟨y,hy⟩
    · simp [h]
    · have hu : s = Set.univ := Set.eq_univ_of_forall fun z ↦ sub.elim y z ▸ hy
      simp [hu,H]
  let := planeMarginal_sigmaFinite (d := 3)
  unfold HaarProduct
  rw [he, ← Measure.compProd_const]
  exact Measure.compProd_congr (Filter.Eventually.of_forall hk)

/-- Conditional on the rank-two Haar product, any Borel plane window has the rank-one
primitive-line upper bound for a normalized outer minimum below c. -/
theorem window_bound_of_haar (hr : 2 ≤ r) (D : Set (SL n)) (Q : Set (SL r))
    (hqM : MeasurableSet Q) (hq : IsFundamentalDomain (integerGroup r).op Q (groupHaar r))
    (qp : groupHaar r Q ≠ 0) (qf : groupHaar r Q ≠ ⊤) (law : HaarProduct i j D Q)
    (W : Set (Frames n)) {c : ℝ} (hc : 0 < c) :
    joint i j D (W ×ˢ shortShape c) ≤
      planeMarginal n W * (ENNReal.ofReal (c^r) * volume (Metric.ball (0 : E r) 1) /
        (2 * zetaFactor r)) := by
  let := domainProbability_probability (groupHaar r) Q qp qf
  let := planeMarginal_sigmaFinite (d := n)
  rw [law, Measure.prod_prod]
  exact mul_le_mul_right (domainProbability_shortShape_le hr Q hqM hq qp qf hc) _

end SigabaNeo.Wall1.RankTwo

#print axioms SigabaNeo.Wall1.RankTwo.joint_fst
#print axioms SigabaNeo.Wall1.RankTwo.plane_disintegration
#print axioms SigabaNeo.Wall1.RankTwo.window_bound_of_haar

#print axioms SigabaNeo.Wall1.RankTwo.haarProduct_three
#print axioms SigabaNeo.Wall1.RankTwo.joint_apply
#print axioms SigabaNeo.Wall1.RankTwo.haarProduct_of_kernel_invariant
