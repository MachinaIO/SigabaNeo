import SigabaNeo.Lib.Lattices.Research.Wall1.TransverseShapeInvariance
import SigabaNeo.Lib.Lattices.Research.Wall1.TransverseCocycle

/-! Product law for the primitive mark and its transverse lattice. -/
noncomputable section
open MeasureTheory ProbabilityTheory SigabaNeo.Rogers
open scoped ENNReal ProbabilityTheory
namespace SigabaNeo.Wall1

private theorem orbit_unique {G X : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    [MeasurableSpace X] (ρ : Measure G) [SigmaFinite ρ] [NeZero ρ] [ρ.IsMulRightInvariant]
    (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν] (A : G → X ≃ᵐ X)
    (hA : Measurable fun p : G × X ↦ A p.1 p.2)
    (mulA : ∀ a b x, A (a*b) x = A a (A b x))
    (hm : ∀ a, μ.map (A a) = μ) (hn : ∀ a, ν.map (A a) = ν)
    (good : Set X) (hg : ∀ᵐ x ∂μ+ν, x ∈ good)
    (trans : ∀ x ∈ good, ∀ y ∈ good, ∃ b, A b x = y)
    (S : Set X) (hs : μ S = ν S) (hp : μ S ≠ 0) (hf : μ S ≠ ⊤) : μ = ν := by
  let τ := μ + ν
  have : NeZero τ := ⟨fun h ↦ hp (by
    have e := congrArg (fun η : Measure X ↦ η S) h
    simpa [τ, ← hs] using e)⟩
  let f := μ.rnDeriv τ
  have meas : Measurable f := Measure.measurable_rnDeriv _ _
  have fixed (a : G) : ∀ᵐ x ∂τ, f (A a x) = f x := by
    have ht : τ.map (A a) = τ := by simp [τ, Measure.map_add, (A a).measurable, hm, hn]
    simpa only [Filter.EventuallyEq, f, hm, ht] using (A a).measurableEmbedding.rnDeriv_map μ τ
  have swap := (Measure.ae_ae_comm (μ := ρ) (ν := τ)
    (measurableSet_eq_fun (meas.comp hA) (meas.comp measurable_snd))).mp
      (Filter.Eventually.of_forall fixed)
  obtain ⟨x,hx,hgx⟩ := (swap.and hg).exists
  have hc : f =ᵐ[τ] fun _ ↦ f x := by
    filter_upwards [swap,hg] with y hy hgy
    obtain ⟨b,hb⟩ := trans x hgx y hgy
    obtain ⟨a,ha,hab⟩ := (hy.and ((measurePreserving_mul_right ρ b).quasiMeasurePreserving.ae hx)).exists
    exact ha.symm.trans (by simpa [mulA,hb] using hab)
  have he : μ = f x • τ := by
    rw [← Measure.withDensity_rnDeriv_eq μ τ ((Measure.AbsolutelyContinuous.rfl (μ := μ)).add_right ν),
      withDensity_congr_ae hc, withDensity_const]
  have mass := congrArg (fun η : Measure X ↦ η S) he
  have eqmass : (f x + f x) * μ S = 1 * μ S := by
    simpa [τ, Measure.smul_apply, ← hs, add_mul, mul_add] using mass.symm
  have half := (ENNReal.mul_left_inj hp hf).mp eqmass
  have nz : f x ≠ 0 := by intro h; simp [h] at half
  have nt : f x ≠ ⊤ := by intro h; simp [h] at half
  have h₂ : μ = f x • μ + f x • μ := by rw [← add_smul, half, one_smul]
  change μ = f x • (μ + ν) at he
  rw [smul_add] at he
  have : SigmaFinite (f x • μ) := by
    lift f x to NNReal using nt with r hr
    exact SMul.sigmaFinite r
  have hν := (Measure.add_right_inj _ _ _).mp (he.symm.trans h₂)
  simpa [smul_smul, ENNReal.inv_mul_cancel nz nt] using
    (congrArg (fun η : Measure X ↦ (f x)⁻¹ • η) hν.symm)

private def act {m : ℕ} (i : Fin m) (a : SL (m+1))
    (p : E (m+1) × LatticeSpace m) : E (m+1) × LatticeSpace m :=
  (markAction a p.1, transverseCocycle i a p.1 • p.2)

private theorem act_mul {m : ℕ} (i : Fin m) (hn : 2 ≤ m+1) (a b : SL (m+1)) (p) :
    act i (a*b) p = act i a (act i b p) := by
  simp [act, markAction_mul, transverseCocycle_mul i hn, mul_smul]

private theorem act_one {m : ℕ} (i : Fin m) (p) : act i 1 p = p := by
  simp [act, markAction, transverseCocycle]

private theorem act_meas {m : ℕ} (i : Fin m) :
    Measurable fun p : SL (m+1) × (E (m+1) × LatticeSpace m) ↦ act i p.1 p.2 := by
  let pol (n : ℕ) : PolishSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (PolishSpace (Fin n → Fin n → ℝ))
  let pol' (n : ℕ) : PolishSpace (SL n) := Matrix.SpecialLinearGroup.isClosedEmbedding_val.polishSpace
  let bor (n : ℕ) : BorelSpace (SL n) := ⟨rfl⟩
  have he : Topology.IsClosedEmbedding (Int.castRingHom ℝ) := Int.isClosedEmbedding_coe_real
  have : IsClosed (integerGroup m : Set (SL m)) := he.specialLinearGroup_map.isClosed_range
  let : BorelSpace (LatticeSpace m) := CosetSpace.borelSpace
  apply Measurable.prodMk
  · apply Continuous.measurable
    apply (PiLp.continuous_toLp 2 _).comp
    change Continuous fun p : SL (m+1) × (E (m+1) × LatticeSpace m) ↦
      p.1.val.mulVec (WithLp.ofLp p.2.1)
    unfold Matrix.mulVec dotProduct
    fun_prop
  · exact ((measurable_transverseCocycle i).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).smul
      (measurable_snd.comp measurable_snd)

private def actEquiv {m : ℕ} (i : Fin m) (hn : 2 ≤ m+1) (a : SL (m+1)) :
    (E (m+1) × LatticeSpace m) ≃ᵐ (E (m+1) × LatticeSpace m) where
  toFun := act i a
  invFun := act i a⁻¹
  left_inv p := by rw [← act_mul i hn, inv_mul_cancel, act_one]
  right_inv p := by rw [← act_mul i hn, mul_inv_cancel, act_one]
  measurable_toFun := (act_meas i).comp (measurable_const.prodMk measurable_id)
  measurable_invFun := (act_meas i).comp (measurable_const.prodMk measurable_id)

private theorem act_trans {m : ℕ} (i : Fin m) (hn : 2 ≤ m+1)
    (p q : E (m+1) × LatticeSpace m) (hp : p.1 ≠ 0) (hq : q.1 ≠ 0) :
    ∃ b, act i b p = q := by
  let g := markSection i p.1
  let t := markSection i q.1
  let b := t * g⁻¹
  have hb : markAction b p.1 = q.1 := by
    rw [← markSection_spec i hn hp, ← markedColumn_mul]
    simpa [b,g,t,mul_assoc] using markSection_spec i hn hq
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (SL m) (act i b p).2 q.2
  obtain ⟨a, ha, hT⟩ := transverseCocycle_stabilizer i hn q.1 hq h
  refine ⟨a*b, ?_⟩
  rw [act_mul i hn]
  apply Prod.ext
  · change markAction a (markAction b p.1) = q.1
    rw [hb, ha]
  · change transverseCocycle i a (markAction b p.1) • (act i b p).2 = q.2
    rw [hb, hT, hh]

/-- The full joint primitive-incidence measure factors as its normalized Lebesgue marginal
times the normalized domain Haar law on the transverse lattice space. -/
theorem transverseShape_product {m : ℕ} (i : Fin m) (hn : 2 ≤ m+1)
    (D : Set (SL (m+1))) (hm : MeasurableSet D)
    (hd : IsFundamentalDomain (integerGroup (m+1)).op D (groupHaar (m+1)))
    (hp : groupHaar (m+1) D ≠ 0) (hf : groupHaar (m+1) D ≠ ⊤)
    (Q : Set (SL m)) (hq : IsFundamentalDomain (integerGroup m).op Q (groupHaar m))
    (qp : groupHaar m Q ≠ 0) (qf : groupHaar m Q ≠ ⊤) :
    (primitiveIncidence hn D).map (fun g ↦ (markedColumn hn g, transverseShape i g)) =
      ((∑' k, dilationWeight (m+1) k)⁻¹ • (volume : Measure (E (m+1)))).prod
        (domainProbability (groupHaar m) Q) := by
  let pol (n : ℕ) : PolishSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (PolishSpace (Fin n → Fin n → ℝ))
  let pol' (n : ℕ) : PolishSpace (SL n) := Matrix.SpecialLinearGroup.isClosedEmbedding_val.polishSpace
  let lc (n : ℕ) : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℝ))
  let lc' (n : ℕ) : LocallyCompactSpace (SL n) := Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace
  let bor (n : ℕ) : BorelSpace (SL n) := ⟨rfl⟩
  have he : Topology.IsClosedEmbedding (Int.castRingHom ℝ) := Int.isClosedEmbedding_coe_real
  have : IsClosed (integerGroup m : Set (SL m)) := he.specialLinearGroup_map.isClosed_range
  let : BorelSpace (LatticeSpace m) := CosetSpace.borelSpace
  let H := domainProbability (groupHaar m) Q
  have : IsProbabilityMeasure H := domainProbability_probability _ _ qp qf
  let right (n : ℕ) := groupHaar_rightInvariant n
  let : (groupHaar m).IsMulLeftInvariant := inferInstanceAs (Measure.haar : Measure (SL m)).IsMulLeftInvariant
  have : SMulInvariantMeasure (SL m) (LatticeSpace m) H := domainProbability_invariant _ hq
  let ρ := groupHaar (m+1)
  have : NeZero ρ := inferInstanceAs (NeZero (Measure.haar : Measure (SL (m+1))))
  have : SigmaFinite ρ := inferInstanceAs (SigmaFinite (Measure.haar : Measure (SL (m+1))))
  let z := ∑' k, dilationWeight (m+1) k
  obtain ⟨C, _, mass⟩ := siegel_primitive_orbit_covolume _ hn D hm hd hf
  change C * z = groupHaar (m+1) D at mass
  have hc : C ≠ 0 := fun e ↦ hp (by simpa [e] using mass.symm)
  have hz : z ≠ 0 := fun e ↦ hp (by simpa [e] using mass.symm)
  have zfin : z ≠ ⊤ := (ENNReal.lt_top_of_mul_ne_top_right (mass ▸ hf) hc).ne
  let η := z⁻¹ • (volume : Measure (E (m+1)))
  have : SigmaFinite η := by
    have e := ENNReal.inv_ne_top.mpr hz
    change SigmaFinite (z⁻¹ • (volume : Measure (E (m+1))))
    lift z⁻¹ to NNReal using e with r hr
    exact SMul.sigmaFinite r
  let P := fun g ↦ (markedColumn hn g, transverseShape i g)
  have hP : Measurable P := (measurable_markedColumn hn).prodMk (measurable_transverseShape i)
  let μ := (primitiveIncidence hn D).map P
  have marginal : μ.map Prod.fst = η := by
    rw [Measure.map_map measurable_fst hP]
    exact primitiveIncidence_map hn D hm hd hp hf
  have : SigmaFinite μ := SigmaFinite.of_map _ measurable_fst.aemeasurable (marginal ▸ inferInstanceAs (SigmaFinite η))
  let A := actEquiv i hn
  have inv (a : SL (m+1)) : μ.map (A a) = μ := by
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_map hF (A a).measurable]
    unfold μ
    rw [lintegral_map (show Measurable (fun p ↦ F (A a p)) from hF.comp (A a).measurable) hP,
      lintegral_map hF hP]
    have eqn (g : SL (m+1)) : A a (P g) = P (a*g) := by
      apply Prod.ext
      · exact (markedColumn_mul hn a g).symm
      · exact congrArg QuotientGroup.mk (transverseCocycle_frame i hn a g).symm
    simp_rw [eqn]
    exact transverseShape_left_invariant i hn D hm hd a F hF
  have measBase (a : SL (m+1)) : Measurable (markAction a) :=
    measurable_fst.comp ((A a).measurable.comp (measurable_id.prodMk (measurable_const (a := QuotientGroup.mk (1 : SL m)))))
  have base (a : SL (m+1)) : MeasurePreserving (markAction a) η η := by
    refine ⟨measBase a, ?_⟩
    rw [← marginal, Measure.map_map (measBase a) measurable_fst]
    have e := congrArg (Measure.map Prod.fst) (inv a)
    rwa [Measure.map_map measurable_fst (A a).measurable] at e
  let ν := η.prod H
  have prodInv (a : SL (m+1)) : ν.map (A a) = ν := by
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_map hF (A a).measurable]
    unfold ν
    rw [lintegral_prod _ (show Measurable (fun p ↦ F (A a p)) from hF.comp (A a).measurable).aemeasurable,
      lintegral_prod _ hF.aemeasurable]
    calc
      _ = ∫⁻ x, ∫⁻ L, F (markAction a x, L) ∂H ∂η := by
        apply lintegral_congr
        intro x
        exact (measurePreserving_smul (transverseCocycle i a x) H).lintegral_comp
          (show Measurable (fun L ↦ F (markAction a x, L)) from hF.comp (measurable_const.prodMk measurable_id))
      _ = _ := (base a).lintegral_comp hF.lintegral_prod_right'
  have margν : ν.map Prod.fst = η := by simp [ν]
  let good := {p : E (m+1) × LatticeSpace m | p.1 ≠ 0}
  have hgood : ∀ᵐ x ∂η, x ≠ 0 := by simp [η, ae_iff, Measure.smul_apply]
  have onGood (ξ : Measure (E (m+1) × LatticeSpace m)) (h : ξ.map Prod.fst = η) :
      ∀ᵐ p ∂ξ, p ∈ good :=
    (ae_map_iff measurable_fst.aemeasurable (measurableSet_singleton (0 : E (m+1))).compl).mp (h ▸ hgood)
  let B := Metric.ball (0 : E (m+1)) 1
  have hB : MeasurableSet B := measurableSet_ball
  have val (ξ : Measure (E (m+1) × LatticeSpace m)) (h : ξ.map Prod.fst = η) :
      ξ (Prod.fst ⁻¹' B) = η B := by rw [← h, Measure.map_apply measurable_fst hB]
  exact orbit_unique ρ μ ν A (act_meas i) (act_mul i hn) inv prodInv good
    (ae_add_measure_iff.mpr ⟨onGood μ marginal, onGood ν margν⟩)
    (fun p hp q hq ↦ act_trans i hn p q hp hq) (Prod.fst ⁻¹' B)
    ((val μ marginal).trans (val ν margν).symm)
    (by rw [val μ marginal]; simp [η, Measure.smul_apply, zfin, B, (Metric.measure_ball_pos volume (0 : E (m+1)) one_pos).ne'])
    (by rw [val μ marginal]; exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hz) measure_ball_lt_top.ne)

#print axioms transverseShape_product
end SigabaNeo.Wall1
