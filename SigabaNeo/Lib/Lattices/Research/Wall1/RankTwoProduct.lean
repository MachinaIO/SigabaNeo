import SigabaNeo.Lib.Lattices.Research.Wall1.RankTwoOrderedIncidence

/-! Product and conditional laws for the twice-normalized outer lattice. -/
noncomputable section
open Matrix MeasureTheory ProbabilityTheory SigabaNeo.Rogers
open scoped ENNReal ProbabilityTheory
namespace SigabaNeo.Wall1.RankTwo

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

private theorem sigmaFinite_smul {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (c : ℝ≥0∞) (hc : c ≠ ⊤) : SigmaFinite (c • μ) := by
  lift c to NNReal using hc with t ht
  exact SMul.sigmaFinite t

variable {r : ℕ} (i : Fin (r+1)) (j : Fin r)
local notation "n" => (r+2)
local notation "m" => (r+1)

set_option maxHeartbeats 1200000 in
theorem orderedJoint_product (D : Set (SL n))
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (hf : groupHaar n D ≠ ⊤) (hp : groupHaar n D ≠ 0)
    (Q : Set (SL r)) (hq : IsFundamentalDomain (integerGroup r).op Q (groupHaar r))
    (qp : groupHaar r Q ≠ 0) (qf : groupHaar r Q ≠ ⊤) :
    orderedJoint i j D =
      (orderedMeasure (by have := j.isLt; omega : 2 ≤ m) D).prod (domainProbability (groupHaar r) Q) := by
  have hr : 2 ≤ m := by have := j.isLt; omega
  let pol (d : ℕ) : PolishSpace (Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (PolishSpace (Fin d → Fin d → ℝ))
  let pol' (d : ℕ) : PolishSpace (SL d) := SpecialLinearGroup.isClosedEmbedding_val.polishSpace
  let lc (d : ℕ) : LocallyCompactSpace (Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin d → Fin d → ℝ))
  let lc' (d : ℕ) : LocallyCompactSpace (SL d) :=
    SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace
  let bor (d : ℕ) : BorelSpace (SL d) := ⟨rfl⟩
  have he : Topology.IsClosedEmbedding (Int.castRingHom ℝ) := Int.isClosedEmbedding_coe_real
  have : IsClosed (integerGroup r : Set (SL r)) := he.specialLinearGroup_map.isClosed_range
  let : BorelSpace (LatticeSpace r) := CosetSpace.borelSpace
  let H := domainProbability (groupHaar r) Q
  have : IsProbabilityMeasure H := domainProbability_probability _ _ qp qf
  let right (d : ℕ) := groupHaar_rightInvariant d
  let : (groupHaar r).IsMulLeftInvariant :=
    inferInstanceAs (Measure.haar : Measure (SL r)).IsMulLeftInvariant
  have : SMulInvariantMeasure (SL r) (LatticeSpace r) H := domainProbability_invariant _ hq
  let ρ := groupHaar n
  have : NeZero ρ := inferInstanceAs (NeZero (Measure.haar : Measure (SL n)))
  have : SigmaFinite ρ := inferInstanceAs (SigmaFinite (Measure.haar : Measure (SL n)))
  let μ := orderedJoint i j D
  let η := orderedMeasure hr D
  let c := groupHaar n D / (zetaFactor n * zetaFactor m)
  have cfin : c ≠ ⊤ := ENNReal.mul_ne_top hf
    (ENNReal.inv_ne_top.mpr (mul_ne_zero (zetaFactor_ne_zero _) (zetaFactor_ne_zero _)))
  have cpos : c ≠ 0 := mul_ne_zero hp (ENNReal.inv_ne_zero.mpr
    (ENNReal.mul_ne_top (zetaFactor_ne_top (by omega)) (zetaFactor_ne_top (by omega))))
  have hη : η = c • frameVolume n := orderedMeasure_eq hr D hd hf
  let : SigmaFinite (frameVolume n) := Measure.pi.sigmaFinite _
  have : SigmaFinite η := hη ▸ sigmaFinite_smul _ _ cfin
  have marg : μ.map Prod.fst = η := orderedJoint_fst i j D
  have : SigmaFinite μ := SigmaFinite.of_map _ measurable_fst.aemeasurable
    (marg ▸ inferInstanceAs (SigmaFinite η))
  let ν := η.prod H
  let A (a : SL n) : (Frames n × LatticeSpace r) ≃ᵐ (Frames n × LatticeSpace r) := {
    toFun := incidenceAction i j a
    invFun := incidenceAction i j a⁻¹
    left_inv := fun u ↦ by rw [← incidenceAction_mul, inv_mul_cancel, incidenceAction_one]
    right_inv := fun u ↦ by rw [← incidenceAction_mul, mul_inv_cancel, incidenceAction_one]
    measurable_toFun := (measurable_incidenceAction i j).comp (measurable_const.prodMk measurable_id)
    measurable_invFun := (measurable_incidenceAction i j).comp (measurable_const.prodMk measurable_id) }
  have inv (a : SL n) : μ.map (A a) = μ := orderedJoint_invariant i j D hd a
  have base (a : SL n) : MeasurePreserving (frameAction a) η η := by
    have h : Measurable (frameAction a) := measurable_fst.comp
      ((A a).measurable.comp (measurable_id.prodMk (measurable_const (a := QuotientGroup.mk (1 : SL r)))))
    refine ⟨h, ?_⟩
    rw [← marg, Measure.map_map h measurable_fst]
    have e := congrArg (Measure.map Prod.fst) (inv a)
    rwa [Measure.map_map measurable_fst (A a).measurable] at e
  have inv' (a : SL n) : ν.map (A a) = ν := by
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_map hF (A a).measurable]
    unfold ν
    rw [lintegral_prod _ (show Measurable (fun u ↦ F (A a u)) from hF.comp (A a).measurable).aemeasurable, lintegral_prod _ hF.aemeasurable]
    calc
      _ = ∫⁻ x, ∫⁻ L, F (frameAction a x, L) ∂H ∂η := by
        apply lintegral_congr
        intro x
        exact (measurePreserving_smul (outerCocycle i j a x) H).lintegral_comp
          (show Measurable (fun L ↦ F (frameAction a x, L)) from hF.comp (measurable_const.prodMk measurable_id))
      _ = _ := (base a).lintegral_comp hF.lintegral_prod_right'
  have hcols : Continuous (@columns r) := by
    apply continuous_pi
    intro k
    have col (b : Fin n) : Continuous (fun g : SL n ↦ column g b) := by
      apply (PiLp.continuous_toLp 2 _).comp
      exact continuous_pi fun l ↦ (continuous_apply b).comp ((continuous_apply l).comp continuous_subtype_val)
    fin_cases k <;> exact col _
  obtain ⟨B,hB,hcov⟩ := isSigmaCompact_range hcols
  have hgood : MeasurableSet (Set.range (@columns r)) := hcov ▸
    MeasurableSet.iUnion fun k ↦ (hB k).isClosed.measurableSet
  have supp : ∀ᵐ x ∂η, x ∈ Set.range (@columns r) := by
    change ∀ᵐ x ∂Measure.sum _, _
    rw [Measure.ae_sum_iff]
    intro p
    apply (ae_map_iff (measurable_physical hr 0 0 p).aemeasurable (p := fun x ↦ x ∈ Set.range (@columns r)) hgood).mpr
    exact Filter.Eventually.of_forall fun g ↦ ⟨_,adaptedFrame_columns j p g⟩
  have marg' : ν.map Prod.fst = η := by simp [ν]
  have onGood (ξ : Measure (Frames n × LatticeSpace r)) (h : ξ.map Prod.fst = η) :
      ∀ᵐ u ∂ξ, u.1 ∈ Set.range (@columns r) :=
    (ae_map_iff measurable_fst.aemeasurable hgood).mp (h ▸ supp)
  let W := Metric.ball (0 : Frames n) 1
  have val (ξ : Measure (Frames n × LatticeSpace r)) (h : ξ.map Prod.fst = η) :
      ξ (Prod.fst ⁻¹' W) = η W := by rw [← h, Measure.map_apply measurable_fst measurableSet_ball]
  exact orbit_unique ρ μ ν A (measurable_incidenceAction i j) (incidenceAction_mul i j) inv inv'
    {u | u.1 ∈ Set.range (@columns r)} (ae_add_measure_iff.mpr ⟨onGood μ marg,onGood ν marg'⟩)
    (fun _ hu _ hv ↦ incidenceAction_trans i j hu hv) (Prod.fst ⁻¹' W)
    ((val μ marg).trans (val ν marg').symm)
    (by rw [val μ marg,hη,Measure.smul_apply]; exact mul_ne_zero cpos
          (Metric.measure_ball_pos _ _ one_pos).ne')
    (by rw [val μ marg,hη,Measure.smul_apply]; exact ENNReal.mul_ne_top cfin measure_ball_lt_top.ne)

/-- The selected plane basis and the outer lattice have product law. -/
theorem haarProduct (D : Set (SL n)) (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (hf : groupHaar n D ≠ ⊤) (hp : groupHaar n D ≠ 0)
    (Q : Set (SL r)) (hq : IsFundamentalDomain (integerGroup r).op Q (groupHaar r))
    (qp : groupHaar r Q ≠ 0) (qf : groupHaar r Q ≠ ⊤) : HaarProduct i j D Q := by
  have hr : 2 ≤ m := by have := j.isLt; omega
  let H := domainProbability (groupHaar r) Q
  have : IsProbabilityMeasure H := domainProbability_probability _ _ qp qf
  have h := orderedJoint_product i j D hd hf hp Q hq qp qf
  have hc : (groupHaar n D)⁻¹ • orderedMeasure hr D =
      (zetaFactor n * zetaFactor m)⁻¹ • frameVolume n := by
    rw [orderedMeasure_eq hr D hd hf, smul_smul, div_eq_mul_inv, ← mul_assoc,
      ENNReal.inv_mul_cancel hp hf, one_mul]
  change joint i j D = (planeMarginal n).prod H
  unfold planeMarginal
  rw [Measure.restrict_prod_eq_prod_univ]
  change joint i j D = (((zetaFactor n * zetaFactor m)⁻¹ • frameVolume n).prod H).restrict _
  rw [← hc, Measure.prod_smul_left, ← h]
  ext S hS
  rw [joint_apply i j D S hS, Measure.restrict_apply hS, Measure.smul_apply, smul_eq_mul,
    div_eq_mul_inv, mul_comm]
  congr 1
  let T := (Prod.fst ⁻¹' basisDomain n : Set (Frames n × LatticeSpace r)) ∩ S
  have hT : MeasurableSet T := (measurable_fst (measurableSet_basisDomain _)).inter hS
  have e : S ∩ basisDomain n ×ˢ (Set.univ : Set (LatticeSpace r)) = T := by
    ext p; simp [T, and_comm]
  rw [e, ← lintegral_indicator_one hT, orderedJoint_integral _ _ _ _ (measurable_one.indicator hT)]
  rfl

private theorem kernel_unique {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y] (μ : Measure X) [SigmaFinite μ]
    (K J : Kernel X Y) [IsMarkovKernel K] [IsMarkovKernel J] (eqn : μ ⊗ₘ K = μ ⊗ₘ J) :
    K =ᵐ[μ] J := by
  apply ae_of_forall_measure_lt_top_ae_restrict
  intro W hW hfin
  have : IsFiniteMeasure (μ.restrict W) := ⟨by simpa using hfin⟩
  apply Kernel.ae_eq_of_compProd_eq
  ext S hS
  let V := Prod.fst ⁻¹' W ∩ S
  have hV : MeasurableSet V := (measurable_fst hW).inter hS
  have localize (L : Kernel X Y) [IsMarkovKernel L] :
      (μ.restrict W ⊗ₘ L) S = (μ ⊗ₘ L) V := by
    rw [Measure.compProd_apply hS, Measure.compProd_apply hV, ← lintegral_indicator hW]
    apply lintegral_congr
    intro x
    have pre : Prod.mk x ⁻¹' (Prod.fst ⁻¹' W) = {y : Y | x ∈ W} := rfl
    by_cases hx : x ∈ W <;> simp [V, Set.preimage_inter, Set.indicator, hx, pre]
  rw [localize K, localize J, eqn]

/-- A common full-measure set identifies the entire conditional probability. -/
theorem kernel_ae_haar (D : Set (SL n))
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hf : groupHaar n D ≠ ⊤)
    (hp : groupHaar n D ≠ 0) (Q : Set (SL r))
    (hq : IsFundamentalDomain (integerGroup r).op Q (groupHaar r))
    (qp : groupHaar r Q ≠ 0) (qf : groupHaar r Q ≠ ⊤)
    (K : Kernel (Frames n) (LatticeSpace r)) [IsMarkovKernel K]
    (law : joint i j D = planeMarginal n ⊗ₘ K) :
    ∀ᵐ x ∂planeMarginal n, K x = domainProbability (groupHaar r) Q := by
  let : PolishSpace (Matrix (Fin r) (Fin r) ℝ) :=
    inferInstanceAs (PolishSpace (Fin r → Fin r → ℝ))
  let : PolishSpace (SL r) := SpecialLinearGroup.isClosedEmbedding_val.polishSpace
  let : BorelSpace (SL r) := ⟨rfl⟩
  have he : Topology.IsClosedEmbedding (Int.castRingHom ℝ) := Int.isClosedEmbedding_coe_real
  have : IsClosed (integerGroup r : Set (SL r)) := he.specialLinearGroup_map.isClosed_range
  let : BorelSpace (LatticeSpace r) := CosetSpace.borelSpace
  let H := domainProbability (groupHaar r) Q
  have : IsProbabilityMeasure H := domainProbability_probability _ _ qp qf
  let : SigmaFinite (frameVolume n) := Measure.pi.sigmaFinite _
  let c := (zetaFactor n * zetaFactor (n-1))⁻¹
  have : SigmaFinite (c • frameVolume n) := sigmaFinite_smul _ _
    (ENNReal.inv_ne_top.mpr (mul_ne_zero (zetaFactor_ne_zero _) (zetaFactor_ne_zero _)))
  have : SigmaFinite (planeMarginal n) := inferInstanceAs (SigmaFinite ((c • frameVolume n).restrict _))
  apply kernel_unique (planeMarginal n) K (Kernel.const _ H)
  rw [← law, Measure.compProd_const]
  exact haarProduct i j D hd hf hp Q hq qp qf

/-- In outer dimension at least two, every disintegration is simultaneously invariant
under every outer special linear transformation almost everywhere. -/
theorem kernel_ae_invariant (hr : 2 ≤ r) (D : Set (SL n))
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hf : groupHaar n D ≠ ⊤)
    (hp : groupHaar n D ≠ 0) (K : Kernel (Frames n) (LatticeSpace r)) [IsMarkovKernel K]
    (law : joint i j D = planeMarginal n ⊗ₘ K) :
    ∀ᵐ x ∂planeMarginal n, SMulInvariantMeasure (SL r) (LatticeSpace r) (K x) := by
  obtain ⟨Q,_,hq,qp,qf⟩ := open_arithmetic_domain_finite_mass r hr
  let := groupHaar_rightInvariant r
  let : BorelSpace (SL r) := ⟨rfl⟩
  let : LocallyCompactSpace (Matrix (Fin r) (Fin r) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin r → Fin r → ℝ))
  let : LocallyCompactSpace (SL r) := SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace
  let : (groupHaar r).IsMulLeftInvariant :=
    inferInstanceAs (Measure.haar : Measure (SL r)).IsMulLeftInvariant
  filter_upwards [kernel_ae_haar i j D hd hf hp Q hq qp qf K law] with x hx
  rw [hx]
  exact domainProbability_invariant _ hq

/-- The bounded count integrated against the actual plane marginal. -/
theorem bounded_count (hr : 2 ≤ r) (D : Set (SL n))
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (hf : groupHaar n D ≠ ⊤) (hp : groupHaar n D ≠ 0) (a ℓ c : ℝ) (hc : 0 < c) :
    joint i j D (boundedEvent r a ℓ c) ≤ ∫⁻ x in planeWindow n a ℓ,
      min 1 (ENNReal.ofReal (c^r * area x) * volume (Metric.ball (0 : E r) 1) /
        (2 * zetaFactor r)) ∂planeMarginal n := by
  obtain ⟨Q,hQ,hq,qp,qf⟩ := open_arithmetic_domain_finite_mass r hr
  exact bounded_count_of_haar hr i j D Q hQ hq qp qf (haarProduct i j D hd hf hp Q hq qp qf)
    a ℓ c hc

end SigabaNeo.Wall1.RankTwo

#print axioms SigabaNeo.Wall1.RankTwo.orderedJoint_product
#print axioms SigabaNeo.Wall1.RankTwo.haarProduct
#print axioms SigabaNeo.Wall1.RankTwo.kernel_ae_haar
#print axioms SigabaNeo.Wall1.RankTwo.kernel_ae_invariant
#print axioms SigabaNeo.Wall1.RankTwo.bounded_count
