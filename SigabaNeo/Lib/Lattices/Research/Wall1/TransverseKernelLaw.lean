import SigabaNeo.Lib.Lattices.Research.Wall1.TransverseProduct

/-! Almost-sure identification of the entire conditional law. -/
noncomputable section
open MeasureTheory ProbabilityTheory SigabaNeo.Rogers
open scoped ENNReal ProbabilityTheory
namespace SigabaNeo.Wall1

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

/-- Any Markov kernel realizing the full joint disintegration is almost everywhere equal,
as a measure, to transverse Haar probability. All measurable events share one exceptional set. -/
theorem transverseShape_kernel_ae_haar {m : ℕ} (i : Fin m) (hn : 2 ≤ m+1)
    (D : Set (SL (m+1))) (hm : MeasurableSet D)
    (hd : IsFundamentalDomain (integerGroup (m+1)).op D (groupHaar (m+1)))
    (hp : groupHaar (m+1) D ≠ 0) (hf : groupHaar (m+1) D ≠ ⊤)
    (Q : Set (SL m)) (hq : IsFundamentalDomain (integerGroup m).op Q (groupHaar m))
    (qp : groupHaar m Q ≠ 0) (qf : groupHaar m Q ≠ ⊤)
    (K : Kernel (E (m+1)) (LatticeSpace m)) [IsMarkovKernel K]
    (law : ∀ F : E (m+1) × LatticeSpace m → ℝ≥0∞, Measurable F →
      (∫⁻ g, F (markedColumn hn g, transverseShape i g) ∂primitiveIncidence hn D) =
        (∫⁻ x, ∫⁻ L, F (x, L) ∂K x) / ∑' k, dilationWeight (m+1) k) :
    ∀ᵐ x ∂volume, K x = domainProbability (groupHaar m) Q := by
  let : PolishSpace (Matrix (Fin m) (Fin m) ℝ) :=
    inferInstanceAs (PolishSpace (Fin m → Fin m → ℝ))
  let : PolishSpace (SL m) := Matrix.SpecialLinearGroup.isClosedEmbedding_val.polishSpace
  let : BorelSpace (SL m) := ⟨rfl⟩
  have he : Topology.IsClosedEmbedding (Int.castRingHom ℝ) := Int.isClosedEmbedding_coe_real
  have : IsClosed (integerGroup m : Set (SL m)) := he.specialLinearGroup_map.isClosed_range
  let : BorelSpace (LatticeSpace m) := CosetSpace.borelSpace
  let H := domainProbability (groupHaar m) Q
  have : IsProbabilityMeasure H := domainProbability_probability _ _ qp qf
  let z := ∑' k, dilationWeight (m+1) k
  obtain ⟨C, _, mass⟩ := siegel_primitive_orbit_covolume _ hn D hm hd hf
  change C * z = groupHaar (m+1) D at mass
  have hc : C ≠ 0 := fun e ↦ hp (by simpa [e] using mass.symm)
  have hz : z ≠ 0 := fun e ↦ hp (by simpa [e] using mass.symm)
  have ht := (ENNReal.lt_top_of_mul_ne_top_right (mass ▸ hf) hc).ne
  apply kernel_unique volume K (Kernel.const _ H)
  rw [Measure.compProd_const]
  apply Measure.ext_of_lintegral
  intro F hF
  have eqn := congrArg (fun μ : Measure (E (m+1) × LatticeSpace m) ↦ ∫⁻ p, F p ∂μ)
    (transverseShape_product i hn D hm hd hp hf Q hq qp qf)
  rw [lintegral_map hF ((measurable_markedColumn hn).prodMk (measurable_transverseShape i)),
    law F hF, lintegral_prod _ hF.aemeasurable, lintegral_smul_measure] at eqn
  rw [Measure.lintegral_compProd hF, lintegral_prod _ hF.aemeasurable]
  apply (ENNReal.mul_left_inj (ENNReal.inv_ne_zero.mpr ht) (ENNReal.inv_ne_top.mpr hz)).mp
  simpa [H, z, div_eq_mul_inv, mul_comm, smul_eq_mul] using eqn

#print axioms transverseShape_kernel_ae_haar
end SigabaNeo.Wall1
