import SigabaNeo.Lib.Lattices.Research.Wall1.TransverseProduct
import SigabaNeo.Lib.Lattices.Reduction.Rogers.SiegelAssemblyDomain

/-! Exact short-projection count and the Part 105 bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory SigabaNeo.Rogers
open scoped ENNReal
namespace SigabaNeo.Wall1

variable {m : ℕ} (i : Fin m) (hn : 2 ≤ m+1)
    (D : Set (SL (m+1))) (hm : MeasurableSet D)
    (hd : IsFundamentalDomain (integerGroup (m+1)).op D (groupHaar (m+1)))
    (hp : groupHaar (m+1) D ≠ 0) (hf : groupHaar (m+1) D ≠ ⊤)
    (Q : Set (SL m)) (hq : IsFundamentalDomain (integerGroup m).op Q (groupHaar m))
    (qp : groupHaar m Q ≠ 0) (qf : groupHaar m Q ≠ ⊤)

include i hn hm hd hp hf hq qp qf in
/-- Exact factorization for oriented primitive marks in every measurable window and every
strict transverse cutoff. -/
theorem shortProjection_count_product (W : Set (E (m+1))) (hW : MeasurableSet W) (c : ℝ) :
    (∫⁻ g in D, ∑' v : ContentFiber (m+1) 1, shortProjectionTest W c
      (latticePoint g v.val.val) (projectedPoints g v.val.val) ∂groupHaar (m+1)) /
      groupHaar (m+1) D =
    (volume W / ∑' k, dilationWeight (m+1) k) * domainProbability (groupHaar m) Q (shortShape c) := by
  classical
  have := domainProbability_probability (groupHaar m) Q qp qf
  let S := shortShape (m := m) c
  let F := (W ×ˢ S).indicator (1 : E (m+1) × LatticeSpace m → ℝ≥0∞)
  have hs : MeasurableSet (W ×ˢ S) := hW.prod (measurableSet_shortShape c)
  have hF : Measurable F := measurable_one.indicator hs
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
  have H := congrArg (fun μ : Measure (E (m+1) × LatticeSpace m) ↦ ∫⁻ p, F p ∂μ)
    (transverseShape_product i hn D hm hd hp hf Q hq qp qf)
  rw [lintegral_map hF ((measurable_markedColumn hn).prodMk (measurable_transverseShape i))] at H
  simp only [primitiveIncidence, lintegral_smul_measure, smul_eq_mul] at H
  simp_rw [← eqn] at H
  rw [div_eq_mul_inv, mul_comm]
  refine H.trans ?_
  rw [lintegral_indicator_one hs, Measure.prod_prod, Measure.smul_apply, smul_eq_mul,
    div_eq_mul_inv, mul_comm (volume W)]

include i hn hm hd hp hf hq qp qf in
/-- For any kernel satisfying the count disintegration, the short-event probability is Haar
almost everywhere for each fixed cutoff. -/
theorem shortProjection_kernel_ae (K : Kernel (E (m+1)) (LatticeSpace m))
    (law : ∀ W : Set (E (m+1)), MeasurableSet W → ∀ c : ℝ,
      (∫⁻ g in D, ∑' v : ContentFiber (m+1) 1, shortProjectionTest W c
        (latticePoint g v.val.val) (projectedPoints g v.val.val) ∂groupHaar (m+1)) /
        groupHaar (m+1) D = (∫⁻ x in W, K x (shortShape c)) / ∑' k, dilationWeight (m+1) k)
    (c : ℝ) : ∀ᵐ x ∂volume, K x (shortShape c) = domainProbability (groupHaar m) Q (shortShape c) := by
  apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (K.measurable_coe (measurableSet_shortShape c))
    measurable_const
  intro W hW _
  obtain ⟨C, _, mass⟩ := siegel_primitive_orbit_covolume _ hn D hm hd hf
  have hc : C ≠ 0 := fun e ↦ hp (by simpa [e] using mass.symm)
  have hz : (∑' k, dilationWeight (m+1) k) ≠ 0 := fun e ↦ hp (by simpa [e] using mass.symm)
  have ht := (ENNReal.lt_top_of_mul_ne_top_right (mass ▸ hf) hc).ne
  apply (ENNReal.mul_left_inj (ENNReal.inv_ne_zero.mpr ht) (ENNReal.inv_ne_top.mpr hz)).mp
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    ((law W hW c).symm.trans (shortProjection_count_product i hn D hm hd hp hf Q hq qp qf W hW c))

include i hm hd hp hf hq qp qf in
/-- Part 105 for a closed parent ball and strict normalized transverse minimum. -/
theorem shortProjection_ball_bound (hm₂ : 2 ≤ m) (hqM : MeasurableSet Q)
    {ℓ c : ℝ} (hℓ : 0 ≤ ℓ) (hc : 0 < c) :
    (∫⁻ g in D, ∑' v : ContentFiber (m+1) 1, shortProjectionTest (Metric.closedBall 0 ℓ) c
      (latticePoint g v.val.val) (projectedPoints g v.val.val) ∂groupHaar (m+1)) /
      groupHaar (m+1) D ≤
    (ENNReal.ofReal (ℓ ^ (m+1)) * volume (Metric.ball (0 : E (m+1)) 1) /
      ∑' k, dilationWeight (m+1) k) * (ENNReal.ofReal (c ^ m) * volume (Metric.ball (0 : E m) 1) /
        (2 * ∑' k, dilationWeight m k)) := by
  rw [shortProjection_count_product i (by omega) D hm hd hp hf Q hq qp qf _ measurableSet_closedBall,
    Measure.addHaar_closedBall volume _ hℓ, finrank_euclideanSpace, Fintype.card_fin]
  exact mul_le_mul_right (domainProbability_shortShape_le hm₂ Q hqM hq qp qf hc) _

include hm hd hp hf in
/-- Part 105 on any finite-mass parent fundamental domain. The transverse domain and
coordinate choice are supplied internally. -/
theorem part105 (hm₂ : 2 ≤ m) {ℓ c : ℝ} (hℓ : 0 ≤ ℓ) (hc : 0 < c) :
    (∫⁻ g in D, ∑' v : ContentFiber (m+1) 1, shortProjectionTest (Metric.closedBall 0 ℓ) c
      (latticePoint g v.val.val) (projectedPoints g v.val.val) ∂groupHaar (m+1)) /
      groupHaar (m+1) D ≤
    (ENNReal.ofReal (ℓ ^ (m+1)) * volume (Metric.ball (0 : E (m+1)) 1) /
      ∑' k, dilationWeight (m+1) k) * (ENNReal.ofReal (c ^ m) * volume (Metric.ball (0 : E m) 1) /
        (2 * ∑' k, dilationWeight m k)) := by
  obtain ⟨Q, hQ, hfund, hpos, hfin⟩ := open_arithmetic_domain_finite_mass m hm₂
  exact shortProjection_ball_bound ⟨0, by omega⟩ D hm hd hp hf Q hfund hpos hfin hm₂ hQ hℓ hc

#print axioms part105
#print axioms shortProjection_count_product
#print axioms shortProjection_kernel_ae
#print axioms shortProjection_ball_bound
end SigabaNeo.Wall1
