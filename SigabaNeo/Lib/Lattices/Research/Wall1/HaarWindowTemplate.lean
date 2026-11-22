import SigabaNeo.Lib.Lattices.Research.Wall1.HaarMinimumLower
import SigabaNeo.Lib.Lattices.Research.Wall1.TransverseMinimumBound

/-! Part 136 Theorem 8: reselect-by-certificate on a Haar random window.

On a Haar random unimodular lattice of rank `b = m+1` (`m ≥ 2`), the rule "pick an oriented
primitive vector `x` with `‖x‖ ≤ ℓ` whose normalized quotient (`‖x‖^{1/m}`-scaled projection
of the lattice onto `x⊥`, which has unit covolume) has no nonzero point of norm `< c`" fails
with probability at most

  `1/(1+μ) + (ℓ^b V_b/ζ(b)) · (c^m V_m/(2ζ(m)))  =  1/(1+μ) + μ · c^m V_m/ζ(m)`,

with `μ = V_b ℓ^b/(2ζ(b))`. The first term is `primitiveBallPairs_hit_lower` (second moment /
Paley–Zygmund, open ball) and the second is `part105` (closed ball, strict test), combined by
`fail ⊆ {P_open = 0} ∪ {N_closed ≥ 1}` and Markov. With `c = c′·G_m` one has
`c^m V_m = c′^m`. No numeric instance is formalized here. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Wall1
open SigabaNeo.Rogers

/-- The quotient of `g` along the primitive mark `z` passes the certificate at level `c`:
every point of the normalized projected lattice with positive norm has norm at least `c`. -/
def quotientPasses {n : ℕ} (c : ℝ) (g : SL n) (z : Fin n → ℤ) : Prop :=
  ∀ y ∈ projectedPoints g z,
    0 < ‖‖latticePoint g z‖ ^ ((n-1 : ℕ) : ℝ)⁻¹ • y‖ →
      c ≤ ‖‖latticePoint g z‖ ^ ((n-1 : ℕ) : ℝ)⁻¹ • y‖

/-- The template rule accepts: some oriented primitive vector of norm at most `ℓ` has a
quotient passing the certificate. -/
def templateAccepts {n : ℕ} (ℓ c : ℝ) (g : SL n) : Prop :=
  ∃ v : ContentFiber n 1, ‖latticePoint g v.val.val‖ ≤ ℓ ∧ quotientPasses c g v.val.val

private theorem measurable_lp {n : ℕ} (z : Fin n → ℤ) :
    Measurable (fun g : SL n ↦ latticePoint g z) := by
  let : BorelSpace (SL n) := ⟨rfl⟩
  apply Continuous.measurable
  apply (PiLp.continuous_toLp 2 _).comp
  change Continuous (fun g : SL n ↦ g.val.mulVec _)
  unfold Matrix.mulVec dotProduct
  fun_prop

private theorem measurable_test {n : ℕ} (ℓ c : ℝ) (z : Fin n → ℤ) :
    Measurable fun g : SL n ↦ shortProjectionTest (Metric.closedBall 0 ℓ) c
      (latticePoint g z) (projectedPoints g z) := by
  classical
  let x := fun g : SL n ↦ latticePoint g z
  let f := fun (u : Fin n → ℤ) (g : SL n) ↦ ‖‖x g‖ ^ ((n-1 : ℕ) : ℝ)⁻¹ •
    (latticePoint g u - (inner ℝ (x g) (latticePoint g u) / ((‖x g‖ ^ 2 : ℝ) : ℝ)) • x g)‖
  have hx : Measurable x := measurable_lp z
  have hf (u) : Measurable (f u) := by
    have hu := measurable_lp (n := n) u
    apply Measurable.norm
    apply Measurable.smul (hx.norm.pow_const _)
    exact hu.sub ((hx.inner hu).div (hx.norm.pow_const 2) |>.smul hx)
  let S := {g : SL n | x g ∈ Metric.closedBall 0 ℓ} ∩
    ⋃ u : Fin n → ℤ, {g | 0 < f u g ∧ f u g < c}
  have hS : MeasurableSet S :=
    (hx measurableSet_closedBall).inter (MeasurableSet.iUnion fun u ↦
      (measurableSet_lt measurable_const (hf u)).inter (measurableSet_lt (hf u) measurable_const))
  have eq : (fun g : SL n ↦ shortProjectionTest (Metric.closedBall 0 ℓ) c
      (latticePoint g z) (projectedPoints g z)) = S.indicator 1 := by
    funext g
    have proj (u : Fin n → ℤ) : (ℝ ∙ x g)ᗮ.starProjection (latticePoint g u) =
        latticePoint g u - (inner ℝ (x g) (latticePoint g u) / ((‖x g‖ ^ 2 : ℝ) : ℝ)) • x g := by
      rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton]
      rfl
    have iff : (latticePoint g z ∈ Metric.closedBall 0 ℓ ∧ ∃ y ∈ projectedPoints g z,
        0 < ‖‖latticePoint g z‖ ^ ((n-1 : ℕ) : ℝ)⁻¹ • y‖ ∧
          ‖‖latticePoint g z‖ ^ ((n-1 : ℕ) : ℝ)⁻¹ • y‖ < c) ↔ g ∈ S := by
      simp only [projectedPoints, Set.mem_range, exists_exists_eq_and, S, Set.mem_inter_iff,
        Set.mem_ofPred_eq, Set.mem_iUnion, f]
      simp only [x] at proj ⊢
      simp_rw [proj]
    unfold shortProjectionTest
    by_cases h : g ∈ S
    · rw [Set.indicator_of_mem h, if_pos (iff.mpr h)]; rfl
    · rw [Set.indicator_of_notMem h, if_neg (fun h' ↦ h (iff.mp h'))]
  rw [eq]
  exact measurable_one.indicator hS

private theorem measurable_pairs' {n : ℕ} (r : ℝ) : Measurable (@primitiveBallPairs n r) := by
  unfold primitiveBallPairs
  apply Measurable.const_mul
  apply Measurable.tsum
  intro v
  exact (measurable_one.indicator measurableSet_ball).comp (measurable_lp v.val.val)

private theorem pairs_pos_exists {n : ℕ} {r : ℝ} {g : SL n} (h : 0 < primitiveBallPairs r g) :
    ∃ v : ContentFiber n 1, ‖latticePoint g v.val.val‖ < r := by
  by_contra! hno
  apply h.ne'
  unfold primitiveBallPairs
  rw [tsum_eq_zero_iff.mpr, mul_zero]
  intro v
  apply Set.indicator_of_notMem
  change latticePoint g v.val.val ∉ _
  simpa [Metric.mem_ball] using hno v

private theorem one_sub_frac {μ : ℝ≥0∞} (hμ : μ ≠ ⊤) : 1 - μ/(1+μ) = 1/(1+μ) := by
  have h1 : (1 + μ) ≠ 0 := by simp
  have h2 : (1 + μ) ≠ ⊤ := by simp [hμ]
  apply ENNReal.sub_eq_of_eq_add (ENNReal.div_ne_top hμ h1)
  rw [← ENNReal.add_div, ENNReal.div_self h1 h2]

/-- **Part 136 Theorem 8 (Haar-window template).** On any finite-mass fundamental domain of
`SL(m+1, ℝ)/SL(m+1, ℤ)` (`m ≥ 2`), the normalized Haar probability that no oriented primitive
vector of norm `≤ ℓ` has a quotient passing the level-`c` certificate is at most
`1/(1+μ) + part105-bound`, with `μ = vol(B_{m+1}(ℓ))/(2ζ(m+1))`. -/
theorem haarWindowTemplate {m : ℕ} (hm₂ : 2 ≤ m) (D : Set (SL (m+1)))
    (hm : MeasurableSet D) (hd : IsFundamentalDomain (integerGroup (m+1)).op D (groupHaar (m+1)))
    (hp : groupHaar (m+1) D ≠ 0) (hf : groupHaar (m+1) D ≠ ⊤)
    {ℓ c : ℝ} (hℓ : 0 ≤ ℓ) (hc : 0 < c) :
    let μ := volume (Metric.ball (0 : E (m+1)) ℓ) / (2 * ∑' k, dilationWeight (m+1) k)
    (groupHaar (m+1)).restrict D {g | ¬ templateAccepts ℓ c g} / groupHaar (m+1) D ≤
      1 / (1 + μ) +
        (ENNReal.ofReal (ℓ ^ (m+1)) * volume (Metric.ball (0 : E (m+1)) 1) /
          ∑' k, dilationWeight (m+1) k) * (ENNReal.ofReal (c ^ m) * volume (Metric.ball (0 : E m) 1) /
            (2 * ∑' k, dilationWeight m k)) := by
  classical
  intro μ
  let H := groupHaar (m+1)
  let N := fun g : SL (m+1) ↦ ∑' v : ContentFiber (m+1) 1,
    shortProjectionTest (Metric.closedBall 0 ℓ) c (latticePoint g v.val.val)
      (projectedPoints g v.val.val)
  let A := {g : SL (m+1) | primitiveBallPairs ℓ g = 0}
  let B := {g : SL (m+1) | 1 ≤ N g}
  have hA : MeasurableSet A := measurable_pairs' ℓ (measurableSet_singleton 0)
  have hN : Measurable N := Measurable.tsum fun v ↦ measurable_test ℓ c v.val.val
  -- failure ⊆ {P = 0} ∪ {N ≥ 1}
  have cover : {g | ¬ templateAccepts ℓ c g} ⊆ A ∪ B := by
    intro g hg
    by_cases h0 : primitiveBallPairs ℓ g = 0
    · exact Or.inl h0
    right
    obtain ⟨v, hv⟩ := pairs_pos_exists (pos_iff_ne_zero.mpr h0)
    have fails : ¬ quotientPasses c g v.val.val := fun hpass ↦ hg ⟨v, hv.le, hpass⟩
    unfold quotientPasses at fails
    push Not at fails
    obtain ⟨y, hy, hpos, hlt⟩ := fails
    have one : shortProjectionTest (Metric.closedBall 0 ℓ) c (latticePoint g v.val.val)
        (projectedPoints g v.val.val) = 1 := by
      unfold shortProjectionTest
      rw [if_pos]
      have : ((m + 1 - 1 : ℕ) : ℝ) = (m : ℝ) := by simp
      exact ⟨by simpa [Metric.mem_closedBall] using hv.le, y, hy, hpos, hlt⟩
    show 1 ≤ N g
    rw [← one]
    exact le_tsum (fun v : ContentFiber (m+1) 1 ↦
      shortProjectionTest (Metric.closedBall 0 ℓ) c (latticePoint g v.val.val)
        (projectedPoints g v.val.val)) v
  -- the {P = 0} term
  have hz : (∑' k, dilationWeight (m+1) k) ≠ 0 := by
    apply ne_of_gt
    apply lt_of_lt_of_le _ (ENNReal.le_tsum 0)
    simp [dilationWeight]
  have hμ : μ ≠ ⊤ := ENNReal.div_ne_top measure_ball_lt_top.ne (mul_ne_zero (by norm_num) hz)
  have termA : H (A ∩ D) / H D ≤ 1 / (1 + μ) := by
    have low := primitiveBallPairs_hit_lower (by omega) D hm hd hp hf ℓ
    rw [Measure.restrict_apply' hm] at low
    have compl : {g | 0 < primitiveBallPairs ℓ g} = Aᶜ := by
      ext g; simp [A, pos_iff_ne_zero]
    rw [compl] at low
    have split : H (A ∩ D) + H (Aᶜ ∩ D) = H D := by
      rw [Set.inter_comm A, Set.inter_comm Aᶜ]
      exact measure_inter_add_sdiff D hA
    have sum1 : H (A ∩ D) / H D + H (Aᶜ ∩ D) / H D = 1 := by
      rw [← ENNReal.add_div, split, ENNReal.div_self hp hf]
    have hB : H (Aᶜ ∩ D) / H D ≠ ⊤ :=
      ENNReal.div_ne_top (measure_ne_top_of_subset Set.inter_subset_right hf) hp
    rw [← one_sub_frac hμ, ENNReal.eq_sub_of_add_eq hB sum1]
    exact tsub_le_tsub_left low 1
  -- the {N ≥ 1} term (Markov + Part 105)
  have termB : H (B ∩ D) / H D ≤
      (ENNReal.ofReal (ℓ ^ (m+1)) * volume (Metric.ball (0 : E (m+1)) 1) /
        ∑' k, dilationWeight (m+1) k) * (ENNReal.ofReal (c ^ m) * volume (Metric.ball (0 : E m) 1) /
          (2 * ∑' k, dilationWeight m k)) := by
    refine le_trans ?_ (part105 D hm hd hp hf hm₂ hℓ hc)
    gcongr
    have markov := mul_meas_ge_le_lintegral₀ (μ := H.restrict D) hN.aemeasurable 1
    rw [one_mul, Measure.restrict_apply' hm] at markov
    exact markov
  rw [Measure.restrict_apply' hm]
  calc H ({g | ¬ templateAccepts ℓ c g} ∩ D) / H D ≤ (H (A ∩ D) + H (B ∩ D)) / H D := by
        gcongr
        calc H ({g | ¬ templateAccepts ℓ c g} ∩ D) ≤ H ((A ∩ D) ∪ (B ∩ D)) := by
              apply measure_mono
              rw [← Set.union_inter_distrib_right]
              exact Set.inter_subset_inter_left _ cover
          _ ≤ _ := measure_union_le _ _
    _ = H (A ∩ D) / H D + H (B ∩ D) / H D := ENNReal.add_div
    _ ≤ _ := add_le_add termA termB

/-- **Theorem 8, μ-form.** The Part 105 term equals `μ · c^m V_m/ζ(m)`, so the failure
probability is at most `1/(1+μ) + μ · c^m V_m/ζ(m)` (with `c = c′G_m` this is the note's
`1/(1+μ) + μ c′^m/ζ(m)`). -/
theorem haarWindowTemplate_mu {m : ℕ} (hm₂ : 2 ≤ m) (D : Set (SL (m+1)))
    (hm : MeasurableSet D) (hd : IsFundamentalDomain (integerGroup (m+1)).op D (groupHaar (m+1)))
    (hp : groupHaar (m+1) D ≠ 0) (hf : groupHaar (m+1) D ≠ ⊤)
    {ℓ c : ℝ} (hℓ : 0 ≤ ℓ) (hc : 0 < c) :
    let μ := volume (Metric.ball (0 : E (m+1)) ℓ) / (2 * ∑' k, dilationWeight (m+1) k)
    (groupHaar (m+1)).restrict D {g | ¬ templateAccepts ℓ c g} / groupHaar (m+1) D ≤
      1 / (1 + μ) + μ * (ENNReal.ofReal (c ^ m) * volume (Metric.ball (0 : E m) 1) /
        ∑' k, dilationWeight m k) := by
  intro μ
  refine (haarWindowTemplate hm₂ D hm hd hp hf hℓ hc).trans_eq ?_
  congr 1
  have hb : volume (Metric.ball (0 : E (m+1)) ℓ) =
      ENNReal.ofReal (ℓ ^ (m+1)) * volume (Metric.ball (0 : E (m+1)) 1) := by
    rw [Measure.addHaar_ball volume _ hℓ, finrank_euclideanSpace, Fintype.card_fin]
  simp only [μ, hb, div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),
    ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  ring

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.haarWindowTemplate
#print axioms SigabaNeo.Wall1.haarWindowTemplate_mu
