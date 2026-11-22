import SigabaNeo.Lib.Lattices.Research.Wall1.PrimitiveUnfolding
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-! Disintegration of primitive incidence over the marked first column. -/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix SigabaNeo.Rogers
open scoped ENNReal Pointwise ProbabilityTheory
namespace SigabaNeo.Wall1

def markedColumn {n : ℕ} (hn : 2 ≤ n) (g : SL n) : E n :=
  latticePoint g (Pi.single (⟨0, by omega⟩ : Fin n) 1)

private theorem measurable_latticePoint {n : ℕ} (z : Fin n → ℤ) :
    Measurable (fun g : SL n ↦ latticePoint g z) := by
  let : BorelSpace (SL n) := ⟨rfl⟩
  apply Continuous.measurable
  apply (PiLp.continuous_toLp 2 _).comp
  change Continuous (fun g : SL n ↦ g.val.mulVec _)
  unfold Matrix.mulVec dotProduct
  fun_prop

theorem measurable_markedColumn {n : ℕ} (hn : 2 ≤ n) : Measurable (markedColumn hn) :=
  measurable_latticePoint _

def primitiveIncidence {n : ℕ} (hn : 2 ≤ n) (D : Set (SL n)) : Measure (SL n) :=
  (groupHaar n D)⁻¹ • (groupHaar n).restrict (⋃ v, primitiveTranslate hn v • D)

theorem primitiveIncidence_map {n : ℕ} (hn : 2 ≤ n) (D : Set (SL n))
    (hm : MeasurableSet D) (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (hp : groupHaar n D ≠ 0) (hf : groupHaar n D ≠ ⊤) :
    (primitiveIncidence hn D).map (markedColumn hn) =
      (∑' k, dilationWeight n k)⁻¹ • volume := by
  apply Measure.ext_of_lintegral
  intro f h
  rw [lintegral_map h (measurable_markedColumn hn), primitiveIncidence,
    lintegral_smul_measure, lintegral_smul_measure]
  simpa [markedColumn, div_eq_mul_inv, mul_comm] using
    primitive_unfolded_marginal hn D hm hd hp hf f h

/-- Joint law of the first column and any measurable frame statistic on a finite-volume
window. The resulting conditional probabilities may still depend on the marked column. -/
theorem primitive_window_disintegration {n : ℕ} (hn : 2 ≤ n) (D : Set (SL n))
    (hm : MeasurableSet D) (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (hp : groupHaar n D ≠ 0) (hf : groupHaar n D ≠ ⊤)
    (W : Set (E n)) (hW : MeasurableSet W) (hfin : volume W ≠ ⊤)
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (T : SL n → Y) (hT : Measurable T) :
    ∃ K : Kernel (E n) Y, IsMarkovKernel K ∧
      (((∑' k, dilationWeight n k)⁻¹ • (volume : Measure (E n))).restrict W) ⊗ₘ K =
        ((primitiveIncidence hn D).restrict (markedColumn hn ⁻¹' W)).map
          (fun g ↦ (markedColumn hn g, T g)) := by
  let μ := (primitiveIncidence hn D).restrict (markedColumn hn ⁻¹' W)
  have hx := measurable_markedColumn hn
  have marginal : μ.map (markedColumn hn) =
      (((∑' k, dilationWeight n k)⁻¹ • (volume : Measure (E n))).restrict W) := by
    rw [← primitiveIncidence_map hn D hm hd hp hf, Measure.restrict_map hx hW]
  have hz : (∑' k, dilationWeight n k) ≠ 0 := by
    have h := le_tsum (dilationWeight n) 0
    intro e
    rw [e] at h
    simp [dilationWeight] at h
  let : IsFiniteMeasure μ := ⟨by
    have h := congrArg (fun ν : Measure (E n) ↦ ν Set.univ) marginal
    simp [Measure.map_apply hx, Measure.restrict_apply, Measure.smul_apply] at h
    exact h ▸ ENNReal.mul_lt_top (ENNReal.inv_ne_top.mpr hz).lt_top hfin.lt_top⟩
  exact ⟨condDistrib T (markedColumn hn) μ, inferInstance, marginal ▸
    compProd_map_condDistrib hx.aemeasurable hT.aemeasurable⟩

/-- A single conditional law on all first columns, valid simultaneously for every
nonnegative measurable joint test. -/
theorem primitive_incidence_disintegration {n : ℕ} (hn : 2 ≤ n) (D : Set (SL n))
    (hm : MeasurableSet D) (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (hp : groupHaar n D ≠ 0) (hf : groupHaar n D ≠ ⊤)
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (T : SL n → Y) (hT : Measurable T) :
    ∃ K : Kernel (E n) Y, IsMarkovKernel K ∧ ∀ F : E n × Y → ℝ≥0∞, Measurable F →
      (∫⁻ g, F (markedColumn hn g, T g) ∂primitiveIncidence hn D) =
        (∫⁻ x, ∫⁻ y, F (x, y) ∂K x) / ∑' k, dilationWeight n k := by
  classical
  let ν : Measure (E n) := volume
  let W := disjointed (spanningSets ν)
  have hmW : ∀ i, MeasurableSet (W i) := MeasurableSet.disjointed (measurableSet_spanningSets ν)
  have hfW (i : ℕ) : ν (W i) ≠ ⊤ :=
    ((measure_mono (disjointed_subset _ _)).trans_lt (measure_spanningSets_lt_top ν i)).ne
  choose K hK joint using fun i ↦
    primitive_window_disintegration hn D hm hd hp hf (W i) (hmW i) (hfW i) T hT
  let L : Kernel (E n) Y :=
    ⟨fun x ↦ K (spanningSetsIndex ν x) x,
      (measurable_from_prod_countable_left (f := fun p : E n × ℕ ↦ K p.2 p.1)
        (fun i ↦ (K i).measurable)).comp
          (measurable_id.prodMk (measurableSet_spanningSetsIndex ν))⟩
  refine ⟨L, ⟨fun x ↦ (hK _).isProbabilityMeasure x⟩, ?_⟩
  intro F hF
  let η := (∑' k, dilationWeight n k)⁻¹ • ν
  have cover : ⋃ i, W i = Set.univ := iUnion_disjointed.trans (iUnion_spanningSets ν)
  have precover : (⋃ i, markedColumn hn ⁻¹' W i) = Set.univ := by
    rw [← Set.preimage_iUnion, cover, Set.preimage_univ]
  have hx := measurable_markedColumn hn
  have a := lintegral_iUnion (μ := primitiveIncidence hn D) (fun i ↦ hx (hmW i))
    (fun i j hij ↦ (disjoint_disjointed _ hij).preimage (markedColumn hn))
    (fun g ↦ F (markedColumn hn g, T g))
  have b := lintegral_iUnion (μ := η) hmW (disjoint_disjointed _)
    (fun x ↦ ∫⁻ y, F (x, y) ∂L x)
  rw [precover, Measure.restrict_univ] at a
  rw [cover, Measure.restrict_univ] at b
  rw [a, div_eq_mul_inv, mul_comm]
  change _ = (∑' k, dilationWeight n k)⁻¹ • (∫⁻ x, ∫⁻ y, F (x, y) ∂L x ∂ν)
  rw [← lintegral_smul_measure]
  rw [b]
  apply tsum_congr
  intro i
  rw [← lintegral_map hF (hx.prodMk hT), ← joint i, Measure.lintegral_compProd hF]
  apply setLIntegral_congr_fun (hmW i)
  intro x hxW
  change _ = ∫⁻ y, F (x, y) ∂K (spanningSetsIndex ν x) x
  rw [(spanningSetsIndex_eq_iff ν).2 hxW]

/-- The range of this countably indexed family is the scaled projected lattice in
ambient Euclidean coordinates. -/
def normalizedProjection {n : ℕ} (hn : 2 ≤ n) (g : SL n) (z : Fin n → ℤ) : E n :=
  ‖markedColumn hn g‖ ^ ((n - 1 : ℕ) : ℝ)⁻¹ •
    (ℝ ∙ markedColumn hn g)ᗮ.starProjection (latticePoint g z)

theorem measurable_normalizedProjection {n : ℕ} (hn : 2 ≤ n) :
    Measurable (normalizedProjection hn) := by
  apply measurable_pi_lambda
  intro z
  have hx := measurable_markedColumn hn
  have hz := measurable_latticePoint z
  simp only [normalizedProjection, Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_singleton]
  exact (hx.norm.pow_const _).smul (hz.sub (((hx.inner hz).div (hx.norm.pow_const 2)).smul hx))

/-- Conditional law of the entire enumerated, determinant-normalized projection. -/
theorem normalizedProjection_disintegration {n : ℕ} (hn : 2 ≤ n) (D : Set (SL n))
    (hm : MeasurableSet D) (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (hp : groupHaar n D ≠ 0) (hf : groupHaar n D ≠ ⊤) :
    ∃ K : Kernel (E n) ((Fin n → ℤ) → E n), IsMarkovKernel K ∧
      ∀ F : E n × ((Fin n → ℤ) → E n) → ℝ≥0∞, Measurable F →
        (∫⁻ g, F (markedColumn hn g, normalizedProjection hn g) ∂primitiveIncidence hn D) =
          (∫⁻ x, ∫⁻ p, F (x, p) ∂K x) / ∑' k, dilationWeight n k :=
  primitive_incidence_disintegration hn D hm hd hp hf _ (measurable_normalizedProjection hn)

#print axioms measurable_markedColumn
#print axioms primitiveIncidence_map
#print axioms primitive_window_disintegration
#print axioms primitive_incidence_disintegration
#print axioms measurable_normalizedProjection
#print axioms normalizedProjection_disintegration
end SigabaNeo.Wall1
