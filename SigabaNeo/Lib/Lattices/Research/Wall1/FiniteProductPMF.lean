module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option

/-! # Independent seeds indexed by a finite input type -/

public section
noncomputable section

namespace SigabaNeo.Wall1

open scoped ENNReal

universe u v

private theorem tsum_tuple_prod {I : Type u} [Fintype I] {X : I → Type v}
    (w : ∀ i, X i → ℝ≥0∞) : (∑' ω : ∀ i, X i, ∏ i, w i (ω i)) = ∏ i, ∑' z, w i z := by
  classical
  refine Fintype.induction_empty_option (P := fun J _ ↦ ∀ (Y : J → Type v)
    (g : ∀ j, Y j → ℝ≥0∞), (∑' y : ∀ j, Y j, ∏ j, g j (y j)) = ∏ j, ∑' z, g j z)
    ?_ ?_ ?_ I X w
  · intro J K _ e ih X w
    let _ := Fintype.ofEquiv K e.symm
    let f (y : ∀ j, X (e j)) := ∏ j, w (e j) (y j)
    calc
      _ = ∑' ω : ∀ i, X i, f ((Equiv.piCongrLeft X e).symm ω) :=
        tsum_congr fun ω ↦ (e.prod_comp (fun i ↦ w i (ω i))).symm
      _ = ∑' y, f y := (Equiv.piCongrLeft X e).symm.tsum_eq f
      _ = ∏ j, ∑' z, w (e j) z := ih _ _
      _ = _ := e.prod_comp (fun j ↦ ∑' z, w j z)
  · intro X w
    simp
  · intro J _ ih X w
    let f (p : X none × (∀ j : J, X (some j))) :=
      w none p.1 * ∏ j, w (some j) (p.2 j)
    calc
      _ = ∑' ω : ∀ i, X i, f (Equiv.piOptionEquivProd ω) :=
        tsum_congr fun ω ↦ Fintype.prod_option _
      _ = ∑' p, f p := Equiv.piOptionEquivProd.tsum_eq f
      _ = _ := by
        rw [tsum_prod']
        simp only [f, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, ih, Fintype.prod_option]

variable {I : Type u} [Fintype I] {X : I → Type v} (ν : ∀ i, PMF (X i))

/-- The independent product of the coordinate laws on dependent tuples. -/
@[expose] def finiteProductPMF : PMF (∀ i, X i) :=
  ⟨fun ω ↦ ∏ i, ν i (ω i), CompleteLattice.summable.hasSum_iff.mpr (by simp [tsum_tuple_prod])⟩

@[simp] theorem finiteProductPMF_apply (ω : ∀ i, X i) :
    finiteProductPMF ν ω = ∏ i, ν i (ω i) := rfl

/-- A rectangle has mass equal to the product of its coordinate masses. -/
theorem finiteProductPMF_rectangle (B : ∀ i, Set (X i)) :
    (finiteProductPMF ν).toOuterMeasure (Set.univ.pi B) = ∏ i, (ν i).toOuterMeasure (B i) := by
  classical
  simp only [PMF.toOuterMeasure_apply]
  rw [← tsum_tuple_prod]
  apply tsum_congr
  intro ω
  by_cases h : ∀ i, ω i ∈ B i
  · have hmem : ω ∈ Set.univ.pi B := fun i _ ↦ h i
    simp [Set.indicator_of_mem, h, hmem]
  · obtain ⟨i, hi⟩ := Classical.not_forall.mp h
    have hmem : ω ∉ Set.univ.pi B := fun hm ↦ hi (hm i (Set.mem_univ _))
    rw [Set.indicator_of_notMem hmem]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm

/-- An arbitrary event tested at one coordinate has its original outer measure. -/
theorem finiteProductPMF_cylinder (i : I) (B : Set (X i)) :
    (finiteProductPMF ν).toOuterMeasure {ω | ω i ∈ B} = (ν i).toOuterMeasure B := by
  classical
  change (finiteProductPMF ν).toOuterMeasure (Function.eval i ⁻¹' B) = _
  rw [← Set.univ_pi_update_univ, finiteProductPMF_rectangle, Fintype.prod_eq_mul_prod_subtype_ne _ i,
    Function.update_self]
  suffices (∏ j : {j : I // j ≠ i}, (ν j.val).toOuterMeasure
      (Function.update (fun k ↦ Set.univ) i B j.val)) = 1 by rw [this, mul_one]
  apply Finset.prod_eq_one
  intro j _
  simp [Function.update_of_ne j.property, PMF.toOuterMeasure_apply]

/-- Evaluation at a coordinate pushes the product law forward to the prescribed PMF. -/
@[simp] theorem finiteProductPMF_map_eval (i : I) :
    (finiteProductPMF ν).map (fun ω ↦ ω i) = ν i := by
  apply PMF.ext
  intro z
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  exact (finiteProductPMF_cylinder ν i {z}).trans ((ν i).toOuterMeasure_apply_singleton z)

/-- The single product seed preserves the failure bound for every input. -/
theorem finiteProductPMF_uniform_bound {Output : Type*} (F : ∀ i, X i → Output)
    (Good : I → Output → Prop) (δ : ℝ)
    (herr : ∀ i, (ν i).toOuterMeasure {z | ¬ Good i (F i z)} ≤ ENNReal.ofReal δ) :
    let μ := finiteProductPMF ν
    let S := fun (ω : ∀ i, X i) (i : I) ↦ F i (ω i)
    ∀ i, μ.toOuterMeasure {ω | ¬ Good i (S ω i)} ≤ ENNReal.ofReal δ := by
  intro μ S i
  exact (finiteProductPMF_cylinder ν i {z | ¬ Good i (F i z)}).le.trans (herr i)

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.finiteProductPMF
#print axioms SigabaNeo.Wall1.finiteProductPMF_apply
#print axioms SigabaNeo.Wall1.finiteProductPMF_rectangle
#print axioms SigabaNeo.Wall1.finiteProductPMF_cylinder
#print axioms SigabaNeo.Wall1.finiteProductPMF_map_eval
#print axioms SigabaNeo.Wall1.finiteProductPMF_uniform_bound
