module

public import SigabaNeo.Lib.Lattices.Research.Wall1.SelectorUniformValidation
public import SigabaNeo.Lib.Lattices.Research.Wall1.MultiBlockVerify
public import SigabaNeo.Lib.Lattices.Research.Wall1.UniqueClosestSelection
public import SigabaNeo.Lib.Lattices.Research.Wall1.ShiftedGaussianError
import all SigabaNeo.Lib.Lattices.Attacks.Primal.SampleDeletionBall
import Mathlib.Tactic

/-! Finite sets of tied integer minimizers and a common-event transfer for four selectors. -/

public section
noncomputable section
namespace SigabaNeo.Wall1.SelectorUniform
open SigabaNeo.SampleDeletion
open scoped Classical

variable {ι α : Type*} [Fintype ι]

/-- All least-norm integer points satisfying a predicate on the observed data. -/
def isMinimum (F : (ι → ℤ) → Prop) (x : ι → ℤ) : Prop :=
  F x ∧ ∀ y, F y → normSq x ≤ normSq y

theorem finite_minima (F : (ι → ℤ) → Prop) : {x | isMinimum F x}.Finite := by
  classical
  by_cases he : ∃ y, F y
  · obtain ⟨y, hy⟩ := he
    let : Finite (Points ι (normSq y)) := pointsFinite _ _
    apply Set.Finite.subset (Set.finite_range (fun z : Points ι (normSq y) ↦ z.val))
    intro x hx
    exact ⟨⟨x, hx.2 _ hy⟩, rfl⟩
  · have h : {x | isMinimum F x} = ∅ := Set.eq_empty_iff_forall_notMem.mpr
      fun x hx ↦ he ⟨x, hx.1⟩
    rw [h]
    exact Set.finite_empty

/-- Distinct decoded answers, including a possible rejection, with every tie retained. -/
def minimumOptions (F : (ι → ℤ) → Prop) (decode : (ι → ℤ) → Option α) : Finset (Option α) :=
  (finite_minima F).toFinset.image decode

theorem mem_minimumOptions {F : (ι → ℤ) → Prop} {decode : (ι → ℤ) → Option α} {a : Option α} :
    a ∈ minimumOptions F decode ↔ ∃ x, isMinimum F x ∧ decode x = a := by
  simp [minimumOptions]

theorem minimumOptions_of_unique {F : (ι → ℤ) → Prop} {p : ι → ℤ}
    (hp : isMinimum F p) (hu : ∀ x, isMinimum F x → x = p) (decode : (ι → ℤ) → Option α) :
    minimumOptions F decode = {decode p} := by
  ext a
  rw [mem_minimumOptions, Finset.mem_singleton]
  exact ⟨fun ⟨x, hx, he⟩ ↦ (hu x hx) ▸ he.symm, fun h ↦ ⟨p, hp, h.symm⟩⟩

/-- Conditional on the non-validation data, charge each distinct residue decoded from any
minimum of any block once. The validation matrix is uniform and independent of those data. -/
theorem minima_validation_le {Ω : Type*} [Fintype Ω] {k n q v : ℕ} [Fact q.Prime]
    (hq : 6 < q) (p : Ω → ℚ) (hp : ∀ ω, 0 ≤ p ω)
    (F : Ω → Fin k → (ι → ℤ) → Prop) (decode : Ω → Fin k → (ι → ℤ) → Option (Fin n → ZMod q))
    (s : Ω → Fin n → ZMod q) (e : Ω → Fin v → ZMod q) :
    let C ω := wrong (fun i ↦ minimumOptions (F ω i) (decode ω i)) (s ω)
    (∑ ω, p ω * (((Finset.univ.filter fun A : Matrix (Fin v) (Fin n) (ZMod q) ↦
      ∃ c ∈ C ω, ∀ j, MultiBlock.accept
        (dotProduct (A j) (s ω) + e ω j - dotProduct (A j) c)).card : ℚ) /
          (q : ℚ)^(n*v))) ≤ (∑ ω, p ω * (C ω).card) * (7/q)^v := by
  apply MultiBlock.verify_union_avg hq p hp
  exact fun ω h ↦ (mem_wrong.mp h).1 rfl

open Cslib.Probability

/-- Four approximate choices on one probability space. The marginal solver estimate can
use a one-draw coupling furnished by the explicit sampler excess-mass hypothesis. -/
theorem transfer_four {Ω : Type*} {X : Type} (law : PMF Ω)
    (options : Ω → Fin 4 → Finset (Option α)) (truth : Ω → α) (accept : Ω → α → Bool)
    (choose : Ω → Fin 4 → Option α) (ht : ∀ ω, accept ω (truth ω) = true)
    (credit : 643162094166 / (10 : ℝ)^12 <
      (law.toOuterMeasure {ω | credited (options ω) (truth ω) (accept ω)}).toReal)
    (P Q : Fin 4 → PMF X)
    (samplerTV : ∀ i, ∑' x, (P i x - Q i x) ≤ ENNReal.ofReal (1 / (2 : ℝ)^923))
    (marginal : ∀ i, PMF.CoupledWithin (P i) (Q i) (ENNReal.ofReal (1 / (2 : ℝ)^923)) →
      law.toOuterMeasure {ω | choose ω i ∉ options ω i} ≤ ENNReal.ofReal (1 / (2 : ℝ)^168)) :
    6431620941 / (10 : ℝ)^10 <
      (law.toOuterMeasure {ω | first (choose ω) (accept ω) = some (truth ω)}).toReal := by
  apply CVP638.four_event_transfer law _ _ (fun i ↦ {ω | choose ω i ∉ options ω i}) _ credit
    (fun i ↦ marginal i (oneDrawCoupling_of_samplerTV _ _ (samplerTV i)))
  intro ω hω
  by_cases h : ∀ i, choose ω i ∈ options ω i
  · exact Or.inl (first_of_credited hω (ht ω) _ h)
  · exact Or.inr (Set.mem_iUnion.mpr (not_forall.mp h))

end SigabaNeo.Wall1.SelectorUniform

#print axioms SigabaNeo.Wall1.SelectorUniform.finite_minima
#print axioms SigabaNeo.Wall1.SelectorUniform.mem_minimumOptions
#print axioms SigabaNeo.Wall1.SelectorUniform.minimumOptions_of_unique
#print axioms SigabaNeo.Wall1.SelectorUniform.minima_validation_le
#print axioms SigabaNeo.Wall1.SelectorUniform.transfer_four
