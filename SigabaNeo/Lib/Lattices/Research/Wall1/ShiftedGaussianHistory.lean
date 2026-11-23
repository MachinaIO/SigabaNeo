module

public import SigabaNeo.Lib.Lattices.Research.Wall1.ShiftedGaussianPair
public import SigabaNeo.Lib.Lattices.Research.Wall1.AdrsStableProcedure
import all SigabaNeo.Lib.Lattices.Research.Wall1.AdrsStableProcedure
import Mathlib.Tactic

/-! Stable maximal pairing for arbitrary Gaussian shifts. The ideal Poisson list and
the fixed-size algorithm have a joint law with the stated unconditional marginals. -/

@[expose] public section
noncomputable section
namespace SigabaNeo.Wall1.CVP638

open SigabaNeo.Wall1.ADRS ProbabilityTheory ZLattice Cslib.Probability.PMF MeasureTheory
open scoped ENNReal NNReal

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
variable (L : Submodule ℤ E) (b : Module.Basis ι ℤ L) {r : ℕ} (e : (ι → ZMod 2) ≃ Fin r)
variable [FiniteDimensional ℝ E] [DiscreteTopology L]

theorem shifted_labels_bind {s : ℝ} (hs : 0 < s) (t : E) :
    (labelLaw L b hs t e).bind (restricted L b hs t e) = discreteGaussian L s hs t := by
  classical
  ext x
  rw [PMF.bind_apply, tsum_eq_single (binLabel L b e x)]
  · simp only [restricted, fiberLaw_apply, eq_self, ite_true]
    rw [mul_comm, labelLaw, ENNReal.div_mul_cancel
      (labelMass_ne_zero _ _ (shiftedBin_possible L b hs t e) _) (PMF.apply_ne_top _ _)]
  · intro c hc
    simp [restricted, fiberLaw_apply, Ne.symm hc]

variable {s : ℝ} (hs : 0 < s) (t : E)

/-- The actual maximal-pairing label-count transition; each bin contributes floor(N/2)
independent average labels. -/
private def procedureStep (j : ℕ) : Multiset (Fin r) → PMF (Multiset (Fin r)) :=
  maximalMarks fun c ↦ (averageLaw L b (stepWidth_pos hs j) t e c).map (binLabel L b e)

/-- Procedure E started with a fixed number of iid samples, retaining label histories. -/
private def procedureLabels (n : ℕ) : ℕ → PMF (Multiset (Fin r))
  | 0 => (iid (labelLaw L b hs t e) n).map tupleBag
  | j+1 => (procedureLabels n j).bind (procedureStep L b e hs t j)

/-- Recover the actual value multiset after the label history. -/
private def procedureValues (n j : ℕ) : PMF (Multiset L) :=
  (procedureLabels L b e hs t n j).bind (mark (restricted L b (stepWidth_pos hs j) t e))

/-- The local hypotheses of the count coupling, only at steps strictly before ℓ. -/
def ShiftedSchedule (ℓ : ℕ) (rate θ A : ℕ → ℝ≥0) (m : ℕ → ℕ) : Prop :=
  ∀ j < ℓ, 0 < rate j ∧ 0 < θ j ∧ 0 < A j ∧
      (∀ c, rate j * (labelLaw L b (stepWidth_pos hs j) t e c).toNNReal ≤ A j) ∧
      m j = ⌊(A j:ℝ)/(4*θ j)-1/2⌋₊ ∧ 1 ≤ m j ∧
      rate (j+1) = nextRate (rate j) (labelLaw L b (stepWidth_pos hs j) t e) (θ j) (A j)

/-- History induction for an arbitrary starting count law and its input coupling error. -/
private theorem gaussian_history_from (ℓ : ℕ) (rate θ A : ℕ → ℝ≥0) (m : ℕ → ℕ)
    (hparams : ShiftedSchedule L b e hs t ℓ rate θ A m) (actual : ℕ → PMF (Multiset (Fin r)))
    (δ : ℝ≥0∞) (h₀ : Dominated (poissonList (rate 0) (labelLaw L b hs t e)) (actual 0) δ)
    (hstep : ∀ j < ℓ, actual (j+1) = (actual j).bind (procedureStep L b e hs t j)) :
    Dominated (poissonList (rate ℓ) (discreteGaussian L (stepWidth s ℓ) (stepWidth_pos hs ℓ) t))
      ((actual ℓ).bind (mark (restricted L b (stepWidth_pos hs ℓ) t e)))
      (δ + ∑ j ∈ Finset.range ℓ, stepError (rate j) (rate (j+1)) (θ j) (m j)) := by
  let q j := labelLaw L b (stepWidth_pos hs j) t e
  let err j := stepError (rate j) (rate (j+1)) (θ j) (m j)
  have hlocal (j) (hj : j < ℓ) : Dominated (poissonList (rate (j+1)) (q (j+1)))
      ((poissonList (rate j) (q j)).bind (procedureStep L b e hs t j)) (err j) := by
    obtain ⟨hr,hθ,hA,hmax,hm,hm₁,hrate⟩ := hparams j hj
    let M := fun c ↦ (averageLaw L b (stepWidth_pos hs j) t e c).map (binLabel L b e)
    have hM : (squaredLabels (q j)).bind M = q (j+1) := by
      change ((squaredLabels (q j)).bind fun c ↦ (averageLaw L b _ t e c).map _) = _
      rw [← PMF.map_bind, shifted_squared_labels]
      rfl
    obtain ⟨_, _, _, _, hmaximal⟩ := poisson_selected_marks (rate j) (θ j) (A j) (q j) M hr hθ hA
      (labelMass_ne_zero _ _ (shiftedBin_possible L b (stepWidth_pos hs j) t e)) hmax hm hm₁
    change rate (j+1) = nextRate (rate j) (q j) (θ j) (A j) at hrate
    simp only [hM, ← hrate] at hmaximal
    exact hmaximal
  have H := history_domination (fun j ↦ poissonList (rate j) (q j)) actual
    (procedureStep L b e hs t) err δ ℓ h₀ hlocal hstep (fun j ↦ maximalMarks_mono _)
  have h := H.bind (mark (restricted L b (stepWidth_pos hs ℓ) t e)) (mark_submultiset_coupling _)
  simpa only [poissonList_bind_mark, q, shifted_labels_bind, err] using h

/-- Unconditional exact Poisson marginal after any finite number of combiner steps.
The input-size overflow and the individual step errors are charged once each. -/
private theorem procedure_history (n ℓ : ℕ) (rate θ A : ℕ → ℝ≥0) (m : ℕ → ℕ)
    (hparams : ShiftedSchedule L b e hs t ℓ rate θ A m) :
    Dominated (poissonList (rate ℓ) (discreteGaussian L (stepWidth s ℓ) (stepWidth_pos hs ℓ) t))
      (procedureValues L b e hs t n ℓ) (poissonMeasure (rate 0) {t | n < t} +
        ∑ j ∈ Finset.range ℓ, stepError (rate j) (rate (j+1)) (θ j) (m j)) := by
  exact gaussian_history_from L b e hs t ℓ rate θ A m hparams (procedureLabels L b e hs t n)
    _ (poisson_initial_domination (rate 0) _ n) (fun _ _ ↦ rfl)

/-- The physical run, starting with exactly n independent Gaussians and then mapping
the deterministic stable pairing function over the ordered list at each step. -/
def shiftedRun (n : ℕ) : ℕ → PMF (SampleList L)
  | 0 => (iid (discreteGaussian L s hs t) n).map (Sigma.mk n)
  | j+1 => (shiftedRun n j).map (stablePair (binLabel L b e) (latticeMidpoint L))

private def labelRun (n : ℕ) : ℕ → PMF (SampleList (Fin r))
  | 0 => (iid (labelLaw L b hs t e) n).map (Sigma.mk n)
  | j+1 => (labelRun n j).bind fun u ↦ drawList (fun c ↦
      (averageLaw L b (stepWidth_pos hs j) t e c).map (binLabel L b e)) (sourceLabels u)

private theorem labelRun_bag (n j : ℕ) :
    (labelRun L b e hs t n j).map sampleBag = procedureLabels L b e hs t n j := by
  induction j with
  | zero => rw [labelRun, procedureLabels, PMF.map_comp]; rfl
  | succ j ih =>
    rw [labelRun, procedureLabels, ← ih, PMF.bind_map, PMF.map_bind]
    congr 1
    funext u
    rw [drawList_bag, sourceLabels_bag]
    rfl

private theorem shiftedRun_disintegrate (n j : ℕ) :
    shiftedRun L b e hs t n j = (labelRun L b e hs t n j).bind
      (drawList (restricted L b (stepWidth_pos hs j) t e)) := by
  induction j with
  | zero =>
    rw [shiftedRun, labelRun, PMF.bind_map]
    simp only [Function.comp_def, drawList, ← PMF.map_bind, ← piFin_const, piFin_bind,
      stepWidth, shifted_labels_bind]
  | succ j ih =>
    rw [shiftedRun, ih, PMF.map_bind, labelRun, PMF.bind_bind]
    congr 1
    funext u
    rw [drawList_bind]
    have hres (c) : ((averageLaw L b (stepWidth_pos hs j) t e c).map (binLabel L b e)).bind
        (restricted L b (stepWidth_pos hs (j+1)) t e) = averageLaw L b (stepWidth_pos hs j) t e c :=
      shifted_resample L b (stepWidth_pos hs j) t e c
    simp only [hres]
    apply stablePair_drawList
    intro c v hv
    exact ((PMF.mem_support_filter_iff (shiftedBin_possible L b _ t e c)).mp hv).1

/-- The physical output bag agrees exactly with the law used in the history induction. -/
private theorem shiftedRun_bag (n j : ℕ) :
    (shiftedRun L b e hs t n j).map sampleBag = procedureValues L b e hs t n j := by
  rw [shiftedRun_disintegrate, procedureValues, ← labelRun_bag, PMF.bind_map, PMF.map_bind]
  congr 1
  funext u
  exact drawList_bag _ _

/-- For the fixed input size of Procedure E, charge the Poisson input overflow once. -/
theorem shiftedRun_domination (n ℓ : ℕ) (rate θ A : ℕ → ℝ≥0) (m : ℕ → ℕ)
    (hparams : ShiftedSchedule L b e hs t ℓ rate θ A m) :
    Dominated (poissonList (rate ℓ) (discreteGaussian L (stepWidth s ℓ) (stepWidth_pos hs ℓ) t))
      ((shiftedRun L b e hs t n ℓ).map sampleBag) (poissonMeasure (rate 0) {t | n < t} +
        ∑ j ∈ Finset.range ℓ, stepError (rate j) (rate (j+1)) (θ j) (m j)) := by
  rw [shiftedRun_bag]
  exact procedure_history L b e hs t n ℓ rate θ A m hparams

end SigabaNeo.Wall1.CVP638

#print axioms SigabaNeo.Wall1.CVP638.shiftedRun_domination
