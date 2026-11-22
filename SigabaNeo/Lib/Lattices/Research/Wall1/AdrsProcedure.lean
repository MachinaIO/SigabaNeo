module

public import SigabaNeo.Lib.Lattices.Research.Wall1.AdrsGaussianBins
public import SigabaNeo.Lib.Lattices.Research.Wall1.AdrsPairSlots
import Mathlib.Tactic

/-! # Procedure E: Gaussian one-step laws, iteration, and the shortest-vector hit -/

@[expose] public section

noncomputable section

namespace SigabaNeo.Wall1.ADRS

open Cslib.Probability.PMF ProbabilityTheory MeasureTheory ZLattice
open scoped ENNReal NNReal

variable {C V W : Type*}

theorem mark_bind (M : C → PMF V) (N : V → PMF W) (u : Multiset C) :
    (mark M u).bind (mark N) = mark (fun c ↦ (M c).bind N) u := by
  induction u using Multiset.induction with
  | empty => simp [mark]
  | cons c u ih =>
    simp only [mark_cons, PMF.bind_bind, PMF.bind_map, Function.comp_def, ← ih, PMF.map_bind]
    congr 1
    funext v
    rw [PMF.bind_comm]

theorem poissonList_bind_mark (rate : ℝ≥0) (q : PMF C) (M : C → PMF V) :
    (poissonList rate q).bind (mark M) = poissonList rate (q.bind M) := by
  simp only [poissonList, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  congr 1
  funext n
  change ((iid q n).bind fun x ↦ mark M (tupleBag x)) = _
  simp only [mark_tupleBag]
  rw [← PMF.map_bind, ← piFin_const, piFin_bind, piFin_const]
  rfl

/-- Exact Poisson versus fixed input-size coupling, with the actual upper-tail probability. -/
theorem poisson_initial_domination (rate : ℝ≥0) (p : PMF C) (n : ℕ) :
    Dominated (poissonList rate p) ((iid p n).map tupleBag) (poissonMeasure rate {t | n < t}) := by
  let P := (poissonMeasure rate).toPMF
  have hf (t) : mark (fun _ : Fin 1 ↦ p) (countsBag fun _ ↦ t) = (iid p t).map tupleBag := by
    have he : countsBag (fun _ : Fin 1 ↦ t) = tupleBag (fun _ : Fin t ↦ (0 : Fin 1)) := by
      rw [← countsBag_binCounts]
      congr 1
      funext c
      fin_cases c
      simp [binCounts, Finset.sum_apply]
    rw [he, mark_tupleBag, piFin_const]
  have h := counts_domination P (fun t _ ↦ t) (fun _ _ ↦ n) (fun _ : Fin 1 ↦ p)
    (poissonMeasure rate {t | n < t}) (by
      simp only [exists_const]
      rw [← P.toMeasure_apply_eq_toOuterMeasure_apply MeasurableSet.of_discrete]
      simp [P])
  change Dominated (P.bind fun t ↦ (iid p t).map tupleBag) _ _
  simpa only [hf, PMF.bind_const] using h

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
variable (L : Submodule ℤ E) (b : Module.Basis ι ℤ L) {r : ℕ} (e : (ι → ZMod 2) ≃ Fin r)
variable [FiniteDimensional ℝ E] [DiscreteTopology L]

theorem gaussianLabels_bind {s : ℝ} (hs : 0 < s) :
    (gaussianLabels L b e hs).bind (gaussianBin L b e hs) = discreteGaussian L s hs 0 := by
  classical
  ext x
  rw [PMF.bind_apply, tsum_eq_single (binLabel L b e x)]
  · simp only [gaussianBin, fiberLaw_apply, eq_self, ite_true]
    rw [mul_comm, gaussianLabels, ENNReal.div_mul_cancel
      (labelMass_ne_zero _ _ (gaussianBin_possible L b e hs) _) (PMF.apply_ne_top _ _)]
  · intro c hc
    simp [gaussianBin, fiberLaw_apply, Ne.symm hc]

/-- Step width after j exact halvings of the variance. -/
def stepWidth (s : ℝ) : ℕ → ℝ
  | 0 => s
  | j+1 => stepWidth s j / √2

theorem stepWidth_pos {s : ℝ} (hs : 0 < s) (j : ℕ) : 0 < stepWidth s j := by
  induction j with
  | zero => exact hs
  | succ j ih => exact div_pos ih (by positivity)

variable {s : ℝ} (hs : 0 < s)

/-- The actual maximal-pairing label-count transition; each bin contributes floor(N/2)
independent average labels. -/
def procedureStep (j : ℕ) : Multiset (Fin r) → PMF (Multiset (Fin r)) :=
  maximalMarks fun c ↦ (binAverage L b e (stepWidth_pos hs j) c).map (binLabel L b e)

/-- Procedure E started with a fixed number of iid samples, retaining label histories. -/
def procedureLabels (n : ℕ) : ℕ → PMF (Multiset (Fin r))
  | 0 => (iid (gaussianLabels L b e hs) n).map tupleBag
  | j+1 => (procedureLabels n j).bind (procedureStep L b e hs j)

/-- Recover the actual value multiset after the label history. -/
def procedureValues (n j : ℕ) : PMF (Multiset L) :=
  (procedureLabels L b e hs n j).bind (mark (gaussianBin L b e (stepWidth_pos hs j)))

/-- Inside every label history, drawing the next labels and then their conditional Gaussian
values gives exactly the independent physical averages. -/
theorem procedureStep_values (j : ℕ) (u : Multiset (Fin r)) :
    (procedureStep L b e hs j u).bind (mark (gaussianBin L b e (stepWidth_pos hs (j+1)))) =
      maximalMarks (binAverage L b e (stepWidth_pos hs j)) u := by
  unfold procedureStep maximalMarks
  rw [mark_bind]
  congr 1
  funext c
  exact binAverage_resample L b e _ c

/-- Complete Gaussian version of the one-step selected-list law. K_c has the exact
squared-weight Poisson marginal. The selected physical size is min(K_c, floor(N_c/2)). -/
theorem gaussian_selected_step (rate θ A : ℝ≥0) (hrate : 0 < rate) (hθ : 0 < θ) (hA : 0 < A)
    (hmax : ∀ c, rate * (gaussianLabels L b e hs c).toNNReal ≤ A) {m : ℕ}
    (hm : m = ⌊(A:ℝ)/(4*θ)-1/2⌋₊) (hm₁ : 1 ≤ m) :
    let q := gaussianLabels L b e hs
    let outRate := nextRate rate q θ A
    let ideal := poissonList outRate (discreteGaussian L (s/√2) (by positivity) 0)
    ∃ J : Fin r → PMF (ℕ × ℕ),
      (∀ c, (J c).map Prod.fst = (poissonMeasure (rate * (q c).toNNReal)).toPMF ∧
        (J c).map Prod.snd = (poissonMeasure (outRate * (squaredLabels q c).toNNReal)).toPMF) ∧
      (piFin J).toOuterMeasure {z | ∃ c, (z c).1 / 2 < (z c).2} ≤ stepError rate outRate θ m ∧
      Dominated ideal ((piFin J).bind fun z ↦ mark (binAverage L b e hs)
        (countsBag fun c ↦ min (z c).2 ((z c).1/2))) (stepError rate outRate θ m) ∧
      Dominated ideal ((poissonList rate q).bind (maximalMarks (binAverage L b e hs)))
        (stepError rate outRate θ m) := by
  simpa only [squaredLabels_binAverage] using poisson_selected_marks rate θ A
    (gaussianLabels L b e hs) (binAverage L b e hs) hrate hθ hA
    (labelMass_ne_zero _ _ (gaussianBin_possible L b e hs)) hmax hm hm₁

/-- The local hypotheses of the count coupling, only at steps strictly before ℓ. -/
def ValidSchedule (ℓ : ℕ) (rate θ A : ℕ → ℝ≥0) (m : ℕ → ℕ) : Prop :=
  ∀ j < ℓ, 0 < rate j ∧ 0 < θ j ∧ 0 < A j ∧
      (∀ c, rate j * (gaussianLabels L b e (stepWidth_pos hs j) c).toNNReal ≤ A j) ∧
      m j = ⌊(A j:ℝ)/(4*θ j)-1/2⌋₊ ∧ 1 ≤ m j ∧
      rate (j+1) = nextRate (rate j) (gaussianLabels L b e (stepWidth_pos hs j)) (θ j) (A j)

/-- History induction for an arbitrary starting count law and its input coupling error. -/
theorem gaussian_history_from (ℓ : ℕ) (rate θ A : ℕ → ℝ≥0) (m : ℕ → ℕ)
    (hparams : ValidSchedule L b e hs ℓ rate θ A m) (actual : ℕ → PMF (Multiset (Fin r)))
    (δ : ℝ≥0∞) (h₀ : Dominated (poissonList (rate 0) (gaussianLabels L b e hs)) (actual 0) δ)
    (hstep : ∀ j < ℓ, actual (j+1) = (actual j).bind (procedureStep L b e hs j)) :
    Dominated (poissonList (rate ℓ) (discreteGaussian L (stepWidth s ℓ) (stepWidth_pos hs ℓ) 0))
      ((actual ℓ).bind (mark (gaussianBin L b e (stepWidth_pos hs ℓ))))
      (δ + ∑ j ∈ Finset.range ℓ, stepError (rate j) (rate (j+1)) (θ j) (m j)) := by
  let q j := gaussianLabels L b e (stepWidth_pos hs j)
  let err j := stepError (rate j) (rate (j+1)) (θ j) (m j)
  have hlocal (j) (hj : j < ℓ) : Dominated (poissonList (rate (j+1)) (q (j+1)))
      ((poissonList (rate j) (q j)).bind (procedureStep L b e hs j)) (err j) := by
    obtain ⟨hr,hθ,hA,hmax,hm,hm₁,hrate⟩ := hparams j hj
    let M := fun c ↦ (binAverage L b e (stepWidth_pos hs j) c).map (binLabel L b e)
    have hM : (squaredLabels (q j)).bind M = q (j+1) := by
      change ((squaredLabels (q j)).bind fun c ↦ (binAverage L b e _ c).map _) = _
      rw [← PMF.map_bind, squaredLabels_binAverage]
      rfl
    obtain ⟨_, _, _, _, hmaximal⟩ := poisson_selected_marks (rate j) (θ j) (A j) (q j) M hr hθ hA
      (labelMass_ne_zero _ _ (gaussianBin_possible L b e (stepWidth_pos hs j))) hmax hm hm₁
    change rate (j+1) = nextRate (rate j) (q j) (θ j) (A j) at hrate
    simp only [hM, ← hrate] at hmaximal
    exact hmaximal
  have H := history_domination (fun j ↦ poissonList (rate j) (q j)) actual
    (procedureStep L b e hs) err δ ℓ h₀ hlocal hstep (fun j ↦ maximalMarks_mono _)
  have h := H.bind (mark (gaussianBin L b e (stepWidth_pos hs ℓ))) (mark_submultiset_coupling _)
  simpa only [poissonList_bind_mark, q, gaussianLabels_bind, err] using h

/-- Unconditional exact Poisson marginal after any finite number of combiner steps.
The input-size overflow and the individual step errors are charged once each. -/
theorem procedure_history (n ℓ : ℕ) (rate θ A : ℕ → ℝ≥0) (m : ℕ → ℕ)
    (hparams : ValidSchedule L b e hs ℓ rate θ A m) :
    Dominated (poissonList (rate ℓ) (discreteGaussian L (stepWidth s ℓ) (stepWidth_pos hs ℓ) 0))
      (procedureValues L b e hs n ℓ) (poissonMeasure (rate 0) {t | n < t} +
        ∑ j ∈ Finset.range ℓ, stepError (rate j) (rate (j+1)) (θ j) (m j)) := by
  exact gaussian_history_from L b e hs ℓ rate θ A m hparams (procedureLabels L b e hs n)
    _ (poisson_initial_domination (rate 0) _ n) (fun _ _ ↦ rfl)

end SigabaNeo.Wall1.ADRS

#print axioms SigabaNeo.Wall1.ADRS.gaussian_selected_step
#print axioms SigabaNeo.Wall1.ADRS.procedureStep_values
#print axioms SigabaNeo.Wall1.ADRS.procedure_history
