module

public import SigabaNeo.Lib.Lattices.Research.Wall1.AdrsProcedure
public import Mathlib.Data.Fintype.Sort
import Mathlib.Tactic

/-! # The ordered, stable-bucket version of Procedure E -/

@[expose] public section

noncomputable section

namespace SigabaNeo.Wall1.ADRS

open Cslib.Probability.PMF ProbabilityTheory MeasureTheory ZLattice
open scoped ENNReal NNReal

variable {C V W : Type*} {n r : ℕ}

/-- A finite ordered sample whose length is part of the random outcome. -/
abbrev SampleList (V : Type*) := Σ n : ℕ, Fin n → V

def sampleBag (t : SampleList V) : Multiset V := tupleBag t.2

def drawList (M : C → PMF V) (t : SampleList C) : PMF (SampleList V) :=
  (piFin fun i ↦ M (t.2 i)).map (Sigma.mk t.1)

private theorem drawList_bind (M : C → PMF V) (N : V → PMF W) (t : SampleList C) :
    (drawList M t).bind (drawList N) = drawList (fun c ↦ (M c).bind N) t := by
  rcases t with ⟨n,x⟩
  simp only [drawList, PMF.bind_map, Function.comp_def]
  rw [← PMF.map_bind, piFin_bind]

private theorem drawList_bag (M : C → PMF V) (t : SampleList C) :
    (drawList M t).map sampleBag = mark M (sampleBag t) := by
  rw [drawList, PMF.map_comp, sampleBag, mark_tupleBag]; rfl

/-- The length of one stable bucket. -/
def bucketSize (l : Fin n → Fin r) (c : Fin r) := Fintype.card {i // l i = c}

/-- The j-th position of each label in increasing original position order. -/
def stableLayout (l : Fin n → Fin r) : Layout (n := n) (bucketSize l) :=
  (Equiv.sigmaCongrRight fun c ↦ (monoEquivOfFin {i // l i = c} rfl).toEquiv).trans
    (Equiv.sigmaFiberEquiv l)

theorem stableLayout_label (l : Fin n → Fin r) (i : Σ c, Fin (bucketSize l c)) :
    l (stableLayout l i) = i.1 := ((monoEquivOfFin {j // l j = i.1} rfl) i.2).property

/-- Flatten pair slots in increasing bin order, then increasing position in that bin. -/
def orderedSlots (l : Fin n → Fin r) :
    Fin (∑ c, bucketSize l c / 2) ≃ PairSlot (bucketSize l) := finSigmaFinEquiv.symm

def sourceLabels (t : SampleList (Fin r)) : SampleList (Fin r) :=
  ⟨_, fun i ↦ (orderedSlots t.2 i).1⟩

private theorem sourceLabels_bag (t : SampleList (Fin r)) :
    sampleBag (sourceLabels t) = halfBag (sampleBag t) := by
  classical
  obtain ⟨n,l⟩ := t
  have hc (c) : (tupleBag l).count c = bucketSize l c := by
    rw [tupleBag_eq, Multiset.count_sum']
    simp [Multiset.count_singleton, bucketSize, Fintype.card_subtype, eq_comm]
  change tupleBag (fun i ↦ (orderedSlots l i).1) = countsBag _
  rw [tupleBag_eq, ← (orderedSlots l).symm.sum_comp
    (fun i ↦ ({(orderedSlots l i).1} : Multiset (Fin r)))]
  simp only [Equiv.apply_symm_apply, Fintype.sum_sigma, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Multiset.nsmul_singleton, countsBag, hc, sampleBag]

/-- Pair consecutive elements of each stable bucket, discarding its odd leftover.
The input and output are ordered lists and no random coins are used. -/
def stablePair (label : V → Fin r) (avg : V → V → W) (t : SampleList V) : SampleList W :=
  let l := label ∘ t.2
  ⟨_, orderedAverages (stableLayout l) avg (orderedSlots l) t.2⟩

/-- Exact ordered-list kernel for a fixed history of input labels. -/
theorem stablePair_drawList (label : V → Fin r) (G : Fin r → PMF V)
    (hG : ∀ c v, v ∈ (G c).support → label v = c) (avg : V → V → W) (t : SampleList (Fin r)) :
    (drawList G t).map (stablePair label avg) =
      drawList (fun c ↦ ((G c).bind fun x ↦ (G c).map (x,·)).map (fun z ↦ avg z.1 z.2))
        (sourceLabels t) := by
  obtain ⟨n,l⟩ := t
  let g := orderedAverages (stableLayout l) avg (orderedSlots l)
  have hslots := orderedAverages_law l G (stableLayout l) (stableLayout_label l) avg
    (orderedSlots l) (orderedSlots l).injective
  rw [drawList, PMF.map_comp]
  have hg : (piFin (G ∘ l)).map (stablePair label avg ∘ Sigma.mk n) =
      (piFin (G ∘ l)).map (Sigma.mk _ ∘ g) := by
    apply map_congr_on_support
    intro x hx
    have hprod := (PMF.mem_support_iff ..).mp hx
    rw [piFin_apply, Finset.prod_ne_zero_iff] at hprod
    have hl : label ∘ x = l := funext fun i ↦ hG _ _ ((PMF.mem_support_iff ..).mpr
      (hprod i (Finset.mem_univ _)))
    change stablePair label avg ⟨n,x⟩ = _
    exact congrArg (fun a : Fin n → Fin r ↦ (⟨_, orderedAverages (stableLayout a) avg
      (orderedSlots a) x⟩ : SampleList W)) hl
  change (piFin (G ∘ l)).map (stablePair label avg ∘ Sigma.mk n) = _
  rw [hg, ← PMF.map_comp, show g = _ from rfl, hslots]
  rfl

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
variable (L : Submodule ℤ E) (b : Module.Basis ι ℤ L) (e : (ι → ZMod 2) ≃ Fin r)
variable [FiniteDimensional ℝ E] [DiscreteTopology L] {s : ℝ} (hs : 0 < s)

/-- The physical run, starting with exactly n independent Gaussians and then mapping
the deterministic stable pairing function over the ordered list at each step. -/
def stableRun (n : ℕ) : ℕ → PMF (SampleList L)
  | 0 => (iid (discreteGaussian L s hs 0) n).map (Sigma.mk n)
  | j+1 => (stableRun n j).map (stablePair (binLabel L b e) (latticeMidpoint L))

private def labelRun (n : ℕ) : ℕ → PMF (SampleList (Fin r))
  | 0 => (iid (gaussianLabels L b e hs) n).map (Sigma.mk n)
  | j+1 => (labelRun n j).bind fun t ↦ drawList (fun c ↦
      (binAverage L b e (stepWidth_pos hs j) c).map (binLabel L b e)) (sourceLabels t)

private theorem labelRun_bag (n j : ℕ) :
    (labelRun L b e hs n j).map sampleBag = procedureLabels L b e hs n j := by
  induction j with
  | zero => rw [labelRun, procedureLabels, PMF.map_comp]; rfl
  | succ j ih =>
    rw [labelRun, procedureLabels, ← ih, PMF.bind_map, PMF.map_bind]
    congr 1
    funext t
    rw [drawList_bag, sourceLabels_bag]
    rfl

private theorem stableRun_disintegrate (n j : ℕ) :
    stableRun L b e hs n j = (labelRun L b e hs n j).bind
      (drawList (gaussianBin L b e (stepWidth_pos hs j))) := by
  induction j with
  | zero =>
    rw [stableRun, labelRun, PMF.bind_map]
    simp only [Function.comp_def, drawList, ← PMF.map_bind, ← piFin_const, piFin_bind,
      stepWidth, gaussianLabels_bind]
  | succ j ih =>
    rw [stableRun, ih, PMF.map_bind, labelRun, PMF.bind_bind]
    congr 1
    funext t
    rw [drawList_bind]
    have hres (c) : ((binAverage L b e (stepWidth_pos hs j) c).map (binLabel L b e)).bind
        (gaussianBin L b e (stepWidth_pos hs (j+1))) = binAverage L b e (stepWidth_pos hs j) c :=
      binAverage_resample L b e (stepWidth_pos hs j) c
    simp only [hres]
    apply stablePair_drawList
    intro c v hv
    exact ((PMF.mem_support_filter_iff (gaussianBin_possible L b e _ c)).mp hv).1

/-- The physical output bag agrees exactly with the law used in the history induction. -/
theorem stableRun_bag (n j : ℕ) :
    (stableRun L b e hs n j).map sampleBag = procedureValues L b e hs n j := by
  rw [stableRun_disintegrate, procedureValues, ← labelRun_bag, PMF.bind_map, PMF.map_bind]
  congr 1
  funext t
  exact drawList_bag _ _

/-- For the fixed input size of Procedure E, charge the Poisson input overflow once. -/
theorem stableRun_domination (n ℓ : ℕ) (rate θ A : ℕ → ℝ≥0) (m : ℕ → ℕ)
    (hparams : ValidSchedule L b e hs ℓ rate θ A m) :
    Dominated (poissonList (rate ℓ) (discreteGaussian L (stepWidth s ℓ) (stepWidth_pos hs ℓ) 0))
      ((stableRun L b e hs n ℓ).map sampleBag) (poissonMeasure (rate 0) {t | n < t} +
        ∑ j ∈ Finset.range ℓ, stepError (rate j) (rate (j+1)) (θ j) (m j)) := by
  rw [stableRun_bag]
  exact procedure_history L b e hs n ℓ rate θ A m hparams

/-- With Poissonized input there is no initial overflow charge. The final ideal list
is an exact Poisson marginal and is contained with probability at least 1 − Σ ε_j. -/
theorem stableRun_poisson_coupling (ℓ : ℕ) (rate θ A : ℕ → ℝ≥0) (m : ℕ → ℕ)
    (hparams : ValidSchedule L b e hs ℓ rate θ A m) :
    ∃ J : PMF (Multiset L × Multiset L),
      J.map Prod.fst =
        poissonList (rate ℓ) (discreteGaussian L (stepWidth s ℓ) (stepWidth_pos hs ℓ) 0) ∧
      J.map Prod.snd = (poissonMeasure (rate 0)).toPMF.bind
        (fun n ↦ (stableRun L b e hs n ℓ).map sampleBag) ∧
      1 - ∑ j ∈ Finset.range ℓ, stepError (rate j) (rate (j+1)) (θ j) (m j) ≤
        J.toOuterMeasure {z | z.1 ≤ z.2} := by
  let P := (poissonMeasure (rate 0)).toPMF
  let actual j := P.bind (fun n ↦ procedureLabels L b e hs n j)
  have h₀ : Dominated (poissonList (rate 0) (gaussianLabels L b e hs)) (actual 0) 0 := by
    exact Dominated.refl _
  have hstep (j) (_ : j < ℓ) : actual (j+1) = (actual j).bind (procedureStep L b e hs j) := by
    simp only [actual, procedureLabels, PMF.bind_bind]
  obtain ⟨J,hi,ha,hf⟩ := gaussian_history_from L b e hs ℓ rate θ A m hparams actual 0 h₀ hstep
  refine ⟨J,hi,?_,?_⟩
  · simp only [ha, actual, PMF.bind_bind, stableRun_bag, procedureValues, P]
  · rw [zero_add] at hf
    apply tsub_le_iff_right.mpr
    exact (toOuterMeasure_add_compl_ennreal J {z | z.1 ≤ z.2}).ge.trans
      (add_le_add le_rfl hf)

/-- Final success for any target set, in particular the set of nonzero vectors of minimum norm. -/
theorem stableRun_hit (n ℓ : ℕ) (rate θ A : ℕ → ℝ≥0) (m : ℕ → ℕ)
    (hparams : ValidSchedule L b e hs ℓ rate θ A m)
    (S : Set L) :
    let D := discreteGaussian L (stepWidth s ℓ) (stepWidth_pos hs ℓ) 0
    let ε := poissonMeasure (rate 0) {t | n < t} +
      ∑ j ∈ Finset.range ℓ, stepError (rate j) (rate (j+1)) (θ j) (m j)
    1 - (ENNReal.ofReal (Real.exp (-(rate ℓ : ℝ) * (D.toOuterMeasure S).toReal)) + ε) ≤
      (stableRun L b e hs n ℓ).toOuterMeasure {t | ∃ v ∈ sampleBag t, v ∈ S} := by
  intro D ε
  have h := stableRun_domination L b e hs n ℓ rate θ A m hparams
  have hb := poisson_dominated_miss h S
  rw [PMF.toOuterMeasure_map_apply] at hb
  let hit : Set (SampleList L) := {t | ∃ v ∈ sampleBag t, v ∈ S}
  have hsum := toOuterMeasure_add_compl_ennreal (stableRun L b e hs n ℓ) hit
  have he : hitᶜ = sampleBag ⁻¹' {u : Multiset L | ∀ v ∈ u, v ∉ S} := by ext; simp [hit]
  rw [he] at hsum
  apply tsub_le_iff_right.mpr
  exact hsum.ge.trans (add_le_add le_rfl hb)

end SigabaNeo.Wall1.ADRS

#print axioms SigabaNeo.Wall1.ADRS.stablePair_drawList
#print axioms SigabaNeo.Wall1.ADRS.stableRun_bag
#print axioms SigabaNeo.Wall1.ADRS.stableRun_domination
#print axioms SigabaNeo.Wall1.ADRS.stableRun_poisson_coupling
#print axioms SigabaNeo.Wall1.ADRS.stableRun_hit
