module

public import SigabaNeo.Lib.Lattices.Research.Wall1.AdrsPoissonLists
public import SigabaNeo.Lib.Lattices.Research.Wall1.AdrsPairing
import Mathlib.Tactic

/-! # Independent marking of Poisson bins and the phantom-pair coupling -/

@[expose] public section

noncomputable section

namespace SigabaNeo.Wall1.ADRS

open ProbabilityTheory MeasureTheory Cslib.Probability.PMF
open scoped ENNReal NNReal

variable {C V W : Type*} {r n : ℕ}

def drawCons (M : C → PMF V) (c : C) (p : PMF (Multiset V)) :=
  (M c).bind fun w ↦ p.map (w ::ₘ ·)

instance (M : C → PMF V) : LeftCommutative (drawCons M) where
  left_comm a b p := by
    simp only [drawCons, PMF.map_bind, PMF.map_comp, Function.comp_def]
    rw [PMF.bind_comm]
    simp only [Multiset.cons_swap]

/-- Each occurrence of a label receives an independent mark from its own kernel. -/
def mark (M : C → PMF V) (labels : Multiset C) : PMF (Multiset V) :=
  labels.foldr (drawCons M) (PMF.pure 0)

@[simp] theorem mark_cons (M : C → PMF V) (c : C) (s : Multiset C) :
    mark M (c ::ₘ s) = (M c).bind fun w ↦ (mark M s).map (w ::ₘ ·) :=
  Multiset.foldr_cons _ _ _ _

theorem mark_add (M : C → PMF V) (s t : Multiset C) :
    mark M (s + t) = (mark M s).bind fun u ↦ (mark M t).map (u + ·) := by
  induction s using Multiset.induction with
  | empty => simp [mark]; exact (PMF.map_id _).symm
  | cons a s ih =>
    simp only [Multiset.cons_add, mark_cons, ih, PMF.bind_bind, PMF.map_bind,
      PMF.bind_map, PMF.map_comp, Function.comp_def]

/-- Relabeling after an independent marking composes the two mark kernels. -/
theorem mark_map (M : C → PMF V) (f : V → W) (s : Multiset C) :
    (mark M s).map (Multiset.map f) = mark (fun c ↦ (M c).map f) s := by
  induction s using Multiset.induction with
  | empty => simp [mark]
  | cons c s ih =>
    simp only [mark_cons, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def,
      Multiset.map_cons, ← ih]

/-- The bag of all tuple coordinates. -/
def tupleBag (x : Fin n → V) : Multiset V := Finset.univ.val.map x

theorem tupleBag_eq (x : Fin n → V) : tupleBag x = ∑ i, {x i} := by
  rw [Finset.sum_eq_multiset_sum]
  simpa only [tupleBag, Multiset.map_map, Function.comp_def] using
    (Multiset.sum_map_singleton (Finset.univ.val.map x)).symm

private theorem tupleBag_cons (w : V) (x : Fin n → V) :
    tupleBag (Fin.cons w x) = w ::ₘ tupleBag x := by
  simp only [tupleBag_eq, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Multiset.singleton_add]

/-- Reconstruct the bag of input labels from the bin counts. -/
def countsBag [Fintype C] (k : C → ℕ) : Multiset C := ∑ c, Multiset.replicate (k c) c

@[simp] theorem count_countsBag [Fintype C] [DecidableEq C] (k : C → ℕ) (c : C) :
    (countsBag k).count c = k c := by
  simp [countsBag, Multiset.count_sum', Multiset.count_replicate]

theorem countsBag_binCounts [Fintype C] [DecidableEq C] (x : Fin n → C) :
    countsBag (binCounts x) = tupleBag x := by
  ext c
  simp [tupleBag_eq, binCounts, Pi.single_apply, Finset.sum_apply, Multiset.count_sum',
    Multiset.count_singleton]

/-- Marking a tuple of known labels gives the unordered independent product of the marks. -/
theorem mark_tupleBag (M : C → PMF V) (x : Fin n → C) :
    mark M (tupleBag x) = (piFin fun i ↦ M (x i)).map tupleBag := by
  induction n with
  | zero => simp [tupleBag_eq, piFin, mark]
  | succ n ih =>
    conv_lhs => rw [← Fin.cons_self_tail x, tupleBag_cons, mark_cons, ih]
    simp only [piFin, PMF.map_bind, PMF.map_comp, Function.comp_def, tupleBag_cons, Fin.tail]

/-- Superposition of independently Poissonized bins with iid marks in each bin. -/
theorem poisson_marked_bins (rate : ℝ≥0) (q : PMF (Fin r)) (M : Fin r → PMF V) :
    (piFin fun c ↦ (poissonMeasure (rate * (q c).toNNReal)).toPMF).bind
      (fun k ↦ mark M (countsBag k)) = poissonList rate (q.bind M) := by
  rw [← poisson_split_bins rate q, PMF.bind_bind]
  unfold poissonList
  congr 1
  funext n
  rw [PMF.bind_map]
  simp only [Function.comp_def, countsBag_binCounts, mark_tupleBag]
  rw [← PMF.map_bind, ← piFin_const, piFin_bind, piFin_const]
  rfl

/-- Given bin counts, share all common marks and draw independent phantom marks for
the excess. In particular containment holds on every ordered input. -/
theorem mark_submultiset_coupling (M : C → PMF V) (s t : Multiset C) :
    ∃ J : PMF (Multiset V × Multiset V), J.map Prod.fst = mark M s ∧
      J.map Prod.snd = mark M t ∧ (s ≤ t → ∀ z ∈ J.support, z.1 ≤ z.2) := by
  classical
  by_cases h : s ≤ t
  · obtain ⟨u, rfl⟩ := exists_add_of_le h
    let J := (mark M s).bind fun v ↦ (mark M u).map fun w ↦ (v, v+w)
    refine ⟨J, ?_, ?_, fun _ z hz ↦ ?_⟩
    · simp only [J, PMF.map_bind, PMF.map_comp, Function.comp_def]
      change (mark M s).bind (fun v ↦ (mark M u).map (Function.const _ v)) = _
      simp
    · rw [mark_add]
      simp only [J, PMF.map_bind, PMF.map_comp, Function.comp_def]
    · obtain ⟨v, _, hv⟩ := (PMF.mem_support_bind_iff ..).mp hz
      obtain ⟨w, _, rfl⟩ := (PMF.mem_support_map_iff ..).mp hv
      exact le_add_of_nonneg_right zero_le
  · refine ⟨(mark M s).bind fun v ↦ (mark M t).map (v, ·), map_fst_bind_pair .., ?_, by simp [h]⟩
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_const]
    exact PMF.map_id _

end SigabaNeo.Wall1.ADRS

#print axioms SigabaNeo.Wall1.ADRS.poisson_marked_bins
#print axioms SigabaNeo.Wall1.ADRS.mark_submultiset_coupling
