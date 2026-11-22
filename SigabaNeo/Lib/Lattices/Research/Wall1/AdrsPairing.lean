module

public import CslibFrontier.Probability.IID
public import CslibFrontier.Probability.PMF.Map
public import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic

/-! # Value-oblivious pairing and sub-multiset domination (Part 140, Lemma 4.5)

Conditional on the labels, N c is the number of positions carrying c. A layout orders all
positions within their own fibers. Consecutive positions form pairs, leaving the last one
unused for an odd count. Layouts and selected pairs can depend on a separate random coin.
-/

@[expose] public section

noncomputable section

namespace SigabaNeo.Wall1.ADRS

open Cslib.Probability.PMF

variable {C V W H : Type*} [Fintype C] {n : ℕ}

/-- A layout assigns every per-label position to a distinct position in the whole list. -/
abbrev Layout (N : C → ℕ) := (Σ c, Fin (N c)) ≃ Fin n

/-- A pair slot records the input label and the pair's position within that bin. -/
abbrev PairSlot (N : C → ℕ) := Σ c, Fin (N c / 2)

/-- Multiset of outputs of the given pair slots, preserving repetitions of equal values. -/
def pairOutputs {N : C → ℕ} (layout : Layout (n := n) N) (avg : V → V → W)
    (pairs : Multiset (PairSlot N)) (x : Fin n → V) : Multiset W :=
  pairs.map fun ⟨c, j⟩ ↦ avg (x (layout ⟨c, ⟨2*j.val, by have := j.isLt; omega⟩⟩))
    (x (layout ⟨c, ⟨2*j.val+1, by have := j.isLt; omega⟩⟩))

/-- Any ordered selection of disjoint pairs in one bin can occupy the first k pair slots
of a maximal pairing. The embedding enumerates the 2k distinct selected endpoints. -/
theorem extend_selected_pairs {k N : ℕ} (hk : 2*k ≤ N) (selected : Fin (2*k) ↪ Fin N) :
    ∃ order : Equiv.Perm (Fin N), ∀ i : Fin (2*k), order (Fin.castLE hk i) = selected i :=
  Equiv.Perm.exists_extending_pair _ _ (Fin.castLE_injective hk) selected.injective

omit [Fintype C] in
private theorem permute_product (label : Fin n → C) (μ : C → PMF V)
    (e : Equiv.Perm (Fin n)) (he : ∀ i, label (e i) = label i) :
    (piFin (μ ∘ label)).map (fun x ↦ x ∘ e) = piFin (μ ∘ label) := by
  let E : Equiv.Perm (Fin n → V) := e.symm.arrowCongr (Equiv.refl V)
  change (piFin (μ ∘ label)).map E = _
  ext x
  rw [map_equiv_apply, piFin_apply, piFin_apply]
  change (∏ i, μ (label i) (x (e.symm i))) = ∏ i, μ (label i) (x i)
  rw [← Equiv.prod_comp e (fun i ↦ μ (label i) (x (e.symm i)))]
  simp [he]

omit [Fintype C] in
/-- Given the input labels, every maximal value-oblivious pairing has the same transition law.
The equality also holds for any fixed sub-multiset of the canonical pair slots. -/
theorem pairing_law_eq {N : C → ℕ} (label : Fin n → C) (μ : C → PMF V)
    (A B : Layout (n := n) N) (hA : ∀ i, label (A i) = i.1) (hB : ∀ i, label (B i) = i.1)
    (avg : V → V → W) (pairs : Multiset (PairSlot N)) :
    (piFin (μ ∘ label)).map (pairOutputs A avg pairs) =
      (piFin (μ ∘ label)).map (pairOutputs B avg pairs) := by
  let e := B.symm.trans A
  have he (i) : label (e i) = label i := by
    simpa [e] using (hA (B.symm i)).trans (hB (B.symm i)).symm
  conv_rhs => rw [← permute_product label μ e he]
  rw [PMF.map_comp]
  congr 1
  funext x
  simp [pairOutputs, Function.comp_def, e]

/-- The joint law couples a coin-selected list to the canonical maximal output. The
containment holds at every point in its support. Input values may have infinite support. -/
theorem pairing_coupling {N : C → ℕ} (label : Fin n → C) (μ : C → PMF V)
    (canonical : Layout (n := n) N) (hc : ∀ i, label (canonical i) = i.1)
    (coin : PMF H) (layout : H → Layout (n := n) N) (hl : ∀ h i, label (layout h i) = i.1)
    (avg : V → V → W) (selected : H → Finset (PairSlot N)) :
    ∃ J : PMF (Multiset W × Multiset W),
      J.map Prod.fst = coin.bind (fun h ↦ (piFin (μ ∘ label)).map
        (pairOutputs (layout h) avg (selected h).val)) ∧
      J.map Prod.snd = (piFin (μ ∘ label)).map (pairOutputs canonical avg Finset.univ.val) ∧
      ∀ z ∈ J.support, z.1 ≤ z.2 := by
  classical
  let D := piFin (μ ∘ label)
  let f h (x : Fin n → V) := (pairOutputs (layout h) avg (selected h).val x,
    pairOutputs (layout h) avg Finset.univ.val x)
  refine ⟨coin.bind (fun h ↦ D.map (f h)), ?_, ?_, ?_⟩
  · simp only [PMF.map_bind, PMF.map_comp]; rfl
  · rw [PMF.map_bind]
    change (coin.bind fun h ↦ (D.map (f h)).map Prod.snd) = _
    have he (h) : (D.map (f h)).map Prod.snd = D.map (pairOutputs canonical avg Finset.univ.val) := by
      rw [PMF.map_comp]
      exact pairing_law_eq label μ (layout h) canonical (hl h) hc avg _
    simp only [he, PMF.bind_const]
    rfl
  · intro z hz
    obtain ⟨h, _, hz⟩ := (PMF.mem_support_bind_iff _ _ _).1 hz
    obtain ⟨x, _, rfl⟩ := (PMF.mem_support_map_iff ..).1 hz
    exact Multiset.map_le_map (show (selected h).val ≤ Finset.univ.val from
      Finset.val_le_iff.mpr (Finset.subset_univ _))

/-- Outputs of an arbitrary partial pairing. Each embedding enumerates its distinct endpoints
in pairs, in the positions of the corresponding label in the original layout. -/
def selectedOutputs {N k : C → ℕ} (A : Layout (n := n) N)
    (sel : ∀ c, Fin (2*k c) ↪ Fin (N c)) (avg : V → V → W) (x : Fin n → V) : Multiset W :=
  (Finset.univ : Finset (Σ c, Fin (k c))).val.map fun ⟨c,j⟩ ↦ avg
    (x (A ⟨c, sel c ⟨2*j.val, by have := j.isLt; omega⟩⟩))
    (x (A ⟨c, sel c ⟨2*j.val+1, by have := j.isLt; omega⟩⟩))

/-- Lemma 4.5, one conditional step. Complete the selected disjoint pairs within each bin,
then couple their output to the canonical maximal pairing with the correct marginals. -/
theorem selected_pairing_coupling {N : C → ℕ} (label : Fin n → C) (μ : C → PMF V)
    (A : Layout (n := n) N) (hA : ∀ i, label (A i) = i.1) (coin : PMF H)
    (k : H → C → ℕ) (hk : ∀ h c, 2*k h c ≤ N c)
    (sel : ∀ h c, Fin (2*k h c) ↪ Fin (N c)) (avg : V → V → W) :
    ∃ J : PMF (Multiset W × Multiset W),
      J.map Prod.fst = coin.bind (fun h ↦ (piFin (μ ∘ label)).map
        (selectedOutputs A (sel h) avg)) ∧
      J.map Prod.snd = (piFin (μ ∘ label)).map (pairOutputs A avg Finset.univ.val) ∧
      ∀ z ∈ J.support, z.1 ≤ z.2 := by
  classical
  choose order he using fun h c ↦ extend_selected_pairs (hk h c) (sel h c)
  let layout (h) := (Equiv.sigmaCongrRight (order h)).trans A
  have hl (h) (i) : label (layout h i) = i.1 := hA _
  let emb (h) : (Σ c, Fin (k h c)) ↪ PairSlot N :=
    Function.Embedding.sigmaMap (Function.Embedding.refl C) (fun c ↦
      Fin.castLEEmb (show k h c ≤ N c / 2 by have := hk h c; omega))
  let selected (h) := Finset.univ.map (emb h)
  obtain ⟨J,h₁,h₂,h₃⟩ := pairing_coupling label μ A hA coin layout hl avg selected
  refine ⟨J, h₁.trans ?_, h₂, h₃⟩
  congr 1
  funext h
  congr 1
  funext x
  simp only [pairOutputs, selected, Finset.map_val, Multiset.map_map, selectedOutputs]
  congr 1
  funext ⟨c,j⟩
  change avg (x (A ⟨c, order h c _⟩)) (x (A ⟨c, order h c _⟩)) = _
  have h₀ := he h c (⟨2*j.val, by have := j.isLt; omega⟩ : Fin (2*k h c))
  have h₁' := he h c (⟨2*j.val+1, by have := j.isLt; omega⟩ : Fin (2*k h c))
  exact congrArg₂ avg (congrArg (fun t ↦ x (A ⟨c,t⟩)) h₀)
    (congrArg (fun t ↦ x (A ⟨c,t⟩)) h₁')

/-- A sub-multiset coupling orders the probabilities of every upward-closed event. -/
theorem submultiset_event_le (J : PMF (Multiset W × Multiset W))
    (hJ : ∀ z ∈ J.support, z.1 ≤ z.2) (A : Set (Multiset W)) (hA : IsUpperSet A) :
    (J.map Prod.fst).toOuterMeasure A ≤ (J.map Prod.snd).toOuterMeasure A := by
  simp only [PMF.toOuterMeasure_map_apply]
  exact J.toOuterMeasure_mono fun z hz ↦ hA (hJ z hz.2) hz.1

end SigabaNeo.Wall1.ADRS

#print axioms SigabaNeo.Wall1.ADRS.extend_selected_pairs
#print axioms SigabaNeo.Wall1.ADRS.pairing_law_eq
#print axioms SigabaNeo.Wall1.ADRS.pairing_coupling
#print axioms SigabaNeo.Wall1.ADRS.submultiset_event_le
#print axioms SigabaNeo.Wall1.ADRS.selected_pairing_coupling
