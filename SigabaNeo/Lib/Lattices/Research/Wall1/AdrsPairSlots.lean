module

public import SigabaNeo.Lib.Lattices.Research.Wall1.AdrsSelected
import Mathlib.Tactic

/-! # From physical disjoint pair slots to independent within-bin marks -/

@[expose] public section

noncomputable section

namespace SigabaNeo.Wall1.ADRS

open Cslib.Probability.PMF MeasureTheory
open scoped ENNReal

variable {I C V W : Type*} {n k : ℕ}

/-- Prescribing distinct coordinates of a product has the product of their point masses. -/
private theorem coordinates_prob [Fintype I] (p : Fin n → PMF V) (g : I ↪ Fin n) (y : I → V) :
    (piFin p).toOuterMeasure {x | ∀ j, x (g j) = y j} = ∏ j, p (g j) (y j) := by
  classical
  let A := Function.extend g (fun j ↦ ({y j} : Set V)) (fun _ ↦ Set.univ)
  have hA (j) : A (g j) = {y j} := g.injective.extend_apply _ _ _
  have hB {i} (hi : ¬∃ j, g j = i) : A i = Set.univ := Function.extend_apply' _ _ _ hi
  have he : {x : Fin n → V | ∀ j, x (g j) = y j} = {x | ∀ i, x i ∈ A i} := by
    ext x
    constructor
    · intro h i
      by_cases hi : ∃ j, g j = i
      · obtain ⟨j,rfl⟩ := hi
        simpa only [hA, Set.mem_singleton_iff] using h j
      · simp [hB hi]
    · intro h j
      simpa only [hA, Set.mem_singleton_iff] using h (g j)
  rw [he, toOuterMeasure_piFin_forall]
  calc _ = ∏ i ∈ Finset.univ.map g, (p i).toOuterMeasure (A i) := by
         symm
         apply Finset.prod_subset (Finset.subset_univ _)
         intro i _ hi
         have hi' : ¬∃ j, g j = i := by simpa using hi
         rw [hB hi', PMF.toOuterMeasure_apply, Set.indicator_univ, PMF.tsum_coe]
       _ = _ := by simp [Finset.prod_map, hA, PMF.toOuterMeasure_apply_singleton]

/-- The pairs at distinct endpoint positions are independent even when unused positions remain. -/
private theorem disjoint_pair_law (p : Fin n → PMF V) (g : Fin k ⊕ Fin k ↪ Fin n)
    (q : Fin k → PMF V) (hl : ∀ j, p (g (.inl j)) = q j) (hr : ∀ j, p (g (.inr j)) = q j) :
    (piFin p).map (fun x j ↦ (x (g (.inl j)), x (g (.inr j)))) =
      piFin (fun j ↦ (q j).bind fun u ↦ (q j).map (u,·)) := by
  ext y
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  let f := Sum.elim (fun j ↦ (y j).1) (fun j ↦ (y j).2)
  have hset : (fun x : Fin n → V ↦ fun j ↦ (x (g (.inl j)), x (g (.inr j)))) ⁻¹' {y} =
      {x | ∀ j, x (g j) = f j} := by
    ext x
    change (fun j ↦ (x (g (.inl j)),x (g (.inr j)))) = y ↔ _
    constructor
    · intro h j
      cases j with
      | inl j => exact congrArg Prod.fst (congrFun h j)
      | inr j => exact congrArg Prod.snd (congrFun h j)
    · intro h
      exact funext fun j ↦ Prod.ext (h (.inl j)) (h (.inr j))
  rw [hset, coordinates_prob, Fintype.prod_sum_type, piFin_apply]
  simp only [f, Sum.elim_inl, Sum.elim_inr, hl, hr, bind_map_prodMk_apply, Finset.prod_mul_distrib]

variable {N : C → ℕ}

/-- Apply the supplied distinct pair slots in the indicated order. -/
def orderedAverages (A : Layout (n := n) N) (avg : V → V → W) (j : Fin k → PairSlot N)
    (x : Fin n → V) (i : Fin k) : W :=
  let p := j i
  avg (x (A ⟨p.1, ⟨2*p.2.val, by have := p.2.isLt; omega⟩⟩))
    (x (A ⟨p.1, ⟨2*p.2.val+1, by have := p.2.isLt; omega⟩⟩))

/-- Joint law of the ordered slots, before forgetting the order of their outputs. -/
theorem orderedAverages_law (label : Fin n → C) (μ : C → PMF V)
    (A : Layout (n := n) N) (hA : ∀ i, label (A i) = i.1) (avg : V → V → W)
    (j : Fin k → PairSlot N) (hj : Function.Injective j) :
    (piFin (μ ∘ label)).map (orderedAverages A avg j) =
      piFin (fun i ↦ ((μ (j i).1).bind fun u ↦ (μ (j i).1).map (u,·)).map
        (fun z ↦ avg z.1 z.2)) := by
  let endpoint (p : PairSlot N) (b : ℕ) (hb : b < 2) : Σ c, Fin (N c) :=
    ⟨p.1, ⟨2*p.2.val + b, by have := p.2.isLt; omega⟩⟩
  let g₀ := fun (i : Fin k ⊕ Fin k) ↦
    Sum.elim (fun t ↦ endpoint (j t) 0 (by decide)) (fun t ↦ endpoint (j t) 1 (by decide)) i
  have injEndpoint {p q : PairSlot N} {a b : ℕ} (ha : a < 2) (hb : b < 2)
      (h : endpoint p a ha = endpoint q b hb) : p = q ∧ a = b := by
    rcases p with ⟨c,p⟩
    rcases q with ⟨d,q⟩
    obtain rfl : c = d := congrArg Sigma.fst h
    have he := congrArg (fun t : Σ c, Fin (N c) ↦ t.2.val) h
    change 2*p.val + a = 2*q.val + b at he
    exact ⟨by congr 1; exact Fin.ext (by omega), by omega⟩
  let g : _ ↪ Fin n := ⟨A ∘ g₀, by
    intro u v h
    have hh := A.injective h
    cases u <;> cases v
    · exact congrArg Sum.inl (hj (injEndpoint (a := 0) (b := 0) (by decide) (by decide) hh).1)
    · have := (injEndpoint (a := 0) (b := 1) (by decide) (by decide) hh).2; omega
    · have := (injEndpoint (a := 1) (b := 0) (by decide) (by decide) hh).2; omega
    · exact congrArg Sum.inr (hj (injEndpoint (a := 1) (b := 1) (by decide) (by decide) hh).1)⟩
  let l := fun i ↦ (j i).1
  have hp := disjoint_pair_law (μ ∘ label) g (μ ∘ l)
    (fun i ↦ congrArg μ (hA _)) (fun i ↦ congrArg μ (hA _))
  simp only [Function.comp_def] at hp
  rw [← piFin_map_values, ← hp, PMF.map_comp]
  rfl

/-- The committed slot-based pairing law: every value-oblivious subset of the slots
gives independent bin-average marks, including repeated labels and repeated outputs. -/
theorem pairOutputs_eq_mark (label : Fin n → C) (μ : C → PMF V)
    (A : Layout (n := n) N) (hA : ∀ i, label (A i) = i.1) (avg : V → V → W)
    (slots : Finset (PairSlot N)) :
    (piFin (μ ∘ label)).map (pairOutputs A avg slots.val) =
      mark (fun c ↦ ((μ c).bind fun u ↦ (μ c).map (u,·)).map (fun z ↦ avg z.1 z.2))
        (slots.val.map Sigma.fst) := by
  classical
  let e := (Fintype.equivFin (↥slots)).symm
  let j := fun i ↦ (e i).val
  have hj : Function.Injective j := Subtype.val_injective.comp e.injective
  have hbag : tupleBag j = slots.val := by
    change (Finset.univ.val.map (Subtype.val ∘ e)) = _
    rw [← Multiset.map_map]
    have he : Finset.univ.val.map e = (Finset.univ : Finset (↥slots)).val := by
      exact congrArg Finset.val (Finset.map_univ_equiv e)
    rw [he]
    exact Multiset.attach_map_val _
  have hp := orderedAverages_law label μ A hA avg j hj
  have hlabels : slots.val.map Sigma.fst = tupleBag (fun i ↦ (j i).1) := by
    rw [← hbag]
    exact Multiset.map_map ..
  rw [hlabels, mark_tupleBag, ← hp, PMF.map_comp]
  congr 1
  funext x
  rw [pairOutputs, ← hbag]
  simp only [tupleBag, Multiset.map_map, Function.comp_def]
  rfl

/-- Select the first requested slots in each bucket, clipping at the number of disjoint pairs. -/
def clippedSlots [Fintype C] (N K : C → ℕ) : Finset (PairSlot N) :=
  Finset.univ.map (Function.Embedding.sigmaMap (Function.Embedding.refl C) fun c ↦
    Fin.castLEEmb (min_le_right (K c) (N c / 2)))

/-- The physical clipped selection has exactly the conditional mark law in
`gaussian_selected_step`, for every realization of the counts and the count coins. -/
theorem clipped_pairOutputs_law [Fintype C] (label : Fin n → C) (μ : C → PMF V)
    (A : Layout (n := n) N) (hA : ∀ i, label (A i) = i.1) (avg : V → V → W) (K : C → ℕ) :
    (piFin (μ ∘ label)).map (pairOutputs A avg (clippedSlots N K).val) =
      mark (fun c ↦ ((μ c).bind fun u ↦ (μ c).map (u,·)).map (fun z ↦ avg z.1 z.2))
        (countsBag fun c ↦ min (K c) (N c / 2)) := by
  classical
  rw [pairOutputs_eq_mark label μ A hA]
  congr 1
  simp only [clippedSlots, Finset.map_val, Multiset.map_map]
  change Finset.univ.val.map (fun p : Σ c, Fin (min (K c) (N c / 2)) ↦ p.1) = _
  let f := fun p : Σ c, Fin (min (K c) (N c / 2)) ↦ p.1
  have he : Finset.univ.val.map f = ∑ p, ({f p} : Multiset C) := by
    rw [Finset.sum_eq_multiset_sum]
    simpa only [Multiset.map_map, Function.comp_def] using
      (Multiset.sum_map_singleton (Finset.univ.val.map f)).symm
  rw [he, Fintype.sum_sigma]
  simp [f, countsBag, Multiset.nsmul_singleton]

end SigabaNeo.Wall1.ADRS

#print axioms SigabaNeo.Wall1.ADRS.pairOutputs_eq_mark
#print axioms SigabaNeo.Wall1.ADRS.clipped_pairOutputs_law
