module

public import SigabaNeo.Lib.Lattices.Research.Wall1.AdrsMarks
public import CslibFrontier.Probability.Conditioning
import CslibFrontier.Probability.PMF.Event
import Mathlib.Tactic

/-! # Composing approximate sub-multiset couplings across a history -/

@[expose] public section

noncomputable section

namespace SigabaNeo.Wall1.ADRS

open Cslib.Probability.PMF MeasureTheory
open scoped ENNReal NNReal

variable {V W : Type*}

/-- An unconditional ideal marginal coupled below a physical marginal with failure at most ε. -/
def Dominated (p q : PMF (Multiset V)) (ε : ℝ≥0∞) : Prop :=
  ∃ J : PMF (Multiset V × Multiset V), J.map Prod.fst = p ∧ J.map Prod.snd = q ∧
    J.toOuterMeasure {z | ¬z.1 ≤ z.2} ≤ ε

theorem Dominated.refl (p : PMF (Multiset V)) : Dominated p p 0 := by
  refine ⟨p.map fun v ↦ (v,v), ?_, ?_, ?_⟩
  · rw [PMF.map_comp]; exact PMF.map_id _
  · rw [PMF.map_comp]; exact PMF.map_id _
  · rw [PMF.toOuterMeasure_map_apply]
    simp

/-- Gluing with the conditional right-coordinate kernel preserves both exact marginals. -/
theorem Dominated.trans {p q r : PMF (Multiset V)} {ε δ : ℝ≥0∞}
    (hpq : Dominated p q ε) (hqr : Dominated q r δ) : Dominated p r (ε+δ) := by
  obtain ⟨J,hp,hq,hJ⟩ := hpq
  obtain ⟨K,hq',hr,hK⟩ := hqr
  let H := J.bind fun z ↦ (conditionalSnd K z.2).map (z, ·)
  let right (u : (Multiset V × Multiset V) × Multiset V) := (u.1.2,u.2)
  let ends (u : (Multiset V × Multiset V) × Multiset V) := (u.1.1,u.2)
  have hleft : H.map Prod.fst = J := map_fst_bind_pair ..
  have hright : H.map right = K := by
    rw [← bind_conditionalSnd K, hq', ← hq, PMF.bind_map]
    simp only [H, right, PMF.map_bind, PMF.map_comp, Function.comp_def]
  refine ⟨H.map ends, ?_, ?_, ?_⟩
  · rw [← hp, ← hleft, PMF.map_comp, PMF.map_comp]; rfl
  · rw [← hr, ← hright, PMF.map_comp, PMF.map_comp]; rfl
  · let bad : Set (Multiset V × Multiset V) := {z | ¬z.1 ≤ z.2}
    rw [PMF.toOuterMeasure_map_apply]
    calc _ ≤ H.toOuterMeasure (Prod.fst ⁻¹' bad ∪ right ⁻¹' bad) := by
           apply H.toOuterMeasure.mono
           intro u hu
           by_cases h₁ : u.1.1 ≤ u.1.2
           · exact Or.inr (fun h₂ ↦ hu (h₁.trans h₂))
           · exact Or.inl h₁
         _ ≤ _ := measure_union_le _ _
         _ ≤ ε + δ := by
           rw [← PMF.toOuterMeasure_map_apply, ← PMF.toOuterMeasure_map_apply, hleft, hright]
           exact add_le_add hJ hK

/-- A value-oblivious kernel that can share marks on ordered input bags transports a
previous failure bound. Its marginals must be correct also after a failure. -/
theorem Dominated.bind {p q : PMF (Multiset V)} {ε : ℝ≥0∞}
    (h : Dominated p q ε) (F : Multiset V → PMF (Multiset W))
    (hF : ∀ s t, ∃ J : PMF (Multiset W × Multiset W),
      J.map Prod.fst = F s ∧ J.map Prod.snd = F t ∧
      (s ≤ t → ∀ z ∈ J.support, z.1 ≤ z.2)) :
    Dominated (p.bind F) (q.bind F) ε := by
  obtain ⟨J,hp,hq,hJ⟩ := h
  choose K h₁ h₂ horder using hF
  let G (z : Multiset V × Multiset V) := K z.1 z.2
  refine ⟨J.bind G, ?_, ?_, ?_⟩
  · simp only [G, PMF.map_bind, h₁, ← hp, PMF.bind_map, Function.comp_def]
  · simp only [G, PMF.map_bind, h₂, ← hq, PMF.bind_map, Function.comp_def]
  · apply le_trans (toOuterMeasure_bind_le_add J G {z | ¬ z.1 ≤ z.2} _ 0 ?_)
    · simpa using hJ
    · intro z _ hz
      rw [le_zero_iff, PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
      exact fun v hv hb ↦ hb (horder _ _ (by simpa using hz) v hv)

/-- Induct on the history using an unconditional ideal one-step law. The per-step
error is measured under the ideal marginal and can depend on its random counts. -/
theorem history_domination (ideal actual : ℕ → PMF (Multiset V))
    (step : ℕ → Multiset V → PMF (Multiset V)) (ε : ℕ → ℝ≥0∞) (δ : ℝ≥0∞) (ℓ : ℕ)
    (h₀ : Dominated (ideal 0) (actual 0) δ)
    (hstep : ∀ j < ℓ, Dominated (ideal (j+1)) ((ideal j).bind (step j)) (ε j))
    (hactual : ∀ j < ℓ, actual (j+1) = (actual j).bind (step j))
    (hmono : ∀ j s t, ∃ J : PMF (Multiset V × Multiset V),
      J.map Prod.fst = step j s ∧ J.map Prod.snd = step j t ∧
      (s ≤ t → ∀ z ∈ J.support, z.1 ≤ z.2)) :
    Dominated (ideal ℓ) (actual ℓ) (δ + ∑ j ∈ Finset.range ℓ, ε j) := by
  have H (k) (hk : k ≤ ℓ) : Dominated (ideal k) (actual k) (δ + ∑ j ∈ Finset.range k, ε j) := by
    induction k with
    | zero => simpa using h₀
    | succ j ih =>
      rw [hactual j (by omega), Finset.sum_range_succ]
      simpa only [add_comm, add_left_comm, add_assoc] using
        (hstep j (by omega)).trans ((ih (by omega)).bind (step j) (hmono j))
  exact H ℓ le_rfl

/-- A miss by the physical list requires an ideal miss or a coupling failure. -/
theorem Dominated.miss_le {p q : PMF (Multiset V)} {ε : ℝ≥0∞}
    (h : Dominated p q ε) (S : Set V) :
    q.toOuterMeasure {u | ∀ v ∈ u, v ∉ S} ≤ p.toOuterMeasure {u | ∀ v ∈ u, v ∉ S} + ε := by
  obtain ⟨J,hp,hq,hJ⟩ := h
  let miss : Set (Multiset V) := {u | ∀ v ∈ u, v ∉ S}
  change q.toOuterMeasure miss ≤ p.toOuterMeasure miss + ε
  rw [← hq, ← hp, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  calc _ ≤ J.toOuterMeasure (Prod.fst ⁻¹' miss ∪ {z | ¬z.1 ≤ z.2}) := by
         apply J.toOuterMeasure.mono
         intro z hz
         by_cases ho : z.1 ≤ z.2
         · exact Or.inl (fun v hv ↦ hz v (Multiset.mem_of_le ho hv))
         · exact Or.inr ho
       _ ≤ _ := measure_union_le _ _
       _ ≤ _ := add_le_add le_rfl hJ

theorem poisson_dominated_miss {rate : ℝ≥0} {μ : PMF V} {q : PMF (Multiset V)} {ε : ℝ≥0∞}
    (h : Dominated (poissonList rate μ) q ε) (S : Set V) :
    q.toOuterMeasure {u | ∀ v ∈ u, v ∉ S} ≤
      ENNReal.ofReal (Real.exp (-(rate : ℝ) * (μ.toOuterMeasure S).toReal)) + ε := by
  simpa only [poissonList_miss] using h.miss_le S

end SigabaNeo.Wall1.ADRS

#print axioms SigabaNeo.Wall1.ADRS.history_domination
#print axioms SigabaNeo.Wall1.ADRS.poisson_dominated_miss
