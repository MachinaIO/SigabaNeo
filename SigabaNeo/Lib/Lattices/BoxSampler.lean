import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Cslib.Probability.PMF

/-!
# Preimages by box rejection (one try)

The trapdoor sampler of Lyubashevsky–Wichs ("Simple lattice trapdoor sampling from a broad class of
distributions", PKC 2015) with uniform boxes, as an abstract statement. A public map is
`x = (x₁, z) ↦ F x₁ + F_T z` with `F_T z = F (T z) + G z` for a trapdoor `T`, a gadget map `G` and
a decomposition `dec` with `G (dec y) = y`. To find `x` with `F x₁ + F_T z = u`:

* draw `p` uniform in a big box `Big`; set `z = dec (u − F p)` and `x₁ = p − T z`;
* output `(x₁, z)` if `x₁` lies in a small box `Small`, and nothing otherwise.

If `Small + T z ⊆ Big` for every decomposition `z`, every output `x` in the target set
`{(x₁, z) : x₁ ∈ Small, z a decomposition, F x₁ + F_T z = u}` comes from exactly one `p`, namely
`x₁ + T z` (`boxSample_some`). So the law of the output depends on `F`, `F_T`, `u` and the boxes only,
not on `T` (`boxSample_eq`): two trapdoors with the same public map give the same law.
-/

namespace SigabaNeo.Lattices

open scoped ENNReal
open Cslib.Probability

variable {P Y Z : Type*} [AddCommGroup P] [AddCommGroup Y] [DecidableEq P]

/-- Two laws on `Option α` that agree on every `some x` are equal. -/
theorem PMF.ext_option {α : Type*} {μ ν : PMF (Option α)} (h : ∀ x, μ (some x) = ν (some x)) :
    μ = ν := by
  classical
  ext o
  cases o with
  | some x => exact h x
  | none =>
    have key : ∀ ρ : PMF (Option α), ρ none + ∑' x, ρ (some x) = 1 := by
      intro ρ
      rw [← ρ.tsum_coe, tsum_eq_add_tsum_ite none]
      congr 1
      refine Eq.trans ?_ (Function.Injective.tsum_eq (Option.some_injective α) ?_)
      · simp
      · intro o ho
        cases o with
        | none => simp at ho
        | some x => exact ⟨x, rfl⟩
    have h1 := key μ
    have h2 := key ν
    simp only [h] at h1
    have hfin : (∑' x, ν (some x)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (h2 ▸ le_add_self)
    exact (ENNReal.add_left_inj hfin).mp (h1.trans h2.symm)

/-- One try of box rejection with the trapdoor `T`. -/
noncomputable def boxSample (Big : Finset P) (hBig : Big.Nonempty) (Small : Finset P) (F : P →+ Y)
    (dec : Y → Z) (T : Z → P) (u : Y) : PMF (Option (P × Z)) :=
  (PMF.uniformOfFinset Big hBig).map fun p =>
    if p - T (dec (u - F p)) ∈ Small then some (p - T (dec (u - F p)), dec (u - F p)) else none

/-- The target set: short `x₁`, a decomposition `z`, and `F x₁ + F_T z = u`. -/
def boxTarget (Small : Finset P) (F : P →+ Y) (dec : Y → Z) (FT : Z → Y) (u : Y) (x : P × Z) :
    Prop :=
  x.1 ∈ Small ∧ (∃ y, dec y = x.2) ∧ F x.1 + FT x.2 = u

open Classical in
/-- **Every output in the target set has probability `1 / |Big|`.** -/
theorem boxSample_some (Big : Finset P) (hBig : Big.Nonempty) (Small : Finset P) (F : P →+ Y)
    (G : Z → Y) (dec : Y → Z) (hdec : ∀ y, G (dec y) = y) (T : Z → P) (u : Y)
    (hcover : ∀ x₁ ∈ Small, ∀ y, x₁ + T (dec y) ∈ Big) (x : P × Z) :
    boxSample Big hBig Small F dec T u (some x) =
      if boxTarget Small F dec (fun z => F (T z) + G z) u x then (Big.card : ℝ≥0∞)⁻¹ else 0 := by
  obtain ⟨x₁, z⟩ := x
  unfold boxSample
  rw [PMF.map_apply]
  split_ifs with ht
  · obtain ⟨hs, ⟨y, rfl⟩, hu⟩ := ht
    -- the only proposal is `x₁ + T z`
    have hp : ∀ p, (some (x₁, dec y) = if p - T (dec (u - F p)) ∈ Small then
        some (p - T (dec (u - F p)), dec (u - F p)) else none) ↔ p = x₁ + T (dec y) := by
      intro p
      constructor
      · intro h
        split_ifs at h with h'
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨h1, h2⟩ := h
          rw [h1, ← h2]; abel
      · rintro rfl
        have hz : dec (u - F (x₁ + T (dec y))) = dec y := by
          have : u - F (x₁ + T (dec y)) = G (dec y) := by
            simp only at hu
            rw [map_add, ← hu]; abel
          rw [this, hdec]
        rw [hz, add_sub_cancel_right]; simp [hs]
    rw [tsum_eq_single (x₁ + T (dec y))]
    · simp only [(hp _).mpr rfl, ite_true, PMF.uniformOfFinset_apply, hcover x₁ hs y]
    · intro p hne
      simp only [show ¬ _ from fun h => hne ((hp p).mp h), ite_false]
  · refine tsum_eq_zero_iff.mpr fun p => ?_
    split_ifs with h' heq
    · exfalso
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨h1, h2⟩ := heq
      apply ht
      refine ⟨h1 ▸ h', ⟨_, h2.symm⟩, ?_⟩
      simp only
      rw [h1, h2, map_sub, hdec]
      abel
    all_goals first | rfl | (exfalso; assumption)

open Classical in
/-- **The law does not depend on the trapdoor.** -/
theorem boxSample_eq (Big : Finset P) (hBig : Big.Nonempty) (Small : Finset P) (F : P →+ Y)
    (G : Z → Y) (dec : Y → Z) (hdec : ∀ y, G (dec y) = y) (T T' : Z → P) (u : Y)
    (hcover : ∀ x₁ ∈ Small, ∀ y, x₁ + T (dec y) ∈ Big)
    (hcover' : ∀ x₁ ∈ Small, ∀ y, x₁ + T' (dec y) ∈ Big) (hpub : ∀ z, F (T z) = F (T' z)) :
    boxSample Big hBig Small F dec T u = boxSample Big hBig Small F dec T' u := by
  have hsome : ∀ x, boxSample Big hBig Small F dec T u (some x) =
      boxSample Big hBig Small F dec T' u (some x) := by
    intro x
    rw [boxSample_some Big hBig Small F G dec hdec T u hcover,
      boxSample_some Big hBig Small F G dec hdec T' u hcover']
    have : boxTarget Small F dec (fun z => F (T z) + G z) u x ↔
        boxTarget Small F dec (fun z => F (T' z) + G z) u x := by
      simp only [boxTarget, hpub]
    exact if_congr this rfl rfl
  exact PMF.ext_option hsome

end SigabaNeo.Lattices
