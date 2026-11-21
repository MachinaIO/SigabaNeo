import SigabaNeo.Lib.Machines.AlmostConst
import SigabaNeo.Trusted.Primitive
import SigabaNeo.Lib.Lattices.BitLaw
import Mathlib.Data.Set.Finite.List

/-!
# Algorithms on finitely many valid inputs

A randomized algorithm whose valid inputs form a finite set `A` (encoded as tuples of words by an
injective `encA`), and whose output law on each valid input is an image of `m` fair coins, has a
machine that realizes these laws exactly on the valid inputs (`Machine.exists_finiteAlg`): its
output word is the tuple of the outputs. The deterministic case is
`Machine.exists_finiteAlg_det`.
-/

namespace SigabaNeo

open Lattices Cslib

/-- **Machines of algorithms on finitely many valid inputs**, with the answer `encodeTuple []` on
every other tuple. -/
theorem Machine.exists_finiteAlg' {A : Type} [Finite A] (encA : A → List (List Bool))
    (hinj : Function.Injective encA) (m : ℕ) (g : A → List Bool → List (List Bool)) :
    ∃ M : Machine, (∀ a, M.run (encodeTuple (encA a)) =
      (BitString.uniformList m).map fun w => encodeTuple (g a w)) ∧
      ∀ xs, (¬ ∃ a, encA a = xs) → M.run (encodeTuple xs) = PMF.pure (encodeTuple []) := by
  classical
  let encIn : List (List Bool) ↪ List Bool := ⟨encodeTuple, encodeTuple_injective⟩
  let encOut : List (List Bool) ↪ List Bool := ⟨encodeTuple, encodeTuple_injective⟩
  let G : List (List Bool) × List Bool → List (List Bool) := fun xw =>
    if h : (∃ a, encA a = xw.1) ∧ xw.2.length = m then g h.1.choose xw.2 else []
  have hG : ∃ b, {xw | G xw ≠ b}.Finite := by
    refine ⟨[], Set.Finite.subset ((Set.finite_range encA).prod
      (List.finite_length_eq Bool m)) fun xw hxw => ?_⟩
    by_contra hn
    apply hxw
    simp only [Set.mem_prod, Set.mem_range, Set.mem_setOf_eq, not_and_or] at hn
    simp only [G]
    rw [dif_neg]
    rintro ⟨⟨a, ha⟩, hl⟩
    rcases hn with h | h
    · exact h ⟨a, ha⟩
    · exact h hl
  have hL : ∃ L, ∀ a, (encodeTuple (encA a)).length ≤ L := by
    have := Fintype.ofFinite A
    exact ⟨Finset.univ.sup fun a => (encodeTuple (encA a)).length,
      fun a => Finset.le_sup (f := fun a => (encodeTuple (encA a)).length) (Finset.mem_univ a)⟩
  obtain ⟨L, hL⟩ := hL
  obtain ⟨M, hM⟩ := Machine.exists_randomized_of_almostConst (encIn := encIn) (encOut := encOut)
    hG L m []
  refine ⟨M, fun a => ?_, fun xs hxs => ?_⟩
  · have h := hM (encA a)
    rw [if_pos (show (encIn (encA a)).length ≤ L from hL a)] at h
    refine h.trans ?_
    apply PMF.map_congr_support
    intro w hw
    have hwl := BitString.length_of_mem_support_uniformList hw
    have hex : (∃ a', encA a' = encA a) ∧ w.length = m := ⟨⟨a, rfl⟩, hwl⟩
    simp only [G, dif_pos hex]
    rw [hinj hex.1.choose_spec]
    rfl
  · have h := hM xs
    refine h.trans ?_
    split_ifs
    · have : (fun w => encOut (G (xs, w))) = fun _ => encOut [] := funext fun w => by
        simp only [G]
        rw [dif_neg (fun h => hxs h.1)]
      rw [this]
      exact PMF.map_const _ _
    · rfl

/-- **Machines of algorithms on finitely many valid inputs.** -/
theorem Machine.exists_finiteAlg {A : Type} [Finite A] (encA : A → List (List Bool))
    (hinj : Function.Injective encA) (m : ℕ) (g : A → List Bool → List (List Bool)) :
    ∃ M : Machine, ∀ a, M.run (encodeTuple (encA a)) =
      (BitString.uniformList m).map fun w => encodeTuple (g a w) :=
  let ⟨M, h, _⟩ := Machine.exists_finiteAlg' encA hinj m g
  ⟨M, h⟩

/-- **Deterministic algorithms on finitely many valid inputs**, with the answer
`encodeTuple []` on every other tuple. -/
theorem Machine.exists_finiteAlg_det' {A : Type} [Finite A] (encA : A → List (List Bool))
    (hinj : Function.Injective encA) (f : A → List Bool) :
    ∃ M : Machine, M.Deterministic ∧
      (∀ a, M.run (encodeTuple (encA a)) = PMF.pure (encodeTuple [f a])) ∧
      ∀ xs, (¬ ∃ a, encA a = xs) → M.run (encodeTuple xs) = PMF.pure (encodeTuple []) := by
  classical
  let F : List (List Bool) → List (List Bool) := fun xs =>
    if h : ∃ a, encA a = xs then [f h.choose] else []
  have hF : ∃ b, {xs | F xs ≠ b}.Finite := by
    refine ⟨[], Set.Finite.subset (Set.finite_range encA) fun xs hxs => ?_⟩
    by_contra hn
    apply hxs
    simp only [F]
    rw [dif_neg]
    rintro ⟨a, ha⟩
    exact hn ⟨a, ha⟩
  obtain ⟨M, hdet, hM⟩ := Machine.exists_of_almostConst (encIn := ⟨encodeTuple, encodeTuple_injective⟩)
    (encOut := ⟨encodeTuple, encodeTuple_injective⟩) hF
  refine ⟨M, hdet, fun a => ?_, fun xs hxs => ?_⟩
  · have h := hM (encA a)
    have hex : ∃ a', encA a' = encA a := ⟨a, rfl⟩
    refine h.trans ?_
    show PMF.pure (encodeTuple (F (encA a))) = _
    simp only [F, dif_pos hex]
    rw [hinj hex.choose_spec]
  · refine (hM xs).trans ?_
    show PMF.pure (encodeTuple (F xs)) = _
    simp only [F, dif_neg hxs]

/-- **Deterministic algorithms on finitely many valid inputs.** -/
theorem Machine.exists_finiteAlg_det {A : Type} [Finite A] (encA : A → List (List Bool))
    (hinj : Function.Injective encA) (f : A → List Bool) :
    ∃ M : Machine, M.Deterministic ∧ ∀ a, M.run (encodeTuple (encA a)) = PMF.pure (encodeTuple [f a]) :=
  let ⟨M, hdet, h, _⟩ := Machine.exists_finiteAlg_det' encA hinj f
  ⟨M, hdet, h⟩

end SigabaNeo
