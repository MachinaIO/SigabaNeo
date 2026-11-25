import CslibFrontier.Probability.BitString
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Cslib.Probability.PMF

/-!
# Uniform laws from fair coins

**`map_uniformList_eq_uniformOfFinset`**: a function of `n` fair coins that is injective on the
words of `n` bits and maps them onto `S` has the uniform law on `S`. (A machine decoding the coins
of a key try in its own order samples the big box uniformly.)
-/

namespace SigabaNeo.Lattices

open Cslib Cslib.BitString Cslib.Probability
open scoped ENNReal

theorem map_uniformList_eq_uniformOfFinset {β : Type*} [DecidableEq β] (n : ℕ)
    (f : List Bool → β) (S : Finset β) (hS : S.Nonempty)
    (hinj : Function.Injective fun r : Fin n → Bool => f (List.ofFn r))
    (himg : Finset.univ.image (fun r : Fin n → Bool => f (List.ofFn r)) = S) :
    (uniformList n).map f = PMF.uniformOfFinset S hS := by
  have hcard : S.card = 2 ^ n := by
    rw [← himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
  ext b
  rw [uniformList_map_apply, PMF.uniformOfFinset_apply]
  by_cases hb : b ∈ S
  · rw [if_pos hb, hcard]
    rw [← himg, Finset.mem_image] at hb
    obtain ⟨r, -, hr⟩ := hb
    have h1 : (Finset.univ.filter fun r' : Fin n → Bool => f (List.ofFn r') = b) = {r} := by
      ext r'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; exact hinj (h.trans hr.symm)
      · rintro rfl; exact hr
    rw [h1, Finset.card_singleton]
    push_cast
    rw [one_div]
  · rw [if_neg hb]
    have h0 : (Finset.univ.filter fun r' : Fin n → Bool => f (List.ofFn r') = b) = ∅ := by
      ext r'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro h
      exact hb (himg ▸ Finset.mem_image.mpr ⟨r', Finset.mem_univ _, h⟩)
    rw [h0, Finset.card_empty]
    simp

end SigabaNeo.Lattices
