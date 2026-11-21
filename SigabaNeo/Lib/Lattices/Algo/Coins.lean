import SigabaNeo.Lib.Lattices.BitLaw
import SigabaNeo.Lib.Lattices.BoxSampler

/-!
# Box rejection from fair coins

One try of box rejection (`SigabaNeo.Lattices.boxSample`) draws `p` uniform in a big box. When the
box is the image of an embedding of `m` bits, the try is a fixed deterministic function `boxTry` of
exactly `m` fair coins (no loop, no rejection of coins):

* `bitsOf m l`: the coins as a function `Fin m → Bool` (bit `i` is `l[i]`, `false` past the end);
* `uniformOfFinset_map_eq`: the uniform law on `univ.map emb` is the image of `m` uniform bits under
  `emb ∘ bitsOf m` (the explicit form of `BitLaw.uniformOfFinset_map`);
* `boxSample_coins`: `boxSample` is the image of `m` uniform bits under `boxTry ∘ emb ∘ bitsOf m`.
-/

namespace SigabaNeo.Lattices.Algo

open Cslib Cslib.Probability

/-- The coins as a function on bit positions. -/
def bitsOf (m : ℕ) (l : List Bool) : Fin m → Bool := fun i => l.getD i false

theorem bitsOf_ofFn (m : ℕ) (b : Fin m → Bool) : bitsOf m (List.ofFn b) = b := by
  funext i
  simp [bitsOf, List.getD_eq_getElem?_getD]

/-- **The uniform law on the image of `m` bits**, explicitly. -/
theorem uniformOfFinset_map_eq {α : Type*} (m : ℕ) (emb : (Fin m → Bool) ↪ α) :
    PMF.uniformOfFinset (Finset.univ.map emb) (Finset.univ_nonempty.map) =
      (BitString.uniformList m).map (fun l => emb (bitsOf m l)) := by
  classical
  rw [BitString.uniformList, PMF.map_comp]
  ext a
  rw [PMF.uniformOfFinset_apply, PMF.map_apply]
  split_ifs with ha
  · obtain ⟨b, -, rfl⟩ := Finset.mem_map.mp ha
    rw [tsum_eq_single b]
    · simp [Finset.card_map, Fintype.card_bool, bitsOf_ofFn]
    · intro b' hb'
      simp only [Function.comp_apply, bitsOf_ofFn]
      rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hb' (emb.injective h.symm))]
  · refine (tsum_eq_zero_iff.mpr fun b => ?_).symm
    refine ite_eq_right_of_eq_false _ _ (eq_false fun h => ha ?_)
    rw [h]
    exact Finset.mem_map_of_mem _ (Finset.mem_univ _)

variable {P Y Z : Type*} [AddCommGroup P] [AddCommGroup Y] [DecidableEq P]

/-- **One try of box rejection from the box element `p`**: `z = dec (u − F p)`, `x₁ = p − T z`, and
`(x₁, z)` if `x₁` is in the small box. -/
def boxTry (Small : Finset P) (F : P →+ Y) (dec : Y → Z) (T : Z → P) (u : Y) (p : P) :
    Option (P × Z) :=
  if p - T (dec (u - F p)) ∈ Small then some (p - T (dec (u - F p)), dec (u - F p)) else none

/-- **Box rejection is a function of `m` fair coins.** -/
theorem boxSample_coins {m : ℕ} (emb : (Fin m → Bool) ↪ P) (Small : Finset P) (F : P →+ Y)
    (dec : Y → Z) (T : Z → P) (u : Y) :
    boxSample (Finset.univ.map emb) (Finset.univ_nonempty.map) Small F dec T u =
      (BitString.uniformList m).map (fun l => boxTry Small F dec T u (emb (bitsOf m l))) := by
  unfold boxSample
  rw [uniformOfFinset_map_eq, PMF.map_comp]
  rfl

end SigabaNeo.Lattices.Algo
