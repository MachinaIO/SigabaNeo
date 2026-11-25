import SigabaNeoStd.Lattices.RingLWEInst
import CslibFrontier.Probability.BitString

/-!
# Samples from fair coins

Every law the dual-use scheme draws is the image of uniform bits under an explicit map, so a
machine with fair coins realizes it exactly:

* `bitsToZMod`: `K` bits as a residue mod `2^K` (`uniform_bitsToZMod`: uniform).
-/

namespace SigabaNeo.Lattices

open Cslib Cslib.Probability

theorem finEquiv_eq_cast : ∀ (n : ℕ) [NeZero n] (x : Fin n), ZMod.finEquiv n x = ((x : ℕ) : ZMod n)
  | 0, h, _ => (h.ne _ rfl).elim
  | m + 1, _, x => by
    show x = ((x : ℕ) : ZMod (m + 1))
    exact (Fin.cast_val_eq_self x).symm

/-- `K` bits, least significant first, as a residue mod `2^K`. -/
def bitsToZMod (K : ℕ) (b : Fin K → Bool) : ZMod (2 ^ K) :=
  ((finFunctionFinEquiv (fun i => if b i then (1 : Fin 2) else 0) : Fin (2 ^ K)) : ℕ)

/-- **Uniform bits give a uniform residue mod `2^K`.** -/
theorem uniform_bitsToZMod (K : ℕ) :
    (PMF.uniformOfFintype (Fin K → Bool)).map (bitsToZMod K) =
      PMF.uniformOfFintype (ZMod (2 ^ K)) := by
  have hK : NeZero (2 ^ K) := ⟨by positivity⟩
  let e₁ : (Fin K → Bool) ≃ (Fin K → Fin 2) := Equiv.arrowCongr (Equiv.refl _) finTwoEquiv.symm
  let e₂ : Fin (2 ^ K) ≃ ZMod (2 ^ K) := (ZMod.finEquiv (2 ^ K)).toEquiv
  let e : (Fin K → Bool) ≃ ZMod (2 ^ K) := (e₁.trans finFunctionFinEquiv).trans e₂
  have he : ∀ b, e b = bitsToZMod K b := by
    intro b
    simp only [e, e₁, e₂, Equiv.trans_apply, bitsToZMod, RingEquiv.toEquiv_eq_coe,
      RingEquiv.coe_toEquiv, finEquiv_eq_cast]
    congr 2
    congr 1
    funext i
    simp only [Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.coe_refl, Function.comp_apply, id]
    cases b i <;> decide
  rw [show bitsToZMod K = e from funext fun b => (he b).symm]
  exact Cslib.Probability.PMF.uniformOfFintype_map_equiv e

end SigabaNeo.Lattices
