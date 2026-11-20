import SigabaNeo.Lib.Lattices.Trapdoor.Family.Params
import SigabaNeo.Lib.Lattices.Trapdoor
import SigabaNeo.Lib.Lattices.Gaussian.Facts
import SigabaNeo.Lib.Lattices.Gadget
import CslibFrontier.Tactic.PPT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Matrix.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-!
# The proven trapdoor family: the dimensions are computable in polynomial time
-/

namespace SigabaNeo.Lattices.Trapdoor.Family

open Cslib Turing.MultiTapeTM

@[fun_prop] theorem n_tidy : ComputableTidilyInPolyTime n encUnary encUnary := by
  unfold n; fun_prop
@[fun_prop] theorem w_tidy : ComputableTidilyInPolyTime w encUnary encUnary := by
  unfold w; fun_prop
@[fun_prop] theorem m_tidy : ComputableTidilyInPolyTime m encUnary encUnary := by
  unfold m n w; fun_prop
@[fun_prop] theorem k_tidy : ComputableTidilyInPolyTime k encUnary encUnary := by
  unfold k m n w; fun_prop
@[fun_prop] theorem m_plain : ComputableInPolyTime m encUnary encUnary := .of_tidy m_tidy
@[fun_prop] theorem k_plain : ComputableInPolyTime k encUnary encUnary := .of_tidy k_tidy

/-- A sum over `range count` whose body also reads the input. -/
theorem sumRange {γ : Type} {encIn : γ ↪ List Bool} {count : γ → ℕ} {f : γ → ℕ → ℕ}
    (hc : ComputableTidilyInPolyTime count encIn encUnary)
    (hf : ComputableInPolyTime (fun p : γ × ℕ => f p.1 p.2) (encPair encIn encUnary) encNat) :
    ComputableInPolyTime (fun x => ((List.range (count x)).map (f x)).sum) encIn encNat :=
  ComputableInPolyTime.binary_sum.comp
    (ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.mapWithInput (ComputableTidilyInPolyTime.range.comp hc) hf.tidy))

end SigabaNeo.Lattices.Trapdoor.Family
