import SigabaNeoStd.Lattices.Homomorphic.SLP
import SigabaNeoStd.Lattices.Homomorphic.Eval

/-!
# The circuit of a wire of a straight-line program

`SLP.circuit p w` unfolds the gates below the wire `w` into a tree (`Circuit`): the run of `p` on
circuits. Every evaluation of the tree is the run of `p` on the corresponding values
(`evalBool_circuit`, `eval_circuit`, `evalMat_circuit`), by `SLP.valueOf_map`. The tree may be
exponentially larger than the program; it serves the analysis, while programs are evaluated
gate by gate.
-/

namespace SigabaNeo.Lattices

namespace SLP

variable {ι : Type*}

/-- The circuit of a wire. -/
def circuit (p : SLP ι) (w : Wire ι) : Circuit ι := valueOf .input .one .nand p w

theorem evalBool_circuit (x : ι → Bool) (p : SLP ι) (w : Wire ι) :
    (p.circuit w).evalBool x = evalBool x p w :=
  valueOf_map _ _ _ x true _ (Circuit.evalBool x) (fun _ => rfl) rfl (fun _ _ => rfl) p w

theorem eval_circuit {R : Type*} [CommRing R] (x : ι → R) (p : SLP ι) (w : Wire ι) :
    (p.circuit w).eval x = eval x p w :=
  valueOf_map _ _ _ x 1 _ (Circuit.eval x) (fun _ => rfl) rfl (fun _ _ => rfl) p w

theorem evalMat_circuit {R : Type*} [CommRing R] {r W : Type*} [Fintype r] [Fintype W]
    (Γ : GadgetMatrix R r W) (M : ι → Matrix r W R) (p : SLP ι) (w : Wire ι) :
    evalMat Γ M (p.circuit w) = valueOf M Γ.G (fun a b => Γ.G - a * Γ.ginv b) p w :=
  valueOf_map _ _ _ M Γ.G _ (evalMat Γ M) (fun _ => rfl) rfl (fun _ _ => rfl) p w

end SLP

end SigabaNeo.Lattices
