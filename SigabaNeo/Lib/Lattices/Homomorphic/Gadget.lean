import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Gadget matrices and their decompositions

The gadget `g = (g₀, …, g_{k-1})` with a digit map `d` such that `∑ᵢ gᵢ · dᵢ(a) = a`
(`GadgetDigits`), the gadget matrix `G = I ⊗ g` of a set of rows embedded in a larger one, and its right
inverse `G⁻¹` on matrices: `G · G⁻¹(A) = A` (`GadgetMatrix.mul_ginv`). With rows `Fin 2` this is the
Ring-GSW gadget; with the single top row of `Fin 2` it is the gadget `G̲` of BGG+ encodings with the
same column blocks, as in the dual use of BTVW17 §4.2 (`gswGadget`, `topRowGadget`).

`binaryDigits` (`SigabaNeo.Lib.Lattices.Homomorphic.BinaryDigits`) is the instance for
`ℤ_q[X]/(X^N + 1)`. For `ℤ_q` itself with integer digits, the gadget of LWE trapdoors is
`SigabaNeo.Lattices.gadget` (`SigabaNeo.Lib.Lattices.Gadget`).

The algebra follows mxx's `GadgetsGadgetMatrix`/`GadgetsDecomposition` (`crates/khe/lean`), here in
the exact form (no residual).
-/

namespace SigabaNeo.Lattices

open Matrix

/-- A gadget vector `g` and digits `d` with `∑ᵢ gᵢ · dᵢ(a) = a`. -/
structure GadgetDigits (R : Type*) [CommRing R] (k : ℕ) where
  /-- The gadget vector. -/
  g : Fin k → R
  /-- The digits of an element. -/
  d : R → Fin k → R
  /-- Recomposition. -/
  recompose : ∀ a, ∑ i, g i * d a i = a

/-- A gadget matrix on rows `r` with columns `W` and its right inverse on `r × W` matrices. -/
structure GadgetMatrix (R : Type*) [CommRing R] (r W : Type*) [Fintype W] where
  /-- The gadget matrix. -/
  G : Matrix r W R
  /-- The decomposition. -/
  ginv : Matrix r W R → Matrix W W R
  /-- `G · G⁻¹(A) = A`. -/
  mul_ginv : ∀ A, G * ginv A = A

variable {R : Type*} [CommRing R] {k : ℕ}

section Embedded

variable {r ρ : Type*} [Fintype r] [Fintype ρ] [DecidableEq r] [DecidableEq ρ]

/-- The gadget matrix `I ⊗ g` of the rows `r`, embedded by `ι` into the rows `ρ` that index the
column blocks: row `a` has `g` in the block of `ι a` and zero elsewhere. -/
def gadgetOf (D : GadgetDigits R k) (ι : r → ρ) (hι : Function.Injective ι) :
    GadgetMatrix R r (ρ × Fin k) where
  G := Matrix.of fun a c => if ι a = c.1 then D.g c.2 else 0
  ginv A := Matrix.of fun c col => ∑ a, if ι a = c.1 then D.d (A a col) c.2 else 0
  mul_ginv A := by
    ext a col
    simp only [Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type]
    have h : ∀ (x : ρ) (i : Fin k),
        ((if ι a = x then D.g i else 0) *
            ∑ a', if ι a' = x then D.d (A a' col) i else 0) =
          if ι a = x then D.g i * D.d (A a col) i else 0 := by
      intro x i
      split_ifs with hx
      · congr 1
        rw [Finset.sum_eq_single a]
        · simp [hx]
        · intro b _ hb
          rw [if_neg]
          intro hb'
          exact hb (hι (hb'.trans hx.symm))
        · simp
      · simp
    simp only [h]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact D.recompose _

end Embedded

/-- The Ring-GSW gadget `G ∈ R^{2 × 2k}`. -/
def gswGadget (D : GadgetDigits R k) : GadgetMatrix R (Fin 2) (Fin 2 × Fin k) :=
  gadgetOf D id Function.injective_id

/-- The gadget `G̲ ∈ R^{1 × 2k}` of BGG+ encodings: the top row of the Ring-GSW gadget. -/
def topRowGadget (D : GadgetDigits R k) : GadgetMatrix R (Fin 1) (Fin 2 × Fin k) :=
  gadgetOf D (fun _ => 0) (fun a b _ => Subsingleton.elim a b)

theorem topRowGadget_G (D : GadgetDigits R k) : (topRowGadget D).G = fun _ => (gswGadget D).G 0 := by
  ext a c
  simp [topRowGadget, gswGadget, gadgetOf]

end SigabaNeo.Lattices
