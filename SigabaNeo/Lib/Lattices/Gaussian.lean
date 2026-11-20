import SigabaNeo.Lib.Lattices.Basic
import CslibFrontier.Foundations.Probability.Gaussian.Discrete

/-!
# Discrete Gaussian distributions

Both are cslib-frontier's `ZLattice.discreteGaussian`, with its width convention
`ρ_s(x) = exp(−π‖x‖²/s²)`.

* `gaussZ s`: `D_{Z,s}`, the discrete Gaussian on `Z ⊂ R^1`.
* `cosetGauss B u τ`: the discrete Gaussian of width `τ` on the coset
  `{x ∈ Z^m : B·x = u (mod q)}` of `Λ^⊥(B)`, or `none` if the coset is empty.

Their tails, smoothing and point masses are in `SigabaNeo.Lib.Lattices.Gaussian.*`.
-/

namespace SigabaNeo.Lattices

open scoped Matrix

/-- The discrete Gaussian `D_{Z,s}`: cslib-frontier's discrete Gaussian on `Z ⊂ R^1`. -/
noncomputable def gaussZ (s : ℝ) (hs : 0 < s) : PMF ℤ :=
  (ZLattice.discreteGaussian (perp (0 : Matrix (Fin 0) (Fin 1) (ZMod 1))) s hs 0).map
    fun z => toInt (z : EuclideanSpace ℝ (Fin 1)) 0

open Classical in
/-- The discrete Gaussian of width `τ` on the coset `{x ∈ Z^m : B·x = u}`, if it is nonempty. -/
noncomputable def cosetGauss {n m q : ℕ} (B : Matrix (Fin n) (Fin m) (ZMod q))
    (u : Fin n → ZMod q) (τ : ℝ) (hτ : 0 < τ) : Option (PMF (Fin m → ℤ)) :=
  if h : ∃ x0 : Fin m → ℤ, B *ᵥ (fun i => (x0 i : ZMod q)) = u then
    some ((ZLattice.discreteGaussian (perp B) τ hτ (-(embed m h.choose))).map
      fun z => h.choose + toInt (z : EuclideanSpace ℝ (Fin m)))
  else none

end SigabaNeo.Lattices
