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

/-- `cosetGauss B u τ` is defined exactly when the coset is nonempty. -/
theorem cosetGauss_isSome_iff {n m q : ℕ} (B : Matrix (Fin n) (Fin m) (ZMod q))
    (u : Fin n → ZMod q) (τ : ℝ) (hτ : 0 < τ) :
    (cosetGauss B u τ hτ).isSome ↔ ∃ x0 : Fin m → ℤ, B *ᵥ (fun i => (x0 i : ZMod q)) = u := by
  unfold cosetGauss
  split_ifs with h <;> simp [h]

/-- Every point drawn by `cosetGauss B u τ` is in the coset `{x : B·x = u (mod q)}`. -/
theorem cosetGauss_mem_coset {n m q : ℕ} (B : Matrix (Fin n) (Fin m) (ZMod q))
    (u : Fin n → ZMod q) (τ : ℝ) (hτ : 0 < τ) {d : PMF (Fin m → ℤ)}
    (hd : cosetGauss B u τ hτ = some d) {x : Fin m → ℤ} (hx : x ∈ d.support) :
    B *ᵥ (fun i => (x i : ZMod q)) = u := by
  unfold cosetGauss at hd
  split_ifs at hd with h
  obtain rfl := Option.some.inj hd
  have hb : (ZLattice.discreteGaussian (perp B) τ hτ (-(embed m h.choose)) >>= fun a =>
      pure (a : EuclideanSpace ℝ (Fin m))) =
      (ZLattice.discreteGaussian (perp B) τ hτ (-(embed m h.choose))).map Subtype.val := rfl
  rw [PMF.support_map, hb, PMF.support_map] at hx
  obtain ⟨z, ⟨w, -, rfl⟩, rfl⟩ := hx
  obtain ⟨y, hy, hyz⟩ := Submodule.mem_map.mp w.2
  have hte : toInt (embed m y) = y := by funext i; simp [toInt, embed]
  rw [← hyz]
  simp only [hte]
  have hk : B *ᵥ (fun i => (y i : ZMod q)) = 0 := hy
  have : (fun i => ((h.choose + y) i : ZMod q)) =
      (fun i => (h.choose i : ZMod q)) + fun i => (y i : ZMod q) := by ext i; simp
  rw [this, Matrix.mulVec_add, hk, add_zero]
  exact h.choose_spec

end SigabaNeo.Lattices
