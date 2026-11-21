import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Cslib.Probability.PMF

/-!
# Integer lattices and independent draws

* `embed m`: `Z^m` inside `R^m`, coordinatewise; `toInt` reads integer coordinates back.
* `kernel B`: the integer kernel `{x ∈ Z^m : B·x = 0 (mod q)}` of `B ∈ Z_q^{n×m}`, and
  `perp B = Λ^⊥(B) ⊂ R^m`, a discrete subgroup (so cslib-frontier's discrete Gaussians apply).
* `sampleList d n`, `sampleMat d r c`, `sampleFun d`, `sampleOptList ds`: independent draws.
-/

namespace SigabaNeo.Lattices

open scoped Matrix

/-! ### Integer lattices in Euclidean space -/

/-- `Z^m` inside `R^m`, coordinatewise. -/
noncomputable def embed (m : ℕ) : (Fin m → ℤ) →ₗ[ℤ] EuclideanSpace ℝ (Fin m) where
  toFun x := WithLp.toLp 2 fun i => (x i : ℝ)
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

/-- The integer kernel `{x ∈ Z^m : B·x = 0 (mod q)}`. -/
def kernel {n m q : ℕ} (B : Matrix (Fin n) (Fin m) (ZMod q)) : Submodule ℤ (Fin m → ℤ) where
  carrier := {x | B *ᵥ (fun i => (x i : ZMod q)) = 0}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at *
    have : (fun i => ((x + y) i : ZMod q)) = (fun i => (x i : ZMod q)) + fun i => (y i : ZMod q) := by
      ext i; simp
    rw [this, Matrix.mulVec_add, hx, hy, add_zero]
  zero_mem' := by simp; exact Matrix.mulVec_zero B
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq] at *
    have : (fun i => ((c • x) i : ZMod q)) = (c : ZMod q) • fun i => (x i : ZMod q) := by
      ext i; simp
    rw [this, Matrix.mulVec_smul, hx, smul_zero]

/-- The lattice `Λ^⊥(B) ⊂ R^m`. -/
noncomputable def perp {n m q : ℕ} (B : Matrix (Fin n) (Fin m) (ZMod q)) :
    Submodule ℤ (EuclideanSpace ℝ (Fin m)) :=
  (kernel B).map (embed m)

theorem perp_le {n m q : ℕ} (B : Matrix (Fin n) (Fin m) (ZMod q)) :
    perp B ≤ Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin m) ℝ).toBasis) := by
  rintro _ ⟨x, -, rfl⟩
  have : embed m x = ∑ i, x i • (EuclideanSpace.basisFun (Fin m) ℝ).toBasis i := by
    ext j; simp [embed, Finset.sum_apply, Pi.single_apply]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

instance {n m q : ℕ} (B : Matrix (Fin n) (Fin m) (ZMod q)) : DiscreteTopology (perp B) :=
  DiscreteTopology.of_subset (s := (Submodule.span ℤ
    (Set.range (EuclideanSpace.basisFun (Fin m) ℝ).toBasis) : Set (EuclideanSpace ℝ (Fin m))))
    (inferInstanceAs (DiscreteTopology
      (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin m) ℝ).toBasis)))) (perp_le B)

/-- The integer coordinates of a lattice point. -/
noncomputable def toInt {m : ℕ} (z : EuclideanSpace ℝ (Fin m)) : Fin m → ℤ := fun i => round (z i)

/-! ### Independent draws -/

/-- `n` independent draws. -/
noncomputable def sampleList {α : Type} (d : PMF α) : ℕ → PMF (List α)
  | 0 => PMF.pure []
  | n + 1 => d.bind fun a => (sampleList d n).map (a :: ·)

/-- An `r × c` matrix with independent entries. -/
noncomputable def sampleMat {α : Type} [Inhabited α] (d : PMF α) (r c : ℕ) :
    PMF (Matrix (Fin r) (Fin c) α) :=
  (sampleList d (r * c)).map fun l i j => l.getD (i.val * c + j.val) default

/-- A function on a finite type with independent values, each drawn from `d`. -/
noncomputable def sampleFun {ι α : Type} [Fintype ι] [Inhabited α] (d : PMF α) : PMF (ι → α) :=
  (sampleList d (Fintype.card ι)).map fun l i => l.getD (Fintype.equivFin ι i).val default

/-- An optional list of independent draws: `none` as soon as one draw is unavailable. -/
noncomputable def sampleOptList {α : Type} : List (Option (PMF α)) → PMF (Option (List α))
  | [] => PMF.pure (some [])
  | none :: _ => PMF.pure none
  | some d :: ds => d.bind fun a => (sampleOptList ds).map (Option.map (a :: ·))

end SigabaNeo.Lattices
