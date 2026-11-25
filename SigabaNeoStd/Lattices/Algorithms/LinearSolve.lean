import Mathlib.LinearAlgebra.Matrix.ToLin

namespace SigabaNeo.LinearSolve

/-- A right-hand side in the column span has a unique preimage under a matrix
with trivial kernel. -/
theorem existsUnique_mulVec {K : Type*} [Field K] {m D : ℕ}
    (M : Matrix (Fin m) (Fin D) K) (c : Fin m → K)
    (hker : LinearMap.ker M.mulVecLin = ⊥)
    (hc : c ∈ Submodule.span K (Set.range M.col)) :
    ∃! y : Fin D → K, M.mulVec y = c := by
  rw [← Matrix.range_mulVecLin] at hc
  obtain ⟨y, hy⟩ := hc
  exact ⟨y, hy, fun z hz ↦ (LinearMap.ker_eq_bot.mp hker) (hz.trans hy.symm)⟩

#print axioms existsUnique_mulVec

end SigabaNeo.LinearSolve
