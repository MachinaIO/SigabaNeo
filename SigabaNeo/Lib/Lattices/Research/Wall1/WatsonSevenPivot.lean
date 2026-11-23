import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenRepresentatives

namespace SigabaNeo.Wall1.Watson.HigherGram.Seven
open Matrix
abbrev IntMat := Matrix (Fin 7) (Fin 7) ℤ

/-- An integral direction in the tangent cone, with a positive step to a listed form. -/
structure Pivot (k : Fin 33) where
  dst : Fin 33
  step : ℚ
  direction : IntMat
  change : IntMat
  unit : IsUnit change
  positive : 0 < step
  endpoint : forms k + step • direction.map (Int.castRingHom ℚ) =
    (change.map (Int.castRingHom ℚ))ᵀ * forms dst * change.map (Int.castRingHom ℚ)

def entries {α : Type} [DecidableEq α] (A B : Matrix (Fin 7) (Fin 7) α) :
    Decidable (∀ i j, A i j = B i j) := by
  letI (i j : Fin 7) : Decidable (A i j = B i j) := inferInstance
  letI (i : Fin 7) : Decidable (∀ j, A i j = B i j) := Nat.decidableForallFin _
  exact Nat.decidableForallFin _
theorem matrix_eq_of_entries {α : Type} [DecidableEq α] (A B : Matrix (Fin 7) (Fin 7) α)
    (h : @decide _ (entries A B) = true) : A = B := Matrix.ext (@of_decide_eq_true _ (entries A B) h)

end SigabaNeo.Wall1.Watson.HigherGram.Seven
