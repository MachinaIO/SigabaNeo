module

public import SigabaNeo.Lib.Lattices.Research.Wall1.PlanarHermite
import all SigabaNeo.Lib.Lattices.Research.Wall1.PlanarHermite

public section

namespace SigabaNeo.Wall1

/-- Assemble the sharp Hermite bounds in dimensions three through five. -/
theorem middleHermite_of_ranks (three : ExactHermiteRange 3 3) (four : ExactHermiteRange 4 4)
    (five : ExactHermiteRange 5 5) : ExactHermiteRange 3 5 := by
  intro k lo hi
  have cases : k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases cases with rfl | rfl | rfl
  · exact three 3 le_rfl le_rfl
  · exact four 4 le_rfl le_rfl
  · exact five 5 le_rfl le_rfl

end SigabaNeo.Wall1
