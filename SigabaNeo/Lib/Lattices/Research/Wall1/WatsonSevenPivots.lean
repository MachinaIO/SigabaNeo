import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenPivots0
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenPivots1
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenPivots2
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenPivots3
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenPivots4
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenPivots5
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenPivots6
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenPivots7
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenPivots8
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenPivots9
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenPivots10
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenPivots11
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenPivots12
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenPivots13

namespace SigabaNeo.Wall1.Watson.HigherGram.Seven
open PivotData

/-- Oriented pivots grouped by their source representative. -/
def pivots : (k : Fin 33) → List (Pivot k)
  | ⟨0,_⟩ => form0part0
  | ⟨1,_⟩ => form1part0
  | ⟨2,_⟩ => form2part0
  | ⟨3,_⟩ => form3part0
  | ⟨4,_⟩ => form4part0 ++ form4part1
  | ⟨5,_⟩ => form5part0
  | ⟨6,_⟩ => form6part0
  | ⟨7,_⟩ => form7part0 ++ form7part1
  | ⟨8,_⟩ => form8part0
  | ⟨9,_⟩ => form9part0
  | ⟨10,_⟩ => form10part0
  | ⟨11,_⟩ => form11part0
  | ⟨12,_⟩ => form12part0 ++ form12part1 ++ form12part2 ++ form12part3 ++ form12part4
  | ⟨13,_⟩ => form13part0
  | ⟨14,_⟩ => form14part0
  | ⟨15,_⟩ => form15part0
  | ⟨16,_⟩ => form16part0 ++ form16part1 ++ form16part2
  | ⟨17,_⟩ => form17part0 ++ form17part1
  | ⟨18,_⟩ => form18part0 ++ form18part1
  | ⟨19,_⟩ => form19part0
  | ⟨20,_⟩ => form20part0 ++ form20part1
  | ⟨21,_⟩ => form21part0
  | ⟨22,_⟩ => form22part0
  | ⟨23,_⟩ => form23part0 ++ form23part1
  | ⟨24,_⟩ => form24part0
  | ⟨25,_⟩ => form25part0
  | ⟨26,_⟩ => form26part0
  | ⟨27,_⟩ => form27part0 ++ form27part1
  | ⟨28,_⟩ => form28part0
  | ⟨29,_⟩ => form29part0
  | ⟨30,_⟩ => form30part0
  | ⟨31,_⟩ => form31part0
  | ⟨32,_⟩ => form32part0
  | ⟨n+33,h⟩ => by omega

end SigabaNeo.Wall1.Watson.HigherGram.Seven
