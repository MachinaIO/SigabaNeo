import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenSimplex0
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenSimplex2
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenSimplex3
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenSimplex10
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenSimplex11
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenSimplex13
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenSimplex15
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenSimplex17
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenSimplex21
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenSimplex24
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenSimplex25
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenSimplex27
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenSimplex28
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenSimplex29
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenSimplex30
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenSimplex31
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenSimplex32
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenContacts1
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenContacts4
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenContacts5
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenContacts6
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenContacts7
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenContacts8
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenContacts9
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenContacts12
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenContacts14
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenContacts16
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenContacts18
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenContacts19
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenContacts20
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenContacts22
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenContacts23
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenContacts26

namespace SigabaNeo.Wall1.Watson.HigherGram.Seven

/-- Each of the 33 representatives has a certified spanning family of tangent directions. -/
theorem rayCoverage : ∀ k, RayCoverageAt k := by
  intro k
  fin_cases k
  · exact Simplex0.coverage
  · exact Certificate1.coverage
  · exact Simplex2.coverage
  · exact Simplex3.coverage
  · exact Certificate4.coverage
  · exact Certificate5.coverage
  · exact Certificate6.coverage
  · exact Certificate7.coverage
  · exact Certificate8.coverage
  · exact Certificate9.coverage
  · exact Simplex10.coverage
  · exact Simplex11.coverage
  · exact Certificate12.coverage
  · exact Simplex13.coverage
  · exact Certificate14.coverage
  · exact Simplex15.coverage
  · exact Certificate16.coverage
  · exact Simplex17.coverage
  · exact Certificate18.coverage
  · exact Certificate19.coverage
  · exact Certificate20.coverage
  · exact Simplex21.coverage
  · exact Certificate22.coverage
  · exact Certificate23.coverage
  · exact Simplex24.coverage
  · exact Simplex25.coverage
  · exact Certificate26.coverage
  · exact Simplex27.coverage
  · exact Simplex28.coverage
  · exact Simplex29.coverage
  · exact Simplex30.coverage
  · exact Simplex31.coverage
  · exact Simplex32.coverage

end SigabaNeo.Wall1.Watson.HigherGram.Seven
