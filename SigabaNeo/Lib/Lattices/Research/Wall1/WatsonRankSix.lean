import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSixContacts0
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSixContacts1
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSixContacts2
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSixContacts3
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSixContacts4
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSixContacts5
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSixContacts6
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonVertexCoverage

/-! The sharp rank-six Hermite inequality from the certified local cones. -/
noncomputable section
namespace SigabaNeo.Wall1.Watson
open ControlledPlane TerminalProjection TerminalProjection.Restart506 DualExit

namespace HigherGram.Six
theorem rayCoverage : RayCoverage := by
  intro k D sym admissible f slopes
  have cost : ∀ R, IsRay k R → 0 ≤ f R := by
    rintro _ ⟨j,S,src,unit,fix,rfl⟩
    exact slopes j src S unit fix
  fin_cases k
  · exact cone_of_support Certificate0.Z Certificate0.tight Certificate0.separates
      Certificate0.normal D sym admissible f cost
  · exact cone_of_support Certificate1.Z Certificate1.tight Certificate1.separates
      Certificate1.normal D sym admissible f cost
  · exact cone_of_support Certificate2.Z Certificate2.tight Certificate2.separates
      Certificate2.normal D sym admissible f cost
  · exact cone_of_support Certificate3.Z Certificate3.tight Certificate3.separates
      Certificate3.normal D sym admissible f cost
  · exact cone_of_support Certificate4.Z Certificate4.tight Certificate4.separates
      Certificate4.normal D sym admissible f cost
  · exact cone_of_support Certificate5.Z Certificate5.tight Certificate5.separates
      Certificate5.normal D sym admissible f cost
  · exact cone_of_support Certificate6.Z Certificate6.tight Certificate6.separates
      Certificate6.normal D sym admissible f cost
end HigherGram.Six

theorem intrinsic_rank_six : IntrinsicHermite 6 (flagGamma 6) :=
  HigherGram.Six.intrinsic_of_rays HigherGram.Six.rayCoverage

/-- The sixth power of the intrinsic Hermite constant is exactly 64/3. -/
theorem sharp_six : IsLeast {t : ℝ | ∃ g, IntrinsicHermite 6 g ∧ t = g^6} (64/3) := by
  have eg : flagGamma 6 ^ 6 = 64/3 := by
    change Real.exp (Real.log (64/3) / 6) ^ 6 = (64/3 : ℝ)
    rw [← Real.exp_nat_mul]
    convert Real.exp_log (by norm_num : (0:ℝ) < 64/3) using 2
    ring
  refine ⟨⟨_,intrinsic_rank_six,eg.symm⟩,?_⟩
  rintro _ ⟨g,h,rfl⟩
  have := necessary_hermite 6 (by decide) (by decide) h
  norm_num at this
  linarith

local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

theorem terminal_bound_of_seven_twentyfour
    (h7 : IntrinsicHermite 7 (flagGamma 7)) (h24 : IntrinsicHermite 24 4) :
    probability terminalHit < probability residual₁ + probability residual₂ + 6.515/(10:ℝ)^12 :=
  terminal_bound_of_six_seven_twentyfour intrinsic_rank_six h7 h24

end SigabaNeo.Wall1.Watson

#print axioms SigabaNeo.Wall1.Watson.HigherGram.Six.rayCoverage
#print axioms SigabaNeo.Wall1.Watson.intrinsic_rank_six
#print axioms SigabaNeo.Wall1.Watson.sharp_six
#print axioms SigabaNeo.Wall1.Watson.terminal_bound_of_seven_twentyfour
