import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonCodeBasis
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonRankSix
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenRayCoverage

/-! Sharp rank-six and rank-seven determinant bounds in every residue-code chart. -/
noncomputable section
namespace SigabaNeo.Wall1.Watson.HigherGram
open Matrix ControlledPlane TerminalProjection TerminalProjection.Restart506 DualExit

/-- The sharp estimate holds throughout every marked rank-six chart. -/
theorem six_chart_bound : Bound 6 4 (6 * ·) (64/3) := by
  intro d hd _ C card G mem
  obtain ⟨pd,minimum⟩ := six_box hd C mem
  apply chart_bound_of_minimum _ hd C card G pd minimum
  intro A ap short
  linarith [Six.determinant_of_rays Six.rayCoverage A ap short]

namespace Seven

/-- Congruence transforms of a normalized rank-seven representative obey the marked
bound. The frame index d is the absolute determinant of the change of coordinates. -/
theorem marked_bound (k : Fin 33) (U : Mat 7) {d : ℕ} (hd : 0 < d) (hU : |U.det| = d) :
    (Uᴴ * representative k * U).PosDef ∧ (d : ℝ)^2 ≤ 64 * (Uᴴ * representative k * U).det := by
  have dp : (0 : ℝ) < d := by exact_mod_cast hd
  have nz : U.det ≠ 0 := by intro h; simp [h] at hU; linarith
  obtain ⟨pos,_,det⟩ := representative_bound k
  refine ⟨pos.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det U).mpr (isUnit_iff_ne_zero.mpr nz))),?_⟩
  have sq : U.det^2 = (d : ℝ)^2 := by rw [← sq_abs,hU]
  rw [det_mul,det_mul,det_conjTranspose,star_trivial]
  calc
    (d : ℝ)^2 ≤ (64 * (representative k).det) * d^2 :=
      le_mul_of_one_le_left (sq_nonneg _) (by linarith)
    _ = _ := by rw [← sq]; ring

def Coverage : Prop :=
  ∀ d, 0 < d → d ≤ 10 → ∀ C : Code 7 d, Nat.card C = d →
    ∀ G ∈ (polytope d (11*d) C).extremePoints ℝ,
      ∃ (k : Fin 33) (U : Matrix (Fin 7) (Fin 7) ℤ), |U.det| = (d : ℤ) ∧
        G = (U.map (Int.castRingHom ℝ))ᴴ * representative k * U.map (Int.castRingHom ℝ)

theorem chart_bound_of_coverage (h : Coverage) : Bound 7 10 (11 * ·) 64 := by
  apply bound_of_vertices (by norm_num)
  intro d hd hi C hc G hG
  obtain ⟨k,U,idx,rfl⟩ := h d hd hi C hc G hG
  apply marked_bound k _ hd
  change |((Int.castRingHom ℝ).mapMatrix U).det| = _
  rw [← RingHom.map_det]
  change |(U.det : ℝ)| = (d : ℝ)
  exact_mod_cast idx

theorem intrinsic_of_coverage (h : Coverage) : IntrinsicHermite 7 (flagGamma 7) :=
  intrinsic_seven (chart_bound_of_coverage h)

private theorem sharp_seven_of_intrinsic (h : IntrinsicHermite 7 (flagGamma 7)) :
    IsLeast {t : ℝ | ∃ g, IntrinsicHermite 7 g ∧ t = g^7} 64 := by
  have eg : flagGamma 7 ^ 7 = 64 := by
    change Real.exp (Real.log 64 / 7) ^ 7 = (64 : ℝ)
    rw [← Real.exp_nat_mul]
    convert Real.exp_log (by norm_num : (0:ℝ) < 64) using 2
    ring
  refine ⟨⟨_,h,eg.symm⟩,?_⟩
  rintro _ ⟨g,hg,rfl⟩
  have := necessary_hermite 7 (by decide) (by decide) hg
  norm_num at this
  linarith

theorem sharp_seven_of_coverage (h : Coverage) :
    IsLeast {t : ℝ | ∃ g, IntrinsicHermite 7 g ∧ t = g^7} 64 :=
  sharp_seven_of_intrinsic (intrinsic_of_coverage h)

/-- The determinant bound holds on every marked rank-seven chart. -/
theorem chart_bound : Bound 7 10 (11 * ·) 64 := chart_bound_of_rays rayCoverage

theorem intrinsic_rank_seven : IntrinsicHermite 7 (flagGamma 7) :=
  intrinsic_seven chart_bound

/-- The least seventh power of an intrinsic Hermite bound in dimension seven is 64. -/
theorem sharp_seven : IsLeast {t : ℝ | ∃ g, IntrinsicHermite 7 g ∧ t = g^7} 64 :=
  sharp_seven_of_intrinsic intrinsic_rank_seven

end Seven
end SigabaNeo.Wall1.Watson.HigherGram

namespace SigabaNeo.Wall1.Watson
open ControlledPlane TerminalProjection TerminalProjection.Restart506 DualExit

/-- The pointwise rank-six inequality for every shortest lattice vector. -/
theorem rank_six {L : Submodule ℤ (CoordSpace 6)} [DiscreteTopology L] [IsZLattice ℝ L]
    {v : CoordSpace 6} (hv : DecoupledDecoder.IsShortest L v) :
    ‖v‖^12 ≤ (64/3) * ZLattice.covolume L^2 := by
  simpa only [← pow_mul] using HigherGram.power_of_bound (by norm_num)
    rank_six_minimal_index HigherGram.six_chart_bound L hv

/-- The squared covolume bounds the fourteenth power of every shortest-vector length. -/
theorem rank_seven {L : Submodule ℤ (CoordSpace 7)} [DiscreteTopology L] [IsZLattice ℝ L]
    {v : CoordSpace 7} (hv : DecoupledDecoder.IsShortest L v) :
    ‖v‖^14 ≤ 64 * ZLattice.covolume L^2 := by
  simpa only [← pow_mul] using HigherGram.power_of_bound (by norm_num)
    rank_seven_minimal_index HigherGram.Seven.chart_bound L hv

local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

theorem terminal_bound_of_seven_coverage_twentyfour (c : HigherGram.Seven.Coverage)
    (h24 : IntrinsicHermite 24 4) :
    probability terminalHit < probability residual₁ + probability residual₂ + 6.515/(10:ℝ)^12 :=
  terminal_bound_of_seven_twentyfour (HigherGram.Seven.intrinsic_of_coverage c) h24

end SigabaNeo.Wall1.Watson

#print axioms SigabaNeo.Wall1.Watson.HigherGram.six_chart_bound
#print axioms SigabaNeo.Wall1.Watson.HigherGram.Seven.marked_bound
#print axioms SigabaNeo.Wall1.Watson.HigherGram.Seven.intrinsic_of_coverage

#print axioms SigabaNeo.Wall1.Watson.HigherGram.Seven.sharp_seven_of_coverage
#print axioms SigabaNeo.Wall1.Watson.rank_six
#print axioms SigabaNeo.Wall1.Watson.terminal_bound_of_seven_coverage_twentyfour

#print axioms SigabaNeo.Wall1.Watson.rank_seven
#print axioms SigabaNeo.Wall1.Watson.HigherGram.Seven.intrinsic_rank_seven
#print axioms SigabaNeo.Wall1.Watson.HigherGram.Seven.sharp_seven
