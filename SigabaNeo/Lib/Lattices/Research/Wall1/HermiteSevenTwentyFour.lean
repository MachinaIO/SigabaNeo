import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonRankSix

/-! Unconditional intrinsic Hermite upper bounds at ranks 7, 8 and 24. -/

noncomputable section

namespace SigabaNeo.Wall1.Watson

open ControlledPlane Real

/-- Apply Mordell to the sharp rank-six bound. -/
theorem intrinsic_seven_mordell : IntrinsicHermite 7 ((64 / 3 : ℝ) ^ (1 / 5 : ℝ)) := by
  have h := intrinsic_mordell (k := 6) (by decide)
    (show 0 < flagGamma 6 from Real.exp_pos _) (familyHermite_of_intrinsic intrinsic_rank_six)
  change IntrinsicHermite 7 (exp (log (64 / 3) / 6) ^ ((6 : ℝ) / (6 - 1))) at h
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 64 / 3)]
  rwa [← exp_mul,
    show log (64 / 3) / 6 * (6 / (6 - 1)) = log (64 / 3) * (1 / 5) by ring] at h

/-- The second Mordell step from rank six, used when rank eight is also required. -/
theorem intrinsic_eight_mordell : IntrinsicHermite 8 ((64 / 3 : ℝ) ^ (7 / 30 : ℝ)) := by
  have h := intrinsic_mordell (k := 7) (by decide)
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 64 / 3) _)
    (familyHermite_of_intrinsic intrinsic_seven_mordell)
  change IntrinsicHermite 8 (((64 / 3 : ℝ) ^ (1 / 5 : ℝ)) ^ ((7 : ℝ) / (7 - 1))) at h
  rwa [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 64 / 3),
    show (1 / 5 : ℝ) * (7 / (7 - 1)) = 7 / 30 by norm_num] at h

/-- The direct Blichfeldt coefficient at rank 24, with the Gamma function evaluated. -/
theorem intrinsic_twentyfour_blichfeldt :
    IntrinsicHermite 24 ((2 / π) * (Nat.factorial 13 : ℝ) ^ (1 / 12 : ℝ)) := by
  intro L _ _
  have h := BKZ.hermite_blichfeldt L
  rw [show ((24 : ℕ) : ℝ) / 2 + 2 = ((13 : ℕ) : ℝ) + 1 by norm_num,
    Real.Gamma_nat_eq_factorial, show (2 : ℝ) / (24 : ℕ) = 1 / 12 by norm_num] at h
  convert h using 1
  norm_num

end SigabaNeo.Wall1.Watson

#print axioms SigabaNeo.Wall1.Watson.intrinsic_seven_mordell
#print axioms SigabaNeo.Wall1.Watson.intrinsic_eight_mordell
#print axioms SigabaNeo.Wall1.Watson.intrinsic_twentyfour_blichfeldt
