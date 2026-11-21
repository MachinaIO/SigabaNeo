module

public import SigabaNeo.Lib.Lattices.Research.Wall1.HorizontalSelected

@[expose] public section

namespace SigabaNeo.Wall1
open QAry

/-- When the prefix contains the plant, the off-line test holds vacuously and the
same-line test fails at its nonvanishing condition. -/
theorem prefixPlant_terminal {m n q β k : ℕ} [Fact q.Prime] (pos : 0 < β)
    (shape : k*β = dim m n) (e : Fin m → ℤ) (s : Fin n → ℤ)
    (A : Matrix (Fin m) (Fin n) (ZMod q))
    (h : WithLp.toLp 2 (fun i ↦ ((Planted.plantedPoint e s (indexEquiv.symm i) : ℤ) : ℝ))
      ∈ selectedPrefixSpan pos shape e s A) :
    (terminal pos shape e s A).offLine ∧ ¬ (terminal pos shape e s A).sameLine := by
  have hz := Submodule.orthogonalProjectionOnto_orthogonal_apply_eq_zero h
  have hnorm := congrArg norm hz
  rw [norm_zero] at hnorm
  constructor
  · rintro z ⟨_, hn, hb⟩
    exact False.elim ((norm_pos_iff.mpr hn).not_ge (hb.trans hnorm.le))
  · exact fun hs ↦ hs.1 hz

#print axioms prefixPlant_terminal
end SigabaNeo.Wall1
