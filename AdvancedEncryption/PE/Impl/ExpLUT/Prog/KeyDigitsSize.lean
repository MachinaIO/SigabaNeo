import PE.Impl.ExpLUT.Prog.KeyPublicSize
import PE.Impl.ExpLUT.Prog.KeyCorrectionSize
/-! State-count bounds for the complete public-map and gadget-decomposition stage. -/
namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Params

theorem publicSizeInputs_Dc : PublicSizeInputs Dc (2 ^ 66) := by
  obtain ⟨hs, hr, hp, hn, hh⟩ := public_input_lengths Dc
  refine ⟨hs.le.trans ?_, hr.le.trans ?_, hp.le.trans ?_, hn.le.trans ?_,
    correction_counts_Dc.2.2, hh.le.trans ?_⟩ <;> norm_num [Dc, Kc, mbar]

theorem weight_targetC (D : Dims) : codeWeight (targetC D) ≤
    3 * mpkDOffset D + 3 * (((setting D).E.W - 1) * (D.N * D.K)) + 8 := by
  have hh := weight_natC 2 rB1 (mpkDOffset D)
  have ht := weight_natC 2 rB1 (((setting D).E.W - 1) * (D.N * D.K))
  simp only [targetC, targetHeadC, codeWeight]
  omega

noncomputable def keyDigitsBudget (D : Dims) (S : ℕ) : ℕ :=
  2 ^ D.b * (publicRowBudget D S + 1) + 3 * mpkDOffset D +
    3 * (((setting D).E.W - 1) * (D.N * D.K)) + 3 * (setting D).E.W + 3 * D.K + 113

theorem weight_keyDigitsC (D : Dims) (S : ℕ) (h : PublicSizeInputs D S) :
    codeWeight (keyDigitsC D) ≤ keyDigitsBudget D S := by
  have hp := weight_publicRowsAppendC D S h Enum.list
  have hl : (Enum.list (α := Fin (setting D).E.W)).length = 2 ^ D.b := len_fin _
  rw [hl] at hp
  have ht := weight_targetC D
  have hw := weight_natC rQc rB1 (setting D).E.W
  have hk := weight_natC rQk rB1 D.K
  have hd : codeWeight decRowsC ≤ 100 := by decide
  simp only [keyDigitsC, publicRowsC, codeWeight, keyDigitsBudget]
  omega

theorem size_keyDigitsC (D : Dims) (S : ℕ) (h : PublicSizeInputs D S) :
    (compile (keyDigitsC D)).size ≤ 100000 * keyDigitsBudget D S :=
  (size_compile_weight _).trans (Nat.mul_le_mul_left _ (weight_keyDigitsC D S h))

end AdvancedEncryption.ExpLUT.Prog
