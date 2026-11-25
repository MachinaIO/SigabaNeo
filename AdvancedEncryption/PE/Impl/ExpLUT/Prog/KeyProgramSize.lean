import PE.Impl.ExpLUT.Prog.KeyPrepareSize
import PE.Impl.ExpLUT.Prog.SetupSize
import SigabaNeoStd.Machines.Prog.AppendWCost

/-! State-count bound for the complete framed KeyGen program, including both branches. -/
namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable def invalidKeyBudget (D : Dims) : ℕ :=
  6 * codecSize (mpkEnc D) + 3 * codecSize (matE D (Wb D) (Fin D.K)) +
    3 * codecSize (keyEnc D) + 21

theorem size_invalidKeyC (D : Dims) :
    (compile (invalidKeyC D)).size ≤ 100000 * invalidKeyBudget D := by
  apply (size_compile_weight _).trans
  apply Nat.mul_le_mul_left
  have hi := weight_keyInputC D
  have hn := weight_natC 19 rB1 (codecSize (keyEnc D))
  simp only [invalidKeyC, packKeyC, codeWeight, invalidKeyBudget]
  omega

namespace KeyCore

theorem size_sampleP (n m : ℕ) (hn : n < 2 ^ m) :
    (sampleP n).size ≤ 195 * m + 1108 := by
  have h := size_coinsF_le hn
  simp only [sampleP, XProg.size, Prog.size, Prim.pad]
  omega

theorem size_enter_post (D : Dims) :
    (enterP D).size + MVM.IO.post.size ≤ 108000 + 6300 * (D.N * D.K) := by
  have hN : D.N ≤ D.N * D.K := Nat.le_mul_of_pos_right _ D.K_pos
  have hK : D.K ≤ D.N * D.K := Nat.le_mul_of_pos_left _ D.N_pos
  have hb (t : Fin 105) :
      (MVM.enc D.N D.K (fun _ ↦ List.replicate 0 false) t).length ≤ D.N * D.K := by
    simp only [MVM.enc, encX]
    split_ifs <;> simp_all
  have h := size_frontIO_le D.N D.K (fun _ ↦ 0) (.cp rCs 1) (D.N * D.K) hb
  have hc := size_compile_weight (.cp rCs 1)
  simp only [codeWeight] at hc
  simpa only [enterP, frontIO, XProg.size, Nat.add_assoc, Nat.mul_one, Nat.reduceAdd] using
    h.trans (Nat.add_le_add_right (Nat.add_le_add_right hc 8000) _)

theorem size_parse : parse.size ≤ 100000 := by decide +kernel

theorem size_frameKeyP : frameKeyP.size ≤ 100000 := by decide +kernel

theorem size_checkP : checkP.size ≤ 500 * Nat.log2 predLen + 2000 := by
  simpa only [checkP, Prog.size_map] using Prog.size_lenEqP predLen

noncomputable def keyProgramBudget (D : Dims) (S B m : ℕ) : ℕ :=
  100000 * (keyPrepareBudget D + candidateTryBudget D S B + invalidKeyBudget D) +
    12600 * (D.N * D.K) + 195 * m + 500 * Nat.log2 predLen + 620000

theorem size_keyProgram (D : Dims) (S B r m : ℕ) (h : TrySizeInputs D S)
    (hn : nPI D * D.N * B < 2 ^ m) :
    (keyProgram D B r).size ≤ keyProgramBudget D S B m := by
  have hp := size_keyPrepareC D
  have hc := size_candidateTryC D S B r h
  have hs := size_sampleP _ m hn
  have hi := size_invalidKeyC D
  have he := size_enter_post D
  have ho := size_compile_weight packKeyC
  simp only [packKeyC, codeWeight] at ho
  have hparse := size_parse
  have hframe := size_frameKeyP
  have hcheck := size_checkP
  simp only [keyProgram, chooseP, validP, invalidP, outputProgram, program,
    XProg.size_seq, XProg.size_prog, XProg.size_ifBit, keyProgramBudget, packKeyC]
  omega

open Params

theorem keyCoinCount_Dc : nPI Dc * Dc.N * Bk < 2 ^ 106 := by
  have hc : nPI Dc ≤ 2 ^ 66 := correction_counts_Dc.2.2
  apply lt_of_le_of_lt (Nat.mul_le_mul_right Bk (Nat.mul_le_mul_right Dc.N hc))
  norm_num [Dc, Bk_def]

theorem size_keyProgram_Dc :
    (keyProgram Dc Bk rSmall).size ≤ keyProgramBudget Dc (2 ^ 66) Bk 106 :=
  size_keyProgram Dc (2 ^ 66) Bk rSmall 106 trySizeInputs_Dc keyCoinCount_Dc

end KeyCore
end AdvancedEncryption.ExpLUT.Prog
