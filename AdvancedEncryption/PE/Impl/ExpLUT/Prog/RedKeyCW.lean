import PE.Impl.ExpLUT.Prog.RedKeyCWPk

/-!
# The weights of the M4 codes (`≤ 2^160`, hypothesis `hw4` of `c3_spec`), and `c3_spec` without
its weight hypotheses

* `simKeyC Dc = seLoopKC ; natC seMb rBit1 Dc.mb ; sePostC` (fixed parts by `decide`, the count
  by F3's linear `natC` weight);
* `setXC Dc`: six fixed instructions, `readFieldC 14 rxH nB nH` (`nB + nH ≤ 2^120`, codec sizes of
  the public-key word), `natC rxTs rB1 (2^b · m̄)`;
* `simXC` by `decide`.

**`cw_m4`** (`hw4`) and **`c3_spec_w`**: `c3_spec` with `hw3 := cw_pkOf`, `hw4 := cw_m4`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 2000
set_option maxRecDepth 100000

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyC

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM
open AdvancedEncryption.ExpLUT.Prog.RedKeyPkt AdvancedEncryption.ExpLUT.Prog.RedKeyMid
open AdvancedEncryption.ExpLUT.Params AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open SigabaNeo.Lattices.Algo
open AdvancedEncryption.ExpLUT.Prog.RedKeyC4 AdvancedEncryption.ExpLUT.Prog.KeyTime
open AdvancedEncryption.PE.Generic

theorem cw_seLoopKC : codeWeight seLoopKC ≤ 10000 := by decide +kernel
theorem cw_sePostC : codeWeight sePostC ≤ 1000 := by decide +kernel
theorem cw_simXC : codeWeight simXC ≤ 1000 := by decide +kernel

theorem cw_simKeyC : codeWeight (simKeyC Dc) ≤ 2 ^ 44 := by
  have h1 := cw_seLoopKC
  have h2 := cw_sePostC
  have h3 := weight_natC seMb rBit1 Dc.mb
  have h4 := cw_mb
  rw [show simKeyC Dc = .seq seLoopKC (.seq (natC seMb rBit1 Dc.mb) sePostC) from rfl,
    cs_cw_seq, cs_cw_seq]
  omega

/-- The `B` and `H` field lengths of the public-key word at `Dc`. -/
theorem cw_nBH : RedKeyMid.nB Dc + RedKeyMid.nH Dc ≤ 2 ^ 120 := by
  simp only [RedKeyMid.nB, RedKeyMid.nH, codecSize, Wb, Jh, Pos, len_sum, Enum.length_prod, len_fin]
  have hmb := cw_mb
  simp only [cw_K, cw_N, cw_b, cw_w8]
  generalize Dc.mb = m at hmb
  omega

theorem cw_setXC_gen (D : Dims) :
    codeWeight (setXC D) ≤
      6 + (3 * RedKeyMid.nB D + 3 * RedKeyMid.nH D + 6) + (3 * (2 ^ D.b * D.mb) + 1) := by
  have h1 := weight_readFieldC 14 rxH (RedKeyMid.nB D) (RedKeyMid.nH D)
  have h2 := weight_natC rxTs rB1 (2 ^ D.b * D.mb)
  rw [setXC]
  simp only [cs_cw_seq]
  simp only [show ∀ d s : Fin 64, codeWeight (.cp d s) = 1 from fun _ _ => rfl,
    show ∀ f a b : Fin 64, codeWeight (.eqb f a b) = 1 from fun _ _ _ => rfl]
  omega

theorem cw_setXC : codeWeight (setXC Dc) ≤ 2 ^ 123 := by
  have h1 := cw_setXC_gen Dc
  have h3 := cw_nBH
  have h5 : 2 ^ Dc.b * Dc.mb ≤ 4194304 * 4398046511104 := by
    rw [cw_b]; exact Nat.mul_le_mul (by norm_num) cw_mb
  generalize 2 ^ Dc.b * Dc.mb = x at h1 h5
  generalize RedKeyMid.nB Dc = p at h1 h3
  generalize RedKeyMid.nH Dc = q at h1 h3
  omega

/-- **Hypothesis `hw4` of `c3_spec`.** -/
theorem cw_m4 : codeWeight (simKeyC Dc) + codeWeight (setXC Dc) + codeWeight simXC ≤ 2 ^ 160 := by
  have h1 := cw_simKeyC
  have h2 := cw_setXC
  have h3 := cw_simXC
  omega

/-- **`c3_spec` without its weight hypotheses.** -/
theorem c3_spec_w (x : Fin 64 → ℕ) (hx : x ≤ bx c4In) (T : ℕ) (hT : T ≤ 2 ^ 438)
    (h3 : Cert (MVM.compile (pkOf RedKeyPkt.pkt)) c3In (c4L x) T) :
    Spec (BranchingProgram.primitive BranchingProgram.w8) Sub.registry
      (Sub.submissionOf TapeDec.decMachineP Sub.decMachine_det Sub.Ncost) :=
  c3_spec x hx T hT h3 cw_pkOf cw_m4

end AdvancedEncryption.ExpLUT.Prog.RedKeyC
