import PE.Impl.ExpLUT.Prog.DecTightFront
/-!
# The tight clock of the concrete `Dec` machine (part 6)

`decProgram Dc` from the input bound (`dtPsh (2^105)`): parsing (`≤ 2^221` steps), the length test
(`≤ 2^222`), and on a valid word the templates (`≤ 2^210`), the constants, the compiled code
(`dtTvm ≤ 2^224`, `DecTight.dt_decCode`) and the output; the output tape ends with at most `3`
bits. Hence

**`DecConf.time_decMachine_tight : decMachine.time ≤ 2 ^ 225`**

(down from `2^727`, `DecConf.time_decMachine`).
-/

namespace AdvancedEncryption.ExpLUT.Prog.DecTight

set_option autoImplicit false
set_option maxRecDepth 100000

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM AdvancedEncryption.ExpLUT.Params
open DecM
open SigabaNeo.Tape.XProg

/-- The clock of the valid branch. -/
def fuValidT : ℕ := fuTmplT + (fuConstT + (dtTvm + fuOutT))

/-- The clock of the program. -/
def fuProgT : ℕ := fuParseT + (fuLenT + (max fuValidT fuInvT + 1))

/-- **The per-tape bounds of the `Dec` program.** -/
theorem fu_decProgram : VB (decProgram Dc) (dtPsh (2 ^ 105)) fuProgT dtLfin := by
  have hv : VB (validP Dc) (dtPsh (2 ^ 109)) fuValidT dtLfin :=
    fu_tmplsDc.seq (fu_constP.seq (fu_vm.seq fu_outP))
  exact fu_parseX.seq (fu_lenX.seq (DecConf.vb_ifBitD hv fu_invP))

theorem inputBound_le_Psh (n : ℕ) (hn : n ≤ 2 ^ 105) :
    Prog.inputBound (255 : Fin 256) n ≤ dtPsh (2 ^ 105) := dtPile fun t => by
  simp only [Prog.inputBound, Function.update_apply]
  split_ifs with h
  · subst h; rw [dtPsh, dtFv_high 255 (by decide)]; exact hn
  · exact Nat.zero_le _

set_option exponentiation.threshold 2000 in
theorem fuParseT_le : fuParseT ≤ 2 ^ 221 := by
  unfold fuParseT Prog.unfrT; norm_num

set_option exponentiation.threshold 2000 in
theorem fuLenT_le : fuLenT ≤ 2 ^ 222 := by
  unfold fuLenT predLen; norm_num

set_option exponentiation.threshold 2000 in
theorem fuValidT_le : fuValidT ≤ 2 ^ 224 + 2 ^ 212 := by
  have h := dtTvm_le
  have h1 : fuTmplT ≤ 2 ^ 211 := by unfold fuTmplT; norm_num
  have h2 : fuConstT ≤ 2 ^ 152 := by unfold fuConstT; norm_num
  have h3 : fuOutT ≤ 2 ^ 112 := by unfold fuOutT; norm_num
  have h4 : (2 : ℕ) ^ 211 + 2 ^ 152 + 2 ^ 112 ≤ 2 ^ 212 := by norm_num
  unfold fuValidT
  linarith

set_option exponentiation.threshold 2000 in
theorem fuProgT_le : fuProgT ≤ 2 ^ 225 - 2 ^ 120 := by
  have h1 := fuParseT_le
  have h2 := fuLenT_le
  have h3 := fuValidT_le
  have h4 : fuInvT ≤ 2 ^ 112 := by unfold fuInvT; norm_num
  have h5 : max fuValidT fuInvT ≤ 2 ^ 224 + 2 ^ 212 := max_le h3 (h4.trans (by norm_num))
  have : (2 : ℕ) ^ 221 + (2 ^ 222 + (2 ^ 224 + 2 ^ 212 + 1)) ≤ 2 ^ 225 - 2 ^ 120 := by norm_num
  unfold fuProgT
  linarith

/-- The clock of a program from the shape bounds. -/
theorem fu_total {p : XProg 256} {n T : ℕ} (hn : n ≤ 2 ^ 105) (h : VB p (dtPsh (2 ^ 105)) T dtLfin) :
    XProg.totalTimeT p 255 0 n ≤ (2 * 2 ^ 105 + 2) + T + (2 * 3 + 2) := by
  have hb := h _ (inputBound_le_Psh n hn)
  have h0 : XProg.lenBoundT p (Prog.inputBound 255 n) 0 ≤ 3 := (hb.2 0).trans (by simp [dtLfin])
  unfold XProg.totalTimeT
  have := hb.1
  linarith

end AdvancedEncryption.ExpLUT.Prog.DecTight

namespace AdvancedEncryption.ExpLUT.Prog.DecConf

open AdvancedEncryption.ExpLUT.Prog.DecTight

set_option exponentiation.threshold 2000 in
/-- **The tight clock of the concrete `Dec` machine.** -/
theorem time_decMachine_tight : decMachine.time ≤ 2 ^ 225 := by
  rw [decMachine, DecM.time_decMP]
  refine (fu_total dtInput_le fu_decProgram).trans ?_
  have hT := fuProgT_le
  have : (2 * 2 ^ 105 + 2) + (2 ^ 225 - 2 ^ 120) + (2 * 3 + 2) ≤ (2 : ℕ) ^ 225 := by norm_num
  linarith

end AdvancedEncryption.ExpLUT.Prog.DecConf
