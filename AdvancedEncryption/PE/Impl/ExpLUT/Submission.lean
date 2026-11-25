import PE.Impl.ExpLUT.Prog.RedKeyC3M
import PE.Impl.ExpLUT.Prog.RedKeyCW
import PE.Impl.ExpLUT.Prog.RedKeyCWPk
import PE.Impl.ExpLUT.Prog.KeyTightFront
import PE.Impl.ExpLUT.Prog.KeyTightSize

/-!
# The submission for predicate encryption from lookup tables over exponents (ePrint 2026/2539 §5)

`submission`: the ExpLUT implementation (`Setup` `setupMP (binSampler Dc)`, `Enc`
`TapeEnc.encMachineP` (the encryption program packed onto `118` tapes), `KeyGen` `keyMachine`,
`Dec` `TapeDec.decMachineP` (packed onto `50` tapes), `Eval` `evalMachineX`) at the concrete
dimensions `Dc`, with attribute hiding resting on **decision circular Ring-LWE with automorphism
keys** at `1155` bits (`circParamsD Dc`), correctness and expressiveness on nothing, claimed cost
`2^386` (`NcostFinal`).

* **`spec_submission`**: the final statement `Spec`;
* **`valid_submission`**: the premise is valid at the initial strengths of the registry;
* `machine_bounds`: the clock and description length of each machine.
-/

namespace AdvancedEncryption.ExpLUT.Sub

open SigabaNeo AdvancedEncryption.PE AdvancedEncryption.ExpLUT AdvancedEncryption.ExpLUT.Prog

/-- **The per-algorithm bounds** of the submission's machines (clock, description length). -/
theorem machine_bounds :
    (setupMP (binSampler Dc)).time ≤ 2 ^ 241 ∧ (setupMP (binSampler Dc)).descLen ≤ 2 ^ 233 ∧
    TapeEnc.encMachineP.time ≤ 2 ^ 253 ∧ TapeEnc.encMachineP.descLen ≤ 2 ^ 325 ∧
    KeyCore.keyMachine.time ≤ 2 ^ 385 ∧ KeyCore.keyMachine.descLen ≤ 2 ^ 295 ∧
    TapeDec.decMachineP.time ≤ 2 ^ 356 ∧ TapeDec.decMachineP.descLen ≤ 2 ^ 137 := by
  have hmb : Dc.mb = 3 * 2 ^ 40 + 408 := by
    show Params.mbar = _
    rw [Params.mbar_def, Params.Kc_def]; norm_num [Params.en]
  have hK : Dc.K = 2 ^ 16 := by show Params.Kc = _; rw [Params.Kc_def]
  exact ⟨time_setupMP_conf_tight Dc rfl hK rfl hmb, descLen_setupMP_conf_tight Dc rfl hK rfl hmb,
    TapeEnc.time_encMachineP, TapeEnc.descLen_encMachineP,
    KeyCore.time_keyMachine_tight, KeyCore.descLen_keyMachine_tight,
    TapeDec.time_decMachineP, TapeDec.descLen_decMachineP⟩

/-- The claimed cost. -/
def NcostFinal : ℕ := 2 ^ 386

set_option exponentiation.threshold 2000 in
theorem cost_num : 2 ^ 241 + 1 * 2 ^ 385 + 1 * (2 ^ 253 + 2 ^ 356) +
    (2 ^ 233 + 2 ^ 295 + 2 ^ 325 + 2 ^ 137) ≤ NcostFinal := by
  unfold NcostFinal; norm_num

/-- Changing the claimed cost keeps the propositions of a submission. -/
theorem spec_submissionOf_N {decM : Machine} {hdet : decM.Deterministic} {N N' : ℕ}
    (h : Spec (BranchingProgram.primitive BranchingProgram.w8) registry (submissionOf decM hdet N))
    (hc : PE.cost BranchingProgram.params (implE decM hdet) ≤ N') :
    Spec (BranchingProgram.primitive BranchingProgram.w8) registry (submissionOf decM hdet N') :=
  ⟨h.1, hc⟩

/-- **The cost of the implementation** is at most `2^386`. -/
theorem cost_implX_final : PE.cost BranchingProgram.params implX ≤ NcostFinal := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := machine_bounds
  have hs : (implX.machine .setup).time ≤ 2 ^ 241 := by rw [implE_setup]; exact h1
  have hsd : (implX.machine .setup).descLen ≤ 2 ^ 233 := by rw [implE_setup]; exact h2
  have he : (implX.machine .enc).time ≤ 2 ^ 253 := by rw [implE_enc]; exact h3
  have hed : (implX.machine .enc).descLen ≤ 2 ^ 325 := by rw [implE_enc]; exact h4
  have hk : (implX.machine .keyGen).time ≤ 2 ^ 385 := by rw [implE_key]; exact h5
  have hkd : (implX.machine .keyGen).descLen ≤ 2 ^ 295 := by rw [implE_key]; exact h6
  have hd : (implX.machine .dec).time ≤ 2 ^ 356 := by rw [implE_dec]; exact h7
  have hdd : (implX.machine .dec).descLen ≤ 2 ^ 137 := by rw [implE_dec]; exact h8
  exact (cost_le_parts hs hk he hd hsd hkd hed hdd).trans cost_num

/-- **The submission.** -/
noncomputable def submission :
    Submission (BranchingProgram.primitive BranchingProgram.w8) registry :=
  submissionOf TapeDec.decMachineP decMachine_det NcostFinal

/-- **The final statement of the submission.** -/
theorem spec_submission :
    Spec (BranchingProgram.primitive BranchingProgram.w8) registry submission :=
  spec_submissionOf_N (RedKeyC.c3_spec_closed RedKeyC.cw_pkOf RedKeyC.cw_m4) cost_implX_final

/-- **The submission is valid** at the initial strengths of the registry. -/
theorem valid_submission : submission.Valid (Registry.initial assumptions) :=
  valid_submissionOf TapeDec.decMachineP decMachine_det NcostFinal

end AdvancedEncryption.ExpLUT.Sub
