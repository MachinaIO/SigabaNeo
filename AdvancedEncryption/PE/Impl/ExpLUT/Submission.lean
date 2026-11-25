import PE.Impl.ExpLUT.Prog.RedKeyC3M
import PE.Impl.ExpLUT.Prog.RedKeyCW
import PE.Impl.ExpLUT.Prog.RedKeyCWPk
import PE.Impl.ExpLUT.Prog.KeyTightFront
import PE.Impl.ExpLUT.Prog.KeyTightSize
import PE.Impl.ExpLUT.Prog.DecTight

/-!
# The submission for predicate encryption from lookup tables over exponents (ePrint 2026/2539 §5)

`submission`: the ExpLUT implementation (`Setup` `setupMP (binSampler Dc)`, `Enc` `encMachine`,
`KeyGen` `keyMachine`, `Dec` `decMachine`, `Eval` `evalMachineX`) at the concrete dimensions `Dc`,
with attribute hiding resting on **decision circular Ring-LWE with automorphism keys** at
`1155` bits (`circParamsD Dc`), correctness and expressiveness on nothing, claimed cost `2^636`.

* **`spec_submission`**: the final statement `Spec`;
* **`valid_submission`**: the premise is valid at the initial strengths of the registry.
-/

namespace AdvancedEncryption.ExpLUT.Sub

open SigabaNeo AdvancedEncryption.PE AdvancedEncryption.ExpLUT AdvancedEncryption.ExpLUT.Prog

/-- **The submission.** -/
noncomputable def submission :
    Submission (BranchingProgram.primitive BranchingProgram.w8) registry :=
  submissionOf DecConf.decMachine decMachine_det Ncost

/-- **The final statement of the submission.** -/
theorem spec_submission :
    Spec (BranchingProgram.primitive BranchingProgram.w8) registry submission :=
  RedKeyC.c3_spec_closed RedKeyC.cw_pkOf RedKeyC.cw_m4

/-- **The submission is valid** at the initial strengths of the registry. -/
theorem valid_submission : submission.Valid (Registry.initial assumptions) :=
  valid_submissionOf DecConf.decMachine decMachine_det Ncost

/-- **The per-algorithm bounds** of the submission's machines (clock, description length). -/
theorem machine_bounds :
    (setupMP (binSampler Dc)).time ≤ 2 ^ 241 ∧ (setupMP (binSampler Dc)).descLen ≤ 2 ^ 233 ∧
    EncConf.encMachine.time ≤ 2 ^ 253 ∧ EncConf.encMachine.descLen ≤ 2 ^ 635 ∧
    KeyCore.keyMachine.time ≤ 2 ^ 385 ∧ KeyCore.keyMachine.descLen ≤ 2 ^ 295 ∧
    DecConf.decMachine.time ≤ 2 ^ 225 ∧ DecConf.decMachine.descLen ≤ 2 ^ 447 := by
  have hmb : Dc.mb = 3 * 2 ^ 40 + 408 := by
    show Params.mbar = _
    rw [Params.mbar_def, Params.Kc_def]; norm_num [Params.en]
  have hK : Dc.K = 2 ^ 16 := by show Params.Kc = _; rw [Params.Kc_def]
  exact ⟨time_setupMP_conf_tight Dc rfl hK rfl hmb, descLen_setupMP_conf_tight Dc rfl hK rfl hmb,
    EncConf.time_encMachine_tight, EncConf.descLen_encMachine_tight,
    KeyCore.time_keyMachine_tight, KeyCore.descLen_keyMachine_tight,
    DecConf.time_decMachine_tight, DecConf.descLen_decMachine_tight⟩

end AdvancedEncryption.ExpLUT.Sub
