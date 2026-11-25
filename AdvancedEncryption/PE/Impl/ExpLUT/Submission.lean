import PE.Impl.ExpLUT.Prog.RedKeyC3M
import PE.Impl.ExpLUT.Prog.RedKeyCW
import PE.Impl.ExpLUT.Prog.RedKeyCWPk

/-!
# The submission for predicate encryption from lookup tables over exponents (ePrint 2026/2539 §5)

`submission`: the ExpLUT implementation (`Setup` `setupMP (binSampler Dc)`, `Enc` `encMachine`,
`KeyGen` `keyMachine`, `Dec` `decMachine`, `Eval` `evalMachineX`) at the concrete dimensions `Dc`,
with attribute hiding resting on **decision circular Ring-LWE with automorphism keys** at
`1155` bits (`circParamsD Dc`), correctness and expressiveness on nothing, claimed cost `2^745`.

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

end AdvancedEncryption.ExpLUT.Sub
