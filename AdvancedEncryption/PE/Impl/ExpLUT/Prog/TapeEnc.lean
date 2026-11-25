import SigabaNeoStd.Machines.Pack.Leaves
import PE.Impl.ExpLUT.Prog.EncTightFront
import PE.Impl.ExpLUT.Prog.DescTightEnc

/-!
# The packed encryption machine (fewer physical tapes)

`encMachineP := packMachineT 105 8 (encProgram Dc 16 6 eFl) 0 0 (encInputLength Dc)`: the
encryption program compiled by the packing translation (`SigabaNeoStd.Machines.Pack`) onto
`5 + 105 + 8 = 118` physical tapes instead of `326`. With a workspace of `105` tapes the parser and
sampler (`105` tapes) and each of the four core phases (`≤ 104` tapes) run natively as one leaf
group each; only the glue between them is packed.

* **`encSpec_encMachineP : EncSpec Dc χc χc χfl encMachineP`** (from `run_packMachineT`, exactly as
  `EncConf.encSpec_encMachine` from `XProg.run_toMachineT`);
* `okX_encProgram`: the wide loops nest at most `8` deep (the deepest core phase, `tailP`);
* **`descLen_encMachineP : encMachineP.descLen ≤ 2 ^ 325`** (from `states_packMachineT_le` and
  `size_encProgram_tight`).

The clock is in `TapeEncTime`.
-/

namespace AdvancedEncryption.ExpLUT.Prog.TapeEnc

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Pack AdvancedEncryption.ExpLUT.Params
open AdvancedEncryption.ExpLUT.Prog.EncW

/-- The workspace width. -/
abbrev wE : ℕ := 105
/-- The nesting depth of the wide loops. -/
abbrev dE : ℕ := 8

/-- **The packed encryption machine**, `118` tapes. -/
noncomputable def encMachineP : Machine :=
  packMachineT wE dE (encProgram Dc 16 6 eFl) 0 0 (encInputLength Dc)

theorem tapes_encMachineP : encMachineP.tapes = 118 := rfl

/-! ### The depth condition -/

theorem loopDepth_eraseP : ∀ is : List (Fin 326), Pack.Prog.loopDepth (eraseP is) = 0
  | [] => rfl
  | i :: is => by simp only [eraseP, Pack.Prog.loopDepth, loopDepth_eraseP is]; rfl

theorem loopDepth_trimP {k : ℕ} (src tmp : Fin k) (n : ℕ) :
    Pack.Prog.loopDepth (trimP src tmp n) = 0 := by
  simp only [trimP, Pack.Prog.loopDepth, loopDepth_putW]; rfl

set_option maxRecDepth 100000 in
theorem loopDepth_mvP : Pack.Prog.loopDepth SigabaNeo.Tape.Prog.mvP = 1 := by decide +kernel

theorem loopDepth_initProgram : ∀ ops : List InitOp, Pack.Prog.loopDepth (initProgram ops) ≤ 1
  | [] => by decide
  | op :: ops => by
    have ih := loopDepth_initProgram ops
    have hop : Pack.Prog.loopDepth op.program ≤ 1 := by
      cases op with
      | read src dst n =>
        simp only [InitOp.program, readFieldP, Pack.Prog.loopDepth, loopDepth_putW,
          loopDepth_map, loopDepth_mvP]
        simp [SigabaNeo.Tape.Prog.cp, SigabaNeo.Tape.Prog.clr, Pack.Prog.loopDepth]
      | copy dst src => simp [InitOp.program, SigabaNeo.Tape.Prog.cp, Pack.Prog.loopDepth]
      | word dst w => simp [InitOp.program, loopDepth_putW]
    simp only [initProgram, Pack.Prog.loopDepth]
    omega

set_option maxRecDepth 100000 in
theorem loopDepth_mrowP : Pack.Prog.loopDepth SigabaNeo.Tape.Prog.mrowP = 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem loopDepth_hBlkP : Pack.Prog.loopDepth SigabaNeo.Tape.Prog.hBlkP = 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem loopDepth_autBlkP : Pack.Prog.loopDepth SigabaNeo.Tape.Prog.autBlkP = 7 := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem loopDepth_tailP : Pack.Prog.loopDepth SigabaNeo.Tape.Prog.tailP = 8 := by decide +kernel

theorem loopDepth_helperPairsP (D : Dims) : ∀ (j n : ℕ),
    Pack.Prog.loopDepth (helperPairsP D j n) ≤ 5
  | j, 0 => by simp [helperPairsP, SigabaNeo.Tape.Prog.cp, Pack.Prog.loopDepth]
  | j, n + 1 => by
    have ih := loopDepth_helperPairsP D (j + 1) n
    simp only [helperPairsP, helperRoundP, Pack.Prog.loopDepth, loopDepth_putW, loopDepth_hBlkP]
    omega

theorem loopDepth_autBlocksP (D : Dims) : ∀ (j n : ℕ),
    Pack.Prog.loopDepth (autBlocksP D j n) ≤ 7
  | j, 0 => by simp [autBlocksP, SigabaNeo.Tape.Prog.cp, Pack.Prog.loopDepth]
  | j, n + 1 => by
    have ih := loopDepth_autBlocksP D (j + 1) n
    simp only [autBlocksP, autRoundP, Pack.Prog.loopDepth, loopDepth_putW, loopDepth_autBlkP]
    omega

theorem loopDepth_encCoreP (D : Dims) : Pack.Prog.loopDepth (encCoreP D) ≤ 8 := by
  have h1 := loopDepth_helperPairsP D 0 D.b
  have h2 := loopDepth_autBlocksP D 0 D.b
  simp only [encCoreP, Pack.Prog.loopDepth, loopDepth_map, loopDepth_mrowP, loopDepth_tailP]
  omega

set_option maxRecDepth 100000 in
theorem loopDepth_relocateP : Pack.Prog.loopDepth relocateP = 0 := by decide +kernel

/-- The plain suffix of the encryption program nests its loops at most `8` deep. -/
theorem loopDepth_suffix (D : Dims) : Pack.Prog.loopDepth
    (.seq relocateP (.seq (normalizeInputsP D) (cleanCoreP D))) ≤ 8 := by
  have h1 := loopDepth_initProgram (encInitOps D)
  have h2 := loopDepth_encCoreP D
  simp only [Pack.Prog.loopDepth, loopDepth_relocateP, normalizeInputsP, loopDepth_trimP,
    loopDepth_eraseP, cleanCoreP, initializedCoreP, encInitP, loopDepth_map, eraseNonoutput]
  omega

set_option maxRecDepth 100000 in
theorem loopDepth_frameCiphertextP : Pack.XProg.loopDepth frameCiphertextP = 1 := by
  decide +kernel

/-- **The depth condition** of the encryption program. -/
theorem okX_encProgram : OkX wE dE 0 (encProgram Dc 16 6 eFl) := by
  show OkX wE dE 0 (.seq (.seq (.frame prepareFrame (EncIO.prepare Dc 16 6 eFl))
    (.prog (.seq relocateP (.seq (normalizeInputsP Dc) (cleanCoreP Dc))))) frameCiphertextP)
  exact Or.inr ⟨Or.inr ⟨Or.inr (Or.inl le_rfl),
    Or.inr (okP_of_loopDepth 0 _ (by have := loopDepth_suffix Dc; show 0 + _ ≤ 8; omega))⟩,
    okX_of_loopDepth 0 _ (by rw [loopDepth_frameCiphertextP]; decide)⟩

/-! ### The specification -/

/-- **The packed encryption machine meets the exact encryption specification.** -/
theorem encSpec_encMachineP : EncSpec Dc χc χc χfl encMachineP := by
  rw [EncConf.χc_eq, EncConf.χfl_eq]
  intro mpk x μ
  rw [encMachineP, run_packMachineT (by norm_num) _ okX_encProgram (wf_encProgram Dc 16 6 eFl) 0 0
    (encInputLength Dc) _ (by rw [length_encInput]),
    law_encProgram Dc (by norm_num) (by show 6 ≤ Kc; rw [Kc_def]; norm_num) (by norm_num)
      (by show eFl < Kc; rw [eFl_def, Kc_def]; norm_num) (by show 0 < 22; norm_num)
      (by show 2 ≤ 2 ^ 24; norm_num) (by show (2 : ℕ) ^ 14 * 128 ≤ 2 * 2 ^ 24; norm_num),
    PMF.map_comp]
  congr 1

/-! ### The description length -/

set_option exponentiation.threshold 2000 in
theorem descLen_enc_num : 6 * (stA 105 326 * (2 ^ 105 + 2 ^ 101) + 96 * 326 + 254) * 3 ^ 118 *
    (4 + 4 * 118 + 126) ≤ 2 ^ 325 := by
  unfold stA; norm_num

set_option exponentiation.threshold 2000 in
/-- **The packed encryption machine has a description of at most `2^325` bits.** -/
theorem descLen_encMachineP : encMachineP.descLen ≤ 2 ^ 325 := by
  have hS : (encProgram Dc 16 6 eFl).size ≤ 2 ^ 105 + 2 ^ 101 := by
    have := EncConf.size_encProgram_tight; omega
  have h := descLen_packMachineT_le (w := wE) (D := dE) (encProgram Dc 16 6 eFl) 0 0
    (encInputLength Dc) (m := 126) hS le_rfl (by unfold stA; norm_num)
  exact h.trans descLen_enc_num

end AdvancedEncryption.ExpLUT.Prog.TapeEnc
