import PE.Impl.ExpLUT.Prog.SetupSize
import PE.Impl.ExpLUT.Prog.EncMachine
import PE.Impl.DualUse.Prog.SetupEncDescA
import SigabaNeo.Lib.Machines.Prog.FrameSize

/-! # State counts and description length of the concrete encryption machine -/
namespace AdvancedEncryption.ExpLUT.Prog.EncW
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Prog

theorem size_eraseP (is : List (Fin 326)) :
    (eraseP is).size = 36 + 36 * is.length := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [eraseP, Prog.size, clr, Prim.pad, List.length_cons, ih]
    omega

theorem size_eraseNonoutput : eraseNonoutput.size = 11736 := by
  simp [eraseNonoutput, size_eraseP]

theorem size_relocateP : relocateP.size = 144 := rfl

theorem size_frameCiphertextP : frameCiphertextP.size ≤ 10000 := by decide +kernel

variable (D : Dims)

theorem size_parse_le : EncIO.parse.size ≤ 10000 := by decide +kernel

/-- Repetition counters have logarithmic state cost, even for the large coin queues. -/
theorem size_prepare_le (η L e : ℕ) {m : ℕ}
    (hs : nEncSmall D * D.N < 2 ^ m) (hf : nFl D * D.N < 2 ^ m)
    (hN : D.N < 2 ^ m) :
    (EncIO.prepare D η L e).size ≤ 2 * (cbdPM η L D.K).size +
      (AdvancedEncryption.DualUse.Prog.entF D.K e).size + 585 * m + 10441 := by
  have h1 := size_repF_le (cbdPM η L D.K) hs
  have h2 := size_repF_le (AdvancedEncryption.DualUse.Prog.entF D.K e) hf
  have h3 := size_repF_le (cbdPM η L D.K) hN
  have hp := size_parse_le
  simp only [EncIO.prepare, encCoinsP, cbdManyP, floodManyP, cbdRP,
    XProg.size_seq, XProg.size_frame, XProg.size_prog]
  omega

theorem size_trimP (src tmp : Fin 326) (n : ℕ) :
    (trimP src tmp n).size = 144 + 60 * n := by
  simp only [trimP, Prog.size, size_putW_init, List.length_replicate, Prim.pad, cp, clr]
  omega

theorem size_normalizeInputsP : (normalizeInputsP D).size ≤
    20000 + 60 * (coinLength D + publicLength D) := by
  have hl : inputScratch.length ≤ 326 := (List.length_filter_le _ _).trans (by simp)
  simp only [normalizeInputsP, Prog.size, size_trimP, size_eraseP]
  omega

/-- Count the core, literal initialization, sampler/parser, and cleanup. -/
theorem size_encProgram_le (η L e : ℕ) :
    (encProgram D η L e).size ≤ (EncIO.prepare D η L e).size +
      ((encInitOps D).map InitOp.cost).sum + (encCoreP D).size + (normalizeInputsP D).size + 21916 := by
  have h := size_frameCiphertextP
  simp only [encProgram, encryptionP, widePrepare, cleanCoreP,
    XProg.size_seq, XProg.size_frame, XProg.size_prog, Prog.size,
    size_relocateP, size_eraseNonoutput, size_initializedCoreP]
  omega

/-- Description length includes all 326 tapes of the compiled machine. -/
theorem descLen_encMP_le (η L e : ℕ) {B : ℕ}
    (hB : (EncIO.prepare D η L e).size + ((encInitOps D).map InitOp.cost).sum +
      (encCoreP D).size + (normalizeInputsP D).size + 21920 ≤ B) :
    (encMP D η L e).descLen ≤ 6 * B * 3 ^ 326 * (4 + 4 * 326 + B) := by
  have hs := size_encProgram_le D η L e
  have heq : (encMP D η L e).descLen =
      6 * ((encProgram D η L e).size + 4) * 3 ^ 326 * 3 ^ 0 *
        Machine.entryBits 326 ((encProgram D η L e).size + 4) 0 := by
    rw [Machine.descLen, encMP, XProg.states_toMachineT, XProg.card_state]
    rfl
  rw [heq]
  exact AdvancedEncryption.DualUse.Prog.descLen_arithA (by omega)

set_option exponentiation.threshold 2000 in
/-- Numerical budget for a state bound of `2^112`; its premise is discharged separately. -/
theorem descLen_encMP_le_of_size (η L e : ℕ)
    (hs : (encProgram D η L e).size + 4 ≤ 2 ^ 112) :
    (encMP D η L e).descLen ≤ 2 ^ 744 := by
  have heq : (encMP D η L e).descLen =
      6 * ((encProgram D η L e).size + 4) * 3 ^ 326 * 3 ^ 0 *
        Machine.entryBits 326 ((encProgram D η L e).size + 4) 0 := by
    rw [Machine.descLen, encMP, XProg.states_toMachineT, XProg.card_state]
    rfl
  rw [heq]
  exact (AdvancedEncryption.DualUse.Prog.descLen_arithA hs).trans (by norm_num)

end AdvancedEncryption.ExpLUT.Prog.EncW
