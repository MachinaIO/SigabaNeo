import PE.Impl.ExpLUT.Prog.EncInitSpec
/-! # Phase invariants of the initialized encryption store -/
namespace AdvancedEncryption.ExpLUT.Prog.EncW
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Lattices.Algo.NegaG SigabaNeo.Tape SigabaNeo.Tape.Prog Matrix
open PE.BranchingProgram

variable (D : Dims) (mpk : MPKt D) (x : Attribute w8) (μ : Bool)
  (r : EncCoins (setting D) (Wb D) (Jh D) Pos)

/-- The core's initialized store, before any ciphertext field has been produced. -/
noncomputable def readyCore : Store 321 := preparedState D mpk x μ r ∘ coreTape

theorem finRange8 : List.finRange 8 = [0, 1, 2, 3, 4, 5, 6, 7] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_bOK : BPhaseOK D (readyCore D mpk x μ r ∘ bSlot) := by
  constructor
  · intro i hi
    fin_cases i <;> simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, Function.comp_def] at hi ⊢
  all_goals simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, Function.comp_def]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_helperOK : HelperOK D (readyCore D mpk x μ r ∘ helperSlot) := by
  constructor
  · intro i hi
    fin_cases i <;> simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, Function.comp_def] at hi ⊢
  all_goals simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, Function.comp_def]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_autOK : AutBlockOK D (readyCore D mpk x μ r ∘ autSlot) := by
  constructor
  · intro i hi
    fin_cases i <;> simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, Function.comp_def] at hi ⊢
  all_goals simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, Function.comp_def]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_tailOK : TailOK D.K D.N (readyCore D mpk x μ r ∘ tailSlot) := by
  constructor
  · intro i hi
    fin_cases i <;> simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, Function.comp_def] at hi ⊢
  all_goals simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, Function.comp_def, FixedEnc.length]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_bData :
    let S := readyCore D mpk x μ r ∘ bSlot
    S 1 = wd D r.s ∧ (S 2).length = D.N * D.K ∧ S 3 = wd D 0 ∧
    S 4 = (matE D (Fin 2) (BCol (Wb D) D.K)).enc mpk.B ∧
    S 5 = (vecE D (BCol (Wb D) D.K)).enc r.eb := by
  have hz : (rEnc D).enc 0 = List.replicate (D.N * D.K) false := MVM.encRM_zero D.N D.K
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, Function.comp_def, wd, hz]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_helperData :
    let S := readyCore D mpk x μ r ∘ helperSlot
    S 1 = wd D r.s ∧ S 7 = wd D 1 ∧ (S 4).length = gD D ∧ S 5 = [] ∧ S 6 = [] ∧
    S 2 = (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc mpk.H ∧
    S 3 = (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc r.eh := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, Function.comp_def, wd]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_autData :
    let S := readyCore D mpk x μ r ∘ autSlot
    S 1 = wd D r.s ∧ S 9 = wd D 1 ∧ (S 6).length = gD D ∧ S 7 = [] ∧ S 8 = [] ∧
    S 2 = (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc mpk.H ∧
    S 3 = (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc r.eh ∧
    S 4 = (FixedEnc.fun (α := Fin D.b)
      (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).enc mpk.Aaut ∧
    S 5 = (FixedEnc.fun (α := Fin D.b)
      (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc r.eaut := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, Function.comp_def, wd]


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_output : readyCore D mpk x μ r 0 =
    List.replicate (fixedSize (ctEnc D)) false := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape]

end AdvancedEncryption.ExpLUT.Prog.EncW
