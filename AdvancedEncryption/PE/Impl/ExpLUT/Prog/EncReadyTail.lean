import PE.Impl.ExpLUT.Prog.EncReady
/-! # Data conditions of the initialized encryption tail -/
namespace AdvancedEncryption.ExpLUT.Prog.EncW
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Lattices.Algo.NegaG SigabaNeo.Tape SigabaNeo.Tape.Prog Matrix
open PE.BranchingProgram
variable (D : Dims) (mpk : MPKt D) (x : Attribute w8) (μ : Bool)
  (r : EncCoins (setting D) (Wb D) (Jh D) Pos)

/-- The tail's rotation-template lookup, without evaluating any store contents. -/
theorem τT_tailSlot (S : Store 321) (i : Fin 8) :
    τT (S ∘ tailSlot) i.val = (S (tailSlot ⟨17 + i.val, by omega⟩)).length := by
  fin_cases i <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_tail_secret : readyCore D mpk x μ r (tailSlot 1) = wd D r.s := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, wd]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_tail_one : readyCore D mpk x μ r (tailSlot 16) = wd D 1 := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, wd]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_tail_message : readyCore D mpk x μ r (tailSlot 15) = [μ] := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, wd]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_tail_zero : readyCore D mpk x μ r (tailSlot 37) = List.replicate (D.N * D.K) false := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, wd]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_tail_entries : (readyCore D mpk x μ r (tailSlot 34)).length = D.K + D.K + (D.K + D.K) := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, wd]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_tail_positions : (readyCore D mpk x μ r (tailSlot 35)).length = 16 := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, wd]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_tail_xBot : readyCore D mpk x μ r (tailSlot 2) = encAttribute w8 x := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, wd]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_tail_xDig : readyCore D mpk x μ r (tailSlot 3) = encAttribute w8 x := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, wd]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_tail_aBot : readyCore D mpk x μ r (tailSlot 4) = (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc mpk.a := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, wd]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_tail_aDig : readyCore D mpk x μ r (tailSlot 5) = (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc mpk.a := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, wd]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_tail_aCopy : readyCore D mpk x μ r (tailSlot 6) = (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc mpk.a := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, wd]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_tail_eBot : readyCore D mpk x μ r (tailSlot 7) = (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc r.ein := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, wd]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_tail_eDig : readyCore D mpk x μ r (tailSlot 8) = (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc r.ein := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, wd]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_tail_matrices : readyCore D mpk x μ r (tailSlot 9) = (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).enc mpk.Ain := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, wd]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_tail_errors : readyCore D mpk x μ r (tailSlot 10) = (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc r.edin := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, wd]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_tail_initialMatrix : readyCore D mpk x μ r (tailSlot 11) = (matE D (Fin 2) (Col D.K)).enc mpk.A0 := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, wd]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_tail_initialError : readyCore D mpk x μ r (tailSlot 12) = (vecE D (Col D.K)).enc r.e0 := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, wd]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_tail_messageVector : readyCore D mpk x μ r (tailSlot 13) = (vecE D (Fin 2)).enc mpk.d := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, wd]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem ready_tail_messageError : readyCore D mpk x μ r (tailSlot 14) = wd D r.em := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape, wd]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem ready_rotationWord0 : readyCore D mpk x μ r (tailSlot 17) =
    List.replicate (rotationLength D 0) false := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape]

set_option maxRecDepth 100000 in
private theorem ready_rotation0 : τT (readyCore D mpk x μ r ∘ tailSlot) 0 =
    2 * D.N - wSt * 2 ^ (7 - 0) := by
  have ht : τT (readyCore D mpk x μ r ∘ tailSlot) 0 =
      (readyCore D mpk x μ r (tailSlot 17)).length :=
    τT_tailSlot (readyCore D mpk x μ r) (0 : Fin 8)
  rw [ht, ready_rotationWord0, List.length_replicate]
  exact rotationLength_eq D (0 : Fin 8)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem ready_rotationWord1 : readyCore D mpk x μ r (tailSlot 18) =
    List.replicate (rotationLength D 1) false := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape]

set_option maxRecDepth 100000 in
private theorem ready_rotation1 : τT (readyCore D mpk x μ r ∘ tailSlot) 1 =
    2 * D.N - wSt * 2 ^ (7 - 1) := by
  have ht : τT (readyCore D mpk x μ r ∘ tailSlot) 1 =
      (readyCore D mpk x μ r (tailSlot 18)).length :=
    τT_tailSlot (readyCore D mpk x μ r) (1 : Fin 8)
  rw [ht, ready_rotationWord1, List.length_replicate]
  exact rotationLength_eq D (1 : Fin 8)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem ready_rotationWord2 : readyCore D mpk x μ r (tailSlot 19) =
    List.replicate (rotationLength D 2) false := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape]

set_option maxRecDepth 100000 in
private theorem ready_rotation2 : τT (readyCore D mpk x μ r ∘ tailSlot) 2 =
    2 * D.N - wSt * 2 ^ (7 - 2) := by
  have ht : τT (readyCore D mpk x μ r ∘ tailSlot) 2 =
      (readyCore D mpk x μ r (tailSlot 19)).length :=
    τT_tailSlot (readyCore D mpk x μ r) (2 : Fin 8)
  rw [ht, ready_rotationWord2, List.length_replicate]
  exact rotationLength_eq D (2 : Fin 8)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem ready_rotationWord3 : readyCore D mpk x μ r (tailSlot 20) =
    List.replicate (rotationLength D 3) false := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape]

set_option maxRecDepth 100000 in
private theorem ready_rotation3 : τT (readyCore D mpk x μ r ∘ tailSlot) 3 =
    2 * D.N - wSt * 2 ^ (7 - 3) := by
  have ht : τT (readyCore D mpk x μ r ∘ tailSlot) 3 =
      (readyCore D mpk x μ r (tailSlot 20)).length :=
    τT_tailSlot (readyCore D mpk x μ r) (3 : Fin 8)
  rw [ht, ready_rotationWord3, List.length_replicate]
  exact rotationLength_eq D (3 : Fin 8)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem ready_rotationWord4 : readyCore D mpk x μ r (tailSlot 21) =
    List.replicate (rotationLength D 4) false := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape]

set_option maxRecDepth 100000 in
private theorem ready_rotation4 : τT (readyCore D mpk x μ r ∘ tailSlot) 4 =
    2 * D.N - wSt * 2 ^ (7 - 4) := by
  have ht : τT (readyCore D mpk x μ r ∘ tailSlot) 4 =
      (readyCore D mpk x μ r (tailSlot 21)).length :=
    τT_tailSlot (readyCore D mpk x μ r) (4 : Fin 8)
  rw [ht, ready_rotationWord4, List.length_replicate]
  exact rotationLength_eq D (4 : Fin 8)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem ready_rotationWord5 : readyCore D mpk x μ r (tailSlot 22) =
    List.replicate (rotationLength D 5) false := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape]

set_option maxRecDepth 100000 in
private theorem ready_rotation5 : τT (readyCore D mpk x μ r ∘ tailSlot) 5 =
    2 * D.N - wSt * 2 ^ (7 - 5) := by
  have ht : τT (readyCore D mpk x μ r ∘ tailSlot) 5 =
      (readyCore D mpk x μ r (tailSlot 22)).length :=
    τT_tailSlot (readyCore D mpk x μ r) (5 : Fin 8)
  rw [ht, ready_rotationWord5, List.length_replicate]
  exact rotationLength_eq D (5 : Fin 8)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem ready_rotationWord6 : readyCore D mpk x μ r (tailSlot 23) =
    List.replicate (rotationLength D 6) false := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape]

set_option maxRecDepth 100000 in
private theorem ready_rotation6 : τT (readyCore D mpk x μ r ∘ tailSlot) 6 =
    2 * D.N - wSt * 2 ^ (7 - 6) := by
  have ht : τT (readyCore D mpk x μ r ∘ tailSlot) 6 =
      (readyCore D mpk x μ r (tailSlot 23)).length :=
    τT_tailSlot (readyCore D mpk x μ r) (6 : Fin 8)
  rw [ht, ready_rotationWord6, List.length_replicate]
  exact rotationLength_eq D (6 : Fin 8)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem ready_rotationWord7 : readyCore D mpk x μ r (tailSlot 24) =
    List.replicate (rotationLength D 7) false := by
  simp [readyCore, preparedState, loadedState, initEval, publicWrites, coinWrites, templateInitOps, zeroInit, InitOp.eval, finRange8, bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape]

set_option maxRecDepth 100000 in
private theorem ready_rotation7 : τT (readyCore D mpk x μ r ∘ tailSlot) 7 =
    2 * D.N - wSt * 2 ^ (7 - 7) := by
  have ht : τT (readyCore D mpk x μ r ∘ tailSlot) 7 =
      (readyCore D mpk x μ r (tailSlot 24)).length :=
    τT_tailSlot (readyCore D mpk x μ r) (7 : Fin 8)
  rw [ht, ready_rotationWord7, List.length_replicate]
  exact rotationLength_eq D (7 : Fin 8)

theorem ready_tail_rotation : ∀ i < 8,
    τT (readyCore D mpk x μ r ∘ tailSlot) i = 2 * D.N - wSt * 2 ^ (7 - i) := by
  intro i hi
  interval_cases i
  · exact ready_rotation0 D mpk x μ r
  · exact ready_rotation1 D mpk x μ r
  · exact ready_rotation2 D mpk x μ r
  · exact ready_rotation3 D mpk x μ r
  · exact ready_rotation4 D mpk x μ r
  · exact ready_rotation5 D mpk x μ r
  · exact ready_rotation6 D mpk x μ r
  · exact ready_rotation7 D mpk x μ r

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The complete initialized data invariant, assembled from individually checked tape facts. -/
theorem ready_tailData : TailInput D (readyCore D mpk x μ r ∘ tailSlot) mpk x μ r where
  secret := ready_tail_secret D mpk x μ r
  one := ready_tail_one D mpk x μ r
  message := ready_tail_message D mpk x μ r
  zero := ready_tail_zero D mpk x μ r
  entries := ready_tail_entries D mpk x μ r
  positions := ready_tail_positions D mpk x μ r
  xBot := ready_tail_xBot D mpk x μ r
  xDig := ready_tail_xDig D mpk x μ r
  aBot := ready_tail_aBot D mpk x μ r
  aDig := ready_tail_aDig D mpk x μ r
  aCopy := ready_tail_aCopy D mpk x μ r
  eBot := ready_tail_eBot D mpk x μ r
  eDig := ready_tail_eDig D mpk x μ r
  matrices := ready_tail_matrices D mpk x μ r
  errors := ready_tail_errors D mpk x μ r
  initialMatrix := ready_tail_initialMatrix D mpk x μ r
  initialError := ready_tail_initialError D mpk x μ r
  messageVector := ready_tail_messageVector D mpk x μ r
  messageError := ready_tail_messageError D mpk x μ r
  rotation := ready_tail_rotation D mpk x μ r

end AdvancedEncryption.ExpLUT.Prog.EncW
