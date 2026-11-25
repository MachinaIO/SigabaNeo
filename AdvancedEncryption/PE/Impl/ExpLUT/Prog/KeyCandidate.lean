import PE.Impl.ExpLUT.Prog.KeyEvalInit
/-! Candidate sampling that preserves the evaluated public matrix and master key. -/
namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib

noncomputable def candidateInitOps (D : Dims) (B : ℕ) : List (Fin 64 × TemplateWord) :=
  [(rTBk, .zeros B), (rTKmB, .zeros (D.K - B)), (rTN, .zeros D.N),
   (rC2, .bits (encRM D.N D.K (Negacyclic.ofCoeffs fun _ ↦ cB D B))),
   (rDqn, .zeros (nPI D)), (rZ, .zeros (D.N * D.K))]

/-- Initialize the decoder, keeping its coins on37 and saved inputs on8/14/16. -/
noncomputable def candidateInitC (D : Dims) (B : ℕ) : Code :=
  .seq (.clr 6) <| .seq (bitsC 5 rB1 6) (templateOpsC (candidateInitOps D B))

theorem wf_candidateInitC (D : Dims) (B : ℕ) : (candidateInitC D B).WFc :=
  ⟨trivial, by repeat constructor, wf_templateOpsC _⟩

theorem exec_candidateInitC (D : Dims) (B : ℕ) (w : St) :
    exec D.N D.K (candidateInitC D B) w = templateOpsState (candidateInitOps D B)
      (Function.update (Function.update (Function.update w 6 []) 5 [true]) rB1 [false]) := by
  rw [candidateInitC, exec_seq, exec_seq,
    exec_bitsC _ _ _ (by decide) (by decide) (by decide) _ (by simp)]
  apply exec_templateOpsC
  · simp [candidateInitOps]
  · simp
  · simp

/-- Decode the fair bits and place the candidate on9 for the proposal machine. -/
noncomputable def candidateC (D : Dims) (B : ℕ) : Code :=
  .seq (candidateInitC D B) <| .seq decQC (.cp 9 rDq)

theorem wf_candidateC (D : Dims) (B : ℕ) : (candidateC D B).WFc :=
  ⟨wf_candidateInitC D B, by repeat constructor, trivial⟩

theorem candidateC_saved (D : Dims) (B : ℕ) (r : Fin 64)
    (hr : r = 8 ∨ r = 14 ∨ r = 16) : (candidateC D B).writes r = false := by
  have hf : (templateOpsC (candidateInitOps D B)).writes r = false := by
    apply templateOpsC_frame
    rcases hr with rfl | rfl | rfl <;> simp [candidateInitOps]
  rcases hr with rfl | rfl | rfl <;>
    simp [candidateC, candidateInitC, bitsC, Code.writes, hf, decQC, decQBody, decC, decBody]

theorem exec_candidateC (D : Dims) (B : ℕ) (hBK : B ≤ D.K) (w : St)
    (cs : List Bool) (hcs : cs.length = nPI D * D.N * B) (hcoin : w rCoin = cs) :
    exec D.N D.K (candidateC D B) w 9 =
      encL D.N D.K (Enum.list.map (coinDec D B cs)) := by
  let v := exec D.N D.K (candidateInitC D B) w
  have hv := exec_candidateInitC D B w
  have he : exec D.N D.K decQC v rDq =
      encL D.N D.K (decList D.N D.K cs B (cB D B) (nPI D)) := by
    apply (exec_decQC D.K_pos v cs [] B (nPI D) hBK
      (by simpa [Nat.mul_assoc] using hcs) (cB D B) ?_ ?_ ?_ ?_ ?_ ?_).1
    all_goals simp [v, hv, templateOpsState, candidateInitOps, TemplateWord.value, hcoin]
  rw [candidateC, exec_seq, exec_seq]
  change exec D.N D.K decQC v rDq = _
  rw [map_coinDec]
  exact he

theorem candidateC_templates (D : Dims) (B : ℕ) (w : St) :
    exec D.N D.K (candidateC D B) w rB1 = [false] ∧
    exec D.N D.K (candidateC D B) w rZ = encRM D.N D.K 0 := by
  have hf (r : Fin 64) (hr : r = rB1 ∨ r = rZ) :
      (Code.seq decQC (.cp 9 rDq)).writes r = false := by
    rcases hr with rfl | rfl <;> decide
  have he (r : Fin 64) (hr : r = rB1 ∨ r = rZ) :
      exec D.N D.K (candidateC D B) w r = exec D.N D.K (candidateInitC D B) w r := by
    change exec D.N D.K (.seq (candidateInitC D B) (.seq decQC (.cp 9 rDq))) w r = _
    rw [exec_seq, exec_writes _ _ _ (hf r hr)]
  rw [he rB1 (Or.inl rfl), he rZ (Or.inr rfl)]
  simp [exec_candidateInitC, templateOpsState, candidateInitOps, TemplateWord.value, encRM_zero]

/-- Real decoder execution supplies every input required by the single-try key machine. -/
theorem candidateC_ready (D : Dims) (B : ℕ) (hBK : B ≤ D.K)
    (msk : MSKt D) (F : BP Pos) (w : St) (cs : List Bool)
    (hcs : cs.length = nPI D * D.N * B) (hcoin : w rCoin = cs)
    (hM : w 14 = (mpkEnc D).enc msk.mpk)
    (hA : w 8 = encL D.N D.K (matL (keyPK (helperMap D) msk.mpk F)))
    (hT : w 16 = (matE D (Wb D) (Fin D.K)).enc msk.T) :
    TryReady D msk F (coinDec D B cs) (exec D.N D.K (candidateC D B) w) := by
  refine ⟨?_, ?_, ?_, exec_candidateC D B hBK w cs hcs hcoin,
    (candidateC_templates D B w).1, (candidateC_templates D B w).2⟩
  · exact (exec_writes _ _ _ (candidateC_saved D B 14 (by simp))).trans hM
  · exact (exec_writes _ _ _ (candidateC_saved D B 8 (by simp))).trans hA
  · exact (exec_writes _ _ _ (candidateC_saved D B 16 (by simp))).trans hT

/-- The complete deterministic tail after EvalPK, parameterized only by its fair coins. -/
noncomputable def candidateTryC (D : Dims) (B r : ℕ) : Code :=
  .seq (candidateC D B) (tryKeyC D B r)

theorem exec_candidateTryC (D : Dims) (B r : ℕ) (hB : 2 ^ B ≤ D.q)
    (hBK : B ≤ D.K) (hr : 2 * r < 2 ^ B) (hq : 2 ^ (B + 1) ≤ D.q)
    (hcount : 2 * (D.K - B) < D.q) (msk : MSKt D) (F : BP Pos)
    (w : St) (cs : List Bool) (hcs : cs.length = nPI D * D.N * B)
    (hcoin : w rCoin = cs) (hM : w 14 = (mpkEnc D).enc msk.mpk)
    (hA : w 8 = encL D.N D.K (matL (keyPK (helperMap D) msk.mpk F)))
    (hT : w 16 = (matE D (Wb D) (Fin D.K)).enc msk.T) :
    exec D.N D.K (candidateTryC D B r) w 19 =
      (keyEnc D).enc (attemptOutput D (kbOf D B hB r) msk F (coinDec D B cs)) := by
  have h := candidateC_ready D B hBK msk F w cs hcs hcoin hM hA hT
  rw [candidateTryC, exec_seq]
  exact exec_tryKeyC_output D D.hK B r hB hBK hr hq hcount msk F _ _
    h.publicKey h.evaluated h.trapdoor h.candidate h.bit h.zero

theorem wf_candidateTryC (D : Dims) (B r : ℕ) : (candidateTryC D B r).WFc :=
  ⟨wf_candidateC D B, wf_tryKeyC D B r⟩

open Cslib.Probability Cslib.BitString

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual initialized decoder and attempt realize the fair-coin KeyGen law. -/
theorem map_coins_candidateTryC (D : Dims) (B r : ℕ) (hB : 2 ^ B ≤ D.q)
    (hBK : B ≤ D.K) (hr : 2 * r < 2 ^ B) (hq : 2 ^ (B + 1) ≤ D.q)
    (hcount : 2 * (D.K - B) < D.q) (msk : MSKt D) (F : BP Pos) (w : St)
    (hM : w 14 = (mpkEnc D).enc msk.mpk)
    (hA : w 8 = encL D.N D.K (matL (keyPK (helperMap D) msk.mpk F)))
    (hT : w 16 = (matE D (Wb D) (Fin D.K)).enc msk.T) :
    (uniformList (nPI D * D.N * B)).map
      (fun cs ↦ exec D.N D.K (candidateTryC D B r) (Function.update w rCoin cs) 19) =
    (keyGenLaw (S := setting D) (kbOf D B hB r).Big (kbOf D B hB r).Small
      (kbOf D B hB r).hBig gadDec (helperMap D) msk F).map (keyEnc D).enc := by
  rw [← map_uniform_attemptOutput, ← map_uniformList_coinDec_kbOf D B hB r,
    PMF.map_comp, PMF.map_comp]
  apply PMF.map_congr_support
  intro cs hcs
  apply exec_candidateTryC D B r hB hBK hr hq hcount msk F _ cs
    (length_of_mem_support_uniformList hcs)
  · simp
  · simpa using hM
  · simpa using hA
  · simpa using hT

/-- Evaluate the public key and arrange the saved inputs for candidate sampling. -/
noncomputable def keyEvalPrepareC (D : Dims) : Code :=
  .seq (evalReadyC D) <| .seq (.cp 8 rA) (.cp 14 17)

theorem wf_keyEvalPrepareC (D : Dims) : (keyEvalPrepareC D).WFc :=
  ⟨wf_evalReadyC D, trivial, trivial⟩

theorem exec_keyEvalPrepareC (D : Dims) (hb : D.b = 22) (hn : 2 ^ D.b ≤ D.q)
    (msk : MSKt D) (C : List Bool) (w : St)
    (hM : w 17 = (mpkEnc D).enc msk.mpk)
    (hT : w 16 = (matE D (Wb D) (Fin D.K)).enc msk.T) (hp : w rCs = C) :
    let v := exec D.N D.K (keyEvalPrepareC D) w
    v 14 = (mpkEnc D).enc msk.mpk ∧
    v 8 = encL D.N D.K (matL (keyPK (helperMap D) msk.mpk (bpOf (progOf C)))) ∧
    v 16 = (matE D (Wb D) (Fin D.K)).enc msk.T := by
  have hA := exec_evalReadyC D hb hn msk.mpk C w hM hp
  have hM' := (exec_writes (N := D.N) (K := D.K) _ w _
    (evalReadyC_saved D 17 (Or.inr rfl))).trans hM
  have hT' := (exec_writes (N := D.N) (K := D.K) _ w _
    (evalReadyC_saved D 16 (Or.inl rfl))).trans hT
  simpa [keyEvalPrepareC, exec_seq, exec_cp] using And.intro hM' (And.intro hA hT')

end AdvancedEncryption.ExpLUT.Prog
