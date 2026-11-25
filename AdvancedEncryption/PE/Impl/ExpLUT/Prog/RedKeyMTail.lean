import PE.Impl.ExpLUT.Prog.RedKeyU
import PE.Impl.ExpLUT.Prog.KeyOutput

/-!
# `KGsim` on the VM (module 8, back end): sample, simulated try, output

The back end of the reduction's key component, on the MVM's `105` tapes (the analogue of F3's
`KeyCore.outputProgram` with the simulated try of module 4):

  `rkTailP = sampleP ; compile (candidateC ; simTryKeyC (uC)) ; compile packKeyC ; post`.

**Input contract `RkMidReady`** (the state the middle phases must reach): register `14` = the
public-key word, `8` = `matL A_F` (`A_F = keyPK M mpk F`), `16` = the rows of
`X = simX M (h1Of mpk) A_F R̂`.

* `uC_keeps_mpk`, `simTryKeyC_keeps_mpk`: the try never writes register `14`;
* **`law_rkTailP`**: `law rkTailP (enc w) = ((keyLaw … mpk F (simTrap M mpk F R̂)).map
  keyOfOutput).map (inputStore 0 ∘ skEnc (mpk, ·))` (generic `D`, box conditions as hypotheses);
* **`law_rkTailP_Dc`**: at `Dc` with `kbDc`, all conditions discharged.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)
open Cslib.Probability Cslib.BitString

variable {D : Dims}

/-! ### The try keeps the public key -/

theorem uC_keeps_mpk : (uC D).writes 14 = false := by
  have hb := bRowC_frame D 14 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have hu := writes_false_of_frame (uRowsC_frame D.K (rowExponent D)
    (List.ofFn fun i : Fin (setting D).E.W => i.val)) (r := 14) (by decide)
  have hd := writes_false_of_frame (c := decRowsC) (r := 14)
    (l := [rDq, rQa, rQb, rQc, rQx, rIa, rY, rZq, rU, rCK, rTd])
    (by simp only [decRowsC, decRowBodyC, decRowLoadC, decomposeC, digQC, digQBody, Code.writes]
        decide)
    (by decide)
  have ho := writes_false_of_frame (c := ringOneC D.N D.K) (r := 14) (l := [5, 6, 7])
    (by simp only [ringOneC, bitsC, Code.writes, natC_writes_eq]; decide) (by decide)
  simp only [uC, Code.writes, hb, hu, hd, ho, natC_writes_eq, Bool.or_false, Bool.false_or]
  decide

theorem simTryKeyC_keeps_mpk (B r : ℕ) : (simTryKeyC D (uC D) B r).writes 14 = false := by
  have h2 := natC_writes rVm rB1 (Enum.list (α := ZIdxS D)).length 14 (by decide)
  have h3 := natC_writes rVn rB1 (Enum.list (α := PIdxS D)).length 14 (by decide)
  have h4 : mvSubC.writes 14 = false := by
    cases h : mvSubC.writes 14
    · rfl
    · have := mvSubC_frame 14 h
      simp at this
  have hc : (simCorrectionC D (uC D)).writes 14 = false := by
    simp only [simCorrectionC, Code.writes, uC_keeps_mpk, h2, h3, h4, Bool.or_self]
  have hp : (simProposalC D (uC D)).writes 14 = false := by
    simp only [simProposalC, Code.writes, keyDigitsC_keeps_mpk, hc, Bool.or_false]
    decide
  simp only [simTryKeyC, simProposalKeyC, Code.writes, hp, assembleC_frame D 14 (by decide),
    acceptC_public D B r, Bool.or_self]

/-! ### The back end -/

variable (D)

/-- The deterministic part after the coins: decode the candidate, one simulated try. -/
noncomputable def rkTryC (B r : ℕ) : Code := .seq (candidateC D B) (simTryKeyC D (uC D) B r)

/-- **The back end**: coins, candidate, simulated try, `skEnc (mpk, key)` unframed on tape `0`. -/
noncomputable def rkTailP (B r : ℕ) : XProg 105 :=
  .seq (KeyCore.sampleP (nPI D * D.N * B)) <|
  .seq (compile (rkTryC D B r)) <| .seq (compile packKeyC) (.prog MVM.IO.post)

theorem wf_rkTailP (hK : 2 ≤ D.K) (B r : ℕ) : (rkTailP D B r).WF :=
  ⟨KeyCore.wf_sampleP _, wf_compile _ ⟨wf_candidateC D B, wf_simTryKeyC (uOk_uC hK) B r⟩,
    wf_compile _ wf_packKeyC, ⟨trivial, MVM.IO.wf_setList _ _⟩⟩

variable {D}

/-- **The state the middle phases must reach** (before the coins): the public key, `A_F` and the
rows of `X = simX M (h1Of mpk) A_F R̂`. -/
structure RkMidReady (mpk : MPKt D) (F : BP Pos) (Rh : SimMat (Wb D) (Jh D) (setting D))
    (w : St) : Prop where
  publicKey : w 14 = (mpkEnc D).enc mpk
  evaluated : w 8 = encL D.N D.K (matL (keyPK (helperMap D) mpk F))
  rows : w 16 = encL D.N D.K (rowsWord (α := PIdxS D) (β := ZIdxS D)
    (fun q ic => simX (helperMap D) (h1Of mpk) (keyPK (helperMap D) mpk F) Rh q ic))

/-- After the candidate decoder the try is ready. -/
theorem rkMidReady_candidate (B : ℕ) (hBK : B ≤ D.K) {mpk : MPKt D} {F : BP Pos}
    {Rh : SimMat (Wb D) (Jh D) (setting D)} {w : St} (hw : RkMidReady mpk F Rh w)
    (cs : List Bool) (hcs : cs.length = nPI D * D.N * B) :
    SimTryReady mpk F
      (fun q ic => simX (helperMap D) (h1Of mpk) (keyPK (helperMap D) mpk F) Rh q ic)
      (coinDec D B cs) (exec D.N D.K (candidateC D B) (Function.update w rCoin cs)) := by
  refine ⟨?_, ?_, ?_, ?_, (candidateC_templates D B _).1, (candidateC_templates D B _).2⟩
  · rw [exec_writes _ _ _ (candidateC_saved D B 14 (by simp))]
    simpa using hw.publicKey
  · rw [exec_writes _ _ _ (candidateC_saved D B 8 (by simp))]
    simpa using hw.evaluated
  · rw [exec_writes _ _ _ (candidateC_saved D B 16 (by simp))]
    simpa using hw.rows
  · rw [exec_candidateC D B hBK _ cs hcs (by simp)]
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- **The law of the back end.** -/
theorem law_rkTailP (hK : 2 ≤ D.K) (B r : ℕ) (hB : 2 ^ B ≤ D.q) (hBK : B ≤ D.K)
    (hr : 2 * r < 2 ^ B) (hq : 2 ^ (B + 1) ≤ D.q) (hcount : 2 * (D.K - B) < D.q)
    (mpk : MPKt D) (F : BP Pos) (Rh : SimMat (Wb D) (Jh D) (setting D)) (w : St)
    (hw : RkMidReady mpk F Rh w) :
    (rkTailP D B r).law (enc D.N D.K w) =
      ((keyLaw (S := setting D) (kbOf D B hB r).Big (kbOf D B hB r).Small (kbOf D B hB r).hBig
        gadDec (helperMap D) mpk F (simTrap (helperMap D) mpk F Rh)).map keyOfOutput).map
        (fun k ↦ inputStore (0 : Fin 105) ((skEnc D).enc (mpk, k))) := by
  let tail := fun cs ↦ exec D.N D.K (rkTryC D B r) (Function.update w rCoin cs)
  have hpub (cs : List Bool) : tail cs 14 = (mpkEnc D).enc mpk := by
    simp only [tail, rkTryC, exec_seq]
    rw [exec_writes _ _ _ (simTryKeyC_keeps_mpk B r),
      exec_writes _ _ _ (candidateC_saved D B 14 (by simp))]
    simpa using hw.publicKey
  have hout (cs : List Bool) :
      ((compile packKeyC).seq (.prog MVM.IO.post)).law (enc D.N D.K (tail cs)) =
      PMF.pure (inputStore (0 : Fin 105) ((mpkEnc D).enc mpk ++ tail cs 19)) := by
    rw [XProg.law_seq, law_compile D.N_pos D.K_pos, PMF.pure_bind, XProg.law_prog,
      Prog.law_eq_run_of_coinFree _ MVM.IO.coinFree_post, MVM.IO.run_post, exec_packKeyC, hpub]
    congr 1
    funext t
    simp [io2, inputStore, Function.update_apply]
  have h19 : ∀ cs ∈ (uniformList (nPI D * D.N * B)).support, tail cs 19 =
      (keyEnc D).enc (simAttemptOutput D (kbOf D B hB r) mpk F
        (fun q ic => simX (helperMap D) (h1Of mpk) (keyPK (helperMap D) mpk F) Rh q ic)
        (coinDec D B cs)) := by
    intro cs hcs
    simp only [tail, rkTryC, exec_seq]
    exact exec_simTryKeyC_output hK (uOk_uC hK) B r hB hBK hr hq hcount mpk F _ _ _
      (rkMidReady_candidate B hBK hw cs (length_of_mem_support_uniformList hcs))
  rw [rkTailP, XProg.law_seq, KeyCore.law_sampleP, PMF.bind_map]
  have hc : (((compile (rkTryC D B r)).seq ((compile packKeyC).seq (.prog MVM.IO.post))).law ∘
      fun cs => enc D.N D.K (Function.update w rCoin cs)) =
      PMF.pure ∘ fun cs => inputStore (0 : Fin 105) ((mpkEnc D).enc mpk ++ tail cs 19) := by
    funext cs
    simp only [Function.comp_apply]
    rw [XProg.law_seq, law_compile D.N_pos D.K_pos, PMF.pure_bind]
    exact hout cs
  rw [hc, PMF.bind_pure_comp]
  rw [← map_uniform_simAttemptOutput, PMF.map_comp, ← map_uniformList_coinDec_kbOf D B hB r,
    PMF.map_comp]
  apply PMF.map_congr_support
  intro cs hcs
  simp only [Function.comp_apply, h19 cs hcs]
  rfl

open Params

/-- **The back end at `Dc`.** -/
theorem law_rkTailP_Dc (mpk : MPKt Dc) (F : BP Pos) (Rh : SimMat (Wb Dc) (Jh Dc) (setting Dc))
    (w : St) (hw : RkMidReady mpk F Rh w) :
    (rkTailP Dc Bk rSmall).law (enc Dc.N Dc.K w) =
      ((keyLaw (S := setting Dc) kbDc.Big kbDc.Small kbDc.hBig gadDec (helperMap Dc) mpk F
        (simTrap (helperMap Dc) mpk F Rh)).map keyOfOutput).map
        (fun k ↦ inputStore (0 : Fin 105) ((skEnc Dc).enc (mpk, k))) := by
  rw [kbDc_def]
  exact law_rkTailP (by change 2 ≤ Kc; rw [Kc_def]; norm_num) Bk rSmall hBk_Dc Bk_lt_Kc.le
    small_test_conditions_Dc.1 small_test_conditions_Dc.2.1 small_test_conditions_Dc.2.2
    mpk F Rh w hw

theorem wf_rkTailP_Dc : (rkTailP Dc Bk rSmall).WF :=
  wf_rkTailP Dc (by change 2 ≤ Kc; rw [Kc_def]; norm_num) Bk rSmall

end AdvancedEncryption.ExpLUT.Prog
