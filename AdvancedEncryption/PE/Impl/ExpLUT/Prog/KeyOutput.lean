import PE.Impl.ExpLUT.Prog.KeyCore
/-! Preservation and assembly of the complete secret-key output. -/
namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib Cslib.Probability Cslib.BitString

theorem keyDigitsC_public (D : Dims) : (keyDigitsC D).writes 14 = false := by
  simp only [keyDigitsC, Code.writes, publicRowsC_frame D 14 (by simp),
    targetC_frame D 14 (by decide) (by decide) (by decide) (by decide),
    natC_writes rQc rB1 _ 14 (by decide), natC_writes rQk rB1 _ 14 (by decide),
    decRowsC, decRowBodyC, decRowLoadC, decomposeC, digQC, digQBody]
  decide

theorem correctionCoordC_public (D : Dims)
    (q : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W) :
    (correctionCoordC D q).writes 14 = false := by
  rcases q with ⟨i, row⟩ | q
  · simp only [correctionCoordC, correctionInlC, Code.writes,
      correctionLoadC_frame D i row 14 (by decide),
      natC_writes rQc rB1 _ 14 (by decide), natC_writes rQk rB1 _ 14 (by decide),
      autDotC, autQC, autQBody, ipC, ipBody]
    decide
  · apply loadFamilyC_frame <;> decide

theorem correctionC_public (D : Dims) : (correctionC D).writes 14 = false := by
  have h : ∀ qs, (correctionAppendC D qs).writes 14 = false := by
    intro qs
    induction qs with
    | nil => rfl
    | cons q qs ih => simp [correctionAppendC, Code.writes, correctionCoordC_public, ih]
  change (false || (correctionAppendC D Enum.list).writes 14) = false
  exact h Enum.list

theorem acceptC_public (D : Dims) (B r : ℕ) : (acceptC D B r).writes 14 = false := by
  simp only [acceptC, acceptInitC, Code.writes, radiusC_frame D.N D.K r 14 (by decide),
    natC_writes rTBk rB1 _ 14 (by decide), natC_writes rTKB rB1 _ 14 (by decide),
    natC_writes rQc rB1 _ 14 (by decide), natC_writes 19 rB1 _ 14 (by decide)]
  decide

theorem tryKeyC_public (D : Dims) (B r : ℕ) : (tryKeyC D B r).writes 14 = false := by
  simp [tryKeyC, proposalKeyC, proposalC, Code.writes, keyDigitsC_public,
    correctionC_public, assembleC_frame D 14 (by decide), acceptC_public]

theorem candidateTryC_public (D : Dims) (B r : ℕ) :
    (candidateTryC D B r).writes 14 = false := by
  simp [candidateTryC, Code.writes, candidateC_saved D B 14 (by simp), tryKeyC_public]

/-- Concatenate the retained public key and the final sampled key. -/
def packKeyC : Code := .seq (.cp 0 14) (.app 0 19)

theorem wf_packKeyC : packKeyC.WFc := ⟨trivial, trivial⟩

theorem exec_packKeyC {N K : ℕ} (w : St) :
    exec N K packKeyC w 0 = w 14 ++ w 19 := by simp [packKeyC, exec_seq, exec_cp, exec_app]

namespace KeyCore
open SigabaNeo.Tape.Prog SigabaNeo.Tape.XProg

/-- The complete secret-key word, with all workspace erased. -/
noncomputable def outputProgram (D : Dims) (B r : ℕ) : XProg 105 :=
  .seq (program D B r) <| .seq (compile packKeyC) (.prog MVM.IO.post)

theorem wf_outputProgram (D : Dims) (B r : ℕ) : (outputProgram D B r).WF :=
  ⟨wf_program D B r, wf_compile _ wf_packKeyC, ⟨trivial, MVM.IO.wf_setList _ _⟩⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact unframed output law of the compiled valid-predicate core. -/
theorem law_outputProgram (D : Dims) (hb : D.b = 22) (hn : 2 ^ D.b ≤ D.q)
    (B r : ℕ) (hB : 2 ^ B ≤ D.q) (hBK : B ≤ D.K)
    (hr : 2 * r < 2 ^ B) (hq : 2 ^ (B + 1) ≤ D.q) (hcount : 2 * (D.K - B) < D.q)
    (msk : MSKt D) (C : List Bool) (w : St)
    (hM : w 0 = (mskEnc D).enc msk) (hp : w rCs = C) :
    (outputProgram D B r).law (enc D.N D.K w) =
    (keyGenLaw (S := setting D) (kbOf D B hB r).Big (kbOf D B hB r).Small
      (kbOf D B hB r).hBig gadDec (helperMap D) msk (bpOf (progOf C))).map
      (fun k ↦ inputStore (0 : Fin 105) ((skEnc D).enc (msk.mpk, k))) := by
  let v := exec D.N D.K (keyPrepareC D) w
  let tail := fun cs ↦ exec D.N D.K (candidateTryC D B r) (Function.update v rCoin cs)
  have hv := (exec_keyPrepareC D hb hn msk C w hM hp).1
  have hpub (cs : List Bool) : tail cs 14 = (mpkEnc D).enc msk.mpk := by
    rw [show tail cs 14 = (Function.update v rCoin cs) 14 from
      exec_writes _ _ _ (candidateTryC_public D B r)]
    simpa using hv
  have hout (cs : List Bool) :
      ((compile packKeyC).seq (.prog MVM.IO.post)).law (enc D.N D.K (tail cs)) =
      PMF.pure (inputStore (0 : Fin 105) ((mpkEnc D).enc msk.mpk ++ tail cs 19)) := by
    rw [XProg.law_seq, law_compile D.N_pos D.K_pos, PMF.pure_bind, XProg.law_prog,
      Prog.law_eq_run_of_coinFree _ MVM.IO.coinFree_post, MVM.IO.run_post, exec_packKeyC, hpub]
    congr 1
    funext t
    simp [io2, inputStore, Function.update_apply]
  rw [outputProgram, XProg.law_seq, law_program, PMF.bind_map]
  change (uniformList (nPI D * D.N * B)).bind
    (fun cs ↦ ((compile packKeyC).seq (.prog MVM.IO.post)).law (enc D.N D.K (tail cs))) = _
  simp_rw [hout]
  refine (PMF.bind_pure_comp _ _).trans ?_
  have h := congrArg (PMF.map (fun k ↦ inputStore (0 : Fin 105) ((mpkEnc D).enc msk.mpk ++ k)))
    (map_coins_keyCore D hb hn B r hB hBK hr hq hcount msk C w hM hp)
  simpa only [PMF.map_comp, Function.comp_def, skEnc, FixedEnc.prod, tail, v] using h

end KeyCore
end AdvancedEncryption.ExpLUT.Prog
