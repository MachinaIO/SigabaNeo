import PE.Impl.ExpLUT.Prog.KeyOutput
/-! Both KeyGen branches from the two decoded interface words. -/
namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib Cslib.Probability

/-- Invalid predicate words produce the public key and the canonical zero key. -/
noncomputable def invalidKeyC (D : Dims) : Code :=
  .seq (keyInputC D) <| .seq (.cp 14 17) <|
  .seq (natC 19 rB1 (codecSize (keyEnc D))) packKeyC

theorem wf_invalidKeyC (D : Dims) : (invalidKeyC D).WFc :=
  ⟨wf_keyInputC D, trivial, natC_wfc _ _ _, wf_packKeyC⟩

theorem keyInputC_bit (D : Dims) (w : St) : exec D.N D.K (keyInputC D) w rB1 = [false] := by
  rw [keyInputC, exec_seq, exec_seq,
    exec_bitsC _ _ _ (by decide) (by decide) (by decide) _ (by simp), exec_seq]
  rw [exec_writes _ _ _ (readFieldC_frame _ _ _ _ rB1 (by decide) (by decide) (by decide)),
    exec_writes _ _ _ (readFieldC_frame _ _ _ _ rB1 (by decide) (by decide) (by decide))]
  simp

theorem exec_invalidKeyC (D : Dims) (msk : MSKt D) (w : St)
    (hs : w 0 = (mskEnc D).enc msk) :
    exec D.N D.K (invalidKeyC D) w 0 = (skEnc D).enc (msk.mpk, 0) := by
  have hm := (exec_keyInputC D msk w hs).1
  have hb := keyInputC_bit D w
  rw [invalidKeyC, exec_seq, exec_seq, exec_seq,
    exec_natC _ _ (by decide) _ _ (by simpa using hb), exec_packKeyC]
  simp only [Function.update_apply, exec_cp, Fin.reduceEq, ↓reduceIte, hm]
  exact congrArg ((mpkEnc D).enc msk.mpk ++ ·) (keyEnc_zero D).symm

namespace KeyCore
open SigabaNeo.Tape.Prog SigabaNeo.Tape.XProg

/-- Restore the canonical VM state from arbitrary parser workspace. -/
theorem run_pre_any (N K : ℕ) (s : Store 105) :
    (MVM.IO.pre N K (fun _ ↦ 0)).run s =
      enc N K (MVM.IO.init (s 0) (s 1) (fun _ ↦ 0)) := by
  simp only [MVM.IO.pre, Prog.run_seq, run_copy, MVM.IO.run_setList]
  funext t
  fin_cases t <;> simp [MVM.IO.preTapes, enc, encX, MVM.IO.init]

/-- Move the decoded predicate into the evaluator's input register. -/
noncomputable def enterP (D : Dims) : XProg 105 :=
  .seq (.prog (MVM.IO.pre D.N D.K (fun _ ↦ 0))) (compile (.cp rCs 1))

def initialState (msk C : List Bool) : St :=
  Function.update (MVM.IO.init msk C (fun _ ↦ 0)) rCs C

theorem wf_enterP (D : Dims) : (enterP D).WF :=
  ⟨⟨trivial, trivial, MVM.IO.wf_setList _ _⟩, wf_compile _ trivial⟩

theorem law_enterP (D : Dims) (s : Store 105) :
    (enterP D).law s = PMF.pure (enc D.N D.K (initialState (s 0) (s 1))) := by
  rw [enterP, XProg.law_seq, XProg.law_prog,
    Prog.law_eq_run_of_coinFree _ (MVM.IO.coinFree_pre _ _ _), run_pre_any,
    PMF.pure_bind, law_compile D.N_pos D.K_pos]
  rfl

noncomputable def validP (D : Dims) (B r : ℕ) : XProg 105 :=
  .seq (enterP D) (outputProgram D B r)

noncomputable def invalidP (D : Dims) : XProg 105 :=
  .seq (enterP D) <| .seq (compile (invalidKeyC D)) (.prog MVM.IO.post)

theorem wf_validP (D : Dims) (B r : ℕ) : (validP D B r).WF :=
  ⟨wf_enterP D, wf_outputProgram D B r⟩

theorem wf_invalidP (D : Dims) : (invalidP D).WF :=
  ⟨wf_enterP D, wf_compile _ (wf_invalidKeyC D), ⟨trivial, MVM.IO.wf_setList _ _⟩⟩

theorem law_validP (D : Dims) (hb : D.b = 22) (hn : 2 ^ D.b ≤ D.q)
    (B r : ℕ) (hB : 2 ^ B ≤ D.q) (hBK : B ≤ D.K)
    (hr : 2 * r < 2 ^ B) (hq : 2 ^ (B + 1) ≤ D.q) (hcount : 2 * (D.K - B) < D.q)
    (msk : MSKt D) (C : List Bool) (s : Store 105)
    (hM : s 0 = (mskEnc D).enc msk) (hp : s 1 = C) :
    (validP D B r).law s =
    (keyGenLaw (S := setting D) (kbOf D B hB r).Big (kbOf D B hB r).Small
      (kbOf D B hB r).hBig gadDec (helperMap D) msk (bpOf (progOf C))).map
      (fun k ↦ inputStore (0 : Fin 105) ((skEnc D).enc (msk.mpk, k))) := by
  rw [validP, XProg.law_seq, law_enterP, PMF.pure_bind]
  apply law_outputProgram D hb hn B r hB hBK hr hq hcount msk C
  · simpa [initialState, MVM.IO.init] using hM
  · simpa [initialState] using hp

theorem law_invalidP (D : Dims) (msk : MSKt D) (s : Store 105)
    (hM : s 0 = (mskEnc D).enc msk) :
    (invalidP D).law s = PMF.pure (inputStore (0 : Fin 105) ((skEnc D).enc (msk.mpk, 0))) := by
  rw [invalidP, XProg.law_seq, law_enterP, PMF.pure_bind, XProg.law_seq,
    law_compile D.N_pos D.K_pos, PMF.pure_bind, XProg.law_prog,
    Prog.law_eq_run_of_coinFree _ MVM.IO.coinFree_post, MVM.IO.run_post,
    exec_invalidKeyC D msk _ (by simpa [initialState, MVM.IO.init] using hM)]
  congr 1
  funext t
  simp [io2, inputStore, Function.update_apply]

end KeyCore
end AdvancedEncryption.ExpLUT.Prog
