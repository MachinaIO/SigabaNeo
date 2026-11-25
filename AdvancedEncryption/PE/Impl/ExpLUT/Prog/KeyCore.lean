import PE.Impl.ExpLUT.Prog.KeyInput

/-! The compiled KeyGen core with actual fair-coin generation after public evaluation. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyCore
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Tape.XProg SigabaNeo.Tape.MVM
  Cslib Cslib.Probability Cslib.BitString AdvancedEncryption.RingBTVW.Prog

/-- Sample directly into the VM coin register, using only blank compiler scratch tapes. -/
def coinFrame : Fin 7 ↪ Fin 105 :=
  ⟨![tR rCoin, 0, 1, 2, 3, 4, 5], by decide⟩

noncomputable def sampleP (n : ℕ) : XProg 105 :=
  .seq (.prog (clr (tR rCoin))) (.frame coinFrame (coinsF n))

theorem wf_sampleP (n : ℕ) : (sampleP n).WF := ⟨trivial, wf_coinsF n⟩

theorem law_sampleP (N K n : ℕ) (w : St) :
    (sampleP n).law (enc N K w) =
      (uniformList n).map (fun cs ↦ enc N K (Function.update w rCoin cs)) := by
  rw [sampleP, XProg.law_seq, XProg.law_prog,
    Prog.law_eq_run_of_coinFree _ (by rfl), run_clear, PMF.pure_bind]
  have h := appendLaw_frame coinFrame (law_coinsF n)
  rw [h _ (by
    change Function.update (enc N K w) 78 [] 1 = [] ∧
      Function.update (enc N K w) 78 [] 2 = [] ∧
      Function.update (enc N K w) 78 [] 3 = []
    simp [enc, encX])]
  congr 1
  funext cs
  simp only [coinFrame, Function.Embedding.coeFn_mk, Matrix.cons_val_zero,
    Function.update_self, List.nil_append, Function.update_idem]
  exact update_tR rCoin cs

/-- Load MSK fields, evaluate the predicate, sample a candidate, and execute one key attempt. -/
noncomputable def program (D : Dims) (B r : ℕ) : XProg 105 :=
  .seq (compile (keyPrepareC D)) <|
  .seq (sampleP (nPI D * D.N * B)) (compile (candidateTryC D B r))

theorem wf_program (D : Dims) (B r : ℕ) : (program D B r).WF :=
  ⟨wf_compile _ (wf_keyPrepareC D), wf_sampleP _, wf_compile _ (wf_candidateTryC D B r)⟩

/-- Exact full-store law, retaining compiler canonical state after each phase. -/
theorem law_program (D : Dims) (B r : ℕ) (w : St) :
    (program D B r).law (enc D.N D.K w) =
    (uniformList (nPI D * D.N * B)).map (fun cs ↦ enc D.N D.K
      (exec D.N D.K (candidateTryC D B r)
        (Function.update (exec D.N D.K (keyPrepareC D) w) rCoin cs))) := by
  rw [program, XProg.law_seq, law_compile D.N_pos D.K_pos, PMF.pure_bind,
    XProg.law_seq, law_sampleP, PMF.bind_map]
  have h := fun cs ↦ law_compile D.N_pos D.K_pos (candidateTryC D B r)
    (Function.update (exec D.N D.K (keyPrepareC D) w) rCoin cs)
  exact (congrArg (PMF.bind (uniformList (nPI D * D.N * B))) (funext h)).trans
    (PMF.bind_pure_comp _ _)

/-- The actual probabilistic tape core realizes the scheme's single-try key law. -/
theorem law_program_key (D : Dims) (hb : D.b = 22) (hn : 2 ^ D.b ≤ D.q)
    (B r : ℕ) (hB : 2 ^ B ≤ D.q) (hBK : B ≤ D.K)
    (hr : 2 * r < 2 ^ B) (hq : 2 ^ (B + 1) ≤ D.q) (hcount : 2 * (D.K - B) < D.q)
    (msk : MSKt D) (C : List Bool) (w : St)
    (hM : w 0 = (mskEnc D).enc msk) (hp : w rCs = C) :
    ((program D B r).law (enc D.N D.K w)).map (fun s ↦ s (tR 19)) =
    (keyGenLaw (S := setting D) (kbOf D B hB r).Big (kbOf D B hB r).Small
      (kbOf D B hB r).hBig gadDec (helperMap D) msk (bpOf (progOf C))).map (keyEnc D).enc := by
  rw [law_program, PMF.map_comp]
  exact map_coins_keyCore D hb hn B r hB hBK hr hq hcount msk C w hM hp

end AdvancedEncryption.ExpLUT.Prog.KeyCore
