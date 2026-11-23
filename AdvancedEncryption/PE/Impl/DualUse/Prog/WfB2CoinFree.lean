import PE.Impl.DualUse.Prog.WfB2
import PE.Impl.DualUse.Prog.DecP

/-!
# The block-structured `W_f` block draws no coin

`coinFree_wfB2`: `wfB2 hk c W` is coin-free (needed for `Dec`, whose `c_f̂` block runs it):
compiled machine code (`coinFree_compileA`, for a coin-free step), the templates, the gate
count, the key sum and the clears.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.ValVM

/-- **Compiled machine code is coin-free** when its step is. -/
theorem coinFree_compileA {H : List ℕ → Prop} {P : Prog 132} (cert : StepCert H P)
    (hP : P.CoinFree) : ∀ c : Code, (compileA cert c).toX.CoinFree
  | .gate d a b => by
    simp only [compileA, Sym.XAst.toX]
    exact XProg.coinFree_seq rfl (XProg.coinFree_seq rfl (XProg.coinFree_seq hP rfl))
  | .mvV d s => by simp only [compileA]; split <;> rfl
  | .mv d s c => by simp only [compileA]; split <;> rfl
  | .cp d s => by simp only [compileA]; split <;> rfl
  | .drop t c => by simp only [compileA]; split <;> rfl
  | .clr t => rfl
  | .tl t => rfl
  | .rep c body => coinFree_compileA cert hP body
  | .seq p q => XProg.coinFree_seq (coinFree_compileA cert hP p) (coinFree_compileA cert hP q)
  | .ifb t p q => by
    have h1 := coinFree_compileA cert hP p
    have h2 := coinFree_compileA cert hP q
    simp only [XProg.CoinFree] at h1 h2 ⊢
    simp only [compileA, Sym.XAst.toX, XProg.coinFreeB, h1, h2, Bool.and_self]
  | .nop => rfl

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

theorem coinFree_runT : WB2.runT.CoinFree :=
  coinFree_compileA _ (coinFree_noGrowP _ (Prog.stepSpec_simTop 1 1 1 1).noGrow) _

theorem coinFree_runG : WB2.runG.CoinFree :=
  coinFree_compileA _ (coinFree_noGrowP _ (Prog.stepSpec_simGsw 1 1 1 1).noGrow) _

/-- **The block-structured `W_f` block is coin-free.** -/
theorem coinFree_wfB2 (W : ℕ) : (wfB2 hk c W).CoinFree := by
  show XProg.coinFreeB (WB2.wfBody hk c W) = true
  simp only [WB2.wfBody, WB2.prepT, WB2.prepG, WB2.keyPrep, XProg.coinFreeB, Bool.and_eq_true]
  have h1 := Prog.coinFree_countP (2 * W)
  have h2 := Prog.coinFree_capP W
  have h3 := cfX_tmplP (n := 256)
  have h4 := cfX_putW (n := 256)
  have h5 := coinFree_runT
  have h6 := coinFree_runG
  have h7 := coinFree_noGrowP _ Prog.noGrow_simTmplP
  have h8 := coinFree_noGrowP _ Prog.noGrow_simKeyP
  have h9 : ∀ l : List (Fin 256), (clrsP l).CoinFree := coinFree_clrsP
  have h10 := WB2.coinFree_copiesP
  simp only [Prog.CoinFree, XProg.CoinFree] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, Prog.coinFreeB, Prog.coinFreeB_mapP,
    Prog.cp, Prog.clr, Bool.and_self, and_self, Bool.true_and, and_true, true_and]

end AdvancedEncryption.DualUse.Prog
