import PE.Impl.RingBTVW.Prog.WfB2S
import PE.Impl.RingBTVW.Prog.WfB2CoinFree

/-!
# The `W_f` block on register streams draws no coin

`coinFree_wfB2S`: compiled machine code (`coinFree_compileA`), the templates, the count and its cap
(`coinFree_capN`), the key sum and the clears.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.ValVM

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

theorem coinFree_runTR : WB2.runTR.CoinFree :=
  coinFree_compileA _ (coinFree_noGrowP _ (Prog.stepSpec_simTop 1 1 1 1).noGrow) _

theorem coinFree_runGR : WB2.runGR.CoinFree :=
  coinFree_compileA _ (coinFree_noGrowP _ (Prog.stepSpec_simGsw 1 1 1 1).noGrow) _

/-- **The `W_f` block on register streams is coin-free.** -/
theorem coinFree_wfB2S (Ic W : ℕ) : (wfB2S hk c Ic W).CoinFree := by
  show XProg.coinFreeB (WB2.wfBodyS hk c Ic W) = true
  simp only [WB2.wfBodyS, WB2.prepTS, WB2.prepGS, WB2.cntS, WB2.prepTRest, WB2.prepGRest,
    WB2.keyPrep, XProg.coinFreeB, Bool.and_eq_true]
  have h1 := Prog.coinFree_countP (3 * W)
  have h2 := XProg.coinFree_capN Ic
  have h3 := cfX_tmplP (n := 256)
  have h4 := cfX_putW (n := 256)
  have h5 := coinFree_runTR
  have h6 := coinFree_runGR
  have h7 := coinFree_noGrowP _ Prog.noGrow_simTmplP
  have h8 := coinFree_noGrowP _ Prog.noGrow_simKeyP
  have h9 : ∀ l : List (Fin 256), (clrsP l).CoinFree := WB2.coinFree_clrsP
  have h10 := WB2.coinFree_copiesP
  simp only [Prog.CoinFree, XProg.CoinFree] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, Prog.coinFreeB, Prog.coinFreeB_mapP,
    Prog.cp, Prog.clr, Bool.and_self, and_self, Bool.true_and, and_true, true_and]

end AdvancedEncryption.RingBTVW.Prog
