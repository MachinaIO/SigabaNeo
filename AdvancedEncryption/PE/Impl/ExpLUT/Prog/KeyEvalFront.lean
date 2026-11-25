import PE.Impl.ExpLUT.Prog.KeyEvalRead
/-! Public-key loading followed by the actual EvalPK machine. -/
namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG

/-- Constant templates required before loading the public key. -/
structure EvalTemplates (D : Dims) (w : St) : Prop where
  kc : w rKc = List.replicate (gD D) false
  bit1 : w rBit1 = [false]
  tb : w rTb = List.replicate D.b false
  blk : w rTBlk = List.replicate (16 * D.K ^ 3 * (D.N * D.K)) false
  tm : MulTmpl D.N D.K w
  one : w rOne = encRM D.N D.K 1
  mu0 : w rMu0 = encRM D.N D.K (xInvG (ZMod D.q) D.N)
  t4K : w rT4K = List.replicate (4 * D.K) false
  tw : w rTW = List.replicate (2 ^ D.b) false
  ttab : w rTtab = List.replicate tlK false
  xc : w rXc = encRM D.N D.K (xcK D)
  te : w rTe = List.replicate 14 false
  t15 : w rT15 = List.replicate 15 false

/-- Clear only work registers whose incoming contents are irrelevant to EvalPK. -/
def evalScratchC : Code :=
  .seq (.clr rX0) <| .seq (.clr rX1) <| .seq (.clr rAc0) <| .seq (.clr rAc1) <|
  .seq (.clr rDA) <| .seq (.clr rAl) <| .seq (.clr rCi) <| .seq (.clr rCj) <|
  .seq (.clr rP) <| .seq (.clr rPw2) <| .seq (.clr rCt) <| .seq (.clr rCst) (.clr rCj2)

theorem wf_evalScratchC : evalScratchC.WFc := by repeat constructor

theorem evalScratchC_roS : ∀ r : Fin 64, roS r = true → r ≠ rCst →
    evalScratchC.writes r = false := by decide +kernel

/-- Load the four public-key fields, then evaluate the predicate. -/
noncomputable def evalPublicC (D : Dims) : Code := .seq (evalFieldsC D) (.seq evalScratchC evalC)

/-- This front end needs only the saved MPK, predicate, and constant templates. -/
theorem exec_evalPublicC (D : Dims) (hb : D.b = 22) (hn : 2 ^ D.b ≤ D.q)
    (mpk : MPKt D) (C : List Bool) (w : St)
    (hs : w 17 = (mpkEnc D).enc mpk) (hbit : w rB1 = [false])
    (ht : EvalTemplates D w) (hp : w rCs = C) :
    exec D.N D.K (evalPublicC D) w rA =
      encL D.N D.K (matL (keyPK (helperMap D) mpk (bpOf (progOf C)))) := by
  let v := exec D.N D.K (evalFieldsC D) w
  have fr (r : Fin 64) (h0 : r ≠ 0) (h1 : r ≠ 1) (h2 : r ≠ 2) (h4 : r ≠ 4)
      (h29 : r ≠ 29) (h30 : r ≠ 30) : v r = w r :=
    exec_writes _ _ _ (evalFieldsC_frame D r h0 h1 h2 h4 h29 h30)
  have fm : MulTmpl D.N D.K v := ht.tm.of_writes (by
    intro r hr
    apply fr r <;> intro he <;> subst r <;> norm_num at hr)
  obtain ⟨hH, hA0, hAin, hAaut⟩ := exec_evalFieldsC D mpk w hs hbit
  have hi : StepIn v (gD D) D.b (2 ^ D.b) tlK (HfK D mpk) (HiK D mpk)
      (AaK D mpk) (xInvG (ZMod D.q) D.N) := by
    refine ⟨⟨?_, hAaut.trans (aaut_codec_aautL D mpk),
      hH.trans (helper_codec_hL D mpk), ?_, ?_, ?_, fm⟩, ?_, ?_, ?_, ?_, ?_⟩
    all_goals rw [fr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    · exact ht.kc
    · exact ht.bit1
    · exact ht.tb
    · exact ht.blk
    · exact ht.one
    · exact ht.mu0
    · exact ht.t4K
    · exact ht.tw
    · exact ht.ttab
  have hc : CoefIn v 14 (2 ^ D.b) D.b (xcK D) := by
    refine ⟨hi.one, ?_, hi.ch.bit1, ?_, hi.tw, hi.ch.tb, fm.z⟩
    all_goals rw [fr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    · exact ht.xc
    · exact ht.te
  let u := exec D.N D.K evalScratchC v
  have hfr (r : Fin 64) (hr : evalScratchC.writes r = false) : u r = v r :=
    exec_writes _ _ _ hr
  have hiu := hi.of_roS (fun r hr hn ↦ hfr r (evalScratchC_roS r hr hn))
  have hcu : CoefIn u 14 (2 ^ D.b) D.b (xcK D) := by
    constructor
    all_goals rw [hfr _ (by decide)]
    all_goals first
      | exact hc.one
      | exact hc.xc
      | exact hc.bit1
      | exact hc.te
      | exact hc.tw
      | exact hc.tb
      | exact hc.z
  rw [evalPublicC, exec_seq, exec_seq]
  apply exec_evalC_keyPK D hb hn mpk C u hiu hcu
    ((hfr _ (by decide)).trans hA0) ((hfr _ (by decide)).trans hAin)
  · rw [hfr _ (by decide)]
    exact (fr _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans hp
  · rw [hfr _ (by decide)]
    exact (fr _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ht.t15

theorem wf_evalPublicC (D : Dims) : (evalPublicC D).WFc :=
  ⟨wf_evalFieldsC D, wf_evalScratchC, by repeat constructor⟩

/-- The saved master secret and public key survive public evaluation. -/
theorem evalPublicC_saved (D : Dims) (r : Fin 64) (hr : r = 16 ∨ r = 17) :
    (evalPublicC D).writes r = false := by
  have hf : (evalFieldsC D).writes r = false := by
    apply evalFieldsC_frame <;> rcases hr with rfl | rfl <;> decide
  simp only [evalPublicC, Code.writes, hf, Bool.false_or]
  rcases hr with rfl | rfl <;> decide

end AdvancedEncryption.ExpLUT.Prog
