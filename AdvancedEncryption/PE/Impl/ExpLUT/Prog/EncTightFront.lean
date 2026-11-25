import PE.Impl.ExpLUT.Prog.EncTightPrep
import PE.Impl.ExpLUT.Prog.EncTimeTight
/-!
# The tight clock of the concrete encryption machine (tight encryption clock, part 7)

From the loaded input (`inputBound 0 n`, `n ≤ 2^100`) the parser leaves the sampler's output
register at most `2^100` bits and its other tapes at most `2^102` (`lenBoundT_parse_le`), so the
sampler costs at most `2^252` steps (`coins_time_mid`); with the certified suffix (`suffix_tight`,
`2^242`) and the emitter, **the encryption machine takes at most `2^253` steps**
(`EncConf.time_encMachine_tight`).
-/

namespace AdvancedEncryption.ExpLUT.Prog.EncTight

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Prog
open AdvancedEncryption.ExpLUT.Params AdvancedEncryption.ExpLUT.Prog
  AdvancedEncryption.ExpLUT.Prog.EncW AdvancedEncryption.RingBTVW.Prog

set_option maxRecDepth 100000

theorem parseMap_inj (d : Fin 105) (h0 : d ≠ 0) (h2 : d ≠ 2) (h3 : d ≠ 3) :
    Function.Injective (EncIO.parseMap d) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [EncIO.parseMap] <;> omega

/-- The per-tape bound after the parser, from the bound `B` of the loaded store. -/
def parseB (B : Fin 105 → ℕ) : Fin 105 → ℕ :=
  Function.update (ustep (EncIO.parseMap 1) (ustep (EncIO.parseMap 1)
    (ustep (EncIO.parseMap 1) (ustep (EncIO.parseMap 4) B)))) 4 0

theorem lenBoundT_parse_le {ℓ B : Fin 105 → ℕ} (h : ℓ ≤ B) :
    lenBoundT EncIO.parse ℓ ≤ parseB B := by
  have h4 := parseMap_inj 4 (by decide) (by decide) (by decide)
  have h1 := parseMap_inj 1 (by decide) (by decide) (by decide)
  have s1 := ((lenBoundT_mono _ h).trans (lenBoundT_unfr_le _ h4 B))
  have s2 := ((lenBoundT_mono _ s1).trans (lenBoundT_unfr_le _ h1 _))
  have s3 := ((lenBoundT_mono _ s2).trans (lenBoundT_unfr_le _ h1 _))
  have s4 := ((lenBoundT_mono _ s3).trans (lenBoundT_unfr_le _ h1 _))
  intro t
  have e : ∀ X : Fin 105 → ℕ, lenBoundT (clr (4 : Fin 105)) X = Function.update X 4 0 :=
    fun _ => rfl
  simp only [EncIO.parse, lenBoundT_seq_enc, e]
  unfold parseB
  rw [Function.update_apply, Function.update_apply]
  split_ifs
  · exact le_rfl
  · exact s4 t

/-- The sampler's tapes after parsing an input of at most `2^100` bits. -/
theorem parseB_sample : ∀ j : Fin 7,
    parseB (inputBound (0 : Fin 105) (2 ^ 100)) (EncIO.sampleFrame j) ≤ XProg.shp 0 (2 ^ 100) (2 ^ 102) j := by
  decide +kernel

theorem parseB_all : ∀ t : Fin 105, parseB (inputBound (0 : Fin 105) (2 ^ 100)) t ≤ 2 ^ 102 := by
  decide +kernel

set_option maxHeartbeats 0 in
/-- **The sampler from the parser's per-tape bounds.** -/
theorem coins_time_mid : EncConf.concreteCoinsBound.T (2 ^ 100) (2 ^ 102) ≤ 2 ^ 252 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem coins_len_mid : 2 ^ 100 + EncConf.concreteCoinsBound.a ≤ 2 ^ 103 ∧
    2 ^ 102 + EncConf.concreteCoinsBound.s ≤ 2 ^ 103 := by
  constructor
  · exact (Nat.add_le_add_left EncConf.coins_output _).trans (by norm_num)
  · exact (Nat.add_le_add_left EncConf.coins_scratch _).trans (by norm_num)

/-- A bound from a per-tape input bound. -/
def XBoundP {k : ℕ} (p : XProg k) (B : Fin k → ℕ) (T M' : ℕ) : Prop :=
  ∀ ℓ, ℓ ≤ B → XProg.timeBoundT p ℓ ≤ T ∧ ∀ i, XProg.lenBoundT p ℓ i ≤ M'

set_option exponentiation.threshold 2000 in
/-- **Parser and sampler.** -/
theorem boundsP_prepare :
    XBoundP (EncIO.prepare Dc 16 6 eFl) (inputBound (0 : Fin 105) (2 ^ 100))
      (2 ^ 214 + 2 ^ 252) (2 ^ 104) := by
  intro ℓ hℓ
  have hM : ∀ i, ℓ i ≤ 2 ^ 100 := fun i => (hℓ i).trans (by
    simp only [inputBound, Function.update_apply]; split_ifs <;> simp)
  have hp := bounds_parse ℓ hM
  have hl := lenBoundT_parse_le hℓ
  have hA : ATBb (encCoinsP Dc 16 6 eFl) EncConf.concreteCoinsBound := by
    rw [← EncConf.encCoinsBound_eq]; exact atbb_encCoinsP Dc 16 6 eFl
  have hin : (fun j => lenBoundT EncIO.parse ℓ (EncIO.sampleFrame j)) ≤
      XProg.shp 0 (2 ^ 100) (2 ^ 102) := fun j => (hl _).trans (parseB_sample j)
  have hb := hA (2 ^ 100) (2 ^ 102) (EncConf.coins_threshold.trans (by norm_num))
  rw [show EncIO.prepare Dc 16 6 eFl = .seq (.prog EncIO.parse)
    (.frame EncIO.sampleFrame (encCoinsP Dc 16 6 eFl)) from rfl, xtime_seq, xtime_prog, xlen_seq,
    xlen_prog, xtime_frame, xlen_frame]
  refine ⟨?_, fun i => ?_⟩
  · exact Nat.add_le_add hp.1 (((XProg.timeBoundT_mono _ hin).trans hb.1).trans coins_time_mid)
  · refine embedF_bound _ (fun t => (hl t).trans ((parseB_all t).trans (by norm_num)))
      (fun j => ?_) i
    refine ((XProg.lenBoundT_mono _ hin).trans hb.2 j).trans ?_
    have := coins_len_mid
    simp only [XProg.shp]; split_ifs <;> omega

theorem inputBound_prepareFrame (n : ℕ) (hn : n ≤ 2 ^ 100) :
    (fun j => inputBound (0 : Fin 326) n (prepareFrame j)) ≤ inputBound (0 : Fin 105) (2 ^ 100) := by
  intro j
  simp only [inputBound, Function.update_apply]
  by_cases hj : j = 0
  · subst hj
    have : prepareFrame 0 = 0 := rfl
    simp only [this, if_true]
    exact hn
  · have : prepareFrame j ≠ 0 := by
      intro h; apply hj; apply prepareFrame.injective; rw [h]; rfl
    simp [hj, this]

set_option exponentiation.threshold 2000 in
/-- **The whole encryption program** from the loaded input. -/
theorem total_encProgram_tight (n : ℕ) (hn : n ≤ 2 ^ 100) :
    XProg.totalTimeT (encProgram Dc 16 6 eFl) 0 0 n ≤ 2 ^ 253 := by
  have hW := boundsP_prepare _ (inputBound_prepareFrame n hn)
  have eW : widePrepare Dc 16 6 eFl = .frame prepareFrame (EncIO.prepare Dc 16 6 eFl) := rfl
  have hl₁ : ∀ i, XProg.lenBoundT (widePrepare Dc 16 6 eFl) (inputBound (0 : Fin 326) n) i ≤
      2 ^ 110 := fun i => by
    rw [eW, xlen_frame]
    refine embedF_bound _ (fun t => ?_) (fun j => (hW.2 j).trans (by norm_num)) i
    simp only [inputBound, Function.update_apply]; split_ifs <;> omega
  have hW1 : XProg.timeBoundT (widePrepare Dc 16 6 eFl) (inputBound (0 : Fin 326) n) ≤
      2 ^ 214 + 2 ^ 252 := by
    rw [eW, xtime_frame]; exact hW.1
  have hS := suffix_tight hl₁
  have hF := bounds_frameCiphertextP _ hS.2
  unfold XProg.totalTimeT
  rw [show encProgram Dc 16 6 eFl = .seq (.seq (widePrepare Dc 16 6 eFl)
    (.prog (.seq relocateP (.seq (normalizeInputsP Dc) (cleanCoreP Dc))))) frameCiphertextP
    from rfl, xtime_seqL, xlen_seqL, xtime_prog, xlen_prog]
  have := hS.1
  have := hF.1
  have := hF.2 0
  omega

end AdvancedEncryption.ExpLUT.Prog.EncTight

namespace AdvancedEncryption.ExpLUT.Prog.EncConf

open AdvancedEncryption.ExpLUT.Params EncW

/-- **The tight clock of the encryption machine**: at most `2^253` steps (parser, sampler,
loader, the certified core with every loop charged its actual counter, erasure, emitter). -/
theorem time_encMachine_tight : encMachine.time ≤ 2 ^ 253 :=
  time_encMP_le Dc 16 6 eFl (2 ^ 253) (EncTight.total_encProgram_tight _ encInputLength_le)

end AdvancedEncryption.ExpLUT.Prog.EncConf
