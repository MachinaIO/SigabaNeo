import PE.Impl.ExpLUT.Prog.KeyCoinVM
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMIO
import PE.Impl.RingBTVW.Prog.Setup5

/-! Executable initialization and fair-coin sampling for one key-box candidate. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeySample

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Tape.XProg
open SigabaNeo.Tape.MVM Cslib Cslib.Probability Cslib.BitString
open AdvancedEncryption.RingBTVW.Prog

noncomputable def start (D : Dims) (B : ℕ) (cs : List Bool) : St :=
  coinDecodeStart D B (fun _ ↦ []) cs

theorem start_update (D : Dims) (B : ℕ) (cs : List Bool) :
    start D B cs = Function.update (start D B []) rCoin cs := by
  funext r
  by_cases hr : r = rCoin
  · subst r; simp [start, coinDecodeStart]
  · simp [start, coinDecodeStart, Function.update_apply, hr]

/-- Preserve the copied coin queue while installing all VM templates and initial registers. -/
def initTapes : List (Fin 105) := (List.finRange 105).filter fun t ↦ t ≠ tR rCoin

noncomputable def initP (D : Dims) (B : ℕ) : SigabaNeo.Tape.Prog 105 :=
  .seq (cp (tR rCoin) 0) (MVM.IO.setList (enc D.N D.K (start D B [])) initTapes)

theorem run_initP (D : Dims) (B : ℕ) (s : Store 105) :
    (initP D B).run s = enc D.N D.K (start D B (s 0)) := by
  rw [start_update, enc, ← update_tR]
  simp only [initP, run_seq, run_copy, MVM.IO.run_setList]
  funext t
  by_cases ht : t = tR rCoin
  · subst t; simp [initTapes]
  · simp [initTapes, ht, enc]

theorem coinFree_initP (D : Dims) (B : ℕ) : (initP D B).CoinFree :=
  by
    simpa only [initP, Prog.CoinFree, Prog.coinFreeB, Bool.and_eq_true, true_and] using
      MVM.IO.coinFree_setList (enc D.N D.K (start D B [])) initTapes

theorem wf_initP (D : Dims) (B : ℕ) : (initP D B).WF :=
  ⟨trivial, MVM.IO.wf_setList _ _⟩

/-- A candidate decoder with an executable initializer, taking its coins on tape zero. -/
noncomputable def decodeP (D : Dims) (B : ℕ) : XProg 105 :=
  .seq (.prog (initP D B)) (compile decQC)

theorem law_decodeP (D : Dims) (B : ℕ) (s : Store 105) :
    (decodeP D B).law s = PMF.pure
      (enc D.N D.K (exec D.N D.K decQC (start D B (s 0)))) := by
  rw [decodeP, XProg.law_seq, law_prog, Prog.law_eq_run_of_coinFree _ (coinFree_initP D B),
    run_initP, PMF.pure_bind, law_compile D.N_pos D.K_pos]

theorem wf_decodeP (D : Dims) (B : ℕ) : (decodeP D B).WF :=
  ⟨wf_initP D B, wf_compile_decQC⟩

/-- Sample the candidate's bits in the seven scratch tapes. -/
def sampleFrame : Fin 7 ↪ Fin 105 := Fin.castLEEmb (by decide)

noncomputable def candidateP (D : Dims) (B : ℕ) : XProg 105 :=
  .seq (.frame sampleFrame (coinsF (nPI D * D.N * B))) (decodeP D B)

theorem wf_candidateP (D : Dims) (B : ℕ) : (candidateP D B).WF :=
  ⟨wf_coinsF _, wf_decodeP D B⟩

theorem law_sample (n : ℕ) :
    (.frame sampleFrame (coinsF n) : XProg 105).law (fun _ ↦ []) =
      (uniformList n).map (fun cs ↦ inputStore (0 : Fin 105) cs) := by
  have h := appendLaw_frame sampleFrame (law_coinsF n)
  rw [h _ (by simp [P3])]
  congr 1

/-- The complete sampled and compiled candidate, before the rejection test. -/
theorem law_candidateP (D : Dims) (B : ℕ) :
    (candidateP D B).law (fun _ ↦ []) =
      (uniformList (nPI D * D.N * B)).map
        (fun cs ↦ enc D.N D.K (exec D.N D.K decQC (start D B cs))) := by
  rw [candidateP, XProg.law_seq, law_sample, PMF.bind_map]
  have h : ∀ cs : List Bool,
      (decodeP D B).law (inputStore (0 : Fin 105) cs) =
        PMF.pure (enc D.N D.K (exec D.N D.K decQC (start D B cs))) :=
    fun cs ↦ law_decodeP D B (inputStore 0 cs)
  exact (congrArg (PMF.bind (uniformList (nPI D * D.N * B))) (funext h)).trans
    (PMF.bind_pure_comp _ _)

/-- The candidate output has exactly the intended uniform big-box distribution. -/
theorem law_candidateP_queue (D : Dims) (B : ℕ) (hBK : B ≤ D.K)
    (hB : 2 ^ B ≤ D.q) (r : ℕ) :
    ((candidateP D B).law (fun _ ↦ [])).map (fun s ↦ s (tR rDq)) =
      (PMF.uniformOfFinset (kbOf D B hB r).Big (kbOf D B hB r).hBig).map
        (fun p ↦ encL D.N D.K ((Enum.list (α := PIdxD D)).map p)) := by
  rw [law_candidateP, PMF.map_comp]
  simp only [enc]
  exact map_uniformList_exec_coinDecodeStart D B D.K_pos hBK hB r (fun _ ↦ [])

end AdvancedEncryption.ExpLUT.Prog.KeySample
