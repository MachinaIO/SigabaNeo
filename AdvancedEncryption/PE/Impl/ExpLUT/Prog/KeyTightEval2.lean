import PE.Impl.ExpLUT.Prog.KeyTightChain
import PE.Impl.ExpLUT.Prog.KeyTightEval

/-!
# KeyGen: the public evaluator with the tight chain (Stage 2d)

F3's evaluator envelope with the two counter registers tracked: `rKc ≤ gD Dc` (the automorphism
exponent) and `rTK1 ≤ K - 1` (the digit counter template); both are exact template lengths
(`EvalLengths.kc`, `EvalLengths.tk1`). On this envelope the chain and the matrix products use
the tight kernels of `KeyTightChain`; the coefficient routines, `agC`, `matAddC` and the two
single instructions of a `j`-step are F3's, with exact numeric bounds.

* `t2JBodyK` (`≤ 2^358 + 2^350`), `t2StepK` (`≤ 2^380 + 2^373`), `t2EvalC` (`≤ 2^384 + 2^378`);
* **`t2KeyPrepareC_Dc : Cert (compile (keyPrepareC Dc)) a preparedBounds (2^384 + 2^381)`**.
-/

set_option linter.unusedSectionVars false
set_option exponentiation.threshold 1000
set_option maxRecDepth 100000

namespace AdvancedEncryption.ExpLUT.Prog.KeyTight

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open AdvancedEncryption.ExpLUT.Prog
open AdvancedEncryption.ExpLUT.Prog.KeyTime

/-! ### The envelope with the counters tracked -/

/-- F3's evaluator envelope with `rKc ↦ gD Dc` and `rTK1 ↦ K - 1`. -/
def evEnv2 : Fin 64 → ℕ :=
  Function.update (Function.update evaluatorEnvelope rKc (gD Dc)) rTK1 (Dc.K - 1)

theorem gD_Dc : gD Dc = 9 := by norm_num [gD, SigabaNeo.Lattices.gGen, Dc, Dims.N, Params.en, Params.bc]

theorem evEnv2_kc : evEnv2 rKc ≤ 9 := by simp [evEnv2, gD_Dc]

theorem evEnv2_tk1 : evEnv2 rTK1 ≤ 2 ^ 16 := by simp [evEnv2, Dc, Params.Kc]

theorem evEnv2_top (r : Fin 64) : evEnv2 r ≤ 2 ^ 120 := by
  unfold evEnv2
  by_cases h1 : r = rTK1
  · subst h1; simp [Dc, Params.Kc]
  · rw [Function.update_of_ne h1]
    by_cases h2 : r = rKc
    · subst h2; rw [Function.update_self, gD_Dc]; norm_num
    · rw [Function.update_of_ne h2]; exact evaluatorEnvelope_top r

theorem evEnv2_inputs :
    RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) evEnv2) :=
  layout_inputs _ _ _ _ evEnv2_top (by norm_num) (by norm_num) (by norm_num)

theorem evEnv2_caps : EvaluatorCaps evEnv2 := by
  exact {
    chain := {
      toMatrixCaps := {
        toInnerCaps := {
          x0 := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
          x1 := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
          ac0 := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
          ac1 := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
          da := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
          dx := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
          zero := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
          stream := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
          counter := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
        }
        tmp := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
        row0 := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
        row1 := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
        col0 := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
        col1 := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
        trans0 := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
        trans1 := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
        sums := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
        streamOut := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
        output := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
        columns := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
        rows := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
      }
      out := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
      again := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
      inverse := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
      saved := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
      source := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
      autWords := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
      hWords := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
      bit := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
      count := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
      read := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
      bitOutput := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
      gadget := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    }
    coefficient := {
      accumulator := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
      power := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
      entry := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
      bit := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
      bitCopy := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
      bits := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
      doubling := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
      zero := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
      one := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
      tableCopy := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
      table := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
      predicate := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    }
    alpha := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    digits := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    inner := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    columns := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    exponent := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    chainBits := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    powers := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    rowTemplate := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    gadgetRow := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    gadgetMatrix := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    addCount := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    addCounter := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    accumulator := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    accumulatorStream := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    outputStream := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    baseMatrix := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    gadgetCopy := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    mu := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    index := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    inputMatrix := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    inputStream := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    outputMatrix := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    accumulatorTemplate := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    zeroIndex := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    initialMu := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    tableCopy := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    tableCount := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    result := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    stepsCopy := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
    steps := by norm_num [evEnv2, evaluatorEnvelope, Function.update_apply]
  }

theorem scratchCaps_le_evEnv2 (a : Fin 105 → ℕ)
    (ht : ∀ t, a t ≤ 2 ^ 120) (hl : EvalLengths Dc a) :
    scratchCaps (fun r ↦ a (tR r)) ≤ evEnv2 := by
  intro r
  fin_cases r <;> simp [scratchCaps, evEnv2, evaluatorEnvelope, Function.update_apply]
  all_goals first
    | exact ht _
    | simpa [Dc, Dims.N, Params.Kc, Params.en, Params.bc] using hl.tk.le
    | simpa [Dc, Dims.N, Params.Kc, Params.en, Params.bc] using hl.z.le
    | simpa [Dc, Dims.N, Params.Kc, Params.en, Params.bc] using hl.one.le
    | simpa [Dc, Dims.N, Params.Kc, Params.en, Params.bc] using hl.t4k.le
    | simpa [Dc, Dims.N, Params.Kc, Params.en, Params.bc] using hl.t2k.le
    | simpa [Dc, Dims.N, Params.Kc, Params.en, Params.bc] using hl.tw.le
    | simpa [Dc, Dims.N, Params.Kc, Params.en, Params.bc] using hl.tb.le
    | simpa [Dc, Dims.N, Params.Kc, Params.en, Params.bc] using hl.te.le
    | simpa [Dc, Dims.N, Params.Kc, Params.en, Params.bc] using hl.t15.le
    | simpa [Dc, Dims.N, Params.Kc, Params.en, Params.bc] using hl.bit1.le
    | simpa [Dc, Dims.N, Params.Kc, Params.en, Params.bc] using hl.tknk.le
    | simpa [Dc, Dims.N, Params.Kc, Params.en, Params.bc] using hl.kc.le
    | simpa [Dc, Dims.N, Params.Kc, Params.en, Params.bc] using hl.tk1.le


theorem compile_evalScratchC_Dc2 (a : Fin 105 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) a) (hl : EvalLengths Dc a) :
    Cert (MVM.compile evalScratchC) a
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) evEnv2) (2 ^ 130) := by
  let b := fun r ↦ a (tR r)
  have hi : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) :=
    layout_inputs _ _ _ b (fun r ↦ h.top (tR r)) h.ring h.dimension h.width
  have hin := le_layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b a h.top
    h.templateK h.templateN h.zeros.le h.ones (fun _ ↦ le_rfl)
  exact (compile_evalScratchC _ _ _ b hi).mono hin
    (layout_mono _ _ _ (scratchCaps_le_evEnv2 a h.top hl)) (by norm_num)

/-! ### Exact numbers -/

theorem tChainT_exact :
    tChainT (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) 9 (2 ^ 16) (4 * 2 ^ 16) (2 * 2 ^ 16) (2 ^ 22) 22 ≤
      2 ^ 335 := by decide +kernel

theorem tInvT_exact : tInvT (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) (2 ^ 16) (2 * 2 ^ 16) ≤ 2 ^ 264 := by
  decide +kernel

theorem tMatT_exact :
    tMatT (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) (2 ^ 16) (4 * 2 ^ 16) (2 * 2 ^ 16) ≤ 2 ^ 280 := by
  decide +kernel

theorem agCTime_exact : 4 * (2 * 2 ^ 120 + 5) + 2 ^ 16 * (2 * 2 ^ 120 +
    (appendAllowance (2 ^ 120) + evalInstructionTime (2 ^ 120) (2 ^ 24) (2 ^ 16)) + 4) + 2 +
    3 * appendAllowance (2 ^ 120) ≤ 2 ^ 346 := by decide +kernel

theorem matAddTime_exact : 4 * (2 * 2 ^ 120 + 5) + (4 * 2 ^ 16) * (2 * 2 ^ 120 +
    matrixAddBodyTime (2 ^ 120) (2 ^ 24) (2 ^ 16) + 4) + 2 ≤ 2 ^ 348 := by decide +kernel

/-! ### One `j` step, the step prefix, the steps -/

theorem t2JBodyK (cf : Code) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hc : EvaluatorCaps b) (hC : b rTK1 ≤ 2 ^ 16) (hG : b rKc ≤ 9)
    (hf : Cert (MVM.compile cf) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 358 + 2 ^ 122)) :
    Cert (MVM.compile (jBodyK cf)) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 358 + 2 ^ 350) := by
  have p0 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rMA rB hc.baseMatrix
  have p1 := ((tChainC (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) 9 (2 ^ 16) (4 * 2 ^ 16)
    (2 * 2 ^ 16) (2 ^ 22) 22 b h hc.chain hc.digits hc.inner hc.columns hc.exponent.le
    hc.chainBits (by norm_num) hc.exponent.ge hC hG).mono le_rfl le_rfl tChainT_exact).mono le_rfl
      (layout_mono _ _ _ (cap_update_le b rPw2 _ hc.powers)) le_rfl
  have p2 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rGX rMA hc.gadgetCopy
  have hs : 2 * (2 ^ 16 * (2 ^ 24 * 2 ^ 16)) + 2 * b rTKNK ≤ 2 ^ 120 := by
    have := hc.rowTemplate
    calc
      _ ≤ 2 * (2 ^ 16 * (2 ^ 24 * 2 ^ 16)) + 2 * (2 ^ 16 * (2 ^ 24 * 2 ^ 16)) := by gcongr
      _ ≤ 2 ^ 120 := by norm_num
  have p3 := ((compile_agC_exact (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) b h hc.alpha hc.digits
    hs).mono le_rfl le_rfl agCTime_exact).mono le_rfl
    (layout_mono _ _ _ (gadgetResult_le _ _ _ b hc.chain.x0.ge hc.chain.rows
      hc.gadgetRow hc.gadgetMatrix)) le_rfl
  have p4 := (tGinvMulC (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) (2 ^ 16) (2 * 2 ^ 16)
    b h hc.chain.toMatrixCaps hc.digits hc.columns hc.chain.inverse hC).mono le_rfl le_rfl
      tInvT_exact
  have p5 := ((compile_matAddC_exact (2 ^ 120) (2 ^ 24) (2 ^ 16) (4 * 2 ^ 16) b h hc.chain.zero
    hc.addCount (by norm_num)).mono le_rfl le_rfl matAddTime_exact).mono le_rfl
    (layout_mono _ _ _ (matrixAddResult_le _ _ _ b hc.chain.x0.ge hc.chain.x1.ge
      hc.accumulatorStream hc.outputStream hc.addCounter hc.accumulator)) le_rfl
  have hop := operationBound_concrete (M := 2 ^ 120) (count := 2 ^ 120) le_rfl le_rfl
  have p6 := (layout_op (2 ^ 120) (2 ^ 24) (2 ^ 16) b h .aut rMu rMu rKc hc.mu).mono
    le_rfl le_rfl hop
  have p7 := (layout_op (2 ^ 120) (2 ^ 24) (2 ^ 16) b h .add rJ rJ rOne hc.index).mono
    le_rfl le_rfl hop
  rw [jBodyK]
  have all := hf.seq (p0.seq (p1.seq (p2.seq (p3.seq (p4.seq (p5.seq (p6.seq p7)))))))
  exact all.mono le_rfl le_rfl (by norm_num)

theorem t2StepPre (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hc : EvaluatorCaps b) (hC : b rTK1 ≤ 2 ^ 16) :
    Cert (MVM.compile stepPre) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 281) := by
  have p0 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rMA rA hc.inputMatrix
  have p1 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rMAd rAinS hc.inputStream.le
  have p2 := (tMulPKC (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) (2 ^ 16) (4 * 2 ^ 16) (2 * 2 ^ 16)
    b h hc.chain.toMatrixCaps hc.digits hc.inner hc.columns hC).mono le_rfl le_rfl tMatT_exact
  have p3 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rAinS rMAd hc.inputStream.ge
  have p4 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rB rMOut hc.outputMatrix
  have p5 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rAccL rT4KNK hc.accumulatorTemplate
  have p6 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rJ rZ hc.zeroIndex
  have p7 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rMu rMu0 hc.initialMu
  have p8 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rCj2 rTW hc.tableCopy
  rw [stepPre]
  have all := p0.seq (p1.seq (p2.seq (p3.seq (p4.seq (p5.seq (p6.seq (p7.seq p8)))))))
  exact all.mono le_rfl le_rfl (by norm_num)

theorem t2StepK (cf : Code) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hc : EvaluatorCaps b) (hC : b rTK1 ≤ 2 ^ 16) (hG : b rKc ≤ 9)
    (hf : Cert (MVM.compile cf) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 358 + 2 ^ 122)) :
    Cert (MVM.compile (stepK cf)) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 380 + 2 ^ 373) := by
  have p0 := t2StepPre b h hc hC
  have hb := t2JBodyK cf b h hc hC hG hf
  have p1 := rep_fixed rCj2 (jBodyK cf) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
    (2 ^ 120) (2 ^ 22) (2 ^ 358 + 2 ^ 350) h.top (by simpa using hc.tableCount) hb
  have p2 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rA rAccL hc.result
  have p3 := layout_drop (2 ^ 120) (2 ^ 24) (2 ^ 16) b h rCs rTtab (by decide)
  rw [stepK]
  have all := p0.seq (p1.seq (p2.seq p3))
  exact all.mono le_rfl le_rfl (by norm_num [moveAllowance])

theorem t2EvalC (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hc : EvaluatorCaps b) (hC : b rTK1 ≤ 2 ^ 16) (hG : b rKc ≤ 9) :
    Cert (MVM.compile evalC) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 384 + 2 ^ 378) := by
  have hfa : Cert (MVM.compile cfA) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 358 + 2 ^ 122) := (compile_cfA_flexible (2 ^ 120)
    (2 ^ 24) (2 ^ 16) 14 (2 ^ 22) b h hc.coefficient).mono le_rfl le_rfl
    ((Nat.add_le_add_left alphaCoefficientTime_exact _).trans (by norm_num))
  have hfv : Cert (MVM.compile cfV) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 358 + 2 ^ 122) := (compile_cfV_flexible (2 ^ 120)
    (2 ^ 24) (2 ^ 16) 14 (2 ^ 22) b h hc.coefficient).mono le_rfl le_rfl
    ((Nat.add_le_add_left valueCoefficientTime_exact _).trans (by norm_num))
  have p0 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rCst rT15 hc.stepsCopy
  have ha := t2StepK cfA b h hc hC hG hfa
  have p1 := rep_fixed rCst (stepK cfA) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
    (2 ^ 120) 15 (2 ^ 380 + 2 ^ 373) h.top (by simpa using hc.steps) ha
  have p2 := t2StepK cfV b h hc hC hG hfv
  rw [evalC]
  have all := p0.seq (p1.seq p2)
  exact all.mono le_rfl le_rfl (by norm_num)

/-! ### Preparation -/

theorem t2EvalReadyC_Dc (a : Fin 105 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) a) :
    Cert (MVM.compile (evalReadyC Dc)) a
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) evEnv2) (2 ^ 384 + 2 ^ 379) := by
  let ai := templateBounds (2 ^ 120) (evalInitOps Dc) (initBitsResult a)
  let af := evalFieldsResult Dc (2 ^ 120) ai
  have hi := h.evalInit Dc (by norm_num) evalInitWeight_Dc
  have hbit := evalInitBounds_bit Dc (2 ^ 120) a
  have hl := (evalInitBounds_lengths Dc (2 ^ 120) a).evalFields (2 ^ 120)
  have hsize : codecSize (mpkEnc Dc) ≤ 2 ^ 120 := keyCodec_bounds_Dc.1
  have hf := hi.evalFields Dc hsize
  have p0 := compile_evalInitC_Dc a h.top
  have p1 := compile_evalFieldsC_Dc ai hi.top hbit
  have p2 := compile_evalScratchC_Dc2 af hf hl
  have p3 := t2EvalC evEnv2 evEnv2_inputs evEnv2_caps evEnv2_tk1 evEnv2_kc
  rw [evalReadyC, evalPublicC]
  have all := p0.seq (p1.seq (p2.seq p3))
  exact all.mono le_rfl le_rfl (by norm_num)

theorem t2KeyEvalPrepareC_Dc (a : Fin 105 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) a) :
    Cert (MVM.compile (keyEvalPrepareC Dc)) a preparedBounds (2 ^ 384 + 2 ^ 380) := by
  have p0 := (t2EvalReadyC_Dc a h).mono le_rfl (layout_mono _ _ _ evEnv2_top) le_rfl
  have p1 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) (fun _ ↦ 2 ^ 120)
    preparedBounds_inputs.top 8 rA le_rfl
  have p2 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) (fun _ ↦ 2 ^ 120)
    preparedBounds_inputs.top 14 17 le_rfl
  rw [keyEvalPrepareC]
  have all := p0.seq (p1.seq p2)
  exact all.mono le_rfl le_rfl (by norm_num)

/-- **The preparation with the tight chain**: `≤ 2^384 + 2^381` (F3: `2^461`). -/
theorem t2KeyPrepareC_Dc (a : Fin 105 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) a) :
    Cert (MVM.compile (keyPrepareC Dc)) a preparedBounds (2 ^ 384 + 2 ^ 381) := by
  have p0 := compile_keyInputC_Dc a h.top
  have hi := keyInputResult_inputs Dc (2 ^ 120) (2 ^ 24) (2 ^ 16) a h (by norm_num)
    keyCodec_bounds_Dc.1 keyCodec_bounds_Dc.2.1
  have p1 := t2KeyEvalPrepareC_Dc _ hi
  rw [keyPrepareC]
  have all := p0.seq p1
  exact all.mono le_rfl le_rfl (by norm_num)

end AdvancedEncryption.ExpLUT.Prog.KeyTight
