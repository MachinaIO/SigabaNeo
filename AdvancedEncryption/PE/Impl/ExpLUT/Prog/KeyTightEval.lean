import PE.Impl.ExpLUT.Prog.KeyTimePrepare
/-!
# KeyGen: the public evaluator with exact numeric bounds

F3's generic evaluator certificates (`compile_chainC`, `compile_mulPKC`, `compile_ginvMulC`,
`compile_cfA_flexible`, ...) are re-instantiated at the cap `2^120`, but their time expressions
are bounded exactly (`decide +kernel` on closed natural-number expressions) instead of through
F3's chain of rounded `norm_num` estimates (which lose `≈ 2^30` in total):

* chain `< 2^391` (F3: `2^422`), matrix product `< 2^386` (F3: `2^412`), inverse product
  `< 2^367`, coefficient routines `< 2^358`;
* `tJBodyK`, `tStepPre`, `tStepK`, `tEvalC` (`≤ 2^420`, F3: `2^458`);
* **`tKeyPrepareC_Dc`**: `Cert (compile (keyPrepareC Dc)) a preparedBounds (2^422)`
  (F3: `2^461`).
-/

set_option linter.unusedSectionVars false
set_option exponentiation.threshold 1000
set_option maxRecDepth 100000

namespace AdvancedEncryption.ExpLUT.Prog.KeyTight

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open AdvancedEncryption.ExpLUT.Prog
open AdvancedEncryption.ExpLUT.Prog.KeyTime

/-! ### Exact numbers -/

theorem chainTime_exact :
    chainTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) (4 * 2 ^ 16) (2 * 2 ^ 16) (2 ^ 22) 22 ≤
      2 ^ 391 := by decide +kernel

theorem matrixTime_exact :
    matrixTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) (4 * 2 ^ 16) (2 * 2 ^ 16) ≤ 2 ^ 386 := by
  decide +kernel

theorem inverseMatrixTime_exact :
    inverseMatrixTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) (2 * 2 ^ 16) ≤ 2 ^ 367 := by
  decide +kernel

theorem alphaCoefficientTime_exact :
    alphaCoefficientTime (2 ^ 120) (2 ^ 24) (2 ^ 16) 14 (2 ^ 22) ≤ 2 ^ 358 := by
  decide +kernel

theorem valueCoefficientTime_exact :
    valueCoefficientTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 22) ≤ 2 ^ 358 := by
  decide +kernel

/-! ### One `j` step, the step prefix, one alpha step -/

theorem tJBodyK (cf : Code) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hc : EvaluatorCaps b)
    (hf : Cert (MVM.compile cf) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 359)) :
    Cert (MVM.compile (jBodyK cf)) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 392) := by
  have p0 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rMA rB hc.baseMatrix
  have p1 := ((compile_chainC (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) (4 * 2 ^ 16)
    (2 * 2 ^ 16) (2 ^ 22) 22 b h hc.chain hc.digits hc.inner hc.columns hc.exponent.le
    hc.chainBits (by norm_num) hc.exponent.ge).mono le_rfl le_rfl chainTime_exact).mono le_rfl
      (layout_mono _ _ _ (cap_update_le b rPw2 _ hc.powers)) le_rfl
  have p2 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rGX rMA hc.gadgetCopy
  have p3 := (compile_agC_exact_concrete b h hc.alpha hc.digits hc.rowTemplate).mono le_rfl
    (layout_mono _ _ _ (gadgetResult_le _ _ _ b hc.chain.x0.ge hc.chain.rows
      hc.gadgetRow hc.gadgetMatrix)) le_rfl
  have p4 := (compile_ginvMulC (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) (2 * 2 ^ 16)
    b h hc.chain.toMatrixCaps hc.digits hc.columns hc.chain.inverse).mono le_rfl le_rfl
      inverseMatrixTime_exact
  have p5 := (compile_matAddC_exact_concrete b h hc.chain.zero hc.addCount).mono le_rfl
    (layout_mono _ _ _ (matrixAddResult_le _ _ _ b hc.chain.x0.ge hc.chain.x1.ge
      hc.accumulatorStream hc.outputStream hc.addCounter hc.accumulator)) le_rfl
  have hop := operationBound_concrete (M := 2 ^ 120) (count := 2 ^ 120) le_rfl le_rfl
  have p6 := (layout_op (2 ^ 120) (2 ^ 24) (2 ^ 16) b h .aut rMu rMu rKc hc.mu).mono
    le_rfl le_rfl hop
  have p7 := (layout_op (2 ^ 120) (2 ^ 24) (2 ^ 16) b h .add rJ rJ rOne hc.index).mono
    le_rfl le_rfl hop
  rw [jBodyK]
  exact (hf.seq (p0.seq (p1.seq (p2.seq (p3.seq (p4.seq (p5.seq (p6.seq p7)))))))).mono
    le_rfl le_rfl (by norm_num)

theorem tStepPre (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hc : EvaluatorCaps b) :
    Cert (MVM.compile stepPre) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 387) := by
  have p0 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rMA rA hc.inputMatrix
  have p1 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rMAd rAinS hc.inputStream.le
  have p2 := (compile_mulPKC (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) (4 * 2 ^ 16) (2 * 2 ^ 16)
    b h hc.chain.toMatrixCaps hc.digits hc.inner hc.columns).mono le_rfl le_rfl
      matrixTime_exact
  have p3 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rAinS rMAd hc.inputStream.ge
  have p4 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rB rMOut hc.outputMatrix
  have p5 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rAccL rT4KNK hc.accumulatorTemplate
  have p6 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rJ rZ hc.zeroIndex
  have p7 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rMu rMu0 hc.initialMu
  have p8 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rCj2 rTW hc.tableCopy
  rw [stepPre]
  exact (p0.seq (p1.seq (p2.seq (p3.seq (p4.seq (p5.seq (p6.seq (p7.seq p8)))))))).mono
    le_rfl le_rfl (by norm_num)

theorem tStepK (cf : Code) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hc : EvaluatorCaps b)
    (hf : Cert (MVM.compile cf) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 359)) :
    Cert (MVM.compile (stepK cf)) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 415) := by
  have p0 := tStepPre b h hc
  have hb := tJBodyK cf b h hc hf
  have p1 := rep_fixed rCj2 (jBodyK cf) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
    (2 ^ 120) (2 ^ 22) (2 ^ 392) h.top (by simpa using hc.tableCount) hb
  have p2 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rA rAccL hc.result
  have p3 := layout_drop (2 ^ 120) (2 ^ 24) (2 ^ 16) b h rCs rTtab (by decide)
  rw [stepK]
  exact (p0.seq (p1.seq (p2.seq p3))).mono le_rfl le_rfl (by norm_num [moveAllowance])

/-- The fifteen alpha steps and the value step. -/
theorem tEvalC (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hc : EvaluatorCaps b) :
    Cert (MVM.compile evalC) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 420) := by
  have hfa : Cert (MVM.compile cfA) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 359) := (compile_cfA_flexible (2 ^ 120) (2 ^ 24) (2 ^ 16) 14 (2 ^ 22) b h
    hc.coefficient).mono le_rfl le_rfl
    ((Nat.add_le_add_left alphaCoefficientTime_exact _).trans (by norm_num))
  have hfv : Cert (MVM.compile cfV) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 359) := (compile_cfV_flexible (2 ^ 120) (2 ^ 24) (2 ^ 16) 14 (2 ^ 22) b h
    hc.coefficient).mono le_rfl le_rfl
    ((Nat.add_le_add_left valueCoefficientTime_exact _).trans (by norm_num))
  have p0 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rCst rT15 hc.stepsCopy
  have ha := tStepK cfA b h hc hfa
  have p1 := rep_fixed rCst (stepK cfA) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
    (2 ^ 120) 15 (2 ^ 415) h.top (by simpa using hc.steps) ha
  have p2 := tStepK cfV b h hc hfv
  rw [evalC]
  exact (p0.seq (p1.seq p2)).mono le_rfl le_rfl (by norm_num)

/-! ### Preparation -/

theorem tEvalReadyC_Dc (a : Fin 105 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) a) :
    Cert (MVM.compile (evalReadyC Dc)) a
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) evaluatorEnvelope) (2 ^ 421) := by
  let ai := templateBounds (2 ^ 120) (evalInitOps Dc) (initBitsResult a)
  let af := evalFieldsResult Dc (2 ^ 120) ai
  have hi := h.evalInit Dc (by norm_num) evalInitWeight_Dc
  have hbit := evalInitBounds_bit Dc (2 ^ 120) a
  have hl := (evalInitBounds_lengths Dc (2 ^ 120) a).evalFields (2 ^ 120)
  have hsize : codecSize (mpkEnc Dc) ≤ 2 ^ 120 := keyCodec_bounds_Dc.1
  have hf := hi.evalFields Dc hsize
  have p0 := compile_evalInitC_Dc a h.top
  have p1 := compile_evalFieldsC_Dc ai hi.top hbit
  have p2 := compile_evalScratchC_Dc af hf hl
  have p3 := tEvalC evaluatorEnvelope evaluatorEnvelope_inputs evaluatorEnvelope_caps
  rw [evalReadyC, evalPublicC]
  exact (p0.seq (p1.seq (p2.seq p3))).mono le_rfl le_rfl (by norm_num)

theorem tKeyEvalPrepareC_Dc (a : Fin 105 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) a) :
    Cert (MVM.compile (keyEvalPrepareC Dc)) a preparedBounds (2 ^ 421 + 2 ^ 123) := by
  have p0 := (tEvalReadyC_Dc a h).mono le_rfl
    (layout_mono _ _ _ evaluatorEnvelope_top) le_rfl
  have p1 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) (fun _ ↦ 2 ^ 120)
    preparedBounds_inputs.top 8 rA le_rfl
  have p2 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) (fun _ ↦ 2 ^ 120)
    preparedBounds_inputs.top 14 17 le_rfl
  rw [keyEvalPrepareC]
  exact (p0.seq (p1.seq p2)).mono le_rfl le_rfl (by norm_num)

/-- **The preparation** (master-key input, evaluator initialization, evaluation): `≤ 2^422`. -/
theorem tKeyPrepareC_Dc (a : Fin 105 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) a) :
    Cert (MVM.compile (keyPrepareC Dc)) a preparedBounds (2 ^ 422) := by
  have p0 := compile_keyInputC_Dc a h.top
  have hi := keyInputResult_inputs Dc (2 ^ 120) (2 ^ 24) (2 ^ 16) a h (by norm_num)
    keyCodec_bounds_Dc.1 keyCodec_bounds_Dc.2.1
  have p1 := tKeyEvalPrepareC_Dc _ hi
  rw [keyPrepareC]
  exact (p0.seq p1).mono le_rfl le_rfl (by norm_num)

end AdvancedEncryption.ExpLUT.Prog.KeyTight
