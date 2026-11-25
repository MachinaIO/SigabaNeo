import PE.Impl.ExpLUT.Prog.KeyTimeCoefFlexible

/-! Composition of the actual table evaluator under a shared register envelope. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

theorem gadgetResult_le (N K R : ℕ) (b : Fin 64 → ℕ)
    (hx : N * K ≤ b rX0) (hi : b rTK ≤ b rCi)
    (hr : R * (N * K) ≤ b rRo0) (hm : 2 * (R * (N * K)) + 2 * b rTKNK ≤ b rMA) :
    gadgetResult N K R b ≤ b := by
  intro r
  by_cases h0 : r = rX0 <;> by_cases h1 : r = rCi <;>
    by_cases h2 : r = rRo0 <;> by_cases h3 : r = rMA <;>
    simp_all [gadgetResult, gadgetBase, Function.update_apply]

theorem matrixAddResult_le (N K R : ℕ) (b : Fin 64 → ℕ)
    (hx0 : N * K ≤ b rX0) (hx1 : N * K ≤ b rX1)
    (h0 : b rAccL ≤ b rRo0) (h1 : b rMOut ≤ b rRo1)
    (hc : b rT4K ≤ b rCi) (ha : R * (N * K) ≤ b rAccL) :
    matrixAddResult N K R b ≤ b := by
  intro r
  by_cases h2 : r = rX0 <;> by_cases h3 : r = rX1 <;>
    by_cases h4 : r = rRo0 <;> by_cases h5 : r = rRo1 <;>
    by_cases h6 : r = rCi <;> by_cases h7 : r = rAccL <;>
    simp_all [matrixAddResult, matrixAddBase, matrixAddScratch, Function.update_apply]

/-- All cap obligations for the compiled concrete evaluator, independently of input values. -/
structure EvaluatorCaps (b : Fin 64 → ℕ) where
  chain : ChainCaps (2 ^ 24) (2 ^ 16) b
  coefficient : CoefficientCaps (2 ^ 24) (2 ^ 16) 14 (2 ^ 22) b
  alpha : b rAl ≤ 2 ^ 24 * 2 ^ 16
  digits : b rTK ≤ 2 ^ 16
  inner : b rCi ≤ 4 * 2 ^ 16
  columns : b rCj ≤ 2 * 2 ^ 16
  exponent : b rP = 2 ^ 22
  chainBits : b rCt ≤ 22
  powers : 2 ^ 22 ≤ b rPw2
  rowTemplate : b rTKNK ≤ 2 ^ 16 * (2 ^ 24 * 2 ^ 16)
  gadgetRow : 2 ^ 16 * (2 ^ 24 * 2 ^ 16) ≤ b rRo0
  gadgetMatrix : 2 * (2 ^ 16 * (2 ^ 24 * 2 ^ 16)) + 2 * b rTKNK ≤ b rMA
  addCount : b rT4K ≤ 4 * 2 ^ 16
  addCounter : b rT4K ≤ b rCi
  accumulator : (4 * 2 ^ 16) * (2 ^ 24 * 2 ^ 16) ≤ b rAccL
  accumulatorStream : b rAccL ≤ b rRo0
  outputStream : b rMOut ≤ b rRo1
  baseMatrix : b rB ≤ b rMA
  gadgetCopy : b rMA ≤ b rGX
  mu : 2 ^ 24 * 2 ^ 16 ≤ b rMu
  index : 2 ^ 24 * 2 ^ 16 ≤ b rJ
  inputMatrix : b rA ≤ b rMA
  inputStream : b rAinS = b rMAd
  outputMatrix : b rMOut ≤ b rB
  accumulatorTemplate : b rT4KNK ≤ b rAccL
  zeroIndex : b rZ ≤ b rJ
  initialMu : b rMu0 ≤ b rMu
  tableCopy : b rTW ≤ b rCj2
  tableCount : b rCj2 ≤ 2 ^ 22
  result : b rAccL ≤ b rA
  stepsCopy : b rT15 ≤ b rCst
  steps : b rCst ≤ 15

set_option exponentiation.threshold 1000 in
theorem compile_jBodyK_concrete (cf : Code) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hc : EvaluatorCaps b)
    (hf : Cert (MVM.compile cf) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 376)) :
    Cert (MVM.compile (jBodyK cf)) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 424) := by
  have p0 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rMA rB hc.baseMatrix
  have p1 := (compile_chainC_concrete b h hc.chain hc.digits hc.inner hc.columns
    hc.exponent hc.chainBits).mono le_rfl
      (layout_mono _ _ _ (cap_update_le b rPw2 _ hc.powers)) le_rfl
  have p2 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rGX rMA hc.gadgetCopy
  have p3 := (compile_agC_exact_concrete b h hc.alpha hc.digits hc.rowTemplate).mono le_rfl
    (layout_mono _ _ _ (gadgetResult_le _ _ _ b hc.chain.x0.ge hc.chain.rows
      hc.gadgetRow hc.gadgetMatrix)) le_rfl
  have p4 := compile_ginvMulC_concrete b h hc.chain.toMatrixCaps hc.digits hc.columns hc.chain.inverse
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

set_option exponentiation.threshold 1000 in
theorem compile_stepPre_concrete (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hc : EvaluatorCaps b) :
    Cert (MVM.compile stepPre) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 414) := by
  have p0 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rMA rA hc.inputMatrix
  have p1 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rMAd rAinS hc.inputStream.le
  have p2 := compile_mulPKC_concrete b h hc.chain.toMatrixCaps hc.digits hc.inner hc.columns
  have p3 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rAinS rMAd hc.inputStream.ge
  have p4 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rB rMOut hc.outputMatrix
  have p5 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rAccL rT4KNK hc.accumulatorTemplate
  have p6 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rJ rZ hc.zeroIndex
  have p7 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rMu rMu0 hc.initialMu
  have p8 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rCj2 rTW hc.tableCopy
  rw [stepPre]
  exact (p0.seq (p1.seq (p2.seq (p3.seq (p4.seq (p5.seq (p6.seq (p7.seq p8)))))))).mono
    le_rfl le_rfl (by norm_num)

set_option exponentiation.threshold 1000 in
theorem compile_stepK_concrete (cf : Code) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hc : EvaluatorCaps b)
    (hf : Cert (MVM.compile cf) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 376)) :
    Cert (MVM.compile (stepK cf)) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 452) := by
  have p0 := compile_stepPre_concrete b h hc
  have hb := compile_jBodyK_concrete cf b h hc hf
  have p1 := rep_fixed rCj2 (jBodyK cf) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
    (2 ^ 120) (2 ^ 22) (2 ^ 424) h.top (by simpa using hc.tableCount) hb
  have p2 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rA rAccL hc.result
  have p3 := layout_drop (2 ^ 120) (2 ^ 24) (2 ^ 16) b h rCs rTtab (by decide)
  rw [stepK]
  exact (p0.seq (p1.seq (p2.seq p3))).mono le_rfl le_rfl (by norm_num [moveAllowance])

set_option exponentiation.threshold 1000 in
/-- The actual fifteen alpha steps and final value step, with their real coefficient routines. -/
theorem compile_evalC_concrete (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hc : EvaluatorCaps b) :
    Cert (MVM.compile evalC) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 458) := by
  have hfa := compile_cfA_flexible_concrete b h hc.coefficient
  have hfv := (compile_cfV_flexible_concrete b h hc.coefficient).mono le_rfl le_rfl
    (show 2 ^ 369 ≤ 2 ^ 376 by norm_num)
  have p0 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) b h.top rCst rT15 hc.stepsCopy
  have ha := compile_stepK_concrete cfA b h hc hfa
  have p1 := rep_fixed rCst (stepK cfA) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
    (2 ^ 120) 15 (2 ^ 452) h.top (by simpa using hc.steps) ha
  have p2 := compile_stepK_concrete cfV b h hc hfv
  rw [evalC]
  exact (p0.seq (p1.seq p2)).mono le_rfl le_rfl (by norm_num)

/-- A concrete shared envelope; large streams use M, overwritten scalar work uses small caps. -/
def evaluatorEnvelope (r : Fin 64) : ℕ :=
  if r = rX0 ∨ r = rX1 ∨ r = rAc0 ∨ r = rAc1 ∨ r = rDA ∨ r = rZ ∨ r = rAl ∨ r = rOne then
    2 ^ 24 * 2 ^ 16
  else if r = rTK then 2 ^ 16
  else if r = rCi ∨ r = rT4K then 4 * 2 ^ 16
  else if r = rCj ∨ r = rT2K then 2 * 2 ^ 16
  else if r = rP ∨ r = rPw2 ∨ r = rTW ∨ r = rCj2 then 2 ^ 22
  else if r = rCt ∨ r = rTb then 22
  else if r = rTe then 14
  else if r = rCst ∨ r = rT15 then 15
  else if r = rBit1 then 1
  else if r = rTKNK then 2 ^ 16 * (2 ^ 24 * 2 ^ 16)
  else 2 ^ 120

theorem evaluatorEnvelope_top (r : Fin 64) : evaluatorEnvelope r ≤ 2 ^ 120 := by
  unfold evaluatorEnvelope
  split_ifs <;> norm_num

theorem evaluatorEnvelope_inputs :
    RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) evaluatorEnvelope) :=
  layout_inputs _ _ _ _ evaluatorEnvelope_top (by norm_num) (by norm_num) (by norm_num)

theorem evaluatorEnvelope_caps : EvaluatorCaps evaluatorEnvelope := by
  exact {
    chain := {
      toMatrixCaps := {
        toInnerCaps := {
          x0 := by norm_num [evaluatorEnvelope]
          x1 := by norm_num [evaluatorEnvelope]
          ac0 := by norm_num [evaluatorEnvelope]
          ac1 := by norm_num [evaluatorEnvelope]
          da := by norm_num [evaluatorEnvelope]
          dx := by norm_num [evaluatorEnvelope]
          zero := by norm_num [evaluatorEnvelope]
          stream := by norm_num [evaluatorEnvelope]
          counter := by norm_num [evaluatorEnvelope]
        }
        tmp := by norm_num [evaluatorEnvelope]
        row0 := by norm_num [evaluatorEnvelope]
        row1 := by norm_num [evaluatorEnvelope]
        col0 := by norm_num [evaluatorEnvelope]
        col1 := by norm_num [evaluatorEnvelope]
        trans0 := by norm_num [evaluatorEnvelope]
        trans1 := by norm_num [evaluatorEnvelope]
        sums := by norm_num [evaluatorEnvelope]
        streamOut := by norm_num [evaluatorEnvelope]
        output := by norm_num [evaluatorEnvelope]
        columns := by norm_num [evaluatorEnvelope]
        rows := by norm_num [evaluatorEnvelope]
      }
      out := by norm_num [evaluatorEnvelope]
      again := by norm_num [evaluatorEnvelope]
      inverse := by norm_num [evaluatorEnvelope]
      saved := by norm_num [evaluatorEnvelope]
      source := by norm_num [evaluatorEnvelope]
      autWords := by norm_num [evaluatorEnvelope]
      hWords := by norm_num [evaluatorEnvelope]
      bit := by norm_num [evaluatorEnvelope]
      count := by norm_num [evaluatorEnvelope]
      read := by norm_num [evaluatorEnvelope]
      bitOutput := by norm_num [evaluatorEnvelope]
      gadget := by norm_num [evaluatorEnvelope]
    }
    coefficient := {
      accumulator := by norm_num [evaluatorEnvelope]
      power := by norm_num [evaluatorEnvelope]
      entry := by norm_num [evaluatorEnvelope]
      bit := by norm_num [evaluatorEnvelope]
      bitCopy := by norm_num [evaluatorEnvelope]
      bits := by norm_num [evaluatorEnvelope]
      doubling := by norm_num [evaluatorEnvelope]
      zero := by norm_num [evaluatorEnvelope]
      one := by norm_num [evaluatorEnvelope]
      tableCopy := by norm_num [evaluatorEnvelope]
      table := by norm_num [evaluatorEnvelope]
      predicate := by norm_num [evaluatorEnvelope]
    }
    alpha := by norm_num [evaluatorEnvelope]
    digits := by norm_num [evaluatorEnvelope]
    inner := by norm_num [evaluatorEnvelope]
    columns := by norm_num [evaluatorEnvelope]
    exponent := by norm_num [evaluatorEnvelope]
    chainBits := by norm_num [evaluatorEnvelope]
    powers := by norm_num [evaluatorEnvelope]
    rowTemplate := by norm_num [evaluatorEnvelope]
    gadgetRow := by norm_num [evaluatorEnvelope]
    gadgetMatrix := by norm_num [evaluatorEnvelope]
    addCount := by norm_num [evaluatorEnvelope]
    addCounter := by norm_num [evaluatorEnvelope]
    accumulator := by norm_num [evaluatorEnvelope]
    accumulatorStream := by norm_num [evaluatorEnvelope]
    outputStream := by norm_num [evaluatorEnvelope]
    baseMatrix := by norm_num [evaluatorEnvelope]
    gadgetCopy := by norm_num [evaluatorEnvelope]
    mu := by norm_num [evaluatorEnvelope]
    index := by norm_num [evaluatorEnvelope]
    inputMatrix := by norm_num [evaluatorEnvelope]
    inputStream := by norm_num [evaluatorEnvelope]
    outputMatrix := by norm_num [evaluatorEnvelope]
    accumulatorTemplate := by norm_num [evaluatorEnvelope]
    zeroIndex := by norm_num [evaluatorEnvelope]
    initialMu := by norm_num [evaluatorEnvelope]
    tableCopy := by norm_num [evaluatorEnvelope]
    tableCount := by norm_num [evaluatorEnvelope]
    result := by norm_num [evaluatorEnvelope]
    stepsCopy := by norm_num [evaluatorEnvelope]
    steps := by norm_num [evaluatorEnvelope]
  }

/-- Unconditional runtime certificate on the explicit evaluator envelope. -/
theorem compile_evalC_envelope :
    Cert (MVM.compile evalC)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) evaluatorEnvelope)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) evaluatorEnvelope) (2 ^ 458) :=
  compile_evalC_concrete evaluatorEnvelope evaluatorEnvelope_inputs evaluatorEnvelope_caps

end AdvancedEncryption.ExpLUT.Prog.KeyTime
