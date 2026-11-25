import PE.Impl.ExpLUT.Prog.KeyTimeEvalReady
/-!
# Cost certificate of `mid`, phase M2 (part 1): F3's public evaluator at the tape cap `2^104`

F3's `KeyTime` certificates of the public evaluator are generic in the tape cap `M`; its concrete
layer (`KeyTimeEval`, `compile_evalC_envelope ≤ 2^458`) instantiates them at `M = 2^120` with the
per-instruction cost rounded to `2^341`. In phase M2 every tape is below `2^104` (the msk word
with the zero trapdoor is `≈ 2^98.3` bits), so the same generic lemmas are instantiated here at
**`M = 2^104`**: a ring instruction costs `evalInstructionTime ≤ 2^298` and the evaluator
`≤ 2^388` (**`c2_evalC_env`**). All numeric facts are closed numerals (`decide`/`norm_num`).

The envelope `c2Env` is F3's `evaluatorEnvelope` with the cap `2^104` in place of `2^120`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 2000

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyC

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM
open AdvancedEncryption.ExpLUT.Prog
open AdvancedEncryption.ExpLUT.Prog.KeyTime

/-! ### Numeric facts at `M = 2^104` -/

theorem c2_op : operationBound (2 ^ 104) (2 ^ 24) (2 ^ 16) (2 ^ 104) ≤ 2 ^ 298 := by decide
theorem c2_ins : evalInstructionTime (2 ^ 104) (2 ^ 24) (2 ^ 16) ≤ 2 ^ 298 := by decide
theorem c2_cfA_t : (2 * 2 ^ 104 + 5) + alphaCoefficientTime (2 ^ 104) (2 ^ 24) (2 ^ 16) 14 (2 ^ 22)
    ≤ 2 ^ 326 := by decide
theorem c2_cfV_t : (2 * 2 ^ 104 + 5) + valueCoefficientTime (2 ^ 104) (2 ^ 24) (2 ^ 16) (2 ^ 22)
    ≤ 2 ^ 326 := by decide
theorem c2_mat_t : matrixTime (2 ^ 104) (2 ^ 24) (2 ^ 16) (2 ^ 16) (4 * 2 ^ 16) (2 * 2 ^ 16)
    ≤ 2 ^ 354 := by decide
theorem c2_imat_t : inverseMatrixTime (2 ^ 104) (2 ^ 24) (2 ^ 16) (2 ^ 16) (2 * 2 ^ 16)
    ≤ 2 ^ 335 := by decide
theorem c2_chain_t : chainTime (2 ^ 104) (2 ^ 24) (2 ^ 16) (2 ^ 16) (4 * 2 ^ 16) (2 * 2 ^ 16)
    (2 ^ 22) 22 ≤ 2 ^ 359 := by decide
theorem c2_ag_t : 4 * (2 * 2 ^ 104 + 5) + 2 ^ 16 * (2 * 2 ^ 104 + (appendAllowance (2 ^ 104) +
    evalInstructionTime (2 ^ 104) (2 ^ 24) (2 ^ 16)) + 4) + 2 + 3 * appendAllowance (2 ^ 104)
    ≤ 2 ^ 315 := by decide
theorem c2_ma_t : 4 * (2 * 2 ^ 104 + 5) + (4 * 2 ^ 16) * (2 * 2 ^ 104 +
    matrixAddBodyTime (2 ^ 104) (2 ^ 24) (2 ^ 16) + 4) + 2 ≤ 2 ^ 318 := by decide
theorem c2_mv_t : moveAllowance (2 ^ 104) ≤ 2 ^ 213 := by decide

/-! ### The evaluator -/

theorem c2_jBodyK (cf : Code) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 104) (2 ^ 24) (2 ^ 16) (layout (2 ^ 104) (2 ^ 24) (2 ^ 16) b))
    (hc : EvaluatorCaps b)
    (hf : Cert (MVM.compile cf) (layout (2 ^ 104) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 104) (2 ^ 24) (2 ^ 16) b) (2 ^ 326)) :
    Cert (MVM.compile (jBodyK cf)) (layout (2 ^ 104) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 104) (2 ^ 24) (2 ^ 16) b) (2 ^ 360) := by
  have p0 := layout_copy (2 ^ 104) (2 ^ 24) (2 ^ 16) b h.top rMA rB hc.baseMatrix
  have p1 := ((compile_chainC (2 ^ 104) (2 ^ 24) (2 ^ 16) (2 ^ 16) (4 * 2 ^ 16)
    (2 * 2 ^ 16) (2 ^ 22) 22 b h hc.chain hc.digits hc.inner hc.columns hc.exponent.le
    hc.chainBits (by norm_num) hc.exponent.ge).mono le_rfl le_rfl c2_chain_t).mono le_rfl
      (layout_mono _ _ _ (cap_update_le b rPw2 _ hc.powers)) le_rfl
  have p2 := layout_copy (2 ^ 104) (2 ^ 24) (2 ^ 16) b h.top rGX rMA hc.gadgetCopy
  have hs : 2 * (2 ^ 16 * (2 ^ 24 * 2 ^ 16)) + 2 * b rTKNK ≤ 2 ^ 104 := by
    have := hc.rowTemplate
    calc _ ≤ 2 * (2 ^ 16 * (2 ^ 24 * 2 ^ 16)) + 2 * (2 ^ 16 * (2 ^ 24 * 2 ^ 16)) := by omega
      _ ≤ 2 ^ 104 := by norm_num
  have p3 := ((compile_agC_exact (2 ^ 104) (2 ^ 24) (2 ^ 16) (2 ^ 16) b h hc.alpha hc.digits
    hs).mono le_rfl le_rfl c2_ag_t).mono le_rfl
      (layout_mono _ _ _ (gadgetResult_le _ _ _ b hc.chain.x0.ge hc.chain.rows
        hc.gadgetRow hc.gadgetMatrix)) le_rfl
  have p4 := (compile_ginvMulC (2 ^ 104) (2 ^ 24) (2 ^ 16) (2 ^ 16) (2 * 2 ^ 16) b h
    hc.chain.toMatrixCaps hc.digits hc.columns hc.chain.inverse).mono le_rfl le_rfl c2_imat_t
  have p5 := ((compile_matAddC_exact (2 ^ 104) (2 ^ 24) (2 ^ 16) (4 * 2 ^ 16) b h hc.chain.zero
    hc.addCount (by norm_num)).mono le_rfl le_rfl c2_ma_t).mono le_rfl
      (layout_mono _ _ _ (matrixAddResult_le _ _ _ b hc.chain.x0.ge hc.chain.x1.ge
        hc.accumulatorStream hc.outputStream hc.addCounter hc.accumulator)) le_rfl
  have p6 := (layout_op (2 ^ 104) (2 ^ 24) (2 ^ 16) b h .aut rMu rMu rKc hc.mu).mono
    le_rfl le_rfl c2_op
  have p7 := (layout_op (2 ^ 104) (2 ^ 24) (2 ^ 16) b h .add rJ rJ rOne hc.index).mono
    le_rfl le_rfl c2_op
  rw [jBodyK]
  exact (hf.seq (p0.seq (p1.seq (p2.seq (p3.seq (p4.seq (p5.seq (p6.seq p7)))))))).mono
    le_rfl le_rfl (by norm_num)

theorem c2_stepPre (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 104) (2 ^ 24) (2 ^ 16) (layout (2 ^ 104) (2 ^ 24) (2 ^ 16) b))
    (hc : EvaluatorCaps b) :
    Cert (MVM.compile stepPre) (layout (2 ^ 104) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 104) (2 ^ 24) (2 ^ 16) b) (2 ^ 355) := by
  have p0 := layout_copy (2 ^ 104) (2 ^ 24) (2 ^ 16) b h.top rMA rA hc.inputMatrix
  have p1 := layout_copy (2 ^ 104) (2 ^ 24) (2 ^ 16) b h.top rMAd rAinS hc.inputStream.le
  have p2 := (compile_mulPKC (2 ^ 104) (2 ^ 24) (2 ^ 16) (2 ^ 16) (4 * 2 ^ 16) (2 * 2 ^ 16)
    b h hc.chain.toMatrixCaps hc.digits hc.inner hc.columns).mono le_rfl le_rfl c2_mat_t
  have p3 := layout_copy (2 ^ 104) (2 ^ 24) (2 ^ 16) b h.top rAinS rMAd hc.inputStream.ge
  have p4 := layout_copy (2 ^ 104) (2 ^ 24) (2 ^ 16) b h.top rB rMOut hc.outputMatrix
  have p5 := layout_copy (2 ^ 104) (2 ^ 24) (2 ^ 16) b h.top rAccL rT4KNK hc.accumulatorTemplate
  have p6 := layout_copy (2 ^ 104) (2 ^ 24) (2 ^ 16) b h.top rJ rZ hc.zeroIndex
  have p7 := layout_copy (2 ^ 104) (2 ^ 24) (2 ^ 16) b h.top rMu rMu0 hc.initialMu
  have p8 := layout_copy (2 ^ 104) (2 ^ 24) (2 ^ 16) b h.top rCj2 rTW hc.tableCopy
  rw [stepPre]
  exact (p0.seq (p1.seq (p2.seq (p3.seq (p4.seq (p5.seq (p6.seq (p7.seq p8)))))))).mono
    le_rfl le_rfl (by norm_num)

theorem c2_stepK (cf : Code) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 104) (2 ^ 24) (2 ^ 16) (layout (2 ^ 104) (2 ^ 24) (2 ^ 16) b))
    (hc : EvaluatorCaps b)
    (hf : Cert (MVM.compile cf) (layout (2 ^ 104) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 104) (2 ^ 24) (2 ^ 16) b) (2 ^ 326)) :
    Cert (MVM.compile (stepK cf)) (layout (2 ^ 104) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 104) (2 ^ 24) (2 ^ 16) b) (2 ^ 383) := by
  have p0 := c2_stepPre b h hc
  have hb := c2_jBodyK cf b h hc hf
  have p1 := rep_fixed rCj2 (jBodyK cf) (layout (2 ^ 104) (2 ^ 24) (2 ^ 16) b)
    (2 ^ 104) (2 ^ 22) (2 ^ 360) h.top (by simpa using hc.tableCount) hb
  have p2 := layout_copy (2 ^ 104) (2 ^ 24) (2 ^ 16) b h.top rA rAccL hc.result
  have p3 := (layout_drop (2 ^ 104) (2 ^ 24) (2 ^ 16) b h rCs rTtab (by decide)).mono
    le_rfl le_rfl c2_mv_t
  rw [stepK]
  exact (p0.seq (p1.seq (p2.seq p3))).mono le_rfl le_rfl (by norm_num)

theorem c2_evalC (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 104) (2 ^ 24) (2 ^ 16) (layout (2 ^ 104) (2 ^ 24) (2 ^ 16) b))
    (hc : EvaluatorCaps b) :
    Cert (MVM.compile evalC) (layout (2 ^ 104) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 104) (2 ^ 24) (2 ^ 16) b) (2 ^ 388) := by
  have hfa := (compile_cfA_flexible (2 ^ 104) (2 ^ 24) (2 ^ 16) 14 (2 ^ 22) b h
    hc.coefficient).mono le_rfl le_rfl c2_cfA_t
  have hfv := (compile_cfV_flexible (2 ^ 104) (2 ^ 24) (2 ^ 16) 14 (2 ^ 22) b h
    hc.coefficient).mono le_rfl le_rfl c2_cfV_t
  have p0 := layout_copy (2 ^ 104) (2 ^ 24) (2 ^ 16) b h.top rCst rT15 hc.stepsCopy
  have ha := c2_stepK cfA b h hc hfa
  have p1 := rep_fixed rCst (stepK cfA) (layout (2 ^ 104) (2 ^ 24) (2 ^ 16) b)
    (2 ^ 104) 15 (2 ^ 383) h.top (by simpa using hc.steps) ha
  have p2 := c2_stepK cfV b h hc hfv
  rw [evalC]
  exact (p0.seq (p1.seq p2)).mono le_rfl le_rfl (by norm_num)

/-- F3's evaluator envelope with the cap `2^104`. -/
def c2Env (r : Fin 64) : ℕ :=
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
  else 2 ^ 104

theorem c2Env_top (r : Fin 64) : c2Env r ≤ 2 ^ 104 := by
  unfold c2Env
  split_ifs <;> norm_num

theorem c2Env_inputs :
    RingInputs (2 ^ 104) (2 ^ 24) (2 ^ 16) (layout (2 ^ 104) (2 ^ 24) (2 ^ 16) c2Env) :=
  layout_inputs _ _ _ _ c2Env_top (by norm_num) (by norm_num) (by norm_num)

theorem c2Env_caps : EvaluatorCaps c2Env := by
  exact {
    chain := {
      toMatrixCaps := {
        toInnerCaps := {
          x0 := by norm_num [c2Env]
          x1 := by norm_num [c2Env]
          ac0 := by norm_num [c2Env]
          ac1 := by norm_num [c2Env]
          da := by norm_num [c2Env]
          dx := by norm_num [c2Env]
          zero := by norm_num [c2Env]
          stream := by norm_num [c2Env]
          counter := by norm_num [c2Env]
        }
        tmp := by norm_num [c2Env]
        row0 := by norm_num [c2Env]
        row1 := by norm_num [c2Env]
        col0 := by norm_num [c2Env]
        col1 := by norm_num [c2Env]
        trans0 := by norm_num [c2Env]
        trans1 := by norm_num [c2Env]
        sums := by norm_num [c2Env]
        streamOut := by norm_num [c2Env]
        output := by norm_num [c2Env]
        columns := by norm_num [c2Env]
        rows := by norm_num [c2Env]
      }
      out := by norm_num [c2Env]
      again := by norm_num [c2Env]
      inverse := by norm_num [c2Env]
      saved := by norm_num [c2Env]
      source := by norm_num [c2Env]
      autWords := by norm_num [c2Env]
      hWords := by norm_num [c2Env]
      bit := by norm_num [c2Env]
      count := by norm_num [c2Env]
      read := by norm_num [c2Env]
      bitOutput := by norm_num [c2Env]
      gadget := by norm_num [c2Env]
    }
    coefficient := {
      accumulator := by norm_num [c2Env]
      power := by norm_num [c2Env]
      entry := by norm_num [c2Env]
      bit := by norm_num [c2Env]
      bitCopy := by norm_num [c2Env]
      bits := by norm_num [c2Env]
      doubling := by norm_num [c2Env]
      zero := by norm_num [c2Env]
      one := by norm_num [c2Env]
      tableCopy := by norm_num [c2Env]
      table := by norm_num [c2Env]
      predicate := by norm_num [c2Env]
    }
    alpha := by norm_num [c2Env]
    digits := by norm_num [c2Env]
    inner := by norm_num [c2Env]
    columns := by norm_num [c2Env]
    exponent := by norm_num [c2Env]
    chainBits := by norm_num [c2Env]
    powers := by norm_num [c2Env]
    rowTemplate := by norm_num [c2Env]
    gadgetRow := by norm_num [c2Env]
    gadgetMatrix := by norm_num [c2Env]
    addCount := by norm_num [c2Env]
    addCounter := by norm_num [c2Env]
    accumulator := by norm_num [c2Env]
    accumulatorStream := by norm_num [c2Env]
    outputStream := by norm_num [c2Env]
    baseMatrix := by norm_num [c2Env]
    gadgetCopy := by norm_num [c2Env]
    mu := by norm_num [c2Env]
    index := by norm_num [c2Env]
    inputMatrix := by norm_num [c2Env]
    inputStream := by norm_num [c2Env]
    outputMatrix := by norm_num [c2Env]
    accumulatorTemplate := by norm_num [c2Env]
    zeroIndex := by norm_num [c2Env]
    initialMu := by norm_num [c2Env]
    tableCopy := by norm_num [c2Env]
    tableCount := by norm_num [c2Env]
    result := by norm_num [c2Env]
    stepsCopy := by norm_num [c2Env]
    steps := by norm_num [c2Env]
  }

/-- **The evaluator on the envelope `c2Env`.** -/
theorem c2_evalC_env :
    Cert (MVM.compile evalC) (layout (2 ^ 104) (2 ^ 24) (2 ^ 16) c2Env)
      (layout (2 ^ 104) (2 ^ 24) (2 ^ 16) c2Env) (2 ^ 388) :=
  c2_evalC c2Env c2Env_inputs c2Env_caps

end AdvancedEncryption.ExpLUT.Prog.RedKeyC
