import PE.Impl.ExpLUT.Prog.KeyTimeRead

/-! Exact register bounds after initialization and public-field loading. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM
open SigabaNeo.Lattices.Algo

theorem natResult_register (dst r : Fin 64) (n M : ℕ) (a : Fin 105 → ℕ) :
    natResult dst n M a (tR r) = if r = dst then n else a (tR r) := by
  by_cases h : r = dst
  · subst r; simp
  · rw [ite_eq_right h, natResult_other dst r h]

/-- The lengths of all nineteen constant templates used by the real evaluator. -/
structure EvalLengths (D : Dims) (a : Fin 105 → ℕ) : Prop where
  kc : a (tR rKc) = gD D
  bit1 : a (tR rBit1) = 1
  tb : a (tR rTb) = D.b
  blk : a (tR rTBlk) = 16 * D.K ^ 3 * (D.N * D.K)
  tk : a (tR rTK) = D.K
  tk1 : a (tR rTK1) = D.K - 1
  z : a (tR rZ) = D.N * D.K
  t2k : a (tR rT2K) = 2 * D.K
  tknk : a (tR rTKNK) = D.K * (D.N * D.K)
  t2knk : a (tR rT2KNK) = 2 * D.K * (D.N * D.K)
  t4knk : a (tR rT4KNK) = 2 * (2 * D.K) * (D.N * D.K)
  one : a (tR rOne) = D.N * D.K
  mu0 : a (tR rMu0) = D.N * D.K
  t4k : a (tR rT4K) = 4 * D.K
  tw : a (tR rTW) = 2 ^ D.b
  ttab : a (tR rTtab) = tlK
  xc : a (tR rXc) = D.N * D.K
  te : a (tR rTe) = 14
  t15 : a (tR rT15) = 15

theorem evalInitBounds_lengths (D : Dims) (M : ℕ) (a : Fin 105 → ℕ) :
    EvalLengths D (templateBounds M (evalInitOps D) (initBitsResult a)) := by
  constructor
  all_goals simp [templateBounds, evalInitOps, TemplateWord.value, length_encRM, natResult_register]

/-- Loading the public fields leaves every initialized template available to the evaluator. -/
theorem EvalLengths.evalFields {D : Dims} {a : Fin 105 → ℕ} (h : EvalLengths D a) (M : ℕ) :
    EvalLengths D (evalFieldsResult D M a) := by
  have hs (r : Fin 64) (h0 : r ≠ 0) (h1 : r ≠ 1) (h2 : r ≠ 2) (h4 : r ≠ 4)
      (h29 : r ≠ 29) (h30 : r ≠ 30) :=
    evalFieldsResult_other D M a r h0 h1 h2 h4 h29 h30
  constructor
  all_goals rw [hs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  all_goals first
    | exact h.kc
    | exact h.bit1
    | exact h.tb
    | exact h.blk
    | exact h.tk
    | exact h.tk1
    | exact h.z
    | exact h.t2k
    | exact h.tknk
    | exact h.t2knk
    | exact h.t4knk
    | exact h.one
    | exact h.mu0
    | exact h.t4k
    | exact h.tw
    | exact h.ttab
    | exact h.xc
    | exact h.te
    | exact h.t15

theorem evalInitBounds_bit (D : Dims) (M : ℕ) (a : Fin 105 → ℕ) :
    templateBounds M (evalInitOps D) (initBitsResult a) (tR rB1) = 1 := by
  simp [templateBounds, evalInitOps, natResult_register, initBitsResult, bitsResult]

/-- The complete initialization/loading prefix of the concrete evaluator. -/
theorem compile_evalLoad_Dc (a : Fin 105 → ℕ) (ha : ∀ t, a t ≤ 2 ^ 120) :
    Cert (MVM.compile (.seq (evalInitC Dc) (evalFieldsC Dc))) a
      (evalFieldsResult Dc (2 ^ 120)
        (templateBounds (2 ^ 120) (evalInitOps Dc) (initBitsResult a))) (2 ^ 251) := by
  have hi := compile_evalInitC_Dc a ha
  have ht := evalInitBounds_top Dc (2 ^ 120) (by norm_num) a ha evalInitWeight_Dc
  have hb := evalInitBounds_bit Dc (2 ^ 120) a
  exact (hi.seq (compile_evalFieldsC_Dc _ ht hb)).mono le_rfl le_rfl (by norm_num)

/-- Both ring-operation inputs and all evaluator template lengths survive the complete prefix. -/
theorem evalLoad_invariants (D : Dims) (M N K : ℕ) (a : Fin 105 → ℕ)
    (h : RingInputs M N K a) (hM : 1 ≤ M)
    (hw : ((evalInitOps D).map (fun op ↦ op.2.weightBound)).sum ≤ M)
    (hs : codecSize (mpkEnc D) ≤ M) :
    let b := evalFieldsResult D M (templateBounds M (evalInitOps D) (initBitsResult a))
    RingInputs M N K b ∧ EvalLengths D b :=
  ⟨(h.evalInit D hM hw).evalFields D hs, (evalInitBounds_lengths D M a).evalFields M⟩

end AdvancedEncryption.ExpLUT.Prog.KeyTime
