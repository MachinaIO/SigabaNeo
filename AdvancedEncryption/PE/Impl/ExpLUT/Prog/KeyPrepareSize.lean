import PE.Impl.ExpLUT.Prog.KeyTrySize
/-! State-count bounds for master-key input and EvalPK initialization. -/
namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem take_sum_add_getD_le_sum (ns : List ℕ) (j : ℕ) :
    (ns.take j).sum + ns.getD j 0 ≤ ns.sum := by
  induction ns generalizing j with
  | nil => simp
  | cons n ns ih =>
    cases j with
    | zero => simp
    | succ j => simpa [Nat.add_assoc] using Nat.add_le_add_left (ih j) n

theorem publicFieldLengths_sum (D : Dims) :
    (publicFieldLengths D).sum = codecSize (mpkEnc D) := by
  simp only [publicFieldLengths, List.sum_cons, List.sum_nil]
  rfl

theorem weight_readPublicFieldC (D : Dims) (dst : Fin 64) (j : ℕ) :
    codeWeight (readPublicFieldC D dst j) ≤ 3 * codecSize (mpkEnc D) + 6 := by
  have hw := weight_readFieldC 17 dst ((publicFieldLengths D).take j).sum
    ((publicFieldLengths D).getD j 0)
  have hl := take_sum_add_getD_le_sum (publicFieldLengths D) j
  rw [publicFieldLengths_sum] at hl
  change codeWeight (readFieldC 17 dst _ _) ≤ _
  omega

theorem weight_evalFieldsC (D : Dims) :
    codeWeight (evalFieldsC D) ≤ 12 * codecSize (mpkEnc D) + 24 := by
  have h1 := weight_readPublicFieldC D 2 1
  have h3 := weight_readPublicFieldC D 4 3
  have h4 := weight_readPublicFieldC D 0 4
  have h5 := weight_readPublicFieldC D 1 5
  simp only [evalFieldsC, codeWeight]
  omega

theorem weight_keyInputC (D : Dims) : codeWeight (keyInputC D) ≤
    6 * codecSize (mpkEnc D) + 3 * codecSize (matE D (Wb D) (Fin D.K)) + 17 := by
  have hm := weight_readFieldC 0 17 0 (codecSize (mpkEnc D))
  have ht := weight_readFieldC 0 16 (codecSize (mpkEnc D))
    (codecSize (matE D (Wb D) (Fin D.K)))
  simp only [keyInputC, bitsC, codeWeight]
  omega

noncomputable def keyPrepareBudget (D : Dims) : ℕ :=
  18 * codecSize (mpkEnc D) + 3 * codecSize (matE D (Wb D) (Fin D.K)) +
    ((evalInitOps D).map (fun op ↦ op.2.weightBound)).sum + 2 ^ 20 + 49

theorem weight_keyPrepareC (D : Dims) :
    codeWeight (keyPrepareC D) ≤ keyPrepareBudget D := by
  have hi := weight_keyInputC D
  have hf := weight_evalFieldsC D
  have ht := weight_templateOpsC (evalInitOps D)
  have he : codeWeight evalScratchC + codeWeight evalC ≤ 2 ^ 20 := by decide +kernel
  simp only [keyPrepareC, keyEvalPrepareC, evalReadyC, evalPublicC, evalInitC,
    bitsC, codeWeight, keyPrepareBudget]
  omega

theorem size_keyPrepareC (D : Dims) :
    (compile (keyPrepareC D)).size ≤ 100000 * keyPrepareBudget D :=
  (size_compile_weight _).trans (Nat.mul_le_mul_left _ (weight_keyPrepareC D))

end AdvancedEncryption.ExpLUT.Prog
