import PE.Impl.ExpLUT.Prog.KeyTimeCounted
/-! A common explicit polynomial bound for all actual MVM ring instructions. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM
open SigabaNeo.Tape.Sym Prog.SpecT Prog.MersenneT

/-- Includes both loads, the operation, canonicalization, and output cleanup. -/
def operationBound (M N K count : ℕ) : ℕ :=
  1000 * (M + 1) * (N + 1) ^ 2 * (K + 1) ^ 2 * (count + 1)

theorem binaryTime_le (M N K : ℕ) (o : Op) :
    binaryTime M N K o ≤ operationBound M N K 0 := by
  cases o <;>
    simp [binaryTime, binaryPoly, operationBound, wMulRM, wAddRM, pEval, mEval] <;>
    ring_nf <;> omega

theorem countedTime_le (M N K count : ℕ) (o : Op) :
    countedTime M N K count o ≤ operationBound M N K count := by
  cases o <;>
    simp [countedTime, countedPoly, operationBound, wNotM, wAut, wRhoJ, wRotB,
      RingVM.wDigitM, wDigit, pEval, mEval] <;> ring_nf <;> omega

theorem operationBound_mono {M N K c M' N' K' c' : ℕ}
    (hm : M ≤ M') (hn : N ≤ N') (hk : K ≤ K') (hc : c ≤ c') :
    operationBound M N K c ≤ operationBound M' N' K' c' := by
  unfold operationBound
  gcongr

set_option exponentiation.threshold 1000 in
/-- Conditional scalar estimate; callers must establish the tape/counter bounds. -/
theorem operationBound_concrete {M count : ℕ} (hM : M ≤ 2 ^ 120) (hc : count ≤ 2 ^ 120) :
    operationBound M (2 ^ 24) (2 ^ 16) count ≤ 2 ^ 340 := by
  apply (operationBound_mono hM (le_refl _) (le_refl _) hc).trans
  norm_num [operationBound]

def operationResult (M N K : ℕ) (o : Op) (d c : Fin 64) (a : Fin 105 → ℕ) : Fin 105 → ℕ :=
  if o.bin then binaryResult M N K d a else countedResult M N K (a (tR c)) d c a

/-- One uniform certificate covers every ring instruction in the actual compiler. -/
theorem compile_op_cert (M N K : ℕ) (o : Op) (d s c : Fin 64) (a : Fin 105 → ℕ)
    (h : Ready M N K a) :
    Cert (MVM.compile (.op o d s c)) a (operationResult M N K o d c a)
      (operationBound M N K (a (tR c))) := by
  by_cases ho : o.bin = true
  · have hb : o = .add ∨ o = .sub ∨ o = .mul := by cases o <;> simp_all [Op.bin]
    have hh := compile_binary_cert o hb d s c M N K a h.top h.ring h.dimension h.width
      h.templateK h.templateN h.zeros h.ones h.work h.scratch1 h.scratch2
    have ht := (binaryTime_le M N K o).trans
      (operationBound_mono (le_refl M) (le_refl N) (le_refl K) (Nat.zero_le (a (tR c))))
    simpa only [operationResult, ho, ↓reduceIte] using hh.mono le_rfl le_rfl ht
  · have hf : o.bin = false := Bool.eq_false_iff.mpr ho
    have hh := compile_counted_cert o hf d s c M N K a h.top h.ring h.dimension h.width
      h.templateK h.templateN h.zeros h.ones h.work h.scratch1 h.scratch2
    simpa only [operationResult, hf, Bool.false_eq_true, ↓reduceIte] using
      hh.mono le_rfl le_rfl (countedTime_le M N K (a (tR c)) o)

/-- This concrete instruction bound retains an explicit, necessary readiness premise. -/
theorem compile_op_concrete (o : Op) (d s c : Fin 64) (a : Fin 105 → ℕ)
    (h : Ready (2 ^ 120) (2 ^ 24) (2 ^ 16) a) :
    Cert (MVM.compile (.op o d s c)) a
      (operationResult (2 ^ 120) (2 ^ 24) (2 ^ 16) o d c a) (2 ^ 340) :=
  (compile_op_cert _ _ _ o d s c a h).mono le_rfl le_rfl
    (operationBound_concrete le_rfl (h.top _))

end AdvancedEncryption.ExpLUT.Prog.KeyTime
