import PE.Impl.ExpLUT.Prog.KeyGatherSize
/-! Size bounds for the coefficient-stream builders in actual KeyGen public rows. -/
namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

theorem weight_prefixC (n : ℕ) : codeWeight (prefixC n) ≤ 3 * n + 4 := by
  have h := weight_natC 2 rB1 n
  simp only [prefixC, takeC, codeWeight]
  omega

theorem weight_appendAFC (N K : ℕ) (first : Bool) :
    codeWeight (appendAFC N K first) ≤ 6 * K * (N * K) + 5 := by
  have hp := weight_prefixC ((2 * K) * (N * K))
  have hn := weight_natC 6 rB1 ((2 * K) * (N * K))
  cases first <;> simp only [appendAFC, Bool.false_eq_true, ↓reduceIte, codeWeight] <;> nlinarith

theorem weight_negativeCoeffC (N K helpers : ℕ) :
    codeWeight (negativeCoeffC N K helpers) ≤
      3 * K + 3 * K * (N * K) + 3 * helpers + 12 := by
  have hk := weight_natC 2 rB1 K
  have hn := weight_natC 6 rB1 (K * (N * K))
  have hh := weight_natC 2 rB1 helpers
  simp only [negativeCoeffC, powersC, powersBody, repAppC, codeWeight]
  nlinarith

theorem weight_ringOneC (N K : ℕ) : codeWeight (ringOneC N K) ≤ 3 * (N * K) + 8 := by
  have hn := weight_natC 7 rB1 (N * K - 1)
  have hs := Nat.sub_le (N * K) 1
  simp only [ringOneC, bitsC, codeWeight]
  omega

theorem weight_negativeReadyC (N K helpers : ℕ) :
    codeWeight (negativeReadyC N K helpers) ≤
      3 * K + 3 * K * (N * K) + 3 * (N * K) + 3 * helpers + 20 := by
  have hr := weight_ringOneC N K
  have hn := weight_negativeCoeffC N K helpers
  simp only [negativeReadyC, codeWeight]
  omega

theorem weight_autGatheredC (n k : ℕ) : codeWeight (autGatheredC n k) ≤ 3 * n + 3 * k + 9 := by
  have hn := weight_natC rQc rB1 n
  have hk := weight_natC rQk rB1 k
  simp only [autGatheredC, autQC, autQBody, codeWeight]
  omega

theorem weight_gatherAutC (N K k J : ℕ) (js : List ℕ) (hj : ∀ j ∈ js, j ≤ J) :
    codeWeight (gatherAutC N K k js) ≤ js.length * (3 * J * (N * K) + 9) + 3 * k + 11 := by
  have hg := weight_gatherC N K J js hj
  have ha := weight_autGatheredC js.length k
  simp only [gatherAutC, codeWeight]
  nlinarith

end AdvancedEncryption.ExpLUT.Prog
