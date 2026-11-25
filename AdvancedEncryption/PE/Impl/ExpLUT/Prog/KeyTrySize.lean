import PE.Impl.ExpLUT.Prog.KeyDigitsSize
import PE.Impl.ExpLUT.Prog.KeyAcceptSize

/-! State-count composition for a complete deterministic KeyGen attempt. -/
namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

structure TrySizeInputs (D : Dims) (S : ℕ) : Prop extends PublicSizeInputs D S where
  trap : (Enum.list (α := Wb D × Fin D.K)).length ≤ S
  digits : (Enum.list (α := ZIdx (setting D).τ (setting D).E.W)).length ≤ S
  output : (Enum.list (α := KColt D)).length ≤ S
  assembly : (Enum.list (α := AssemblySource D)).length ≤ S

noncomputable def proposalBudget (D : Dims) (S : ℕ) : ℕ :=
  keyDigitsBudget D S + S * (correctionCoordBudget D S + 1) +
    S * (3 * S * (D.N * D.K) + 6) + 8

theorem weight_proposalKeyC (D : Dims) (S : ℕ) (h : TrySizeInputs D S) :
    codeWeight (proposalKeyC D) ≤ proposalBudget D S := by
  have hd := weight_keyDigitsC D S h.toPublicSizeInputs
  have hc := weight_correctionAppendC D S h.trap h.digits h.candidate Enum.list
  have hc' := Nat.mul_le_mul_right (correctionCoordBudget D S + 1) h.candidate
  have ha := weight_assembleC D
  have ha' := Nat.mul_le_mul h.output
    (Nat.add_le_add_right (Nat.mul_le_mul_right (D.N * D.K)
      (Nat.mul_le_mul_left 3 h.assembly)) 6)
  simp only [proposalKeyC, proposalC, correctionC, codeWeight, proposalBudget]
  omega

noncomputable def tryBudget (D : Dims) (S B : ℕ) : ℕ :=
  proposalBudget D S + D.K + 3 * D.N + 3 * B + 3 * (D.K - B) +
    3 * S + 3 * codecSize (keyEnc D) + 119

theorem weight_tryKeyC (D : Dims) (S B r : ℕ) (h : TrySizeInputs D S) :
    codeWeight (tryKeyC D B r) ≤ tryBudget D S B := by
  have hp := weight_proposalKeyC D S h
  have ha := weight_acceptC D B r
  have hc := h.candidate
  simp only [tryKeyC, codeWeight, tryBudget]
  omega

theorem size_tryKeyC (D : Dims) (S B r : ℕ) (h : TrySizeInputs D S) :
    (compile (tryKeyC D B r)).size ≤ 100000 * tryBudget D S B :=
  (size_compile_weight _).trans (Nat.mul_le_mul_left _ (weight_tryKeyC D S B r h))

theorem weight_candidateC (D : Dims) (B : ℕ) :
    codeWeight (candidateC D B) ≤
      3 * B + 3 * (D.K - B) + 3 * D.N + 4 * (D.N * D.K) + 3 * nPI D + 120 := by
  have ht := weight_templateOpsC (candidateInitOps D B)
  simp only [candidateInitOps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    TemplateWord.weightBound, length_encRM] at ht
  have hd : codeWeight decQC ≤ 100 := by decide
  simp only [candidateC, candidateInitC, bitsC, codeWeight, candidateInitOps]
  omega

noncomputable def candidateTryBudget (D : Dims) (S B : ℕ) : ℕ :=
  tryBudget D S B + 3 * B + 3 * (D.K - B) + 3 * D.N +
    4 * (D.N * D.K) + 3 * nPI D + 120

theorem size_candidateTryC (D : Dims) (S B r : ℕ) (h : TrySizeInputs D S) :
    (compile (candidateTryC D B r)).size ≤ 100000 * candidateTryBudget D S B := by
  apply (size_compile_weight _).trans
  apply Nat.mul_le_mul_left
  have hc := weight_candidateC D B
  have ht := weight_tryKeyC D S B r h
  simp only [candidateTryC, codeWeight, candidateTryBudget]
  omega

open Params

theorem trySizeInputs_Dc : TrySizeInputs Dc (2 ^ 66) where
  toPublicSizeInputs := publicSizeInputs_Dc
  trap := correction_counts_Dc.1
  digits := correction_counts_Dc.2.1
  output := assembly_lengths_Dc.1
  assembly := assembly_lengths_Dc.2

end AdvancedEncryption.ExpLUT.Prog
