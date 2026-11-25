import PE.Impl.ExpLUT.Prog.KeyProgramSize
/-! Concrete scalar bounds for the complete KeyGen state count. -/
namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Params PE.BranchingProgram

theorem keyCodec_lengths (D : Dims) :
    codecSize (mpkEnc D) =
      (2 * (D.mb + D.K) + D.b * 2 * (2 * (2 * D.K)) +
        w8.len * (2 * D.K) + 2 * (2 * D.K) +
        w8.len * (2 * (2 * D.K) * D.K) * (2 * (2 * D.K)) +
        D.b * (2 * (2 * D.K) * D.K) * (2 * (2 * D.K)) + 2) * (D.N * D.K) ∧
    codecSize (matE D (Wb D) (Fin D.K)) = D.mb * D.K * (D.N * D.K) := by
  simp only [codecSize,
    BCol, Wb, Jh, Col, Pos, Dig, len_sum, Enum.length_prod, len_fin]
  constructor <;> ring

theorem keyCodec_bounds_Dc : codecSize (mpkEnc Dc) ≤ 2 ^ 120 ∧
    codecSize (matE Dc (Wb Dc) (Fin Dc.K)) ≤ 2 ^ 120 ∧
    codecSize (keyEnc Dc) ≤ 2 ^ 120 := by
  obtain ⟨hp, ht⟩ := keyCodec_lengths Dc
  refine ⟨hp.le.trans ?_, ht.le.trans ?_, accept_counts_Dc.2.trans ?_⟩ <;>
    norm_num [Dc, Kc, mbar, w8, Width.len]

theorem evalInitWeight_eq (D : Dims) :
    ((evalInitOps D).map (fun op ↦ op.2.weightBound)).sum =
    3 * (gD D + D.b + 16 * D.K ^ 3 * (D.N * D.K) + D.K + (D.K - 1) +
      D.N * D.K + 2 * D.K + 7 * D.K * (D.N * D.K) + 4 * D.K + 2 ^ D.b + tlK) +
      3 * (D.N * D.K) + 112 := by
  simp only [evalInitOps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    TemplateWord.weightBound, length_encRM]
  ring

theorem evalInitWeight_Dc :
    ((evalInitOps Dc).map (fun op ↦ op.2.weightBound)).sum ≤ 2 ^ 120 := by
  rw [evalInitWeight_eq]
  norm_num [Dc, Kc, gD, gGen, tlK]

namespace KeyCore

set_option maxRecDepth 100000 in
theorem keyProgramBudget_numeric (D : Dims)
    (hN : D.N = 2 ^ 24) (hK : D.K = 2 ^ 16) (hb : D.b = 22)
    (hp : codecSize (mpkEnc D) ≤ 2 ^ 120)
    (ht : codecSize (matE D (Wb D) (Fin D.K)) ≤ 2 ^ 120)
    (hk : codecSize (keyEnc D) ≤ 2 ^ 120)
    (he : ((evalInitOps D).map (fun op ↦ op.2.weightBound)).sum ≤ 2 ^ 120)
    (hc : nPI D ≤ 2 ^ 66) : keyProgramBudget D (2 ^ 66) 18750 106 + 4 ≤ 2 ^ 220 := by
  have ho : mpkDOffset D ≤ 2 ^ 120 := (Nat.sub_le _ _).trans hp
  have hw : (setting D).E.W = 2 ^ D.b := rfl
  simp only [keyProgramBudget, keyPrepareBudget, candidateTryBudget, tryBudget,
    proposalBudget, keyDigitsBudget, publicRowBudget, publicPositiveBudget,
    publicNegativeBudget, publicGatherBudget, correctionCoordBudget, correctionLoadBudget,
    invalidKeyBudget, hw, hN, hK, hb]
  norm_num [predLen]
  omega

theorem size_keyProgram_Dc_pow : (keyProgram Dc Bk rSmall).size + 4 ≤ 2 ^ 220 := by
  apply (Nat.add_le_add_right size_keyProgram_Dc 4).trans
  rw [Bk_def]
  exact keyProgramBudget_numeric Dc rfl (by norm_num [Dc, Kc]) rfl keyCodec_bounds_Dc.1
    keyCodec_bounds_Dc.2.1 keyCodec_bounds_Dc.2.2 evalInitWeight_Dc correction_counts_Dc.2.2

theorem descLen_program105 (p : XProg 105) (n : ℕ) :
    (p.toMachineT 0 0 n).descLen =
      6 * (p.size + 4) * 3 ^ 105 * 3 ^ 0 * Machine.entryBits 105 (p.size + 4) 0 := by
  rw [Machine.descLen, XProg.states_toMachineT, XProg.card_state]
  rfl

theorem descLen_keyMP_eq (D : Dims) (B r L : ℕ) :
    (keyMP D B r L).descLen =
      6 * ((keyProgram D B r).size + 4) * 3 ^ 105 * 3 ^ 0 *
        Machine.entryBits 105 ((keyProgram D B r).size + 4) 0 :=
  descLen_program105 (keyProgram D B r) (keyInputBound D L)

set_option exponentiation.threshold 1000 in
theorem descLen_keyMP_Dc (L : ℕ) : (keyMP Dc Bk rSmall L).descLen ≤ 2 ^ 620 := by
  rw [descLen_keyMP_eq]
  exact (AdvancedEncryption.RingBTVW.Prog.descLen_arithA size_keyProgram_Dc_pow).trans
    (by norm_num)

end KeyCore
end AdvancedEncryption.ExpLUT.Prog
