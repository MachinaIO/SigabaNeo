import PE.Impl.ExpLUT.Prog.EncInitSize

/-! # Description length of the concrete package-P encryption machine -/
namespace AdvancedEncryption.ExpLUT.Prog.EncConf
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape
open AdvancedEncryption.ExpLUT.Params EncW

theorem cost_initialization : ((encInitOps Dc).map InitOp.cost).sum ≤ 3 * 2 ^ 108 := by
  simp only [encInitOps, List.map_append, List.sum_append]
  exact (Nat.add_le_add (Nat.add_le_add cost_public cost_coins) cost_templates).trans (by norm_num)

/-- The complete coin and public queues fit the normalization budget. -/
theorem normalization_lengths : coinLength Dc + publicLength Dc ≤ 2 ^ 99 := by
  simp only [coinLength, publicLength, fixedSize, BCol, Wb, Jh, Col, Dig, Pos,
    Enum.length_prod, len_sum, len_fin]
  norm_num [Dc, Kc, mbar, PE.BranchingProgram.w8, PE.BranchingProgram.Width.len]

theorem size_normalization : (normalizeInputsP Dc).size ≤ 2 ^ 108 := by
  exact (size_normalizeInputsP Dc).trans ((Nat.add_le_add_left
    (Nat.mul_le_mul_left 60 normalization_lengths) 20000).trans (by norm_num))

/-- State count of the complete encryption program, including all literal templates. -/
theorem size_encProgram : (encProgram Dc 16 6 eFl).size + 4 ≤ 2 ^ 112 := by
  have h := Nat.add_le_add_right (size_encProgram_le Dc 16 6 eFl) 4
  have hb := Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add size_prepare cost_initialization) size_core)
      size_normalization) 21916) 4
  exact h.trans (hb.trans (by norm_num))

/-- The actual compiled encryption machine has a description of at most `2^744` bits. -/
theorem descLen_encMachine : encMachine.descLen ≤ 2 ^ 744 :=
  descLen_encMP_le_of_size Dc 16 6 eFl size_encProgram

end AdvancedEncryption.ExpLUT.Prog.EncConf
