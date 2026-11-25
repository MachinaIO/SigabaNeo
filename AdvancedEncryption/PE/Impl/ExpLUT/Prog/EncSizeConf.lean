import PE.Impl.ExpLUT.Prog.EncSize
import PE.Impl.ExpLUT.Prog.SetupConf
import PE.Impl.ExpLUT.Prog.EncMachineConf
/-! # Concrete encryption sampler state budget -/
namespace AdvancedEncryption.ExpLUT.Prog.EncConf
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Lattices
open AdvancedEncryption.ExpLUT.Params

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem size_cbdPM : (cbdPM 16 6 65536).size ≤ 2 ^ 20 := by decide +kernel

theorem size_entF : (AdvancedEncryption.RingBTVW.Prog.entF 65536 400).size ≤ 2 ^ 16 := by
  decide +kernel

theorem encSmall_count : nEncSmall Dc * Dc.N < 2 ^ 100 := by
  simp only [nEncSmall, BCol, Wb, Jh, Col, len_sum, Enum.length_prod, len_fin]
  norm_num [Dc, Kc, mbar]

theorem flooding_count : nFl Dc * Dc.N < 2 ^ 100 := by
  simp only [nFl, Dig, Col, Pos, Enum.length_prod, len_fin]
  norm_num [Dc, Kc, PE.BranchingProgram.w8, PE.BranchingProgram.Width.len]

set_option maxRecDepth 100000 in
/-- The complete input parser and coin sampler use fewer than `2^22` states. -/
theorem size_prepare : (EncIO.prepare Dc 16 6 eFl).size ≤ 2 ^ 22 := by
  have h := EncW.size_prepare_le Dc 16 6 eFl encSmall_count flooding_count
    (show Dc.N < 2 ^ 100 by norm_num [Dc])
  have hc := size_cbdPM
  have hf := size_entF
  have hk : Dc.K = 65536 := by change Kc = 65536; rw [Kc_def]; norm_num
  have he : eFl = 400 := eFl_def
  rw [hk, he] at h
  rw [he]
  exact h.trans ((Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 2 hc) hf) (585 * 100))
    10441).trans (by norm_num))

end AdvancedEncryption.ExpLUT.Prog.EncConf
