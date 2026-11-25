import PE.Impl.ExpLUT.Prog.RedSetupPDc
import PE.Impl.ExpLUT.Prog.SetupSize
import PE.Impl.ExpLUT.Prog.EncSizeConf
import SigabaNeo.Lib.Machines.Prog.AppendWCost

/-! # The state count of the reduction's setup component at `Dc`: `|setupRX| ≤ 2^20`. -/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.XProg
open AdvancedEncryption.RingBTVW.Prog AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

theorem size_setupRX_eq (D : Dims) {R : ℕ} (hR : 38 ≤ R) (e : ℕ) :
    (setupRX D hR e).size = rsPre.size + ((unifCanonP D.N D.K (nU D)).size +
      ((repF (nFl D * D.N) (entF D.K e)).size + (coinsF (nZ D)).size)) +
        (clearL scr40).size := rfl

theorem size_rsPre_le : rsPre.size ≤ 40000 := by
  have h1 := SigabaNeo.Tape.Prog.size_prim_le' (k := 40) (.tail 0)
  have h2 := SigabaNeo.Tape.Prog.size_prependN 128 (1 : Fin 40) 0 2 3
  unfold rsPre
  rw [SigabaNeo.Tape.Prog.size_seq, h2]
  exact (Nat.add_le_add_right h1 _).trans (by norm_num)

set_option exponentiation.threshold 2000 in
theorem size_setupRX_conf (D : Dims) (he : D.e = 24) (hK : D.K = 2 ^ 16) (hb : D.b = 22)
    (hmb : D.mb = 3 * 2 ^ 40 + 408) {R : ℕ} (hR : 38 ≤ R) {e : ℕ}
    (hE : (entF D.K e).size ≤ 2 ^ 16) : (setupRX D hR e).size ≤ 2 ^ 20 := by
  have hN : D.N = 2 ^ 24 := by simp [Dims.N, he]
  have h1 : nU D * (D.N * D.K) < 2 ^ 110 := by
    rw [nU_eq, hN, hK, hb, hmb]; norm_num
  have h2 : D.K * (D.N * D.K) < 2 ^ 110 := by rw [hN, hK]; norm_num
  have h3 : nFl D * D.N < 2 ^ 110 := by rw [nFl_eq, hN, hK, hb]; norm_num
  have h4 : nZ D < 2 ^ 110 := by rw [nZ_eq, hK, hb, hmb]; norm_num
  have a1 := size_unifCanonP_le (D := D) h1 h2
  have a2 := size_repF_le (entF D.K e) h3
  have a3 := size_coinsF_le h4
  have a4 := size_clearL scr40
  have a5 := size_rsPre_le
  have a6 := length_scr40
  rw [size_setupRX_eq]
  omega

theorem size_setupRX_Dc {R : ℕ} (hR : 38 ≤ R) : (setupRX Dc hR Params.eFl).size ≤ 2 ^ 20 := by
  refine size_setupRX_conf Dc rfl EncConf.Dc_K rfl EncConf.Dc_mb hR ?_
  rw [EncConf.Dc_K, Params.eFl_def]
  exact EncConf.size_entF

end AdvancedEncryption.ExpLUT.Prog
