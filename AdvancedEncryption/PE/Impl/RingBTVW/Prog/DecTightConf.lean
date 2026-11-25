import PE.Impl.RingBTVW.Prog.DecTightGen
import PE.Impl.RingBTVW.Prog.DecCostConf
import PE.Impl.RingBTVW.Prog.WfCConf

/-!
# The clock of `Dec` at `confA`, per tape

The machine of `Dec` in `implC` (`decMachineP hkp confP cfC`: the shell `decGenF` with the front
end `frontBP confP.L` and the `c_f̂` block `cfC = cfX hkp confP wfC` around the stream block
`wfC = wfB2S hkp confP Icn Wn`) at `N = 2^36`, `K = 2^27`, `k = K + 1`, `d = 2^65`, `nA = 128`.
The per-tape phases `ph_decGenF'`, `ph_cfX'`, `ph_preC'`, `WB2.time_wfB2S_out`, `ph_postC'`,
`ph_decFinB'` at these numbers:

* **`ph_cfC_conf'`**: the `c_f̂` block, at most `TbP a Mβ ≤ 2^628 + 2^522` steps
  (the stream block `2^628`, the crafted data `< 2^519`, the read-back `< 2^520`);
* **`ph_decGenP_conf'`**: the program of `Dec`;
* **`time_decMachineP_conf'`**: `(decMachineP hkp confP cfC).time ≤ 2^629`. Besides the block,
  the end of decryption takes `< 2^600` steps (the rounding test `ballP`, `419 (M + 1)^3` at the
  store bound `M ≈ 2^197`), the front end `≤ 2^408`.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg
open AdvancedEncryption.PE.Gates.BPWord
open AdvancedEncryption.RingBTVW.Params AdvancedEncryption.RingBTVW.Sub
open SigabaNeo.Tape.Prog (leT unfrT)

set_option maxRecDepth 100000

/-! ### The numbers -/

theorem F2_le' : (1 * (2 * kp) * Np) * Kp ≤ 2 * kp * (Np * Kp) := le_of_eq (by ring)

theorem F0_le : lenPK hkp confP + lenKA hkp confP + nJ (N := Np) (K := Kp) hkp * RingBTVW.rowL Np Kp kp +
    Np * Kp ≤ 2 ^ 194 := by
  have := lenPK_le; have := lenKA_le; have := nJR_leD; have := NK_le; omega

theorem aD_le : 16 * (nDec hkp confP + 2) ≤ 2 ^ 200 := by have := nDec_le; omega

theorem frontBA_le' : frontBA bpLen ≤ 2 ^ 63 := frontBA_le bpLen_le

theorem frontBTn_confD : frontBTn confP.L bpLen (16 * (nDec hkp confP + 2)) ≤ 2 ^ 8 * (2 ^ 201) ^ 2 :=
  frontBTn_le le_rfl bpLen_le (confP_L_le.trans (by norm_num)) (by have := aD_le; omega)
    (by norm_num)

set_option exponentiation.threshold 2000 in
theorem preTCv_conf : preTCv (2 ^ 259) (2 ^ 194) (2 ^ 157)
    ((confP.d - 2) * RingBTVW.rowL Np Kp kp + 2 * RingBTVW.rowL Np Kp kp)
    (nJ (N := Np) (K := Kp) hkp) (lenZ confP + RingBTVW.rowL Np Kp kp) ≤ 2 ^ 520 := by
  rw [confP_d, rowL_conf, nJ_conf, lenZ_conf]
  simp only [preTCv, wTv, getT, prefT]; norm_num

theorem postCT'_mono {L A NK oW LW Zr N K k Z R nJ D T L' A' oW' : ℕ} (h1 : L ≤ L') (h2 : A ≤ A')
    (h3 : oW ≤ oW') :
    postCT' L A NK oW LW Zr N K k Z R nJ D T ≤ postCT' L' A' NK oW' LW Zr N K k Z R nJ D T := by
  simp only [postCT', gadCT', getT, prefT, skT]; gcongr

set_option exponentiation.threshold 2000 in
theorem postCT'_conf : postCT' (lenPK hkp confP) (lenKA hkp confP) (Np * Kp) (offWk hkp confP)
    (nJ (N := Np) (K := Kp) hkp * (lenZ confP + RingBTVW.rowL Np Kp kp)) (lenZ confP) Np Kp kp
    (lenZ confP) (RingBTVW.rowL Np Kp kp) (nJ (N := Np) (K := Kp) hkp) WB2.Lbn (2 ^ 157) ≤
    2 ^ 521 := by
  refine (postCT'_mono lenPK_le lenKA_le offWk_le).trans ?_
  rw [NK_eq, nJ_conf, lenZ_conf, rowL_conf, Np_def, Kp_def, kp_eq]
  simp only [postCT', gadCT', getT, prefT, skT, WB2.Lbn]; norm_num

/-- The time of the end of decryption at `confA`. -/
noncomputable def TfP : ℕ :=
  decFT' Np Kp kp confP.d (Algo.nT kp) (2 ^ 194) (2 ^ 194) (2 ^ 66)

set_option exponentiation.threshold 2000 in
theorem TfP_conf : TfP ≤ 2 ^ 600 := by
  simp only [TfP]
  rw [confP_d, nTk_eq, Np_def, Kp_def, kp_eq]
  simp only [decFT', getT, prefT, wMV, decTailT, putT, List.length_cons, List.length_nil]
  norm_num

/-! ### The `c_f̂` block at `confA` -/

/-- The crafted data's tape `0` afterwards (from tape `0` at most `a`, the bit moved behind it). -/
noncomputable def aP (a : ℕ) : ℕ := a + 1 + 1 + lenPK hkp confP + confP.d * (Np * Kp) +
  nA * ((confP.d - 2) * RingBTVW.rowL Np Kp kp + 2 * RingBTVW.rowL Np Kp kp) +
  nJ (N := Np) (K := Kp) hkp * (lenZ confP + RingBTVW.rowL Np Kp kp) +
  lPsi (N := Np) (K := Kp) hkp + nA

/-- The time of the `c_f̂` block at `confA`. -/
noncomputable def TbP (a Mβ : ℕ) : ℕ :=
  256 * (2 * (Mβ + 1) + 3) + (2 * (Mβ + 1) + 3) +
    (mvBitT a (frontBA bpLen) +
    (preTCv (2 ^ 259) (2 ^ 194) (2 ^ 157)
      ((confP.d - 2) * RingBTVW.rowL Np Kp kp + 2 * RingBTVW.rowL Np Kp kp)
      (nJ (N := Np) (K := Kp) hkp) (lenZ confP + RingBTVW.rowL Np Kp kp) +
    (2 ^ 628 +
      postCT' (lenPK hkp confP) (lenKA hkp confP) (Np * Kp) (offWk hkp confP)
        (nJ (N := Np) (K := Kp) hkp * (lenZ confP + RingBTVW.rowL Np Kp kp)) (lenZ confP) Np Kp kp
        (lenZ confP) (RingBTVW.rowL Np Kp kp) (nJ (N := Np) (K := Kp) hkp) WB2.Lbn (2 ^ 157))))

theorem dRow_eq : nA * ((confP.d - 2) * RingBTVW.rowL Np Kp kp + 2 * RingBTVW.rowL Np Kp kp) =
    128 * ((2 ^ 62 - 2) * (2 * (2 ^ 26 + 1) * (2 ^ 34 * 2 ^ 26)) +
      2 * (2 * (2 ^ 26 + 1) * (2 ^ 34 * 2 ^ 26))) := by
  rw [confP_d, rowL_conf]

theorem aP_le {a : ℕ} (ha : a ≤ 2 ^ 200) : aP a ≤ WB2.Lbn := by
  have h1 := lenPK_le; have h2 := LW_le; have h3 := lPsi_le
  have e1 := dNK_conf; have e2 := dRow_eq
  have hn : nA = 128 := rfl
  simp only [aP, WB2.Lbn]
  rw [e1, e2, hn]
  omega

theorem hX_arith {a PK KA NK Ps dNK Q Z R Z2 J Cj LW : ℕ} (ha : a ≤ 2 ^ 200 + 1)
    (hPK : PK ≤ 2 ^ 191) (hKA : KA ≤ 2 ^ 132) (hNK : NK ≤ 2 ^ 63) (hPs : Ps ≤ 2 ^ 102)
    (hd : dNK ≤ 2 ^ 128) (hQ : Q ≤ 2 ^ 165) (hZ : Z ≤ 2 ^ 157) (hR : R ≤ 2 ^ 92)
    (hZ2 : Z2 ≤ 2 ^ 157) (hJ : J ≤ 2 ^ 101) (hCj : Cj ≤ 2 ^ 193) (hLW : LW ≤ 2 ^ 258) :
    2 * (a + 6 + PK + KA + (NK + 1) + 2 * Ps + dNK + Q + (Z - (KA + NK + 1)) + Z + R + Z2 + 2 * R +
      Ps + 128 + dNK + (Z - (KA + NK + 1)) + J + 128) + Cj + LW + Ps + 128 ≤ 2 ^ 259 := by
  omega

set_option exponentiation.threshold 2000 in
set_option maxHeartbeats 4000000 in
/-- **The `c_f̂` block at `confA`, per tape.** -/
theorem ph_cfC_conf' {a : ℕ} (ha : a ≤ 2 ^ 200) {β : Fin 256 → ℕ} (h0 : β 0 ≤ a)
    (h1 : β 1 ≤ frontBA bpLen) {Mβ : ℕ} (hβ : ∀ i, β i ≤ Mβ) :
    Ph cfC β (TbP a Mβ)
      (cfOut (lenPK hkp confP + lenKA hkp confP + nJ (N := Np) (K := Kp) hkp * RingBTVW.rowL Np Kp kp +
        Np * Kp) ((1 * (2 * kp) * Np) * Kp)) := by
  have hPK := lenPK_le
  have hKA := lenKA_le
  have hPs := lPsi_le
  have hCj := lenCj_le
  have hLW := LW_le
  have hkE := fixLen_keyEnc_le
  have eNK := NK_eq
  have eD := confP_d
  have eR := rowL_conf
  have eJ := nJ_conf
  have eZ := lenZ_conf
  have hF := frontBA_le'
  have hn : nA = 128 := rfl
  have hR := rowL_le
  have hZ := lenZ_le
  have hJ := nJ_le
  have hdR : (confP.d - 2) * RingBTVW.rowL Np Kp kp ≤ 2 ^ 157 := by rw [eD, eR]; norm_num
  have hdR2 := dRow_eq
  have hdNK := dNK_conf
  have hNK := NK_le
  have hkE' := fixLen_keyEnc_le
  have hn2 : nA = 128 := rfl
  have hpre := ph_preC' (hk := hkp) (c := confP) (a + 1) (frontBA bpLen) (2 ^ 259) (2 ^ 194)
    (2 ^ 157) (hX_arith (a := a + 1) (by omega) hPK hKA hNK hPs (by rw [hdNK]; norm_num)
      (by rw [hdR2]; norm_num) hZ hR hdR (hJ.trans (by norm_num)) hCj hLW) (by omega) (by omega)
    (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by norm_num) hZ (by omega) (by omega) (by rw [hdNK]; norm_num)
    hdR (by omega) (by omega) (by omega) (by rw [hn]; norm_num)
  have hw : Ph wfC (io2 (R := 254) (aP a) (frontBA bpLen) 0) (2 ^ 628) WB2.wOutS := by
    obtain ⟨t1, t2⟩ := WB2.time_wfB2S_out hkp confP Np_def Kp_def confP_d rfl (treeHeight_le.trans (by norm_num [eTree]))
      offB_conf offW_conf (offPsi_conf.trans (by unfold WB2.Lbn; norm_num)) offR_conf offX_conf
      (aP a) (frontBA bpLen) (aP_le ha) (by unfold WB2.Lgn; omega)
    exact fun ℓ hℓ => ⟨(timeBoundT_mono _ hℓ).trans t1, (lenBoundT_mono _ hℓ).trans t2⟩
  have hpost := ph_postC' (hk := hkp) (c := confP) (2 ^ 157) (by unfold WB2.Lbn; norm_num)
    (by unfold WB2.wOut2S WB2.Lbn WB2.dn WB2.kn WB2.Kn WB2.Nn; norm_num)
    (by rw [eZ, Np_def, Kp_def, kp_eq]; unfold WB2.wOut2S WB2.dn WB2.kn WB2.Kn WB2.Nn; norm_num)
    (by rw [eZ, eR]; omega)
    (by rw [Kp_def]; norm_num) (by rw [Np_def]; norm_num) (by rw [eNK]; norm_num)
    (by rw [kp_eq]; norm_num) (by rw [kp_eq, eNK]; norm_num) (by rw [kp_eq, Np_def]; norm_num)
    hZ (by omega) (kNK_le.trans (by norm_num))
  exact ph_cfX' hpre hw hpost h0 h1 hβ

/-! ### The program of `Dec` at `confA` -/

set_option maxHeartbeats 4000000 in
/-- **The program of `Dec` at `confA`, per tape.** -/
theorem ph_decGenP_conf' :
    timeBoundT (decGenP hkp confP cfC) (Prog.inputBound (255 : Fin 256) (nDec hkp confP + 1)) ≤
        decGT' (nDec hkp confP) (frontBTn confP.L bpLen (16 * (nDec hkp confP + 2)))
          (max (16 * (nDec hkp confP + 2)) (frontBA bpLen))
          (TbP (16 * (nDec hkp confP + 2)) (max (16 * (nDec hkp confP + 2)) (frontBA bpLen))) TfP
          (decG' Kp (2 ^ 194) (2 ^ 194)) ∧
      lenBoundT (decGenP hkp confP cfC) (Prog.inputBound (255 : Fin 256) (nDec hkp confP + 1)) 0 ≤
        decBL' (max (16 * (nDec hkp confP + 2)) (frontBA bpLen)) (decG' Kp (2 ^ 194) (2 ^ 194)) := by
  have eNK := NK_eq
  exact ph_decGenF' (hk := hkp) (c := confP) frEmb_eF (by norm_num) (frontSpec_frontBP confP.L).ph
    cfC (2 ^ 194) (2 ^ 194) (2 ^ 66)
    (lenPK hkp confP + lenKA hkp confP + nJ (N := Np) (K := Kp) hkp * RingBTVW.rowL Np Kp kp +
      Np * Kp) ((1 * (2 * kp) * Np) * Kp)
    (fun β h0 h1 hβ => ph_cfC_conf' aD_le h0 h1 hβ)
    decOffs_conf F0_le F2_le' (by norm_num)
    (by rw [Kp_def]; norm_num) (by rw [Np_def]; norm_num) (by rw [eNK]; norm_num) (by norm_num)
    (by rw [kp_eq]; norm_num) (by rw [confP_d]; norm_num) (by rw [nTk_eq]; norm_num)
    (by rw [kp_eq, eNK]; norm_num)

/-! ### The clock -/

theorem decGT'_mono {n Fr Mβ Tb Tf G n' Fr' Mβ' Tb' Tf' G' : ℕ} (h1 : n ≤ n') (h2 : Fr ≤ Fr')
    (h3 : Mβ ≤ Mβ') (h4 : Tb ≤ Tb') (h5 : Tf ≤ Tf') (h6 : G ≤ G') :
    decGT' n Fr Mβ Tb Tf G ≤ decGT' n' Fr' Mβ' Tb' Tf' G' := by
  simp only [decGT', decBT', decBL', leT, parse4T, unfrT, longT, putT]; gcongr

theorem decBL'_mono {Mβ G Mβ' G' : ℕ} (h3 : Mβ ≤ Mβ') (h6 : G ≤ G') :
    decBL' Mβ G ≤ decBL' Mβ' G' := by
  simp only [decBL']; gcongr

theorem TbP_conf {a Mβ : ℕ} (ha : a ≤ 2 ^ 200) (h : Mβ ≤ 2 ^ 200) :
    TbP a Mβ ≤ 256 * (2 * (2 ^ 200 + 1) + 3) + (2 * (2 ^ 200 + 1) + 3) +
      (mvBitT (2 ^ 200) (2 ^ 63) + (2 ^ 520 + (2 ^ 628 + 2 ^ 521))) := by
  simp only [TbP]
  have := preTCv_conf
  have := postCT'_conf
  have := frontBA_le'
  have : mvBitT a (frontBA bpLen) ≤ mvBitT (2 ^ 200) (2 ^ 63) := by simp only [mvBitT]; omega
  have : 256 * (2 * (Mβ + 1) + 3) ≤ 256 * (2 * (2 ^ 200 + 1) + 3) := by omega
  omega

set_option exponentiation.threshold 2000 in
theorem decGT'_num : decGT' (2 ^ 195) (2 ^ 8 * (2 ^ 201) ^ 2) (2 ^ 200)
    (256 * (2 * (2 ^ 200 + 1) + 3) + (2 * (2 ^ 200 + 1) + 3) +
      (mvBitT (2 ^ 200) (2 ^ 63) + (2 ^ 520 + (2 ^ 628 + 2 ^ 521)))) (2 ^ 600)
      (decG' (2 ^ 26) (2 ^ 194) (2 ^ 194)) ≤ 2 ^ 628 + 2 ^ 602 := by
  simp only [decGT', decBT', decBL', decG', leT, parse4T, unfrT, longT, putT, mvBitT,
    List.length_cons, List.length_nil]
  norm_num

set_option exponentiation.threshold 2000 in
theorem decBL'_num : decBL' (2 ^ 200) (decG' (2 ^ 26) (2 ^ 194) (2 ^ 194)) ≤ 2 ^ 201 := by
  simp only [decBL', decG', List.length_cons, List.length_nil]; norm_num

theorem dec_arith' {n T L : ℕ} (hn : n ≤ 2 ^ 195) (hT : T ≤ 2 ^ 628 + 2 ^ 602) (hL : L ≤ 2 ^ 201) :
    2 * (n + 1) + 2 + T + (2 * L + 2) ≤ 2 ^ 629 := by omega

set_option maxHeartbeats 4000000 in
/-- **The clock of `Dec` at `confA`, per tape**: at most `2^629` steps. The dominating term is the
stream block `W_f` (`≤ 2^628`); the end of decryption takes less than `2^600` steps (the rounding
test `ballP`), the read-back and the crafted data less than `2^521`, `2^520`, the front end at
most `2^408`. -/
theorem time_decMachineP_conf' : (decMachineP hkp confP cfC).time ≤ 2 ^ 629 := by
  rw [time_decMachineP]
  obtain ⟨h1, h2⟩ := ph_decGenP_conf'
  have hn := nDec_le
  have ha := aD_le
  have hF := frontBA_le'
  have hM : max (16 * (nDec hkp confP + 2)) (frontBA bpLen) ≤ 2 ^ 200 :=
    max_le ha (hF.trans (by norm_num))
  have hK : Kp = 2 ^ 26 := Kp_def
  have hT := (h1.trans (decGT'_mono hn frontBTn_confD hM (TbP_conf ha hM) TfP_conf
    (le_of_eq (by rw [hK])))).trans decGT'_num
  have hL := (h2.trans (decBL'_mono hM (le_of_eq (by rw [hK])))).trans decBL'_num
  exact dec_arith' hn hT hL

end AdvancedEncryption.RingBTVW.Prog

namespace AdvancedEncryption.RingBTVW.Sub

open AdvancedEncryption.RingBTVW.Prog

/-- **The clock of the `Dec` machine of `implC`** (`msC.dec`): at most `2^629` steps. -/
theorem time_dec_msC : msC.dec.time ≤ 2 ^ 629 := time_decMachineP_conf'

end AdvancedEncryption.RingBTVW.Sub
