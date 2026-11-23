import PE.Impl.DualUse.Prog.DecTightGen
import PE.Impl.DualUse.Prog.DecCostConf

/-!
# The clock of `Dec` at `confP`, per tape

The per-tape phases (`ph_decGenP'`, `ph_cfX'`, `ph_preC'`, `ph_postC'`, `ph_decFinB'`) at the
parameters of `confP` (`N = 2^34`, `K = 2^25`, `k = K + 1`, `d = 2^61`, `W = 512`), with the
block-structured `W_f` block and its per-tape output (`WB2.wfB2_out_conf`):
**`ph_decGenP_conf'`** bounds the time of `Dec`'s program by `decGT'` of explicit sizes.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg
open AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord
open AdvancedEncryption.DualUse.Params
open SigabaNeo.Tape.Prog (leT unfrT)

set_option maxRecDepth 100000

/-! ### Sizes at `confP` -/

set_option exponentiation.threshold 1000 in
theorem fixLen_skEnc_le' : fixLen (skEnc hkp confP) ≤ 3 * 2 ^ 173 := by
  simp only [fixLen]; comp_unfold; norm_num

set_option exponentiation.threshold 1000 in
theorem fixLen_ctEnc_le' : fixLen (ctEnc hkp confP) ≤ 3 * 2 ^ 173 := by
  simp only [fixLen]; comp_unfold; norm_num

theorem nDec_le177 : nDec hkp confP ≤ 2 ^ 177 :=
  (nDec_le_gen hkp confP fixLen_skEnc_le' fixLen_ctEnc_le' confP_L_le).trans (by norm_num)

theorem frontL_conf' : frontL confP.L WB2.Wc ≤ 2 ^ 64 := by
  rw [confP_L]; exact WB2.frontL_le

theorem NK_eq : Np * Kp = 2 ^ 34 * 2 ^ 25 := by rw [Np_def, Kp_def]

theorem nTk_eq : Algo.nT kp = 1 + (2 * (2 ^ 25 + 1) + 2 * (2 ^ 25 + 1)) := by
  simp only [Algo.nT]; rw [kp_eq]

theorem F2_eq : 1 * (2 * kp) * Np * Kp = 2 * (2 ^ 25 + 1) * 2 ^ 34 * 2 ^ 25 := by
  rw [kp_eq, Np_def, Kp_def]; ring

theorem F2_le : 1 * (2 * kp) * Np * Kp = 2 * kp * (Np * Kp) := by
  rw [Nat.one_mul, Nat.mul_assoc]

theorem nJR_eq : nJ (N := Np) (K := Kp) hkp * DualUse.rowL Np Kp kp =
    29931556208626395342166781734893185832156431457976320 := by
  rw [nJ_conf, rowL_conf]; norm_num

theorem F0_le : lenPK hkp confP + lenKA hkp confP + nJ (N := Np) (K := Kp) hkp * DualUse.rowL Np Kp kp +
    Np * Kp ≤ 2 ^ 177 := by
  have := lenPK_le; have := lenKA_le; have := NK_eq; have := nJR_eq; omega

theorem kNK_eq : kp * (Np * Kp) = (2 ^ 25 + 1) * (2 ^ 34 * 2 ^ 25) := by
  rw [kp_eq, Np_def, Kp_def]

theorem decOffs_conf' : ∀ x ∈ decOffs hkp confP, x ≤ 2 ^ 177 := fun x hx =>
  (decOffs_le_gen hkp confP (X := 2 ^ 175) (fixLen_skEnc_le'.trans (by norm_num)) (fixLen_ctEnc_le'.trans (by norm_num)) (lPsi_le.trans (by norm_num))
    (lenPK_le.trans (by norm_num)) (by rw [dNK_conf]; norm_num)
    (by rw [nTk_eq, Np_def, Kp_def]; norm_num) (rK_le.trans (by norm_num))
    (NK_le.trans (by norm_num)) x hx).trans (by norm_num)

/-! ### The `c_f̂` block at `confP` -/

/-- The crafted data's tape `0` afterwards. -/
local notation "aP" a => a + 1 + lenPK hkp confP + confP.d * (Np * Kp) +
  10 * ((confP.d - 2) * DualUse.rowL Np Kp kp + 2 * DualUse.rowL Np Kp kp) +
  nJ (N := Np) (K := Kp) hkp * (lenZ confP + DualUse.rowL Np Kp kp) +
  lPsi (N := Np) (K := Kp) hkp + 10

/-- The time of the `c_f̂` block at `confP`. -/
noncomputable def TbP (Mβ : ℕ) : ℕ :=
  256 * (2 * (Mβ + 1) + 3) + (2 * (Mβ + 1) + 3) +
    (preTCv (2 ^ 238) (2 ^ 178) (2 ^ 148)
      ((confP.d - 2) * DualUse.rowL Np Kp kp + 2 * DualUse.rowL Np Kp kp)
      (nJ (N := Np) (K := Kp) hkp) (lenZ confP + DualUse.rowL Np Kp kp) +
    ((2 ^ 555 + 2 ^ 552) +
      postCT' (lenPK hkp confP) (lenKA hkp confP) (Np * Kp) (offWk hkp confP)
        (nJ (N := Np) (K := Kp) hkp * (lenZ confP + DualUse.rowL Np Kp kp)) (lenZ confP) Np Kp kp
        (lenZ confP) (DualUse.rowL Np Kp kp) (nJ (N := Np) (K := Kp) hkp) WB2.Lb (2 ^ 148)))

set_option maxHeartbeats 4000000 in
/-- **The `c_f̂` block at `confP`, per tape.** -/
theorem ph_cfX_conf' {a : ℕ} (ha : a ≤ 2 ^ 182) {β : Fin 256 → ℕ} (h0 : β 0 ≤ a)
    (h1 : β 1 ≤ frontL confP.L WB2.Wc) {Mβ : ℕ} (hβ : ∀ i, β i ≤ Mβ) :
    Ph (cfX hkp confP (wfB2 hkp confP WB2.Wc)) β (TbP Mβ)
      (cfOut (lenPK hkp confP + lenKA hkp confP + nJ (N := Np) (K := Kp) hkp * DualUse.rowL Np Kp kp +
        Np * Kp) ((1 * (2 * kp) * Np) * Kp)) := by
  have hPK := lenPK_le
  have hKA := lenKA_le
  have hPs := lPsi_le
  have hCj := lenCj_le
  have hkE := fixLen_keyEnc_le
  have eNK := NK_eq
  have eD := confP_d
  have eR := rowL_conf
  have eJ := nJ_conf
  have eZ := lenZ_conf
  have hF := frontL_conf'
  have hpre := ph_preC' (hk := hkp) (c := confP) a (frontL confP.L WB2.Wc) (2 ^ 238) (2 ^ 178) (2 ^ 148)
    (by rw [eNK, eD, eR, eJ, eZ]; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [eNK]; omega) (by omega) (by omega) (by omega) (by rw [eZ]; omega) (by rw [eR]; omega)
    (by rw [eJ]; omega) (by rw [eNK, eD]; omega) (by rw [eD, eR]; omega) (by rw [eR]; omega)
    (by rw [eZ]; omega) (by omega) (by omega)
  have hw : Ph (wfB2 hkp confP WB2.Wc) (io2 (R := 254) (aP a) (frontL confP.L WB2.Wc) 0)
      (2 ^ 555 + 2 ^ 552) WB2.wOut := by
    obtain ⟨t1, t2⟩ := WB2.wfB2_out_conf (aP a) (frontL confP.L WB2.Wc)
      (by simp only [WB2.Lb]; rw [eNK, eD, eR, eJ, eZ]; omega) (by simp only [WB2.Lgc]; omega)
    exact fun ℓ hℓ => ⟨(timeBoundT_mono _ hℓ).trans t1, (lenBoundT_mono _ hℓ).trans t2⟩
  have hpost := ph_postC' (hk := hkp) (c := confP) (2 ^ 148) (by simp only [WB2.Lb]; norm_num)
    (by simp only [WB2.Lb, WB2.wOut2]; norm_num)
    (by rw [eZ, F2_eq]; simp only [WB2.wOut2]; norm_num) (by rw [eZ, eR]; omega)
    (by rw [Kp_def]; norm_num) (by rw [Np_def]; norm_num) (by rw [eNK]; norm_num)
    (by rw [kp_eq]; norm_num) (by rw [kp_eq, eNK]; norm_num) (by rw [kp_eq, Np_def]; norm_num)
    (by rw [eZ]; omega) (by rw [eJ]; omega) (by rw [kNK_eq]; norm_num)
  exact ph_cfX' hpre hw hpost h0 h1 hβ

/-! ### The program of `Dec` at `confP` -/

/-- The time of the end of decryption at `confP`. -/
noncomputable def TfP : ℕ := decFT' Np Kp kp confP.d (Algo.nT kp) (2 ^ 177) (2 ^ 177) (2 ^ 62)

set_option maxHeartbeats 4000000 in
/-- **The program of `Dec` at `confP`, per tape.** -/
theorem ph_decGenP_conf' :
    timeBoundT (decGenP hkp confP (cfX hkp confP (wfB2 hkp confP WB2.Wc)) WB2.Wc)
        (Prog.inputBound (255 : Fin 256) (nDec hkp confP + 1)) ≤
        decGT' (nDec hkp confP) (frontT confP.L WB2.Wc (16 * (nDec hkp confP + 2)))
          (max (16 * (nDec hkp confP + 2)) (frontL confP.L WB2.Wc))
          (TbP (max (16 * (nDec hkp confP + 2)) (frontL confP.L WB2.Wc))) TfP
          (decG' Kp (2 ^ 177) (2 ^ 177)) ∧
      lenBoundT (decGenP hkp confP (cfX hkp confP (wfB2 hkp confP WB2.Wc)) WB2.Wc)
        (Prog.inputBound (255 : Fin 256) (nDec hkp confP + 1)) 0 ≤
        decBL' (max (16 * (nDec hkp confP + 2)) (frontL confP.L WB2.Wc)) (decG' Kp (2 ^ 177) (2 ^ 177)) := by
  have hn := nDec_le177
  have hPK := lenPK_le
  have hKA := lenKA_le
  have eNK := NK_eq
  have eR := rowL_conf
  have eJ := nJ_conf
  exact ph_decGenP' (hk := hkp) (c := confP) _ WB2.Wc (2 ^ 177) (2 ^ 177) (2 ^ 62)
    (lenPK hkp confP + lenKA hkp confP + nJ (N := Np) (K := Kp) hkp * DualUse.rowL Np Kp kp + Np * Kp)
    ((1 * (2 * kp) * Np) * Kp)
    (fun β h0 h1 hβ => ph_cfX_conf' (a := 16 * (nDec hkp confP + 2)) (by omega) h0 h1 hβ)
    decOffs_conf' F0_le (le_of_eq F2_le) (by norm_num)
    (by rw [Kp_def]; norm_num) (by rw [Np_def]; norm_num) (by rw [eNK]; norm_num) (by norm_num)
    (by rw [kp_eq]; norm_num) (by rw [confP_d]; norm_num) (by rw [nTk_eq]; norm_num)
    (by rw [kp_eq, eNK]; norm_num)

/-! ### The numbers -/

theorem frontTv_mono {n LC T n' LC' T' : ℕ} (h1 : n ≤ n') (h2 : LC ≤ LC') (h3 : T ≤ T') :
    frontTv n LC T ≤ frontTv n' LC' T' := by
  simp only [frontTv]; gcongr

theorem postCT'_mono {L A NK oW LW Zr N K k Z R nJ D T L' A' oW' : ℕ} (h1 : L ≤ L') (h2 : A ≤ A')
    (h3 : oW ≤ oW') :
    postCT' L A NK oW LW Zr N K k Z R nJ D T ≤ postCT' L' A' NK oW' LW Zr N K k Z R nJ D T := by
  simp only [postCT', getT, prefT, skT]; gcongr

theorem decGT'_mono {n Fr Mβ Tb Tf G n' Fr' Mβ' Tb' Tf' G' : ℕ} (h1 : n ≤ n') (h2 : Fr ≤ Fr')
    (h3 : Mβ ≤ Mβ') (h4 : Tb ≤ Tb') (h5 : Tf ≤ Tf') (h6 : G ≤ G') :
    decGT' n Fr Mβ Tb Tf G ≤ decGT' n' Fr' Mβ' Tb' Tf' G' := by
  simp only [decGT', decBT', decBL', leT, parse4T, unfrT, longT, putT]; gcongr

theorem decBL'_mono {Mβ G Mβ' G' : ℕ} (h3 : Mβ ≤ Mβ') (h6 : G ≤ G') :
    decBL' Mβ G ≤ decBL' Mβ' G' := by
  simp only [decBL']; gcongr

set_option exponentiation.threshold 2000 in
theorem preTCv_conf : preTCv (2 ^ 238) (2 ^ 178) (2 ^ 148)
    ((confP.d - 2) * DualUse.rowL Np Kp kp + 2 * DualUse.rowL Np Kp kp)
    (nJ (N := Np) (K := Kp) hkp) (lenZ confP + DualUse.rowL Np Kp kp) ≤ 2 ^ 478 := by
  rw [confP_d, rowL_conf, nJ_conf, lenZ_conf]
  simp only [preTCv, wTv, getT, prefT]; norm_num

set_option exponentiation.threshold 2000 in
theorem postCT'_conf : postCT' (lenPK hkp confP) (lenKA hkp confP) (Np * Kp) (offWk hkp confP)
    (nJ (N := Np) (K := Kp) hkp * (lenZ confP + DualUse.rowL Np Kp kp)) (lenZ confP) Np Kp kp
    (lenZ confP) (DualUse.rowL Np Kp kp) (nJ (N := Np) (K := Kp) hkp) WB2.Lb (2 ^ 148) ≤
    2 ^ 481 := by
  refine (postCT'_mono lenPK_le lenKA_le offWk_le).trans ?_
  rw [NK_eq, nJ_conf, lenZ_conf, rowL_conf, Np_def, Kp_def, kp_eq]
  simp only [postCT', getT, prefT, skT, WB2.Lb]; norm_num

set_option exponentiation.threshold 2000 in
theorem TfP_conf : TfP ≤ 2 ^ 549 := by
  simp only [TfP]
  rw [confP_d, nTk_eq, Np_def, Kp_def, kp_eq]
  simp only [decFT', getT, prefT, wMV, decTailT, putT, List.length_cons, List.length_nil]
  norm_num

set_option exponentiation.threshold 2000 in
theorem frontTv_conf : frontTv (2 ^ 20) (2 ^ 64) (2 ^ 182) ≤ 2 ^ 200 := by
  simp only [frontTv]; norm_num

theorem lookCount_le_of {n W X : ℕ} (h : frontL n W ≤ X) :
    Prog.lookCount (frontTbl n W) [false] ≤ X := by
  simp only [frontL] at h; omega

theorem lookCount_le64 : Prog.lookCount (frontTbl confP.L WB2.Wc) [false] ≤ 2 ^ 64 :=
  lookCount_le_of frontL_conf'

theorem TbP_conf {Mβ : ℕ} (h : Mβ ≤ 2 ^ 182) :
    TbP Mβ ≤ 256 * (2 * (2 ^ 182 + 1) + 3) + (2 * (2 ^ 182 + 1) + 3) +
      (2 ^ 478 + ((2 ^ 555 + 2 ^ 552) + 2 ^ 481)) := by
  simp only [TbP]
  have := preTCv_conf
  have := postCT'_conf
  have : 256 * (2 * (Mβ + 1) + 3) ≤ 256 * (2 * (2 ^ 182 + 1) + 3) := by omega
  omega

set_option exponentiation.threshold 2000 in
theorem decGT'_num : decGT' (2 ^ 177) (2 ^ 200) (2 ^ 182)
    (256 * (2 * (2 ^ 182 + 1) + 3) + (2 * (2 ^ 182 + 1) + 3) +
      (2 ^ 478 + ((2 ^ 555 + 2 ^ 552) + 2 ^ 481))) (2 ^ 549) (decG' (2 ^ 25) (2 ^ 177) (2 ^ 177)) ≤
    2 ^ 555 + 2 ^ 553 := by
  simp only [decGT', decBT', decBL', decG', leT, parse4T, unfrT, longT, putT, List.length_cons,
    List.length_nil]
  norm_num

set_option exponentiation.threshold 2000 in
theorem decBL'_num : decBL' (2 ^ 182) (decG' (2 ^ 25) (2 ^ 177) (2 ^ 177)) ≤ 2 ^ 183 := by
  simp only [decBL', decG', List.length_cons, List.length_nil]; norm_num

set_option exponentiation.threshold 2000 in
theorem dec_arith' {n T L : ℕ} (hn : n ≤ 2 ^ 177) (hT : T ≤ 2 ^ 555 + 2 ^ 553) (hL : L ≤ 2 ^ 183) :
    2 * (n + 1) + 2 + T + (2 * L + 2) ≤ 2 ^ 556 := by omega

/-- **The clock of `Dec` at `confP`, per tape**: at most `2^556` steps. The dominating term is the
`W_f` block (`≤ 2^555 + 2^552`: its key sum `simKeyP`, `≤ 2^555`, and the run of `f̂`, `≤ 2^551`);
the end of decryption takes at most `2^549` (the rounding test `ballP`, charged
`419 (M + 1)^3` at the store's bound `M ≈ 2^180`), the read-back and the crafted data at most
`2^481`, `2^478`, the guard, the parser and the front end `≈ 2^365`. -/
theorem time_decMachineP_conf' :
    (decMachineP hkp confP (cfX hkp confP (wfB2 hkp confP WB2.Wc)) WB2.Wc).time ≤ 2 ^ 556 := by
  rw [time_decMachineP]
  obtain ⟨h1, h2⟩ := ph_decGenP_conf'
  have hn := nDec_le177
  have hF := frontL_conf'
  have hM : max (16 * (nDec hkp confP + 2)) (frontL confP.L WB2.Wc) ≤ 2 ^ 182 :=
    max_le (by omega) (by omega)
  have hFr : frontT confP.L WB2.Wc (16 * (nDec hkp confP + 2)) ≤ 2 ^ 200 := by
    rw [frontT_eq]
    exact (frontTv_mono confP_L_le lookCount_le64 (show 16 * (nDec hkp confP + 2) ≤ 2 ^ 182 by omega)).trans
      frontTv_conf
  have hK : Kp = 2 ^ 25 := Kp_def
  have hT := (h1.trans (decGT'_mono hn hFr hM (TbP_conf hM) TfP_conf (le_of_eq (by rw [hK])))).trans
    decGT'_num
  have hL := (h2.trans (decBL'_mono hM (le_of_eq (by rw [hK])))).trans decBL'_num
  exact dec_arith' hn hT hL

end AdvancedEncryption.DualUse.Prog
