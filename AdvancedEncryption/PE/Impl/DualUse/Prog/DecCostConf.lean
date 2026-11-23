import PE.Impl.DualUse.Prog.KeyCostConf
import PE.Impl.DualUse.Prog.DecGenCost

/-!
# The clock of `Dec` at `confP`

Envelopes (`decGTv`, `postCTv`) of the time bound of `Dec`'s program and of the read-back block of
`c_f̂` with plain numbers as arguments, their monotonicity, and the closed bound
`time_decMachineP_conf` of the clock of the compiled `Dec` at `confP`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg
open SigabaNeo.Tape.Prog (leP unfrP frP leT unfrT frT tailsP)
open AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord
open SigabaNeo.Lattices.Algo
open scoped SigabaNeo.Tape.Prog

/-! ### The read-back block of `c_f̂` -/

/-- `postCT` with numbers (`kNK = k N K`, `nJR = nJ R`) and a bound `Xp` of the templates. -/
def postCTv (L A NK oW LW Zr kNK nJR Xp M : ℕ) : ℕ :=
  let M1 := M + 1 + L
  let M2 := M1 + 1 + A
  let M3 := M2 + 1 + NK
  let M4 := M3 + 1 + LW
  let M5 := M4 + M4 * M4
  let M6 := M5 + 1 + L
  let M7 := M6 + 1 + A
  let M8 := M7 + 1 + nJR
  let M9 := M8 + 1 + NK
  let M10 := M9 + M9 * 1
  let M11 := M10 + 1 + kNK
  getT 0 L M + getT oW A M1 + getT (oW + A) NK M2 + getT oW LW M3 +
    (10 * ((2 * Xp + 1) * (4 * M4 + 12)) + (2 * (M4 + 1) + 3)) + skipT M4 + (2 * (M5 + 1) + 3) +
    prefT L M5 + prefT A M6 + prefT nJR M7 + prefT NK M8 + (Zr + 1) * (2 * (M9 + 1) + 3) +
    375 * (M9 + 1) ^ 4 + forT (fun X => 2 * (X + 1) + 3) 1 M9 + prefT kNK M10 +
    210 * (M11 + 1) ^ 3 + (2 * (M11 + 1) + 3) + (62 * (2 * (M11 + 1) + 3) + (2 * (M11 + 1) + 3))

theorem postCT_le (L A NK oW LW Zr N K k Z R nJ Xp M : ℕ)
    (hX : ∀ x ∈ postTmplC N K k Z R nJ, x.2 ≤ Xp) :
    postCT L A NK oW LW Zr N K k Z R nJ M ≤ postCTv L A NK oW LW Zr (k * (N * K)) (nJ * R) Xp M := by
  have h := tmplT_le (postTmplC N K k Z R nJ) (M + 1 + L + 1 + A + 1 + NK + 1 + LW) Xp hX
  have hl : (postTmplC N K k Z R nJ).length = 10 := rfl
  rw [hl] at h
  unfold postCT postCTv
  dsimp only
  omega

set_option maxHeartbeats 4000000 in
theorem postCTv_mono {L A NK oW LW Zr kNK nJR Xp M L' A' NK' oW' LW' Zr' kNK' nJR' Xp' M' : ℕ}
    (h1 : L ≤ L') (h2 : A ≤ A') (h3 : NK ≤ NK') (h4 : oW ≤ oW') (h5 : LW ≤ LW') (h6 : Zr ≤ Zr')
    (h7 : kNK ≤ kNK') (h8 : nJR ≤ nJR') (h9 : Xp ≤ Xp') (h10 : M ≤ M') :
    postCTv L A NK oW LW Zr kNK nJR Xp M ≤ postCTv L' A' NK' oW' LW' Zr' kNK' nJR' Xp' M' := by
  simp only [postCTv, getT, prefT, skipT, forT, loopT]
  gcongr

/-- `postCG` with numbers. -/
def postCGv (L A NK LW kNK nJR M : ℕ) : ℕ :=
  let M4 := M + 1 + L + 1 + A + 1 + NK + 1 + LW
  let M5 := M4 + M4 * M4
  let M9 := M5 + 1 + L + 1 + A + 1 + nJR + 1 + NK
  M9 + M9 * 1 + 1 + kNK

theorem postCG_eq (L A NK LW N K k nJ R M : ℕ) :
    postCG L A NK LW N K k nJ R M = postCGv L A NK LW (k * (N * K)) (nJ * R) M := rfl

theorem postCGv_mono {L A NK LW kNK nJR M L' A' NK' LW' kNK' nJR' M' : ℕ} (h1 : L ≤ L')
    (h2 : A ≤ A') (h3 : NK ≤ NK') (h5 : LW ≤ LW') (h7 : kNK ≤ kNK') (h8 : nJR ≤ nJR')
    (h10 : M ≤ M') : postCGv L A NK LW kNK nJR M ≤ postCGv L' A' NK' LW' kNK' nJR' M' := by
  simp only [postCGv]
  gcongr

/-! ### The end of decryption -/

/-- `decFT` with the templates bounded by `X`. -/
def decFTv (K B X M : ℕ) : ℕ :=
  let M1 := M + 1 + B
  let M2 := M1 + 1 + B
  let M3 := M2 + 1 + B
  let M4 := M3 + 1 + B
  let M5 := M4 + 1 + B
  let M6 := M5 + 1 + B
  let M7 := M6 + K + 1
  let M8 := M7 + 1 + K
  getT B B M + (getT B B M1 + (getT B B M2 + (getT B B M3 + (getT B B M4 + (getT B B M5 +
    (putT K M6 + ((10 * ((2 * X + 1) * (4 * M7 + 12)) + (2 * (M7 + 1) + 3)) + (6000 * (M7 + 1) ^ 8 +
    (((2 * (M7 + 1) + 3) + (2 * (M7 + 1) + 3)) + (prefT K M7 + ((2 * (M8 + 1) + 3) +
    (419 * (M8 + 1) ^ 3 + ((2 * (M8 + 1) + 3) +
    ((max (putT ([true, false, false] : List Bool).length M8)
      (putT ([true, true, false] : List Bool).length M8) + 1) +
    (256 * (2 * (max (M8 + ([true, false, false] : List Bool).length + 1)
        (M8 + ([true, true, false] : List Bool).length + 1) + 1) + 3) +
      (2 * (max (M8 + ([true, false, false] : List Bool).length + 1)
        (M8 + ([true, true, false] : List Bool).length + 1) + 1) + 3))))))))))))))))

/-- `decFG` with numbers. -/
def decFGv (K B M : ℕ) : ℕ :=
  max (M + 1 + B + 1 + B + 1 + B + 1 + B + 1 + B + 1 + B + K + 1 + 1 + K +
    ([true, false, false] : List Bool).length + 1)
    (M + 1 + B + 1 + B + 1 + B + 1 + B + 1 + B + 1 + B + K + 1 + 1 + K +
    ([true, true, false] : List Bool).length + 1)

section Gen

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

theorem decFT_le (B X M : ℕ) (hT : ∀ x ∈ decTmpl c, x.2 ≤ X) :
    decFT (c := c) K B M ≤ decFTv K B X M := by
  have hK : (Algo.decRadW K).length = K := SigabaNeo.Lattices.Algo.length_toBits _ _
  have h := tmplT_le (decTmpl c) (M + 1 + B + 1 + B + 1 + B + 1 + B + 1 + B + 1 + B + K + 1) X hT
  have hl : (decTmpl c).length = 10 := rfl
  rw [hl] at h
  unfold decFT decFTv
  rw [hK]
  dsimp only
  omega

theorem decFG_eq (B M : ℕ) : decFG K B M = decFGv K B M := by
  have hK : (Algo.decRadW K).length = K := SigabaNeo.Lattices.Algo.length_toBits _ _
  unfold decFG decFGv
  rw [hK]

end Gen

/-- `decGT` with numbers. -/
def decGTv (n FL L LC K B X Tb Gb : ℕ) : ℕ :=
  let Mβ := max (16 * (n + 2)) FL
  let BT := max ((2 * (Mβ + 1) + 3) + (Tb + decFTv K B X Gb))
    (max (longT Mβ) ((2 * (Mβ + 1) + 3) + putT 3 Mβ) + 1) + 1
  let BL := max (decFGv K B Gb) (max Mβ (Mβ + 3 + 1))
  leT n (n + 1) + (max (2 * (n + 2 + 1) + 3)
    (parse4T (n + 2) + (frontTv L LC (16 * (n + 2)) + (BT +
      (256 * (2 * (BL + 1) + 3) + (2 * (BL + 1) + 3))))) + 1)

/-- `decBL` with numbers. -/
def decBLv (n FL K B Gb : ℕ) : ℕ :=
  let Mβ := max (16 * (n + 2)) FL
  max (decFGv K B Gb) (max Mβ (Mβ + 3 + 1))

section Gen2

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

theorem decGT_le (W B Tb Gb : ℕ) (hT : ∀ x ∈ decTmpl c, x.2 ≤ Gb) :
    decGT hk c W B Tb Gb ≤ decGTv (nDec hk c) (frontL c.L W) c.L
      (Prog.lookCount (frontTbl c.L W) [false]) K B Gb Tb Gb := by
  have h := decFT_le c B Gb Gb hT
  have hG := decFG_eq (K := K) B Gb
  unfold decGT decBT decBL decGTv
  rw [frontT_eq, hG]
  dsimp only
  gcongr

theorem decBL_eq (W B Gb : ℕ) :
    decBL hk c W B Gb = decBLv (nDec hk c) (frontL c.L W) K B Gb := by
  unfold decBL decBLv
  rw [decFG_eq]

end Gen2

theorem decGTv_mono {n FL L LC K B X Tb Gb n' FL' L' LC' K' B' X' Tb' Gb' : ℕ}
    (h1 : n ≤ n') (h2 : FL ≤ FL') (h3 : L ≤ L') (h4 : LC ≤ LC') (h5 : K ≤ K') (h6 : B ≤ B')
    (h7 : X ≤ X') (h8 : Tb ≤ Tb') (h9 : Gb ≤ Gb') :
    decGTv n FL L LC K B X Tb Gb ≤ decGTv n' FL' L' LC' K' B' X' Tb' Gb' := by
  simp only [decGTv, decFTv, decFGv, frontTv, prefT, putT, getT, leT, parse4T, unfrT, longT]
  gcongr

theorem decBLv_mono {n FL K B Gb n' FL' K' B' Gb' : ℕ} (h1 : n ≤ n') (h2 : FL ≤ FL') (h5 : K ≤ K')
    (h6 : B ≤ B') (h9 : Gb ≤ Gb') : decBLv n FL K B Gb ≤ decBLv n' FL' K' B' Gb' := by
  simp only [decBLv, decFGv]
  gcongr

/-! ### The constants at `confP` -/

open AdvancedEncryption.DualUse.Params

set_option maxRecDepth 100000 in
theorem fixLen_keyEnc_le : fixLen (keyEnc (N := Np) (K := Kp) confP) ≤ 2 ^ 130 := by
  simp only [fixLen]; comp_unfold; norm_num

set_option maxRecDepth 100000 in
theorem lPsi_le : lPsi (N := Np) (K := Kp) hkp ≤ 2 ^ 100 := by
  simp only [lPsi, fixLen]; comp_unfold; norm_num

set_option maxRecDepth 100000 in
theorem lenKA_conf : lenKA hkp confP + Np * Kp ≤ lenZ confP := by
  simp only [lenKA, lenZ, DualUse.rowL, lPsi, fixLen]
  comp_unfold
  norm_num

theorem lenKA_le : lenKA hkp confP ≤ 2 ^ 147 := by
  have := lenKA_conf; have := lenZ_le; omega

theorem lenCj_le : lenCj (N := Np) (K := Kp) hkp ≤ 2 ^ 176 := by
  simp only [lenCj]; rw [nJ_conf, rowL_conf]; norm_num

theorem LW_le : nJ (N := Np) (K := Kp) hkp * (lenZ confP + DualUse.rowL Np Kp kp) ≤ 2 ^ 236 := by
  rw [nJ_conf, lenZ_conf, rowL_conf]; norm_num

theorem nJR_le : nJ (N := Np) (K := Kp) hkp * DualUse.rowL Np Kp kp ≤ 2 ^ 176 := by
  rw [nJ_conf, rowL_conf]; norm_num

theorem kNK_le : kp * (Np * Kp) ≤ 2 ^ 85 := by rw [kp_eq, Np_def, Kp_def]; norm_num

theorem NK_le : Np * Kp ≤ 2 ^ 59 := by rw [Np_def, Kp_def]; norm_num

theorem nDec_le' {p s L t : ℕ} (hp : p = 515) (hs : s ≤ 2 ^ 200) (hL : L ≤ 2 ^ 20) (ht : t ≤ 2 ^ 200) :
    (2 * p + 1) + (2 * s + 1) + (2 * L + 1) + (2 * t + 1) ≤ 2 ^ 203 := by omega

theorem pw_len : DualUse.pw.length = 515 := by rw [DualUse.pw]; exact length_paramsWord_date

theorem nDec_le_gen {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) {S T L : ℕ}
    (h1 : fixLen (skEnc hk c) ≤ S) (h2 : fixLen (ctEnc hk c) ≤ T) (h3 : c.L ≤ L) :
    nDec hk c ≤ 2 * 515 + 1 + (2 * S + 1) + (2 * L + 1) + (2 * T + 1) := by
  have := pw_len
  unfold nDec
  omega

theorem nDec_le : nDec hkp confP ≤ 2 ^ 203 :=
  (nDec_le_gen hkp confP fixLen_skEnc_le fixLen_ctEnc_le confP_L_le).trans (by norm_num)

theorem decOffs_le_gen {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) {X : ℕ}
    (h1 : fixLen (skEnc hk c) ≤ X) (h2 : fixLen (ctEnc hk c) ≤ X) (h3 : lPsi (N := N) (K := K) hk ≤ X)
    (h4 : lenPK hk c ≤ X) (h5 : c.d * (N * K) ≤ X) (h6 : Algo.nT k * (N * K) ≤ X)
    (h7 : 2 * k * (N * K) ≤ X) (h8 : N * K ≤ X) : ∀ x ∈ decOffs hk c, x ≤ 4 * X := by
  intro x hx
  simp only [decOffs, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem decOffs_conf : ∀ x ∈ decOffs hkp confP, x ≤ 4 * 2 ^ 200 :=
  decOffs_le_gen hkp confP fixLen_skEnc_le fixLen_ctEnc_le (lPsi_le.trans (by norm_num))
    (lenPK_le.trans (by norm_num)) (by rw [dNK_conf]; norm_num)
    (by simp only [Algo.nT]; rw [kp_eq, Np_def, Kp_def]; norm_num) (rK_le.trans (by norm_num))
    (NK_le.trans (by norm_num))

theorem decTmpl_conf {G : ℕ} (hG : 2 ^ 250 ≤ G) : ∀ x ∈ decTmpl confP, x.2 ≤ G := by
  intro x hx
  simp only [decTmpl, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
    refine le_trans ?_ hG <;> (try simp only [Algo.nT]) <;> (try rw [confP_d]) <;> (try rw [kp_eq]) <;>
    (try rw [Np_def]) <;> (try rw [Kp_def]) <;> norm_num

theorem postTmplC_conf : ∀ x ∈ postTmplC Np Kp kp (lenZ confP) (DualUse.rowL Np Kp kp)
    (nJ (N := Np) (K := Kp) hkp), x.2 ≤ 2 ^ 147 := by
  have h1 := lenZ_le
  have h2 : DualUse.rowL Np Kp kp ≤ 2 ^ 86 := by rw [rowL_conf]; norm_num
  have h3 : nJ (N := Np) (K := Kp) hkp ≤ 2 ^ 90 := by rw [nJ_conf]; norm_num
  have h4 := kNK_le; have h5 := NK_le; have h6 := rK_le
  have h7 : kp ≤ 2 ^ 26 := kp_le
  have h8 : Np ≤ 2 ^ 34 := by rw [Np_def]
  have h9 : Kp ≤ 2 ^ 25 := by rw [Kp_def]
  have h10 : 1 * (2 * kp) * Np ≤ 2 ^ 61 := by rw [kp_eq, Np_def]; norm_num
  intro x hx
  simp only [postTmplC, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

set_option maxRecDepth 100000 in
/-- **The block of `c_f̂` at `confP`** (`a`: the bound of tape `0`, `M`: the uniform bound). -/
theorem ph_cfX_conf {a M : ℕ} (ha : a ≤ 2 ^ 210) {β : Fin 256 → ℕ} (h0 : β 0 ≤ a)
    (h1 : β 1 ≤ frontL confP.L WB2.Wc) (hβ : ∀ i, β i ≤ M) :
    Ph (cfX hkp confP (wfB2 hkp confP WB2.Wc)) β
      (256 * (2 * (M + 1) + 3) + (2 * (M + 1) + 3) + (preTCX (2 ^ 242) + (2 ^ 556 +
        postCT (lenPK hkp confP) (lenKA hkp confP) (Np * Kp) (offWk hkp confP)
          (nJ (N := Np) (K := Kp) hkp * (lenZ confP + DualUse.rowL Np Kp kp)) (lenZ confP) Np Kp kp
          (lenZ confP) (DualUse.rowL Np Kp kp) (nJ (N := Np) (K := Kp) hkp) (2 ^ 250))))
      (fun _ => postCG (lenPK hkp confP) (lenKA hkp confP) (Np * Kp)
        (nJ (N := Np) (K := Kp) hkp * (lenZ confP + DualUse.rowL Np Kp kp)) Np Kp kp
        (nJ (N := Np) (K := Kp) hkp) (DualUse.rowL Np Kp kp) (2 ^ 250)) := by
  have hKA := lenKA_le
  have hPs := lPsi_le
  have hCj := lenCj_le
  have hkE := fixLen_keyEnc_le
  have hP := lenPK_le
  have hNK := NK_le
  refine ph_cfX (hk := hkp) (c := confP) (wfB := wfB2 hkp confP WB2.Wc) (Lw := 2 ^ 240)
    (LF := frontL confP.L WB2.Wc) (Tw := 2 ^ 556) (Gw := 2 ^ 250) (a := a) (Mβ := M) (X := 2 ^ 242)
    wfCost_wfB2.time wfCost_wfB2.len ?_ ?_ ?_ ?_ ?_ ?_ h0 h1 hβ
  · rw [nJ_conf, rowL_conf, dNK_conf, lenZ_conf, confP_d, lenPK_eq]
    omega
  · omega
  · omega
  · omega
  · rw [nJ_conf, rowL_conf, dNK_conf, lenZ_conf, confP_d, lenPK_eq]
    omega
  · intro x hx
    exact (postTmplC_conf x hx).trans (by norm_num)

/-! ### The clock of `Dec` -/

theorem aD_le' {n : ℕ} (h : n ≤ 2 ^ 203) : 16 * (n + 2) ≤ 2 ^ 210 := by omega

theorem aD_le : 16 * (nDec hkp confP + 2) ≤ 2 ^ 210 := aD_le' nDec_le

set_option exponentiation.threshold 2000 in
theorem preTCX_conf : preTCX (2 ^ 242) ≤ 2 ^ 1000 := by
  simp only [preTCX, getT, wTX, prefT]; norm_num

set_option exponentiation.threshold 3000 in
theorem postCTv_conf : postCTv (2 ^ 175) (2 ^ 147) (2 ^ 59) (2 ^ 176) (2 ^ 236) (2 ^ 147) (2 ^ 85)
    (2 ^ 176) (2 ^ 147) (2 ^ 250) ≤ 2 ^ 2020 := by
  simp only [postCTv, getT, prefT, skipT, forT, loopT]; norm_num

theorem postCT_conf : postCT (lenPK hkp confP) (lenKA hkp confP) (Np * Kp) (offWk hkp confP)
    (nJ (N := Np) (K := Kp) hkp * (lenZ confP + DualUse.rowL Np Kp kp)) (lenZ confP) Np Kp kp
    (lenZ confP) (DualUse.rowL Np Kp kp) (nJ (N := Np) (K := Kp) hkp) (2 ^ 250) ≤ 2 ^ 2020 :=
  ((postCT_le _ _ _ _ _ _ Np Kp kp _ _ _ (2 ^ 147) (2 ^ 250) postTmplC_conf).trans
    (postCTv_mono lenPK_le lenKA_le NK_le offWk_le LW_le lenZ_le kNK_le nJR_le le_rfl le_rfl)).trans
    postCTv_conf

set_option exponentiation.threshold 2000 in
theorem postCGv_conf : postCGv (2 ^ 175) (2 ^ 147) (2 ^ 59) (2 ^ 236) (2 ^ 85) (2 ^ 176) (2 ^ 250) ≤
    2 ^ 502 := by
  simp only [postCGv]; norm_num

theorem le_postCGv (L A NK LW kNK nJR M : ℕ) : M ≤ postCGv L A NK LW kNK nJR M := by
  simp only [postCGv]; omega

/-- The bound of every tape after the block of `c_f̂`. -/
local notation "GbD" => postCG (lenPK hkp confP) (lenKA hkp confP) (Np * Kp)
  (nJ (N := Np) (K := Kp) hkp * (lenZ confP + DualUse.rowL Np Kp kp)) Np Kp kp
  (nJ (N := Np) (K := Kp) hkp) (DualUse.rowL Np Kp kp) (2 ^ 250)

/-- The time of the block of `c_f̂`. -/
local notation "TbD" => 256 * (2 * (max (16 * (nDec hkp confP + 2)) (frontL confP.L WB2.Wc) + 1) + 3) +
  (2 * (max (16 * (nDec hkp confP + 2)) (frontL confP.L WB2.Wc) + 1) + 3) + (preTCX (2 ^ 242) +
  (2 ^ 556 + postCT (lenPK hkp confP) (lenKA hkp confP) (Np * Kp) (offWk hkp confP)
    (nJ (N := Np) (K := Kp) hkp * (lenZ confP + DualUse.rowL Np Kp kp)) (lenZ confP) Np Kp kp
    (lenZ confP) (DualUse.rowL Np Kp kp) (nJ (N := Np) (K := Kp) hkp) (2 ^ 250)))

theorem GbD_le : GbD ≤ 2 ^ 502 :=
  ((le_of_eq (postCG_eq _ _ _ _ _ _ _ _ _ _)).trans
    (postCGv_mono lenPK_le lenKA_le NK_le LW_le kNK_le nJR_le le_rfl)).trans postCGv_conf

theorem le_GbD : 2 ^ 250 ≤ GbD :=
  (le_postCGv _ _ _ _ _ _ _).trans (le_of_eq (postCG_eq _ _ _ _ _ _ _ _ _ _).symm)

set_option exponentiation.threshold 3000 in
theorem tbD_arith {m q r : ℕ} (hm : m ≤ 2 ^ 232) (hq : q ≤ 2 ^ 1000) (hr : r ≤ 2 ^ 2020) :
    256 * (2 * (m + 1) + 3) + (2 * (m + 1) + 3) + (q + (2 ^ 556 + r)) ≤ 2 ^ 2021 :=
  calc 256 * (2 * (m + 1) + 3) + (2 * (m + 1) + 3) + (q + (2 ^ 556 + r))
      ≤ 256 * (2 * (2 ^ 232 + 1) + 3) + (2 * (2 ^ 232 + 1) + 3) + (2 ^ 1000 + (2 ^ 556 + 2 ^ 2020)) := by
        gcongr
    _ ≤ 2 ^ 2021 := by norm_num

theorem TbD_le : TbD ≤ 2 ^ 2021 :=
  tbD_arith (max_le (aD_le.trans (by norm_num)) frontL_Wc) preTCX_conf postCT_conf

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 5000 in
theorem decGTv_conf : decGTv (2 ^ 203) (2 ^ 232) (2 ^ 20) (2 ^ 231) (2 ^ 25) (4 * 2 ^ 200) (2 ^ 502)
    (2 ^ 2021) (2 ^ 502) ≤ 2 ^ 4100 := by
  simp only [decGTv, decFTv, decFGv, frontTv, prefT, putT, getT, leT, parse4T, unfrT, longT,
    List.length_cons, List.length_nil]
  norm_num

set_option exponentiation.threshold 1000 in
theorem decBLv_conf : decBLv (2 ^ 203) (2 ^ 232) (2 ^ 25) (4 * 2 ^ 200) (2 ^ 502) ≤ 2 ^ 510 := by
  simp only [decBLv, decFGv, List.length_cons, List.length_nil]; norm_num

theorem Kp_le25 : Kp ≤ 2 ^ 25 := by rw [Kp_def]

theorem decGT_conf : decGT hkp confP WB2.Wc (4 * 2 ^ 200) TbD GbD ≤ 2 ^ 4100 :=
  ((decGT_le hkp confP WB2.Wc (4 * 2 ^ 200) TbD GbD (decTmpl_conf le_GbD)).trans
    (decGTv_mono nDec_le frontL_Wc confP_L_le (lookCount_conf Wc_ge Wc_le) Kp_le25 le_rfl GbD_le
      TbD_le GbD_le)).trans decGTv_conf

theorem decBL_conf : decBL hkp confP WB2.Wc (4 * 2 ^ 200) GbD ≤ 2 ^ 510 :=
  ((le_of_eq (decBL_eq hkp confP WB2.Wc (4 * 2 ^ 200) GbD)).trans
    (decBLv_mono nDec_le frontL_Wc Kp_le25 le_rfl GbD_le)).trans decBLv_conf

theorem ph_decGenP_conf :
    timeBoundT (decGenP hkp confP (cfX hkp confP (wfB2 hkp confP WB2.Wc)) WB2.Wc)
        (Prog.inputBound (255 : Fin 256) (nDec hkp confP + 1)) ≤
        decGT hkp confP WB2.Wc (4 * 2 ^ 200) TbD GbD ∧
      lenBoundT (decGenP hkp confP (cfX hkp confP (wfB2 hkp confP WB2.Wc)) WB2.Wc)
        (Prog.inputBound (255 : Fin 256) (nDec hkp confP + 1)) 0 ≤
        decBL hkp confP WB2.Wc (4 * 2 ^ 200) GbD :=
  ph_decGenP (hk := hkp) (c := confP) (cfX hkp confP (wfB2 hkp confP WB2.Wc)) WB2.Wc (4 * 2 ^ 200)
    (Tb := TbD) (Gb := GbD)
    (fun _ h0 h1 hβ => ph_cfX_conf (a := 16 * (nDec hkp confP + 2))
      (M := max (16 * (nDec hkp confP + 2)) (frontL confP.L WB2.Wc)) aD_le h0 h1 hβ)
    decOffs_conf (decTmpl_conf le_GbD)

set_option exponentiation.threshold 5000 in
theorem dec_arith {n T L : ℕ} (hn : n ≤ 2 ^ 203) (hT : T ≤ 2 ^ 4100) (hL : L ≤ 2 ^ 510) :
    2 * (n + 1) + 2 + T + (2 * L + 2) ≤ 2 ^ 4200 :=
  calc 2 * (n + 1) + 2 + T + (2 * L + 2) ≤ 2 * (2 ^ 203 + 1) + 2 + 2 ^ 4100 + (2 * 2 ^ 510 + 2) := by
        gcongr
    _ ≤ 2 ^ 4200 := by norm_num

/-- **The clock of `Dec` at `confP`.** -/
theorem time_decMachineP_conf :
    (decMachineP hkp confP (cfX hkp confP (wfB2 hkp confP WB2.Wc)) WB2.Wc).time ≤ 2 ^ 4200 := by
  rw [time_decMachineP]
  exact dec_arith nDec_le (ph_decGenP_conf.1.trans decGT_conf) (ph_decGenP_conf.2.trans decBL_conf)

end AdvancedEncryption.DualUse.Prog
