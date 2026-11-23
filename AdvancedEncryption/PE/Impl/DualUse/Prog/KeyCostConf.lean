import PE.Impl.DualUse.Prog.CostConf
import PE.Impl.DualUse.Prog.KeyGenCost
import PE.Impl.DualUse.Prog.BlockCost
import PE.Impl.DualUse.Prog.KeyCostC
import PE.Impl.DualUse.AHFinal
import PE.Impl.DualUse.ImplP

/-!
# Envelopes of the clock of `KeyGen`

The time bound `keyGT` of `KeyGen`'s program and the bound `postBT` of the read-back block are
bounded by envelopes (`keyGTv`, `postBTv`) whose arguments are plain numbers (the counts, the
look-up count of the front end, the constants of the key try); the envelopes are monotone
(`keyGTv_mono`, `postBTv_mono`), so closed bounds follow from bounds of their arguments.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg
open SigabaNeo.Tape.Prog (leP unfrP frP leT unfrT frT tailsP)
open AdvancedEncryption.PE.Gates.DateWindow
open SigabaNeo.Lattices.Algo
open scoped SigabaNeo.Tape.Prog

/-! ### The front end -/

/-- `frontT` with the look-up count as a number. -/
def frontTv (n LC T : ℕ) : ℕ :=
  20 * T + ((n + 2) * (2 * (n + 2) + 5) + 10 * (2 * (n + 11) + 5) +
    (LC + 12) * (2 * (n + 1 + (LC + 12)) + 5))

theorem frontT_eq (n W T : ℕ) :
    frontT n W T = frontTv n (Prog.lookCount (frontTbl n W) [false]) T := rfl

/-! ### The window branch -/

/-- `winT2` with numbers for the counts (`P` the public key, `R` the trapdoor row, `sW`, `pW` the
words of the configuration, `tC`, `tD` the constants of the key try). -/
def winT2v (P R sW pW tC tD M : ℕ) : ℕ :=
  let M1 := M + 1 + P
  let M2 := M1 + 1 + R
  let M3 := M2 + sW + 1
  let M4 := M3 + pW + 1
  prefT P M + etT (P + R) P R M1 + putT sW M2 + putT pW M3 +
    (23 * ((2 * M + 1) * (4 * M4 + 12)) + (2 * (M4 + 1) + 3)) +
    (23 * (M4 + 1) ^ 2 + tC * (2 * M4 + 1) ^ tD) + frT (2 * M4) +
    (31 * (2 * (3 * (2 * M4) + 1 + 1) + 3) + (2 * (3 * (2 * M4) + 1 + 1) + 3))

section Gen

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

theorem winT2_le (cf : KeyCfg) (M : ℕ) (hT : tmplMax (keyTmplR hk c cf) ≤ M) :
    winT2 hk c cf M ≤ winT2v (lenPK hk c) (2 * k * (N * K)) cf.sW.length
      (powW K (cf.B - 1)).length (Prog.tbC (ProgKeyR.keyTryRP ⨾ Prog.clr 3))
      (Prog.tbD (ProgKeyR.keyTryRP ⨾ Prog.clr 3)) M := by
  have h := tmplT_le (keyTmplR hk c cf) (M + 1 + lenPK hk c + 1 + 2 * k * (N * K) + cf.sW.length +
    1 + (powW K (cf.B - 1)).length + 1) M (fun x hx => (le_tmplMax _ x hx).trans hT)
  have hl : (keyTmplR hk c cf).length = 23 := rfl
  have hc : keyClrR.length = 31 := rfl
  rw [hl] at h
  unfold winT2 winT2v keyTryRT
  rw [hc]
  dsimp only
  omega

end Gen

/-- `keyGT` with numbers: `n` the input length, `FL` the front end's output bound, `L` the
predicate bound, `LC` the look-up count, `dl` the length of the dummy key. -/
def keyGTv (n FL L LC P R sW pW dl tC tD Tb Gb : ℕ) : ℕ :=
  let Mβ := max (8 * (n + 2)) FL
  let dD := Mβ + 1 + P + dl + 1
  let dT := (2 * (Mβ + 1) + 3) + prefT P Mβ + putT dl (Mβ + 1 + P) + (2 * (dD + 1) + 3) +
    (2 * (dD + 1 + 1) + 3)
  let BT := max ((2 * (Mβ + 1) + 3) + (Tb + winT2v P R sW pW tC tD Gb))
    (max (longT Mβ) (dT + frT (dD + 1)) + 1) + 1
  let BL := max (3 * (2 * (Gb + 1 + P + 1 + R + sW + 1 + pW + 1)) + 1)
    (max Mβ (3 * (dD + 1) + 1))
  leT n (n + 1) + (max (2 * (n + 2 + 1) + 3)
    (parseT (n + 2) + (frontTv L LC (8 * (n + 2)) + (BT +
      (256 * (2 * (BL + 1) + 3) + (2 * (BL + 1) + 3))))) + 1)

/-- `keyBL` with numbers. -/
def keyBLv (n FL P R sW pW dl Gb : ℕ) : ℕ :=
  let Mβ := max (8 * (n + 2)) FL
  max (3 * (2 * (Gb + 1 + P + 1 + R + sW + 1 + pW + 1)) + 1)
    (max Mβ (3 * (Mβ + 1 + P + dl + 1 + 1) + 1))

section Gen2

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

theorem keyGT_le (W : ℕ) (cf : KeyCfg) (Tb Gb : ℕ) (hT : tmplMax (keyTmplR hk c cf) ≤ Gb) :
    keyGT hk c W cf Tb Gb ≤ keyGTv (nKG hk c) (frontL c.L W) c.L
      (Prog.lookCount (frontTbl c.L W) [false]) (lenPK hk c) (2 * k * (N * K)) cf.sW.length
      (powW K (cf.B - 1)).length ((keyEnc (N := N) (K := K) c).enc (dummyKey c)).length
      (Prog.tbC (ProgKeyR.keyTryRP ⨾ Prog.clr 3)) (Prog.tbD (ProgKeyR.keyTryRP ⨾ Prog.clr 3)) Tb Gb := by
  have h := winT2_le hk c cf Gb hT
  unfold keyGT keyBT keyBL winG keyGTv dumT dumD
  rw [frontT_eq]
  dsimp only
  gcongr

theorem keyBL_eq (W : ℕ) (cf : KeyCfg) (Gb : ℕ) :
    keyBL hk c W cf Gb = keyBLv (nKG hk c) (frontL c.L W) (lenPK hk c) (2 * k * (N * K))
      cf.sW.length (powW K (cf.B - 1)).length
      ((keyEnc (N := N) (K := K) c).enc (dummyKey c)).length Gb := rfl

end Gen2

theorem keyGTv_mono {n FL L LC P R sW pW dl tC tD Tb Gb n' FL' L' LC' P' R' sW' pW' dl' tC' tD' Tb' Gb' : ℕ}
    (h1 : n ≤ n') (h2 : FL ≤ FL') (h3 : L ≤ L') (h4 : LC ≤ LC') (h5 : P ≤ P') (h6 : R ≤ R')
    (h7 : sW ≤ sW') (h8 : pW ≤ pW') (h9 : dl ≤ dl') (h10 : tC ≤ tC') (h11 : tD ≤ tD')
    (h12 : Tb ≤ Tb') (h13 : Gb ≤ Gb') :
    keyGTv n FL L LC P R sW pW dl tC tD Tb Gb ≤ keyGTv n' FL' L' LC' P' R' sW' pW' dl' tC' tD' Tb' Gb' := by
  simp only [keyGTv, winT2v, frontTv, prefT, etT, putT, frT, leT, parseT, unfrT, longT]
  gcongr
  all_goals omega

theorem keyBLv_mono {n FL P R sW pW dl Gb n' FL' P' R' sW' pW' dl' Gb' : ℕ}
    (h1 : n ≤ n') (h2 : FL ≤ FL') (h5 : P ≤ P') (h6 : R ≤ R')
    (h7 : sW ≤ sW') (h8 : pW ≤ pW') (h9 : dl ≤ dl') (h13 : Gb ≤ Gb') :
    keyBLv n FL P R sW pW dl Gb ≤ keyBLv n' FL' P' R' sW' pW' dl' Gb' := by
  unfold keyBLv
  dsimp only
  gcongr

/-! ### The read-back block -/

/-- `postBT` with a bound `Xp` of the templates. -/
def postBTv (L LT oW Zr Xp M : ℕ) : ℕ :=
  let Ma := M + 1 + L
  let Mb := Ma + 1 + LT
  let Mc := Mb + 1 + L
  let Md := Mc + 1 + LT
  getT 0 L M + getT oW LT Ma + (2 * (Mb + 1) + 3) + prefT L Mb + prefT LT Mc +
    (Zr + 1) * (2 * (Md + 1) + 3) + (6 * ((2 * Xp + 1) * (4 * Md + 12)) + (2 * (Md + 1) + 3)) +
    375 * (Md + 1) ^ 4 + 210 * (Md + 1) ^ 3 + (2 * (Md + 1) + 3) +
    (52 * (2 * (Md + 1) + 3) + (2 * (Md + 1) + 3))

theorem postBT_le (L LT oW Zr N K k Xp M : ℕ) (hX : ∀ x ∈ postTmpl N K k, x.2 ≤ Xp) :
    postBT L LT oW Zr N K k M ≤ postBTv L LT oW Zr Xp M := by
  have h := tmplT_le (postTmpl N K k) (M + 1 + L + 1 + LT + 1 + L + 1 + LT) Xp hX
  have hl : (postTmpl N K k).length = 6 := rfl
  rw [hl] at h
  unfold postBT postBTv
  dsimp only
  omega

theorem postBTv_mono {L LT oW Zr Xp M L' LT' oW' Zr' Xp' M' : ℕ} (h1 : L ≤ L') (h2 : LT ≤ LT')
    (h3 : oW ≤ oW') (h4 : Zr ≤ Zr') (h5 : Xp ≤ Xp') (h6 : M ≤ M') :
    postBTv L LT oW Zr Xp M ≤ postBTv L' LT' oW' Zr' Xp' M' := by
  simp only [postBTv, getT, prefT]
  gcongr

theorem tmplMax_le_of {n : ℕ} {X : ℕ} : ∀ l : List (Fin n × ℕ), (∀ x ∈ l, x.2 ≤ X) → tmplMax l ≤ X
  | [], _ => Nat.zero_le _
  | x :: l, h => max_le (h x (by simp)) (tmplMax_le_of l fun y hy => h y (by simp [hy]))

/-! ### The constants at `confP` -/

open AdvancedEncryption.DualUse.Params

theorem kp_le : kp ≤ 2 ^ 26 := by rw [kp_eq]; norm_num

theorem rowL_conf : DualUse.rowL Np Kp kp = 2 * (2 ^ 25 + 1) * (2 ^ 34 * 2 ^ 25) := by
  rw [kp_eq, Np_def, Kp_def]

theorem nJ_conf : nJ (N := Np) (K := Kp) hkp = 10 * (2 * (2 * (2 ^ 25 + 1) * ((2 ^ 25 + 1) * 2 ^ 34))) := by
  simp only [nJ, DualUse.JIx, SigabaNeo.Encode.Enum.length_prod, len_Attr, len_Index]
  rw [kp_eq, Np_def]

theorem lenZ_conf : lenZ confP = (2 ^ 61 - 1) * (2 * (2 ^ 25 + 1) * (2 ^ 34 * 2 ^ 25)) := by
  simp only [lenZ]; rw [confP_d, rowL_conf]

theorem lenT_conf : lenT Np Kp kp = 2 * (2 ^ 25 + 1) * (2 ^ 34 * 2 ^ 25) + 2 ^ 34 * 2 ^ 25 := by
  simp only [lenT]; rw [rowL_conf, Np_def, Kp_def]

theorem offBk_conf : offBk confP = 1 * (2 ^ 61 * (2 ^ 34 * 2 ^ 25)) +
    1 * ((1 + (2 * (2 ^ 25 + 1) + 2 * (2 ^ 25 + 1))) * (2 ^ 34 * 2 ^ 25)) := by
  simp only [offBk, len_fin, len_trap]; rw [confP_d, kp_eq, Np_def, Kp_def]

theorem lenPK_le : lenPK hkp confP ≤ 2 ^ 175 := by rw [lenPK_eq]; norm_num

theorem offWk_conf : offWk hkp confP = lenPK hkp confP + 2 ^ 61 * (2 ^ 34 * 2 ^ 25) +
    10 * (2 ^ 61 * (2 * (2 ^ 25 + 1) * (2 ^ 34 * 2 ^ 25))) := by
  simp only [offWk]
  rw [rowL_conf, confP_d, show Np * Kp = 2 ^ 34 * 2 ^ 25 by rw [Np_def, Kp_def]]

theorem dNK_conf : confP.d * (Np * Kp) = 2 ^ 61 * (2 ^ 34 * 2 ^ 25) := by
  rw [confP_d, Np_def, Kp_def]

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 1000 in
theorem nKG_le : nKG hkp confP ≤ 2 ^ 178 := by
  have hL := confP_L_le
  have h515 := length_paramsWord_date
  have hm : fixLen (mskEnc hkp confP) ≤ 2 ^ 176 := by
    simp only [fixLen, mskEnc]; comp_unfold; norm_num
  simp only [nKG, DualUse.pw]
  omega

/-! ### The key-row block at `confP` -/

theorem aK_le' {n : ℕ} (h : n ≤ 2 ^ 178) : 8 * (n + 2) ≤ 2 ^ 182 := by omega

theorem aK_le : 8 * (nKG hkp confP + 2) ≤ 2 ^ 182 := aK_le' nKG_le

theorem frontL_Wc : frontL confP.L WB2.Wc ≤ 2 ^ 232 := frontL_conf Wc_ge Wc_le

theorem lenTc_le : lenT Np Kp kp ≤ 2 ^ 87 := by rw [lenT_conf]; norm_num
theorem lenZ_le : lenZ confP ≤ 2 ^ 147 := by rw [lenZ_conf]; norm_num
theorem offWk_le : offWk hkp confP ≤ 2 ^ 176 := by rw [offWk_conf, lenPK_eq]; norm_num

set_option maxRecDepth 100000 in
/-- **The key-row block at `confP`** (`a`: the bound of tape `0`, `M`: the uniform bound). -/
theorem ph_bfX_conf {a M : ℕ} (ha : a ≤ 2 ^ 182) {β : Fin 256 → ℕ} (h0 : β 0 ≤ a)
    (h1 : β 1 ≤ frontL confP.L WB2.Wc) (hβ : ∀ i, β i ≤ M) :
    Ph (bfX hkp confP (wfB2 hkp confP WB2.Wc)) β
      (256 * (2 * (M + 1) + 3) + (2 * (M + 1) + 3) + (preTX (2 ^ 241) + (2 ^ 556 +
        postBT (lenPK hkp confP) (lenT Np Kp kp) (offWk hkp confP) (lenZ confP) Np Kp kp (2 ^ 250))))
      (fun _ => 2 ^ 250 + 1 + lenPK hkp confP + 1 + lenT Np Kp kp + 1 + lenPK hkp confP + 1 +
        lenT Np Kp kp) := by
  refine ph_bfX (hk := hkp) (c := confP) (wfB := wfB2 hkp confP WB2.Wc) (Lw := 2 ^ 240)
    (LF := frontL confP.L WB2.Wc) (Tw := 2 ^ 556) (Gw := 2 ^ 250) (a := a) (Mβ := M) (X := 2 ^ 241)
    wfCost_wfB2.time wfCost_wfB2.len ?_ ?_ ?_ ?_ ?_ ?_ ?_ h0 h1 hβ
  · refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left (Nat.sub_le _ _) _) 10) ?_
    rw [lenT_conf, nJ_conf, rowL_conf, dNK_conf, lenZ_conf, confP_d, lenPK_eq]
    omega
  · rw [offBk_conf]; norm_num
  · rw [rowL_conf, confP_d]; norm_num
  · rw [rowL_conf]; norm_num
  · rw [nJ_conf]; norm_num
  · rw [nJ_conf, rowL_conf, dNK_conf, lenZ_conf, confP_d, lenPK_eq]
    omega
  · intro x hx
    simp only [postTmpl, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
      (try rw [kp_eq]) <;> (try rw [Np_def]) <;> (try rw [Kp_def]) <;> norm_num

set_option exponentiation.threshold 2000 in
theorem preTX_conf : preTX (2 ^ 241) ≤ 2 ^ 1000 := by
  simp only [preTX, getT, wTX, prefT]; norm_num

set_option exponentiation.threshold 2000 in
theorem postBTv_conf : postBTv (2 ^ 175) (2 ^ 87) (2 ^ 176) (2 ^ 147) (2 ^ 87) (2 ^ 250) ≤ 2 ^ 1010 := by
  simp only [postBTv, getT, prefT]; norm_num

theorem postTmpl_conf : ∀ x ∈ postTmpl Np Kp kp, x.2 ≤ 2 ^ 87 := by
  intro x hx
  simp only [postTmpl, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
    (try rw [kp_eq]) <;> (try rw [Np_def]) <;> (try rw [Kp_def]) <;> norm_num

theorem postBT_conf : postBT (lenPK hkp confP) (lenT Np Kp kp) (offWk hkp confP) (lenZ confP) Np Kp kp
    (2 ^ 250) ≤ 2 ^ 1010 :=
  ((postBT_le _ _ _ _ Np Kp kp (2 ^ 87) (2 ^ 250) postTmpl_conf).trans
    (postBTv_mono lenPK_le lenTc_le offWk_le lenZ_le le_rfl le_rfl)).trans postBTv_conf

set_option exponentiation.threshold 2000 in
theorem tb_arith {m q r : ℕ} (hm : m ≤ 2 ^ 232) (hq : q ≤ 2 ^ 1000) (hr : r ≤ 2 ^ 1010) :
    256 * (2 * (m + 1) + 3) + (2 * (m + 1) + 3) + (q + (2 ^ 556 + r)) ≤ 2 ^ 1011 :=
  calc 256 * (2 * (m + 1) + 3) + (2 * (m + 1) + 3) + (q + (2 ^ 556 + r))
      ≤ 256 * (2 * (2 ^ 232 + 1) + 3) + (2 * (2 ^ 232 + 1) + 3) + (2 ^ 1000 + (2 ^ 556 + 2 ^ 1010)) := by
        gcongr
    _ ≤ 2 ^ 1011 := by norm_num

theorem gb_arith {P T : ℕ} (hP : P ≤ 2 ^ 175) (hT : T ≤ 2 ^ 87) :
    2 ^ 250 ≤ 2 ^ 250 + 1 + P + 1 + T + 1 + P + 1 + T ∧
      2 ^ 250 + 1 + P + 1 + T + 1 + P + 1 + T ≤ 2 ^ 251 := by
  constructor
  · omega
  · have : (2 : ℕ) ^ 251 = 2 ^ 250 + 2 ^ 250 := by norm_num
    have : (2 : ℕ) ^ 176 ≤ 2 ^ 249 := by norm_num
    omega

theorem tbs_keyTryRP : Prog.tbD (ProgKeyR.keyTryRP ⨾ Prog.clr 3) ≤ 16 ∧
    Prog.tbC (ProgKeyR.keyTryRP ⨾ Prog.clr 3) ≤ 2 ^ 40 := by decide +kernel

theorem keyTmplR_conf {G : ℕ} (hG : 2 ^ 250 ≤ G) : tmplMax (keyTmplR hkp confP cfP) ≤ G := by
  refine tmplMax_le_of _ fun x hx => ?_
  simp only [keyTmplR, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hx | rfl | rfl | rfl
  · exact ((le_tmplMax _ x hx).trans tmplMax_conf).trans ((by norm_num : (2:ℕ) ^ 182 ≤ 2 ^ 250).trans hG)
  all_goals (dsimp only; refine le_trans ?_ hG; (try rw [kp_eq]); (try rw [Np_def]); (try rw [Kp_def]); norm_num)

set_option exponentiation.threshold 5000 in
theorem key_arith {n T L : ℕ} (hn : n ≤ 2 ^ 178) (hT : T ≤ 2 ^ 4150) (hL : L ≤ 2 ^ 260) :
    2 * (n + 1) + 2 + T + (2 * L + 2) ≤ 2 ^ 4200 :=
  calc 2 * (n + 1) + 2 + T + (2 * L + 2) ≤ 2 * (2 ^ 178 + 1) + 2 + 2 ^ 4150 + (2 * 2 ^ 260 + 2) := by
        gcongr
    _ ≤ 2 ^ 4200 := by norm_num

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 5000 in
theorem keyGTv_conf : keyGTv (2 ^ 178) (2 ^ 232) (2 ^ 20) (2 ^ 231) (2 ^ 175) (2 ^ 87) (2 ^ 25) (2 ^ 25)
    (2 ^ 130) (2 ^ 40) 16 (2 ^ 1011) (2 ^ 251) ≤ 2 ^ 4150 := by
  simp only [keyGTv, winT2v, frontTv, prefT, etT, putT, frT, leT, parseT, unfrT, longT]
  norm_num

set_option exponentiation.threshold 1000 in
theorem keyBLv_conf : keyBLv (2 ^ 178) (2 ^ 232) (2 ^ 175) (2 ^ 87) (2 ^ 25) (2 ^ 25) (2 ^ 130) (2 ^ 251) ≤
    2 ^ 260 := by
  simp only [keyBLv]; norm_num

theorem rK_le : 2 * kp * (Np * Kp) ≤ 2 ^ 87 := by rw [kp_eq, Np_def, Kp_def]; norm_num

/-- The time of the key-row block at `confP`. -/
local notation "TbK" => 256 * (2 * (max (8 * (nKG hkp confP + 2)) (frontL confP.L WB2.Wc) + 1) + 3) +
  (2 * (max (8 * (nKG hkp confP + 2)) (frontL confP.L WB2.Wc) + 1) + 3) + (preTX (2 ^ 241) +
  (2 ^ 556 + postBT (lenPK hkp confP) (lenT Np Kp kp) (offWk hkp confP) (lenZ confP) Np Kp kp (2 ^ 250)))

/-- The bound of every tape after the key-row block at `confP`. -/
local notation "GbK" => 2 ^ 250 + 1 + lenPK hkp confP + 1 + lenT Np Kp kp + 1 + lenPK hkp confP + 1 +
  lenT Np Kp kp

theorem TbK_le : TbK ≤ 2 ^ 1011 :=
  tb_arith (max_le (aK_le.trans (by norm_num)) frontL_Wc) preTX_conf postBT_conf

theorem GbK_le : GbK ≤ 2 ^ 251 := (gb_arith lenPK_le lenTc_le).2

theorem le_GbK : 2 ^ 250 ≤ GbK := (gb_arith lenPK_le lenTc_le).1

theorem keyGT_conf : keyGT hkp confP WB2.Wc cfP TbK GbK ≤ 2 ^ 4150 :=
  ((keyGT_le hkp confP WB2.Wc cfP TbK GbK (keyTmplR_conf le_GbK)).trans
    (keyGTv_mono (n' := 2 ^ 178) (FL' := 2 ^ 232) (L' := 2 ^ 20) (LC' := 2 ^ 231) (P' := 2 ^ 175)
      (R' := 2 ^ 87) (sW' := 2 ^ 25) (pW' := 2 ^ 25) (dl' := 2 ^ 130) (tC' := 2 ^ 40) (tD' := 16)
      (Tb' := 2 ^ 1011) (Gb' := 2 ^ 251) nKG_le frontL_Wc confP_L_le (lookCount_conf Wc_ge Wc_le)
      lenPK_le rK_le (le_of_eq length_sW_cfP) (le_of_eq length_powW_cfP) lenDummy_le
      tbs_keyTryRP.2 tbs_keyTryRP.1 TbK_le GbK_le)).trans keyGTv_conf

theorem keyBL_conf : keyBL hkp confP WB2.Wc cfP GbK ≤ 2 ^ 260 :=
  ((le_of_eq (keyBL_eq hkp confP WB2.Wc cfP GbK)).trans
    (keyBLv_mono (n' := 2 ^ 178) (FL' := 2 ^ 232) (P' := 2 ^ 175) (R' := 2 ^ 87) (sW' := 2 ^ 25)
      (pW' := 2 ^ 25) (dl' := 2 ^ 130) (Gb' := 2 ^ 251) nKG_le frontL_Wc lenPK_le rK_le
      (le_of_eq length_sW_cfP) (le_of_eq length_powW_cfP) lenDummy_le GbK_le)).trans keyBLv_conf

theorem ph_keyGenP_conf :
    timeBoundT (keyGenP hkp confP (bfX hkp confP (wfB2 hkp confP WB2.Wc)) WB2.Wc cfP)
        (Prog.inputBound (255 : Fin 256) (nKG hkp confP + 1)) ≤ keyGT hkp confP WB2.Wc cfP TbK GbK ∧
      lenBoundT (keyGenP hkp confP (bfX hkp confP (wfB2 hkp confP WB2.Wc)) WB2.Wc cfP)
        (Prog.inputBound (255 : Fin 256) (nKG hkp confP + 1)) 0 ≤ keyBL hkp confP WB2.Wc cfP GbK :=
  ph_keyGenP (hk := hkp) (c := confP) (bfX hkp confP (wfB2 hkp confP WB2.Wc)) WB2.Wc cfP
    (Tb := TbK) (Gb := GbK)
    (fun _ h0 h1 hβ => ph_bfX_conf (a := 8 * (nKG hkp confP + 2))
      (M := max (8 * (nKG hkp confP + 2)) (frontL confP.L WB2.Wc)) aK_le h0 h1 hβ)
    (keyTmplR_conf le_GbK)

/-- **The clock of `KeyGen` at `confP`.** -/
theorem time_keyMachineP_conf :
    (keyMachineP hkp confP (bfX hkp confP (wfB2 hkp confP WB2.Wc)) WB2.Wc cfP).time ≤ 2 ^ 4200 := by
  rw [time_keyMachineP]
  exact key_arith nKG_le (ph_keyGenP_conf.1.trans keyGT_conf) (ph_keyGenP_conf.2.trans keyBL_conf)

end AdvancedEncryption.DualUse.Prog
