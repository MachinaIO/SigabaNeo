import PE.Impl.DualUse.Prog.KeyTightGen
import PE.Impl.DualUse.Prog.KeyCostConf

/-!
# The clock of `KeyGen` at `confP`, per tape

`time_keyMachineP_conf` (`PE.Impl.DualUse.Prog.KeyCostConf`) bounds the clock of `KeyGen` at the
concrete parameters by `2^4200`: the real key try is charged the uniform bound
`tbC · (2M + 1)^tbD` (`tbD = 8`, `M ≈ 2^251`), the row loop of the crafted data `X⁴`, the gadget and
addition of the read-back `375 M⁴`. With every loop charged its own counter (`ph_keyGenP_v`):

* the key try takes at most `coinT T m + (2T + 3) · wKR(ρK)` steps, `T ≈ 2^250` the longest word
  around it and `wKR(ρK) ≤ 2^285` its sweeps (`pEval_wKR_conf`, checked by evaluation), at most
  `2^538`;
* the `W_f` block keeps its bound `2^556` (`wfCost_wfB2`);
* **`time_keyMachineP_conf'`**: the clock of `KeyGen` is at most `2^557`. The bound is dominated by
  the `W_f` block (`2^556`); all the rest together is below `2^539`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg
open SigabaNeo.Tape.Prog (leP unfrP frP leT unfrT frT tailsP)
open AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord
open SigabaNeo.Lattices.Algo
open AdvancedEncryption.DualUse.Params

/-! ### The envelope -/

/-- The whole clock with numbers: `n` the input bound, `FL` the front end's output bound, `L` the
predicate bound, `LC` the look-up count, `P` the public key, `R = 2kNK`, `sW`, `pW` the constant
words, `dl` the dummy key, `Tb` the key-row block, `G` its output bound, `tm` the coins, `KT` the
key try's deterministic part. -/
def keyTotV (n FL L LC P R sW pW dl Tb G tm KT : ℕ) : ℕ :=
  let Mβ := max (8 * (n + 2)) FL
  let T := G + 1 + P + 1 + R
  let winT := prefT P G + etT (P + R) P R (G + 1 + P) + (sW + 1) * (2 * (T + sW + 1) + 3) +
    (pW + 1) * (2 * (T + pW + 1) + 3) + 24 * ((2 * T + 1) * (4 * T + 12)) + (coinT T tm + KT) +
    frT T + (31 * (2 * (3 * T + 1 + 1) + 3) + (2 * (3 * T + 1 + 1) + 3))
  let dD := Mβ + 1 + P + dl + 1
  let dT := (2 * (Mβ + 1) + 3) + prefT P Mβ + putT dl (Mβ + 1 + P) + (2 * (dD + 1) + 3) +
    (2 * (dD + 1 + 1) + 3)
  let BT := max ((2 * (Mβ + 1) + 3) + (Tb + winT)) (max (longT Mβ) (dT + frT (dD + 1)) + 1) + 1
  let BL := max (3 * T + 1) (max Mβ (3 * (dD + 1) + 1))
  2 * (n + 1) + 2 + (leT n (n + 1) + (max (2 * (n + 2 + 1) + 3)
    (parseT (n + 2) + (frontTv L LC (8 * (n + 2)) + (BT + (256 * (2 * (BL + 1) + 3) +
      (2 * (BL + 1) + 3))))) + 1)) + (2 * BL + 2)

section Gen

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

theorem keyTot_eq (W : ℕ) (cf : KeyCfg) (Tb Gb : ℕ) :
    2 * (nKG hk c + 1) + 2 + keyGTv' hk c W cf Tb Gb + (2 * keyBLv' hk c W cf Gb + 2) =
      keyTotV (nKG hk c) (frontL c.L W) c.L (Prog.lookCount (frontTbl c.L W) [false]) (lenPK hk c)
        (2 * k * (N * K)) cf.sW.length (powW K (cf.B - 1)).length
        ((keyEnc (N := N) (K := K) c).enc (dummyKey c)).length Tb Gb cf.m
        ((2 * winTop hk c Gb + 3) * Sym.pEval (ρK hk c Gb cf) KeyV.wKR) := rfl

end Gen

theorem keyTotV_mono {n FL L LC P R sW pW dl Tb G tm KT n' FL' L' LC' P' R' sW' pW' dl' Tb' G' tm' KT' : ℕ}
    (h1 : n ≤ n') (h2 : FL ≤ FL') (h3 : L ≤ L') (h4 : LC ≤ LC') (h5 : P ≤ P') (h6 : R ≤ R')
    (h7 : sW ≤ sW') (h8 : pW ≤ pW') (h9 : dl ≤ dl') (h10 : Tb ≤ Tb') (h11 : G ≤ G') (h12 : tm ≤ tm')
    (h13 : KT ≤ KT') :
    keyTotV n FL L LC P R sW pW dl Tb G tm KT ≤ keyTotV n' FL' L' LC' P' R' sW' pW' dl' Tb' G' tm' KT' := by
  simp only [keyTotV, frontTv, prefT, etT, putT, frT, leT, parseT, unfrT, longT, coinT]
  gcongr

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 5000 in
theorem keyTotV_conf : keyTotV (2 ^ 178) (2 ^ 232) (2 ^ 20) (2 ^ 231) (2 ^ 175) (2 ^ 87) (2 ^ 25)
    (2 ^ 25) (2 ^ 130) (2 ^ 556 + 2 ^ 510) (2 ^ 251) (2 ^ 120) (2 ^ 538) ≤ 2 ^ 557 := by
  simp only [keyTotV, frontTv, prefT, etT, putT, frT, leT, parseT, unfrT, longT, coinT]
  norm_num

/-! ### The read-back and the crafted data at `confP` -/

/-- `postTV` with the templates bounded uniformly and the sweeps of the gadget and the addition
bounded by `W`. -/
def postTVv (L LT oW Zr G W : ℕ) : ℕ :=
  getT 0 L G + getT oW LT (G + 1 + L) + (2 * (G + 1 + L + 1 + LT + 1) + 3) +
    prefT L (G + 1 + L + 1 + LT) + prefT LT (G + 1 + L + 1 + LT + 1 + L) +
    (Zr + 1) * (2 * (postMd L LT G + 1) + 3) +
    7 * ((2 * postMd L LT G + 1) * (4 * postMd L LT G + 12)) +
    (2 * postMd L LT G + 3) * W +
    (2 * (postMd L LT G + 1) + 3) + (52 * (2 * (postMd L LT G + 1) + 3) + (2 * (postMd L LT G + 1) + 3))

theorem postTV_le (L LT oW Zr N K k G W : ℕ) (hT : ∀ x ∈ postTmpl N K k, x.2 ≤ postMd L LT G)
    (hW : Sym.pEval (ρP (postMd L LT G) N K k) PostV.wG +
      Sym.pEval (ρP (postMd L LT G) N K k) PostV.wA ≤ W) :
    postTV L LT oW Zr N K k G ≤ postTVv L LT oW Zr G W := by
  have h1 := tmplTT_le (53 : Fin 54) (postMd L LT G) (postTmpl N K k) (fun _ => postMd L LT G)
    (fun _ => le_rfl) hT
  have hl : (postTmpl N K k).length = 6 := rfl
  rw [hl] at h1
  have h2 := Nat.mul_le_mul_left (2 * postMd L LT G + 3) hW
  rw [Nat.mul_add] at h2
  unfold postTV postTVv
  omega

/-- The bound of the tapes after the key-row block at `confP`. -/
noncomputable abbrev Gc : ℕ := postMd (lenPK hkp confP) (lenT Np Kp kp) (2 ^ 250)

theorem Gc_eq : Gc = 2 ^ 250 + 1 + 29931556208626396671394777597180314650064272740057088 + 1 +
    (2 * (2 ^ 25 + 1) * (2 ^ 34 * 2 ^ 25) + 2 ^ 34 * 2 ^ 25) + 1 +
    29931556208626396671394777597180314650064272740057088 + 1 +
    (2 * (2 ^ 25 + 1) * (2 ^ 34 * 2 ^ 25) + 2 ^ 34 * 2 ^ 25) := by
  simp only [Gc, postMd]; rw [lenPK_eq, lenT_conf]

theorem ρP_conf : ρP Gc Np Kp kp = [2 ^ 250 + 1 + 29931556208626396671394777597180314650064272740057088 + 1 +
    (2 * (2 ^ 25 + 1) * (2 ^ 34 * 2 ^ 25) + 2 ^ 34 * 2 ^ 25) + 1 +
    29931556208626396671394777597180314650064272740057088 + 1 +
    (2 * (2 ^ 25 + 1) * (2 ^ 34 * 2 ^ 25) + 2 ^ 34 * 2 ^ 25), 2 ^ 34, 2 ^ 25, 2 ^ 25 + 1] := by
  rw [ρP, Gc_eq, Np_def, Kp_def, kp_eq]

theorem pEval_post_conf : Sym.pEval (ρP Gc Np Kp kp) PostV.wG + Sym.pEval (ρP Gc Np Kp kp) PostV.wA ≤
    2 ^ 101 := by
  rw [ρP_conf]; decide +kernel

theorem postTmpl_Gc : ∀ x ∈ postTmpl Np Kp kp, x.2 ≤ Gc := fun x hx =>
  (postTmpl_conf x hx).trans (by simp only [Gc, postMd]; have : (2 : ℕ) ^ 87 ≤ 2 ^ 250 := by norm_num
                                 omega)

set_option exponentiation.threshold 2000 in
theorem postTV_conf : postTV (lenPK hkp confP) (lenT Np Kp kp) (offWk hkp confP) (lenZ confP) Np Kp kp
    (2 ^ 250) ≤ 2 ^ 507 := by
  refine (postTV_le _ _ _ _ _ _ _ _ _ postTmpl_Gc pEval_post_conf).trans ?_
  rw [offWk_conf, lenZ_conf, lenT_conf, lenPK_eq]
  simp only [postTVv, postMd, getT, prefT]
  norm_num

set_option exponentiation.threshold 2000 in
theorem preTV_conf : preTV (2 ^ 241) (nJ (N := Np) (K := Kp) hkp) (lenZ confP + DualUse.rowL Np Kp kp) ≤
    2 ^ 491 := by
  rw [nJ_conf, lenZ_conf, rowL_conf]
  simp only [preTV, wTV, getT, prefT]
  norm_num

/-! ### The key-row block at `confP`, per tape -/

set_option maxRecDepth 100000 in
theorem ph_bfX_conf_v {a M : ℕ} (ha : a ≤ 2 ^ 182) {β : Fin 256 → ℕ} (h0 : β 0 ≤ a)
    (h1 : β 1 ≤ frontL confP.L WB2.Wc) (hβ : ∀ i, β i ≤ M) :
    Ph (bfX hkp confP (wfB2 hkp confP WB2.Wc)) β
      (256 * (2 * (M + 1) + 3) + (2 * (M + 1) + 3) +
        (preTV (2 ^ 241) (nJ (N := Np) (K := Kp) hkp) (lenZ confP + DualUse.rowL Np Kp kp) + (2 ^ 556 +
          postTV (lenPK hkp confP) (lenT Np Kp kp) (offWk hkp confP) (lenZ confP) Np Kp kp (2 ^ 250))))
      (v02 Gc) := by
  refine ph_bfX_v (hk := hkp) (c := confP) (wfB := wfB2 hkp confP WB2.Wc) (Lw := 2 ^ 240)
    (LF := frontL confP.L WB2.Wc) (Tw := 2 ^ 556) (Gw := 2 ^ 250) (a := a) (Mβ := M) (X := 2 ^ 241)
    wfCost_wfB2.time wfCost_wfB2.len (wfB2_clear hkp confP WB2.Wc) ?_ ?_ ?_ ?_ ?_ ?_ postTmpl_Gc h0 h1 hβ
  · refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left (Nat.sub_le _ _) _) 10) ?_
    rw [lenT_conf, nJ_conf, rowL_conf, dNK_conf, lenZ_conf, confP_d, lenPK_eq]
    omega
  · rw [offBk_conf]; norm_num
  · rw [rowL_conf, confP_d]; norm_num
  · rw [rowL_conf]; norm_num
  · rw [nJ_conf]; norm_num
  · rw [nJ_conf, rowL_conf, dNK_conf, lenZ_conf, confP_d, lenPK_eq]
    omega

/-! ### The key try at `confP` -/

theorem cfP_B : cfP.B = 16041444 := by show Bp = _; rw [Bp_def]

theorem cfP_m : cfP.m = (2 ^ 61 + (1 + (2 * (2 ^ 25 + 1) + 2 * (2 ^ 25 + 1)))) * 2 ^ 34 * 16041444 := by
  show mBp = _; rw [mBp, dp_def, kp_eq, Np_def, Bp_def]

theorem ρK_conf : ρK hkp confP Gc cfP = [(2 ^ 250 + 1 + 29931556208626396671394777597180314650064272740057088 + 1 + (2 * (2 ^ 25 + 1) * (2 ^ 34 * 2 ^ 25) + 2 ^ 34 * 2 ^ 25) + 1 + 29931556208626396671394777597180314650064272740057088 + 1 + (2 * (2 ^ 25 + 1) * (2 ^ 34 * 2 ^ 25) + 2 ^ 34 * 2 ^ 25)) + 1 + 29931556208626396671394777597180314650064272740057088 + 1 + 2 * (2 ^ 25 + 1) * (2 ^ 34 * 2 ^ 25),
    2 ^ 34, 2 ^ 25, 2 ^ 25 + 1, 2 ^ 61, 1 + (2 * (2 ^ 25 + 1) + 2 * (2 ^ 25 + 1)), 29931556208626396671394777597180314650064272740057088, 16041444,
    (2 ^ 61 + (1 + (2 * (2 ^ 25 + 1) + 2 * (2 ^ 25 + 1)))) * 2 ^ 34 * 16041444] := by
  simp only [ρK, winTop, AdvancedEncryption.DualUse.Algo.nT]
  rw [Gc_eq, lenPK_eq, confP_d, cfP_B, cfP_m, Np_def, Kp_def, kp_eq]

set_option maxRecDepth 100000 in
/-- **The sweeps of the key try at `confP`**, checked by evaluation. -/
theorem pEval_wKR_conf : Sym.pEval (ρK hkp confP Gc cfP) KeyV.wKR ≤ 2 ^ 285 := by
  rw [ρK_conf]; decide +kernel

theorem winTop_conf : winTop hkp confP Gc ≤ 2 ^ 251 := by
  simp only [winTop]; rw [Gc_eq, lenPK_eq, kp_eq, Np_def, Kp_def]; norm_num

set_option exponentiation.threshold 2000 in
theorem KT_conf : (2 * winTop hkp confP Gc + 3) * Sym.pEval (ρK hkp confP Gc cfP) KeyV.wKR ≤ 2 ^ 538 := by
  have h1 := winTop_conf
  have h2 := pEval_wKR_conf
  calc _ ≤ (2 * 2 ^ 251 + 3) * 2 ^ 285 := Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 2 h1) 3) h2
    _ ≤ 2 ^ 538 := by norm_num

theorem Gc_le : Gc ≤ 2 ^ 251 := by rw [Gc_eq]; norm_num

theorem mBp_le : cfP.m ≤ 2 ^ 120 := by rw [cfP_m]; norm_num

theorem winTop_ge : 2 ^ 250 ≤ winTop hkp confP Gc := by
  simp only [winTop, Gc, postMd]; omega

/-! ### The clock -/

/-- The time of the key-row block at `confP`, per tape. -/
local notation "TbV" => 256 * (2 * (max (8 * (nKG hkp confP + 2)) (frontL confP.L WB2.Wc) + 1) + 3) +
  (2 * (max (8 * (nKG hkp confP + 2)) (frontL confP.L WB2.Wc) + 1) + 3) +
  (preTV (2 ^ 241) (nJ (N := Np) (K := Kp) hkp) (lenZ confP + DualUse.rowL Np Kp kp) + (2 ^ 556 +
    postTV (lenPK hkp confP) (lenT Np Kp kp) (offWk hkp confP) (lenZ confP) Np Kp kp (2 ^ 250)))

set_option exponentiation.threshold 1000 in
theorem TbV_le : TbV ≤ 2 ^ 556 + 2 ^ 510 := by
  have h1 : max (8 * (nKG hkp confP + 2)) (frontL confP.L WB2.Wc) ≤ 2 ^ 232 :=
    max_le (aK_le.trans (by norm_num)) frontL_Wc
  have h2 := preTV_conf
  have h3 := postTV_conf
  generalize max (8 * (nKG hkp confP + 2)) (frontL confP.L WB2.Wc) = M at *
  generalize preTV (2 ^ 241) (nJ (N := Np) (K := Kp) hkp) (lenZ confP + DualUse.rowL Np Kp kp) = A at *
  generalize postTV (lenPK hkp confP) (lenT Np Kp kp) (offWk hkp confP) (lenZ confP) Np Kp kp
    (2 ^ 250) = B at *
  have : (2 : ℕ) ^ 510 = 2 ^ 232 * 2 ^ 278 := by norm_num
  have : (2 : ℕ) ^ 491 ≤ 2 ^ 508 := by norm_num
  have : (2 : ℕ) ^ 507 ≤ 2 ^ 508 := by norm_num
  have : (2 : ℕ) ^ 510 = 2 ^ 508 + 2 ^ 508 + 2 ^ 509 := by norm_num
  have : 2 ^ 232 * 1000 ≤ (2 : ℕ) ^ 508 := by norm_num
  omega

theorem keyTmplR_Gc : ∀ x ∈ keyTmplR hkp confP cfP, x.2 ≤ winTop hkp confP Gc := fun x hx =>
  (le_tmplMax _ x hx).trans (keyTmplR_conf winTop_ge)

/-- **The clock of `KeyGen` at `confP`, every loop charged its own counter.** The bound is
dominated by the `W_f` block (`2^556`, `wfCost_wfB2`); the key try costs at most `2^538`. -/
theorem time_keyMachineP_conf' :
    (keyMachineP hkp confP (bfX hkp confP (wfB2 hkp confP WB2.Wc)) WB2.Wc cfP).time ≤ 2 ^ 557 := by
  rw [time_keyMachineP]
  obtain ⟨h1, h2⟩ := ph_keyGenP_v (hk := hkp) (c := confP) (bfX hkp confP (wfB2 hkp confP WB2.Wc))
    WB2.Wc cfP (Tb := TbV) (Gb := Gc)
    (fun _ h0 h1 hβ => ph_bfX_conf_v (a := 8 * (nKG hkp confP + 2))
      (M := max (8 * (nKG hkp confP + 2)) (frontL confP.L WB2.Wc)) aK_le h0 h1 hβ)
    (le_of_eq (by rw [length_sW_cfP, Kp_def])) (le_of_eq (by rw [length_powW_cfP, Kp_def]))
    (Kp_def.le.trans ((by norm_num : (2 : ℕ) ^ 25 ≤ 2 ^ 250).trans winTop_ge)) keyTmplR_Gc
  calc _ ≤ 2 * (nKG hkp confP + 1) + 2 + keyGTv' hkp confP WB2.Wc cfP TbV Gc +
        (2 * keyBLv' hkp confP WB2.Wc cfP Gc + 2) := by omega
    _ = _ := keyTot_eq hkp confP WB2.Wc cfP TbV Gc
    _ ≤ keyTotV (2 ^ 178) (2 ^ 232) (2 ^ 20) (2 ^ 231) (2 ^ 175) (2 ^ 87) (2 ^ 25) (2 ^ 25) (2 ^ 130)
        (2 ^ 556 + 2 ^ 510) (2 ^ 251) (2 ^ 120) (2 ^ 538) :=
      keyTotV_mono nKG_le frontL_Wc confP_L_le (lookCount_conf Wc_ge Wc_le) lenPK_le rK_le
        (le_of_eq length_sW_cfP) (le_of_eq length_powW_cfP) lenDummy_le TbV_le Gc_le mBp_le KT_conf
    _ ≤ 2 ^ 557 := keyTotV_conf

end AdvancedEncryption.DualUse.Prog
