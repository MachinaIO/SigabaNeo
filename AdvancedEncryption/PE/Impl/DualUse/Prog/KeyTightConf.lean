import PE.Impl.DualUse.Prog.KeyTightGen
import PE.Impl.DualUse.Prog.WfCConf

/-!
# The clock of `KeyGen` at `confA`, per tape

The machine of `KeyGen` of `implC` is `keyMachineP hkp confP bfC cfP`: the shell with the front end
`frontBP confP.L` (`ShellsBP`), the key-row block `bfC = bfX hkp confP wfC` around the stream block
`wfC` (`ImplBP`), the key try of `cfP`. With every loop charged its own counter (`ph_keyGenF_v`):

* the front end takes at most `2^8 X^2 ≤ 2^404` steps (`frontBTn_le`, `X = 2^198`), its output at
  most `frontBA bpLen ≤ 2^63` bits;
* the key-row block: the stream block `2^628` (`time_wfC`), the crafted data `≤ 2^521`
  (`preTV_conf`), the read-back `≤ 2^530` (`postTV_conf`, the gadget branch's sweeps `≤ 2^97`
  checked by evaluation); afterwards only tapes `0`, `2` are nonblank, below `Gc ≈ 2^262`;
* the key try takes at most `coinT T m + (2T + 3) · wKR(ρK)` steps, `T = winTop Gc ≈ 2^262` and
  `wKR(ρK) ≤ 2^293` (`pEval_wKR_conf`, checked by evaluation), at most `2^559`;
* **`time_keyMachineP_conf'`**: the clock of `KeyGen` is at most **`2^629`**, dominated by the
  stream block.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg
open SigabaNeo.Tape.Prog (leP unfrP frP leT unfrT frT tailsP)
open AdvancedEncryption.PE.Gates.BPWord
open SigabaNeo.Lattices.Algo
open AdvancedEncryption.DualUse.Params
open AdvancedEncryption.DualUse.Sub

set_option exponentiation.threshold 3000

/-! ### The envelope -/

/-- The whole clock with numbers: `n` the input bound, `FL` the front end's output bound, `FT` its
time, `P` the public key, `R = 2kNK`, `sW`, `pW` the constant words, `dl` the dummy key, `Tb` the
key-row block, `G` its output bound, `tm` the coins, `KT` the key try's deterministic part. -/
def keyTotV (n FL FT P R sW pW dl Tb G tm KT : ℕ) : ℕ :=
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
    (parseT (n + 2) + (FT + (BT + (256 * (2 * (BL + 1) + 3) +
      (2 * (BL + 1) + 3))))) + 1)) + (2 * BL + 2)

section Gen

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

theorem keyTot_eq (FT FL : ℕ) (cf : KeyCfg) (Tb Gb : ℕ) :
    2 * (nKG hk c + 1) + 2 + keyGTFv hk c FT FL cf Tb Gb + (2 * keyBLFv hk c FL cf Gb + 2) =
      keyTotV (nKG hk c) FL FT (lenPK hk c) (2 * k * (N * K)) cf.sW.length
        (powW K (cf.B - 1)).length ((keyEnc (N := N) (K := K) c).enc (dummyKey c)).length Tb Gb cf.m
        ((2 * winTop hk c Gb + 3) * Sym.pEval (ρK hk c Gb cf) KeyV.wKR) := rfl

end Gen

theorem keyTotV_mono {n FL FT P R sW pW dl Tb G tm KT n' FL' FT' P' R' sW' pW' dl' Tb' G' tm' KT' : ℕ}
    (h1 : n ≤ n') (h2 : FL ≤ FL') (h3 : FT ≤ FT') (h5 : P ≤ P') (h6 : R ≤ R')
    (h7 : sW ≤ sW') (h8 : pW ≤ pW') (h9 : dl ≤ dl') (h10 : Tb ≤ Tb') (h11 : G ≤ G') (h12 : tm ≤ tm')
    (h13 : KT ≤ KT') :
    keyTotV n FL FT P R sW pW dl Tb G tm KT ≤ keyTotV n' FL' FT' P' R' sW' pW' dl' Tb' G' tm' KT' := by
  simp only [keyTotV, prefT, etT, putT, frT, leT, parseT, unfrT, longT, coinT]
  gcongr

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 5000 in
theorem keyTotV_conf : keyTotV (2 ^ 193) (2 ^ 63) (2 ^ 404) (2 ^ 191) (2 ^ 92) (2 ^ 27)
    (2 ^ 27) (2 ^ 129) (2 ^ 628 + 2 ^ 531) (2 ^ 263) (2 ^ 130) (2 ^ 559) ≤ 2 ^ 629 := by
  simp only [keyTotV, prefT, etT, putT, frT, leT, parseT, unfrT, longT, coinT]
  norm_num

/-! ### The front end at `confA` -/

theorem frontBA_conf : frontBA bpLen ≤ 2 ^ 63 := frontBA_le bpLen_le

theorem frontBTn_conf : frontBTn confP.L bpLen (8 * (nKG hkp confP + 2)) ≤ 2 ^ 404 := by
  have h := frontBTn_le (n := confP.L) (m := bpLen) (T := 8 * (nKG hkp confP + 2)) (X := 2 ^ 198)
    le_rfl bpLen_le (confP_L_le.trans (by norm_num)) (by have := aK_le; omega) (by norm_num)
  exact h.trans (by norm_num)

/-! ### The read-back and the crafted data at `confA` -/

/-- `postTV` with the templates bounded uniformly and the sweeps of the gadget branch bounded by
`W`. -/
def postTVv (L LT oW Zr G W : ℕ) : ℕ :=
  getT 0 L G + getT oW LT (G + 1 + L) + getT (oW + LT) 1 (G + 1 + L + 1 + LT) +
    (2 * (G + 1 + L + 1 + LT + 1 + 1 + 1) + 3) +
    prefT L (G + 1 + L + 1 + LT + 1 + 1) + prefT LT (G + 1 + L + 1 + LT + 1 + 1 + 1 + L) +
    (Zr + 1) * (2 * (postMd L LT G + 1) + 3) +
    7 * ((2 * postMd L LT G + 1) * (4 * postMd L LT G + 12)) +
    ((2 * postMd L LT G + 3) * W + (2 * (postMd L LT G + 1) + 3) + 1) +
    (53 * (2 * (postMd L LT G + 1) + 3) + (2 * (postMd L LT G + 1) + 3))

theorem postTV_le (L LT oW Zr N K k G W : ℕ) (hT : ∀ x ∈ postTmpl N K k, x.2 ≤ postMd L LT G)
    (hW : Sym.pEval (ρP (postMd L LT G) N K k) PostV.wGA ≤ W) :
    postTV L LT oW Zr N K k G ≤ postTVv L LT oW Zr G W := by
  have h1 := tmplTT_le (53 : Fin 55) (postMd L LT G) (postTmpl N K k) (fun _ => postMd L LT G)
    (fun _ => le_rfl) hT
  have hl : (postTmpl N K k).length = 6 := rfl
  rw [hl] at h1
  have h2 := Nat.mul_le_mul_left (2 * postMd L LT G + 3) hW
  unfold postTV postTVv
  omega

theorem postTVv_mono {L LT oW Zr G W L' LT' oW' Zr' G' W' : ℕ} (h1 : L ≤ L') (h2 : LT ≤ LT')
    (h3 : oW ≤ oW') (h4 : Zr ≤ Zr') (h5 : G ≤ G') (h6 : W ≤ W') :
    postTVv L LT oW Zr G W ≤ postTVv L' LT' oW' Zr' G' W' := by
  simp only [postTVv, postMd, getT, prefT]
  gcongr

/-- The bound of the tapes after the key-row block at `confA`. -/
noncomputable abbrev Gc : ℕ := postMd (lenPK hkp confP) (lenT Np Kp kp) (2 ^ 262)

theorem Gc_eq : Gc = 2 ^ 262 + 1 + 1569275468922709748577758203934090069617389767520910573568 + 1 +
    (2 * (2 ^ 27 + 1) * (2 ^ 36 * 2 ^ 27) + 2 ^ 36 * 2 ^ 27) + 1 + 1 + 1 +
    1569275468922709748577758203934090069617389767520910573568 + 1 +
    (2 * (2 ^ 27 + 1) * (2 ^ 36 * 2 ^ 27) + 2 ^ 36 * 2 ^ 27) := by
  simp only [Gc, postMd]; rw [lenPK_eq, lenT_conf]

theorem ρP_conf : ρP Gc Np Kp kp = [2 ^ 262 + 1 + 1569275468922709748577758203934090069617389767520910573568 + 1 +
    (2 * (2 ^ 27 + 1) * (2 ^ 36 * 2 ^ 27) + 2 ^ 36 * 2 ^ 27) + 1 + 1 + 1 +
    1569275468922709748577758203934090069617389767520910573568 + 1 +
    (2 * (2 ^ 27 + 1) * (2 ^ 36 * 2 ^ 27) + 2 ^ 36 * 2 ^ 27), 2 ^ 36, 2 ^ 27, 2 ^ 27 + 1] := by
  rw [ρP, Gc_eq, Np_def, Kp_def, kp_eq]

set_option maxRecDepth 100000 in
/-- **The sweeps of the gadget branch at `confA`**, checked by evaluation. -/
theorem pEval_post_conf : Sym.pEval (ρP Gc Np Kp kp) PostV.wGA ≤ 2 ^ 97 := by
  rw [ρP_conf]; decide +kernel

theorem Gc_le : Gc ≤ 2 ^ 263 := by rw [Gc_eq]; norm_num

theorem postTmpl_Gc : ∀ x ∈ postTmpl Np Kp kp, x.2 ≤ Gc := fun x hx =>
  (postTmpl_conf x hx).trans (by simp only [Gc, postMd]; have : (2 : ℕ) ^ 92 ≤ 2 ^ 262 := by norm_num
                                 omega)

set_option exponentiation.threshold 2000 in
theorem postTVv_conf : postTVv (2 ^ 191) (2 ^ 92) (2 ^ 191) (2 ^ 157) (2 ^ 262) (2 ^ 97) ≤ 2 ^ 530 := by
  simp only [postTVv, postMd, getT, prefT]
  norm_num

theorem postTV_conf : postTV (lenPK hkp confP) (lenT Np Kp kp) (offWk hkp confP) (lenZ confP) Np Kp kp
    (2 ^ 262) ≤ 2 ^ 530 :=
  ((postTV_le _ _ _ _ _ _ _ _ _ postTmpl_Gc pEval_post_conf).trans
    (postTVv_mono lenPK_le lenTc_le offWk_le lenZ_le le_rfl le_rfl)).trans postTVv_conf

theorem preTV_mono {X n Z X' n' Z' : ℕ} (h1 : X ≤ X') (h2 : n ≤ n') (h3 : Z ≤ Z') :
    preTV X n Z ≤ preTV X' n' Z' := by
  simp only [preTV, wTV, getT, prefT]
  gcongr

set_option exponentiation.threshold 2000 in
theorem preTV_num : preTV (2 ^ 256) (2 ^ 100) (2 ^ 157 + 2 ^ 92) ≤ 2 ^ 521 := by
  simp only [preTV, wTV, getT, prefT]
  norm_num

theorem preTV_conf : preTV (2 ^ 256) (nJ (N := Np) (K := Kp) hkp) (lenZ confP + DualUse.rowL Np Kp kp) ≤
    2 ^ 521 :=
  (preTV_mono le_rfl nJ_le (Nat.add_le_add lenZ_le (by rw [rowL_conf]; norm_num))).trans preTV_num

/-! ### The key-row block at `confA`, per tape -/

set_option maxRecDepth 100000 in
theorem ph_bfC_v {a M : ℕ} (ha : a ≤ 2 ^ 197) {β : Fin 256 → ℕ} (h0 : β 0 ≤ a)
    (h1 : β 1 ≤ frontBA bpLen) (hβ : ∀ i, β i ≤ M) :
    Ph bfC β
      (256 * (2 * (M + 1) + 3) + (2 * (M + 1) + 3) + (mvBitT a (frontBA bpLen) +
        (preTV (2 ^ 256) (nJ (N := Np) (K := Kp) hkp) (lenZ confP + DualUse.rowL Np Kp kp) + (2 ^ 628 +
          postTV (lenPK hkp confP) (lenT Np Kp kp) (offWk hkp confP) (lenZ confP) Np Kp kp (2 ^ 262)))))
      (v02 Gc) := by
  have hA := frontBA_conf
  have hn : nA = 128 := rfl
  refine ph_bfX_v (hk := hkp) (c := confP) (wfB := wfC) (Lw := 2 ^ 260)
    (LF := frontBA bpLen) (Tw := 2 ^ 628) (Gw := 2 ^ 262) (a := a) (Mβ := M) (X := 2 ^ 256)
    (time_wfC le_rfl (hA.trans (by norm_num))).1 (time_wfC le_rfl (hA.trans (by norm_num))).2
    (wfB2S_clear hkp confP _ _) ?_ ?_ ?_ ?_ ?_ ?_ postTmpl_Gc h0 h1 hβ
  · refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left (Nat.sub_le _ _) _) _) ?_
    rw [lenT_conf, nJ_conf, rowL_conf, dNK_conf, lenZ_conf, confP_d, lenPK_eq, hn]
    omega
  · exact offBk_le.trans (by norm_num)
  · rw [rowL_conf, confP_d, hn]; norm_num
  · rw [rowL_conf, hn]; norm_num
  · exact nJ_le.trans (by norm_num)
  · rw [nJ_conf, rowL_conf, dNK_conf, lenZ_conf, confP_d, lenPK_eq, hn]
    omega

/-! ### The key try at `confA` -/

theorem cfP_B : cfP.B = 51056224 := by show Bp = _; rw [Bp_def]

theorem cfP_m : cfP.m = (2 ^ 65 + (1 + (2 * (2 ^ 27 + 1) + 2 * (2 ^ 27 + 1)))) * 2 ^ 36 * 51056224 := by
  show mBp = _; rw [mBp, dp_def, kp_eq, Np_def, Bp_def]

theorem ρK_conf : ρK hkp confP Gc cfP =
    [(2 ^ 262 + 1 + 1569275468922709748577758203934090069617389767520910573568 + 1 +
      (2 * (2 ^ 27 + 1) * (2 ^ 36 * 2 ^ 27) + 2 ^ 36 * 2 ^ 27) + 1 + 1 + 1 +
      1569275468922709748577758203934090069617389767520910573568 + 1 +
      (2 * (2 ^ 27 + 1) * (2 ^ 36 * 2 ^ 27) + 2 ^ 36 * 2 ^ 27)) + 1 +
      1569275468922709748577758203934090069617389767520910573568 + 1 +
      2 * (2 ^ 27 + 1) * (2 ^ 36 * 2 ^ 27),
    2 ^ 36, 2 ^ 27, 2 ^ 27 + 1, 2 ^ 65, 1 + (2 * (2 ^ 27 + 1) + 2 * (2 ^ 27 + 1)),
    1569275468922709748577758203934090069617389767520910573568, 51056224,
    (2 ^ 65 + (1 + (2 * (2 ^ 27 + 1) + 2 * (2 ^ 27 + 1)))) * 2 ^ 36 * 51056224] := by
  simp only [ρK, winTop, AdvancedEncryption.DualUse.Algo.nT]
  rw [Gc_eq, lenPK_eq, confP_d, cfP_B, cfP_m, Np_def, Kp_def, kp_eq]

set_option maxRecDepth 100000 in
/-- **The sweeps of the key try at `confA`**, checked by evaluation. -/
theorem pEval_wKR_conf : Sym.pEval (ρK hkp confP Gc cfP) KeyV.wKR ≤ 2 ^ 293 := by
  rw [ρK_conf]; decide +kernel

theorem winTop_conf : winTop hkp confP Gc ≤ 2 ^ 264 := by
  simp only [winTop]; rw [Gc_eq, lenPK_eq, kp_eq, Np_def, Kp_def]; norm_num

set_option exponentiation.threshold 2000 in
theorem KT_conf : (2 * winTop hkp confP Gc + 3) * Sym.pEval (ρK hkp confP Gc cfP) KeyV.wKR ≤ 2 ^ 559 := by
  have h1 := winTop_conf
  have h2 := pEval_wKR_conf
  calc _ ≤ (2 * 2 ^ 264 + 3) * 2 ^ 293 := Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 2 h1) 3) h2
    _ ≤ 2 ^ 559 := by norm_num

theorem winTop_ge : 2 ^ 262 ≤ winTop hkp confP Gc := by
  simp only [winTop, Gc, postMd]; omega

/-! ### The clock -/

/-- The time of the key-row block at `confA`, per tape. -/
local notation "TbV" => 256 * (2 * (max (8 * (nKG hkp confP + 2)) (frontBA bpLen) + 1) + 3) +
  (2 * (max (8 * (nKG hkp confP + 2)) (frontBA bpLen) + 1) + 3) +
  (mvBitT (8 * (nKG hkp confP + 2)) (frontBA bpLen) +
  (preTV (2 ^ 256) (nJ (N := Np) (K := Kp) hkp) (lenZ confP + DualUse.rowL Np Kp kp) + (2 ^ 628 +
    postTV (lenPK hkp confP) (lenT Np Kp kp) (offWk hkp confP) (lenZ confP) Np Kp kp (2 ^ 262))))

theorem tbV_arith {a F A B : ℕ} (ha : a ≤ 2 ^ 197) (hF : F ≤ 2 ^ 63) (hA : A ≤ 2 ^ 521)
    (hB : B ≤ 2 ^ 530) :
    256 * (2 * (max a F + 1) + 3) + (2 * (max a F + 1) + 3) + (mvBitT a F + (A + (2 ^ 628 + B))) ≤
      2 ^ 628 + 2 ^ 531 := by
  have hM : max a F ≤ 2 ^ 197 := max_le ha (hF.trans (by norm_num))
  unfold mvBitT
  have : (2 : ℕ) ^ 531 = 2 ^ 530 + 2 ^ 530 := by norm_num
  have : (2 : ℕ) ^ 521 ≤ 2 ^ 529 := by norm_num
  have : (2 : ℕ) ^ 530 = 2 ^ 529 + 2 ^ 529 := by norm_num
  have : 2 ^ 197 * 10000 ≤ (2 : ℕ) ^ 528 := by norm_num
  have : (2 : ℕ) ^ 529 = 2 ^ 528 + 2 ^ 528 := by norm_num
  omega

theorem TbV_le : TbV ≤ 2 ^ 628 + 2 ^ 531 :=
  tbV_arith aK_le frontBA_conf preTV_conf postTV_conf

theorem keyTmplR_Gc : ∀ x ∈ keyTmplR hkp confP cfP, x.2 ≤ winTop hkp confP Gc := fun x hx =>
  (le_tmplMax _ x hx).trans (keyTmplR_conf ((by norm_num : (2 : ℕ) ^ 192 ≤ 2 ^ 262).trans winTop_ge))

/-- **The clock of `KeyGen` at `confA`**, every loop charged its own counter: the machine of
`implC` (`msC.key`). The bound is dominated by the stream block (`2^628`, `time_wfC`); the key try
costs at most `2^559`, the crafted data `2^521`. -/
theorem time_keyMachineP_conf' : (keyMachineP hkp confP bfC cfP).time ≤ 2 ^ 629 := by
  rw [time_keyMachineP]
  obtain ⟨h1, h2⟩ : _ ∧ _ := ph_keyGenF_v (hk := hkp) (c := confP) frEmb_eF (by norm_num)
    (frontSpec_frontBP confP.L).ph bfC 512 cfP (Tb := TbV) (Gb := Gc)
    (fun _ h0 h1 hβ => ph_bfC_v (a := 8 * (nKG hkp confP + 2))
      (M := max (8 * (nKG hkp confP + 2)) (frontBA bpLen)) aK_le h0 h1 hβ)
    (le_of_eq (by rw [length_sW_cfP, Kp_def])) (le_of_eq (by rw [length_powW_cfP, Kp_def]))
    (Kp_def.le.trans ((by norm_num : (2 : ℕ) ^ 27 ≤ 2 ^ 262).trans winTop_ge)) keyTmplR_Gc
  calc _ ≤ 2 * (nKG hkp confP + 1) + 2 +
        keyGTFv hkp confP (frontBTn confP.L bpLen (8 * (nKG hkp confP + 2))) (frontBA bpLen) cfP TbV Gc +
        (2 * keyBLFv hkp confP (frontBA bpLen) cfP Gc + 2) := by
        have h1' : XProg.timeBoundT (keyGenP hkp confP bfC cfP)
            (Prog.inputBound (255 : Fin 256) (nKG hkp confP + 1)) ≤
            keyGTFv hkp confP (frontBTn confP.L bpLen (8 * (nKG hkp confP + 2))) (frontBA bpLen)
              cfP TbV Gc := h1
        have h2' : XProg.lenBoundT (keyGenP hkp confP bfC cfP)
            (Prog.inputBound (255 : Fin 256) (nKG hkp confP + 1)) 0 ≤
            keyBLFv hkp confP (frontBA bpLen) cfP Gc := h2
        generalize keyGTFv hkp confP (frontBTn confP.L bpLen (8 * (nKG hkp confP + 2)))
          (frontBA bpLen) cfP TbV Gc = A at *
        generalize keyBLFv hkp confP (frontBA bpLen) cfP Gc = B at *
        omega
    _ = _ := keyTot_eq hkp confP _ _ cfP TbV Gc
    _ ≤ keyTotV (2 ^ 193) (2 ^ 63) (2 ^ 404) (2 ^ 191) (2 ^ 92) (2 ^ 27) (2 ^ 27) (2 ^ 129)
        (2 ^ 628 + 2 ^ 531) (2 ^ 263) (2 ^ 130) (2 ^ 559) :=
      keyTotV_mono nKG_le frontBA_conf frontBTn_conf lenPK_le rK_le
        (le_of_eq length_sW_cfP) (le_of_eq length_powW_cfP) lenDummy_le TbV_le Gc_le mBp_le KT_conf
    _ ≤ 2 ^ 629 := keyTotV_conf

end AdvancedEncryption.DualUse.Prog

namespace AdvancedEncryption.DualUse.Sub

open AdvancedEncryption.DualUse.Prog

/-- **The clock of `KeyGen` of `implC`**: at most `2^629`. -/
theorem time_key_msC : msC.key.time ≤ 2 ^ 629 := time_keyMachineP_conf'

end AdvancedEncryption.DualUse.Sub
