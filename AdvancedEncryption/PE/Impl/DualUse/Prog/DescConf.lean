import PE.Impl.DualUse.Prog.DecCostConf
import PE.Impl.DualUse.Prog.SizeCost
import PE.Impl.DualUse.Prog.SizeConf
import PE.Impl.DualUse.Prog.SetupEncCost

/-!
# The description lengths at `confP`

Closed bounds of the description lengths of the four compiled machines at `confP`, from the state
counts of their programs (`size_setupP_conf`, `size_encP_conf`, `size_keyGenP`, `size_decGenP`, and
the state counts of the crafted-data blocks `size_bfX_le`, `size_cfX_le`).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.DualUse.Params
open AdvancedEncryption.PE.Gates.DateWindow
open SigabaNeo.Lattices.Algo

/-! ### Arithmetic -/

theorem descLen_arith {k S B : ℕ} (h : S ≤ B) :
    6 * S * 3 ^ k * 3 ^ 0 * Machine.entryBits k S 0 ≤ 6 * B * 3 ^ k * (4 + 4 * k + B) := by
  have hs : Nat.size S ≤ S := Nat.size_le.mpr (Nat.lt_two_pow_self)
  unfold Machine.entryBits
  simp only [pow_zero, mul_one, Nat.mul_zero, Nat.add_zero, Nat.size_zero]
  gcongr
  omega

/-! ### The crafted-data blocks -/

section Gen

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

theorem size_bfX_le (wfB : XProg 256) {X m : ℕ} (h1 : lenPK hk c ≤ X) (h2 : lenT N K k ≤ X)
    (h3 : offBk c ≤ X) (h4 : nJ (N := N) hk * DualUse.rowL N K k ≤ X) (h5 : offWk hk c ≤ X)
    (h6 : lenZ c ≤ X)
    (hpre : ∀ x ∈ preTmpl (lenZ c) (DualUse.rowL N K k) (nJ (N := N) hk) (c.d * (N * K))
      (10 * (c.d * DualUse.rowL N K k)) (10 * (2 * DualUse.rowL N K k)) (lenZ c - lenT N K k),
      x.2 < 2 ^ m)
    (hpost : ∀ x ∈ postTmpl N K k, x.2 < 2 ^ m) :
    (bfX hk c wfB).size ≤ 36 * 257 + (600 * X + 8 * (195 * m + 36) + 10000) + wfB.size +
      (1000 * X + 6 * (195 * m + 36) + 40000) := by
  have a := size_preCoreB (lenPK hk c) (lenT N K k) (offBk c) (nJ (N := N) hk * DualUse.rowL N K k)
    (lenZ c) (DualUse.rowL N K k) (nJ (N := N) hk) (c.d * (N * K))
    (10 * (c.d * DualUse.rowL N K k)) (10 * (2 * DualUse.rowL N K k)) (lenZ c - lenT N K k) X m
    h1 h2 h3 h4 hpre
  have b := size_postCoreB (lenPK hk c) (lenT N K k) (offWk hk c) (lenZ c) N K k X m h1 h2 h5 h6 hpost
  have c0 := size_clearL_le clr01
  have c1 := length_clr01_le
  simp only [bfX, preB, postB, size_seq, size_frame]
  omega

theorem size_cfX_le (wfB : XProg 256) {X m : ℕ} (h1 : lenPK hk c ≤ X) (h2 : lenKA hk c ≤ X)
    (h3 : lenPK hk c + lenKA hk c + lenCj (N := N) hk ≤ X) (h4 : N * K ≤ X)
    (h5 : lenPK hk c + fixLen (keyEnc (N := N) (K := K) c) ≤ X) (h6 : lPsi (N := N) (K := K) hk ≤ X)
    (h7 : lenPK hk c + lenKA hk c ≤ X) (h8 : lenCj (N := N) hk ≤ X)
    (h9 : offWk hk c + lenKA hk c ≤ X)
    (h10 : nJ (N := N) hk * (lenZ c + DualUse.rowL N K k) ≤ X) (h11 : lenZ c ≤ X)
    (h12 : nJ (N := N) hk * DualUse.rowL N K k ≤ X) (h13 : k * (N * K) ≤ X)
    (hpre : ∀ x ∈ preTmplC (lenZ c) (DualUse.rowL N K k) (nJ (N := N) hk) (c.d * (N * K))
      ((c.d - 2) * DualUse.rowL N K k) (2 * DualUse.rowL N K k) (lenZ c - (lenKA hk c + N * K))
      (lPsi (N := N) (K := K) hk), x.2 < 2 ^ m)
    (hpost : ∀ x ∈ postTmplC N K k (lenZ c) (DualUse.rowL N K k) (nJ (N := N) hk), x.2 < 2 ^ m) :
    (cfX hk c wfB).size ≤ 36 * 257 + (1200 * X + 9 * (195 * m + 36) + 20000) + wfB.size +
      (2000 * X + 10 * (195 * m + 36) + 60000) := by
  have a := size_preCoreC (lenPK hk c) (lenKA hk c) (lenPK hk c + lenKA hk c + lenCj (N := N) hk)
    (N * K) (lenPK hk c + fixLen (keyEnc (N := N) (K := K) c)) (lPsi (N := N) (K := K) hk)
    (lenPK hk c + lenKA hk c) (lenCj (N := N) hk) (lenZ c) (DualUse.rowL N K k) (nJ (N := N) hk)
    (c.d * (N * K)) ((c.d - 2) * DualUse.rowL N K k) (2 * DualUse.rowL N K k)
    (lenZ c - (lenKA hk c + N * K)) X m h1 h2 h3 h4 h5 h6 h7 h8 hpre
  have b := size_postCoreC (lenPK hk c) (lenKA hk c) (N * K) (offWk hk c)
    (nJ (N := N) hk * (lenZ c + DualUse.rowL N K k)) (lenZ c) N K k (lenZ c) (DualUse.rowL N K k)
    (nJ (N := N) hk) X m h1 h2 h9 h4 h10 h11 h12 h13 hpost
  have c0 := size_clearL_le clr01
  have c1 := length_clr01_le
  simp only [cfX, preC, postC, size_seq, size_frame]
  omega

end Gen

/-! ### The templates at `confP` -/

theorem tmpl8_lt {n : ℕ} {l : List (Fin n × ℕ)} (h : ∀ x ∈ l, x.2 ≤ 2 ^ 239) :
    ∀ x ∈ l, x.2 < 2 ^ 240 := fun x hx => by
  have := h x hx; have : (2 : ℕ) ^ 239 < 2 ^ 240 := by norm_num
  omega

theorem preTmpl_le {Z R nT C0 RM0 PS0 PAD X : ℕ} (h1 : Z ≤ X) (h2 : R ≤ X) (h3 : nT ≤ X)
    (h4 : C0 ≤ X) (h5 : RM0 ≤ X) (h6 : PS0 ≤ X) (h7 : 10 ≤ X) (h8 : PAD ≤ X) :
    ∀ x ∈ preTmpl Z R nT C0 RM0 PS0 PAD, x.2 ≤ X := by
  intro x hx
  simp only [preTmpl, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem preTmplC_le {Z R nJ C0 Z2 R2 PAD LΨ X : ℕ} (h1 : Z ≤ X) (h2 : R ≤ X) (h3 : nJ ≤ X)
    (h4 : C0 ≤ X) (h5 : Z2 ≤ X) (h6 : R2 ≤ X) (h7 : 10 ≤ X) (h8 : PAD ≤ X) (h9 : LΨ ≤ X) :
    ∀ x ∈ preTmplC Z R nJ C0 Z2 R2 PAD LΨ, x.2 ≤ X := by
  intro x hx
  simp only [preTmplC, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem rowL_le : DualUse.rowL Np Kp kp ≤ 2 ^ 86 := by rw [rowL_conf]; norm_num
theorem nJ_le : nJ (N := Np) (K := Kp) hkp ≤ 2 ^ 90 := by rw [nJ_conf]; norm_num
theorem dNK_le : confP.d * (Np * Kp) ≤ 2 ^ 121 := by rw [dNK_conf]; norm_num
theorem dRow_le : 10 * (confP.d * DualUse.rowL Np Kp kp) ≤ 2 ^ 151 := by
  rw [rowL_conf, confP_d]; norm_num
theorem dRow2_le : (confP.d - 2) * DualUse.rowL Np Kp kp ≤ 2 ^ 148 := by
  rw [rowL_conf, confP_d]; norm_num
theorem offBk_le : offBk confP ≤ 2 ^ 122 := by rw [offBk_conf]; norm_num

theorem sub_le_of {a b X : ℕ} (h : a ≤ X) : a - b ≤ X := (Nat.sub_le a b).trans h
theorem mono2 {a b A B X : ℕ} (ha : a ≤ A) (hb : b ≤ B) (h : A + B ≤ X) : a + b ≤ X := by omega
theorem mono3 {a b c A B C X : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) (h : A + B + C ≤ X) :
    a + b + c ≤ X := by omega

/-! ### The description lengths -/

theorem bfX_size_conf : (bfX hkp confP (wfB2 hkp confP WB2.Wc)).size ≤ 2 ^ 248 := by
  have hb := size_bfX_le hkp confP (wfB2 hkp confP WB2.Wc) (X := 2 ^ 237) (m := 240)
    (lenPK_le.trans (by norm_num)) (lenTc_le.trans (by norm_num)) (offBk_le.trans (by norm_num))
    (nJR_le.trans (by norm_num)) (offWk_le.trans (by norm_num)) (lenZ_le.trans (by norm_num))
    (tmpl8_lt (preTmpl_le (lenZ_le.trans (by norm_num)) (rowL_le.trans (by norm_num))
      (nJ_le.trans (by norm_num)) (dNK_le.trans (by norm_num)) (dRow_le.trans (by norm_num))
      (by rw [rowL_conf]; norm_num) (by norm_num) (sub_le_of (lenZ_le.trans (by norm_num)))))
    (tmpl8_lt fun x hx => (postTmpl_conf x hx).trans (by norm_num))
  have hw : (wfB2 hkp confP WB2.Wc).size ≤ 2 ^ 200 := wfCost_wfB2.size
  exact hb.trans (by
    have : (2 : ℕ) ^ 248 = 2 ^ 247 + 2 ^ 247 := by norm_num
    generalize (wfB2 hkp confP WB2.Wc).size = w at hw ⊢
    have : (2 : ℕ) ^ 200 ≤ 2 ^ 246 := by norm_num
    norm_num at hw ⊢
    omega)

theorem ksz_arith {S n F b P R s p d : ℕ}
    (hS : S ≤ 36 * n + F + b + 400 * (P + R) + 60 * (s + p + d) + 23 * (195 * 251 + 36) + 2 ^ 21)
    (hb : b ≤ 2 ^ 248) (hn : n ≤ 2 ^ 178) (hF : F ≤ 2 ^ 238) (hP : P ≤ 2 ^ 175) (hR : R ≤ 2 ^ 87)
    (hs : s ≤ 2 ^ 25) (hp : p ≤ 2 ^ 25) (hd : d ≤ 2 ^ 130) : S + (n + 3) + 2 ≤ 2 ^ 250 := by
  omega

set_option exponentiation.threshold 2000 in
theorem dl_num_key : 6 * 2 ^ 250 * 3 ^ 256 * (4 + 4 * 256 + 2 ^ 250) ≤ 2 ^ 1000 := by norm_num

/-- **The description length of `KeyGen` at `confP`.** -/
theorem descLen_keyMachineP_conf :
    (keyMachineP hkp confP (bfX hkp confP (wfB2 hkp confP WB2.Wc)) WB2.Wc cfP).descLen ≤ 2 ^ 1000 := by
  rw [descLen_keyMachineP]
  have hm : ∀ x ∈ keyTmplR hkp confP cfP, x.2 < 2 ^ 251 := fun x hx =>
    lt_of_le_of_lt ((le_tmplMax _ x hx).trans (keyTmplR_conf le_rfl)) (by norm_num)
  have hS := size_keyGenP (hk := hkp) (c := confP) (bfX hkp confP (wfB2 hkp confP WB2.Wc)) WB2.Wc cfP
    251 hm
  exact (descLen_arith (ksz_arith hS bfX_size_conf nKG_le (size_frontP_conf Wc_ge Wc_le) lenPK_le
    rK_le (le_of_eq length_sW_cfP) (le_of_eq length_powW_cfP) lenDummy_le)).trans dl_num_key

theorem cfX_size_conf : (cfX hkp confP (wfB2 hkp confP WB2.Wc)).size ≤ 2 ^ 249 := by
  have hkE : lenPK hkp confP + fixLen (keyEnc (N := Np) (K := Kp) confP) ≤ 2 ^ 237 :=
    mono2 lenPK_le fixLen_keyEnc_le (by norm_num)
  have hb := size_cfX_le hkp confP (wfB2 hkp confP WB2.Wc) (X := 2 ^ 237) (m := 240)
    (lenPK_le.trans (by norm_num)) (lenKA_le.trans (by norm_num))
    (mono3 lenPK_le lenKA_le lenCj_le (by norm_num)) (NK_le.trans (by norm_num)) hkE
    (lPsi_le.trans (by norm_num)) (mono2 lenPK_le lenKA_le (by norm_num))
    (lenCj_le.trans (by norm_num)) (mono2 offWk_le lenKA_le (by norm_num)) (LW_le.trans (by norm_num))
    (lenZ_le.trans (by norm_num)) (nJR_le.trans (by norm_num)) (kNK_le.trans (by norm_num))
    (tmpl8_lt (preTmplC_le (lenZ_le.trans (by norm_num)) (rowL_le.trans (by norm_num))
      (nJ_le.trans (by norm_num)) (dNK_le.trans (by norm_num)) (dRow2_le.trans (by norm_num))
      (by rw [rowL_conf]; norm_num) (by norm_num) (sub_le_of (lenZ_le.trans (by norm_num)))
      (lPsi_le.trans (by norm_num))))
    (tmpl8_lt fun x hx => (postTmplC_conf x hx).trans (by norm_num))
  have hw : (wfB2 hkp confP WB2.Wc).size ≤ 2 ^ 200 := wfCost_wfB2.size
  exact hb.trans (by
    generalize (wfB2 hkp confP WB2.Wc).size = w at hw ⊢
    have : (2 : ℕ) ^ 249 = 2 ^ 248 + 2 ^ 248 := by norm_num
    have : (2 : ℕ) ^ 200 ≤ 2 ^ 246 := by norm_num
    norm_num at hw ⊢
    omega)

theorem dsz_arith {S n F b B K : ℕ}
    (hS : S ≤ 36 * n + F + b + 4000 * B + 200 * K + 10 * (195 * 251 + 36) + 2 ^ 20)
    (hb : b ≤ 2 ^ 249) (hn : n ≤ 2 ^ 203) (hF : F ≤ 2 ^ 238) (hB : B ≤ 4 * 2 ^ 200) (hK : K ≤ 2 ^ 25) :
    S + (n + 3) + 2 ≤ 2 ^ 251 := by
  omega

set_option exponentiation.threshold 2000 in
theorem dl_num_dec : 6 * 2 ^ 251 * 3 ^ 256 * (4 + 4 * 256 + 2 ^ 251) ≤ 2 ^ 1000 := by norm_num

/-- **The description length of `Dec` at `confP`.** -/
theorem descLen_decMachineP_conf :
    (decMachineP hkp confP (cfX hkp confP (wfB2 hkp confP WB2.Wc)) WB2.Wc).descLen ≤ 2 ^ 1000 := by
  rw [descLen_decMachineP]
  have hm : ∀ x ∈ decTmpl confP, x.2 < 2 ^ 251 := fun x hx =>
    lt_of_le_of_lt (decTmpl_conf le_rfl x hx) (by norm_num)
  have hS := size_decGenP (hk := hkp) (c := confP) (cfX hkp confP (wfB2 hkp confP WB2.Wc)) WB2.Wc
    (4 * 2 ^ 200) 251 decOffs_conf hm
  exact (descLen_arith (dsz_arith hS cfX_size_conf nDec_le (size_frontP_conf Wc_ge Wc_le) le_rfl
    Kp_le25)).trans dl_num_dec

set_option exponentiation.threshold 2000 in
theorem dl_num_setup : 6 * (2 ^ 24 + 4) * 3 ^ 96 * (4 + 4 * 96 + (2 ^ 24 + 4)) ≤ 2 ^ 300 := by norm_num

set_option exponentiation.threshold 2000 in
theorem dl_num_enc : 6 * (2 ^ 24 + 4) * 3 ^ 124 * (4 + 4 * 124 + (2 ^ 24 + 4)) ≤ 2 ^ 300 := by norm_num

/-- **The description length of `Setup` at `confP`.** -/
theorem descLen_setupMP_conf : (setupMP hkp confP chiSamplerP).descLen ≤ 2 ^ 300 := by
  rw [descLen_setupMP]
  exact (descLen_arith (Nat.add_le_add_right size_setupP_conf 4)).trans dl_num_setup

/-- **The description length of `Enc` at `confP`.** -/
theorem descLen_encMP_conf : (encMP hkp confP chiSamplerP).descLen ≤ 2 ^ 300 := by
  rw [descLen_encMP]
  exact (descLen_arith (Nat.add_le_add_right size_encP_conf 4)).trans dl_num_enc

end AdvancedEncryption.DualUse.Prog
