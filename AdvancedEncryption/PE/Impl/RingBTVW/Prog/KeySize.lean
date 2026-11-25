import PE.Impl.RingBTVW.Prog.SizeCost
import PE.Impl.RingBTVW.Prog.KeyTightConf
import PE.Impl.RingBTVW.Prog.DecSize

/-!
# The states and the description length of `KeyGen` at `confA`

* `size_bfX_le`: the states of the key-row block `bfX` from the largest offset `X` it reads (each
  read is unrolled) and the bits `m` of its templates;
* `bfC_size_conf`: the key-row block of `implC` has at most `2^195` states (`X = 2^184`: the
  public key, `offWk + lenT`; the stream block `≤ 2^25`);
* **`keyGen_size_conf`**: the program of `KeyGen` of `implC` with the states of its loader,
  `size + (nKG + 3) + 2 ≤ 2^196` (the reads of the public key and the input guard dominate);
* **`descLen_keyMachineP_conf`**: the description length of `KeyGen` of `implC` is at most
  `2^615`.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.RingBTVW.Params
open AdvancedEncryption.PE.Gates.BPWord
open SigabaNeo.Lattices.Algo
open AdvancedEncryption.RingBTVW.Sub

set_option exponentiation.threshold 3000
set_option maxRecDepth 100000

/-- The description length from a state bound (`Machine.entryBits` with no work tapes). -/
theorem descLen_arithK {k S B : ℕ} (h : S ≤ B) :
    6 * S * 3 ^ k * 3 ^ 0 * Machine.entryBits k S 0 ≤ 6 * B * 3 ^ k * (4 + 4 * k + B) := by
  have hs : Nat.size S ≤ S := Nat.size_le.mpr (Nat.lt_two_pow_self)
  unfold Machine.entryBits
  simp only [pow_zero, mul_one, Nat.mul_zero, Nat.add_zero, Nat.size_zero]
  gcongr
  omega

section Gen

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

theorem size_mvBit : (XProg.prog mvBit).size ≤ 100 := by
  simp [mvBit, size_prog, Prog.size, Prim.pad]

/-- **The states of the key-row block.** -/
theorem size_bfX_le (wfB : XProg 256) {X m : ℕ} (h1 : lenPK hk c ≤ X) (h2 : lenT N K k + 1 ≤ X)
    (h3 : offBk c ≤ X) (h4 : nJ (N := N) hk * RingBTVW.rowL N K k ≤ X)
    (h5 : offWk hk c + lenT N K k ≤ X) (h6 : lenZ c ≤ X)
    (hpre : ∀ x ∈ preTmpl (lenZ c) (RingBTVW.rowL N K k) (nJ (N := N) hk) (c.d * (N * K))
      (nA * (c.d * RingBTVW.rowL N K k)) (nA * (2 * RingBTVW.rowL N K k)) (lenZ c - (lenT N K k + 1)),
      x.2 < 2 ^ m)
    (hpost : ∀ x ∈ postTmpl N K k, x.2 < 2 ^ m) :
    (bfX hk c wfB).size ≤ 36 * 257 + 100 + (600 * X + 8 * (195 * m + 36) + 10000) + wfB.size +
      (1200 * X + 6 * (195 * m + 36) + 40000) := by
  have a := size_preCoreB (lenPK hk c) (lenT N K k + 1) (offBk c)
    (nJ (N := N) hk * RingBTVW.rowL N K k) (lenZ c) (RingBTVW.rowL N K k) (nJ (N := N) hk)
    (c.d * (N * K)) (nA * (c.d * RingBTVW.rowL N K k)) (nA * (2 * RingBTVW.rowL N K k))
    (lenZ c - (lenT N K k + 1)) X m h1 h2 h3 h4 hpre
  have b := size_postCoreB (lenPK hk c) (lenT N K k) (offWk hk c) (lenZ c) N K k X m h1 (by omega)
    h5 h6 (by omega) hpost
  have c0 := size_clearL_le clr01
  have c1 := length_clr01_le
  have c2 := size_mvBit
  simp only [bfX, preB, postB, size_seq, size_frame]
  omega

end Gen

theorem preTmpl_conf : ∀ x ∈ preTmpl (lenZ confP) (RingBTVW.rowL Np Kp kp) (nJ (N := Np) (K := Kp) hkp)
    (confP.d * (Np * Kp)) (nA * (confP.d * RingBTVW.rowL Np Kp kp)) (nA * (2 * RingBTVW.rowL Np Kp kp))
    (lenZ confP - (lenT Np Kp kp + 1)), x.2 < 2 ^ 164 := by
  have hZ := lenZ_le
  have hn : nA = 128 := rfl
  intro x hx
  simp only [preTmpl, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
  · exact lt_of_le_of_lt hZ (by norm_num)
  · rw [rowL_conf]; norm_num
  · exact lt_of_le_of_lt nJ_le (by norm_num)
  · rw [dNK_conf]; norm_num
  · rw [rowL_conf, confP_d, hn]; norm_num
  · rw [rowL_conf, hn]; norm_num
  · rw [hn]; norm_num
  · exact lt_of_le_of_lt ((Nat.sub_le _ _).trans hZ) (by norm_num)

theorem nJR_le : nJ (N := Np) (K := Kp) hkp * RingBTVW.rowL Np Kp kp ≤ 2 ^ 184 := by
  rw [nJ_conf, rowL_conf]; norm_num

theorem offWkT_le : offWk hkp confP + lenT Np Kp kp ≤ 2 ^ 184 := by
  have h1 := offWk_le_t
  have h2 := lenTc_le_t
  have : (2 : ℕ) ^ 184 = 2 ^ 183 + 2 ^ 183 := by norm_num
  have : (2 : ℕ) ^ 88 ≤ 2 ^ 183 := by norm_num
  omega

/-- **The states of the key-row block of `implC`.** -/
theorem bfC_size_conf : bfC.size ≤ 2 ^ 195 := by
  have hb := size_bfX_le hkp confP wfC (X := 2 ^ 184) (m := 164)
    (lenPK_le_t.trans (by norm_num)) (Nat.succ_le_of_lt (lt_of_le_of_lt lenTc_le_t (by norm_num)))
    (offBk_le.trans (by norm_num)) nJR_le offWkT_le (lenZ_le_t.trans (by norm_num)) preTmpl_conf
    (fun x hx => lt_of_le_of_lt (postTmpl_conf x hx) (by norm_num))
  have hw := size_wfC
  refine hb.trans ?_
  generalize wfC.size = w at hw ⊢
  have : 2 ^ 184 * 2048 ≤ (2 : ℕ) ^ 195 := by norm_num
  omega

theorem ksz_arith {S n F b P R s p d : ℕ}
    (hS : S ≤ 36 * n + F + b + 400 * (P + R) + 60 * (s + p + d) + 23 * (195 * 193 + 36) + 2 ^ 21)
    (hb : b ≤ 2 ^ 195) (hn : n ≤ 2 ^ 185) (hF : F ≤ 2 ^ 57) (hP : P ≤ 2 ^ 183) (hR : R ≤ 2 ^ 88)
    (hs : s ≤ 2 ^ 26) (hp : p ≤ 2 ^ 26) (hd : d ≤ 2 ^ 123) : S + (n + 3) + 2 ≤ 2 ^ 196 := by
  omega

theorem fsz_arith {n : ℕ} (h : n ≤ 2 ^ 49) : 36 * n + 2 ^ 56 ≤ 2 ^ 57 := by omega

theorem frontBP_size_conf : (frontBP confP.L).size ≤ 2 ^ 57 :=
  (frontSpec_frontBP confP.L).size.trans (fsz_arith confP_L_le)

/-- **The states of `KeyGen` of `implC`**, with those of its loader. -/
theorem keyGen_size_conf : (keyGenP hkp confP bfC cfP).size + (nKG hkp confP + 3) + 2 ≤ 2 ^ 196 := by
  have hm : ∀ x ∈ keyTmplR hkp confP cfP, x.2 < 2 ^ 193 := fun x hx =>
    lt_of_le_of_lt ((le_tmplMax _ x hx).trans (keyTmplR_conf le_rfl)) (by norm_num)
  have hS := size_keyGenF (hk := hkp) (c := confP) eF (frontBP confP.L) bfC 512 cfP 193 hm
  exact ksz_arith hS bfC_size_conf nKG_le_t frontBP_size_conf lenPK_le_t rK_le_t
    (le_of_eq length_sW_cfP) (le_of_eq length_powW_cfP) lenDummy_le_t

theorem dl_num_key : 6 * 2 ^ 196 * 3 ^ 256 * (4 + 4 * 256 + 197) ≤ 2 ^ 615 := by norm_num

/-- **The description length of `KeyGen` of `implC`** (`Nat.size` of the state count `≤ 197` in
the entry width). -/
theorem descLen_keyMachineP_conf : (keyMachineP hkp confP bfC cfP).descLen ≤ 2 ^ 615 := by
  rw [descLen_keyMachineP]
  have h := keyGen_size_conf
  exact (descLen_arith_size (B := 2 ^ 196) (by omega)
    (lt_of_le_of_lt (by omega) (by norm_num : (2 : ℕ) ^ 196 < 2 ^ 197))).trans dl_num_key

end AdvancedEncryption.RingBTVW.Prog
