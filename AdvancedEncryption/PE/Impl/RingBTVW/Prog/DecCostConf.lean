import PE.Impl.RingBTVW.Prog.KeyCostConf
import PE.Impl.RingBTVW.Prog.DecGenCost
import PE.Impl.RingBTVW.Prog.CfX

/-!
# The constants of `Dec` at `confA`

The lengths that the clock (`DecTightConf`) and the description length of `Dec` use, at
`N = 2^36`, `K = 2^27`, `k = K + 1`, `d = 2^65`, `nA = 128`: the key and the ciphertext
(`< 2^192` bits each), `Ψ`, the key-and-`Ψ` part `lenKA`, the `c_j` (`lenCj`), the input bound
`nDec ≤ 2^195`, the offsets read by the end of decryption (`decOffs_conf`), the templates.
The shared constants (`lenPK`, `rowL`, `nJ`, `lenZ`, …) are those of `KeyCostConf`.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg
open AdvancedEncryption.PE.Gates.BPWord
open SigabaNeo.Lattices.Algo
open AdvancedEncryption.RingBTVW.Params

set_option exponentiation.threshold 1000

set_option maxRecDepth 100000 in
theorem fixLen_skEnc_le : fixLen (skEnc hkp confP) ≤ 2 ^ 192 := by
  simp only [fixLen]; comp_unfold; norm_num

set_option maxRecDepth 100000 in
theorem fixLen_ctEnc_le : fixLen (ctEnc hkp confP) ≤ 2 ^ 192 := by
  simp only [fixLen]; comp_unfold; norm_num

set_option maxRecDepth 100000 in
theorem fixLen_keyEnc_le : fixLen (keyEnc (N := Np) (K := Kp) confP) ≤ 2 ^ 129 := by
  simp only [fixLen]; comp_unfold; norm_num

set_option maxRecDepth 100000 in
theorem lPsi_le : lPsi (N := Np) (K := Kp) hkp ≤ 2 ^ 102 := by
  simp only [lPsi, fixLen]; comp_unfold; norm_num

set_option maxRecDepth 100000 in
theorem lenKA_le : lenKA hkp confP ≤ 2 ^ 132 := by
  simp only [lenKA, lPsi, fixLen]; comp_unfold; norm_num

theorem NK_eq : Np * Kp = 2 ^ 34 * 2 ^ 26 := by rw [Np_def, Kp_def]

theorem NK_le : Np * Kp ≤ 2 ^ 63 := by rw [NK_eq]; norm_num

theorem kNK_eq : kp * (Np * Kp) = (2 ^ 26 + 1) * (2 ^ 34 * 2 ^ 26) := by rw [kp_eq, NK_eq]

theorem kNK_le : kp * (Np * Kp) ≤ 2 ^ 91 := by rw [kNK_eq]; norm_num

theorem rowL_le : RingBTVW.rowL Np Kp kp ≤ 2 ^ 92 := by rw [rowL_conf]; norm_num

theorem lenCj_le : lenCj (N := Np) (K := Kp) hkp ≤ 2 ^ 193 := by
  simp only [lenCj]; rw [nJ_conf, rowL_conf]; norm_num

theorem nJR_leD : nJ (N := Np) (K := Kp) hkp * RingBTVW.rowL Np Kp kp ≤ 2 ^ 193 := lenCj_le

theorem LW_le : nJ (N := Np) (K := Kp) hkp * (lenZ confP + RingBTVW.rowL Np Kp kp) ≤ 2 ^ 258 := by
  rw [nJ_conf, lenZ_conf, rowL_conf]; norm_num

theorem pw_len : RingBTVW.pw.length = 515 := by rw [RingBTVW.pw]; exact length_paramsWord_pu

theorem nDec_le_gen {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) {S T L : ℕ}
    (h1 : fixLen (skEnc hk c) ≤ S) (h2 : fixLen (ctEnc hk c) ≤ T) (h3 : c.L ≤ L) :
    nDec hk c ≤ 2 * 515 + 1 + (2 * S + 1) + (2 * L + 1) + (2 * T + 1) := by
  have := pw_len
  unfold nDec
  omega

theorem nDec_arith {n : ℕ} (h : n ≤ 2 * 515 + 1 + (2 * 2 ^ 192 + 1) + (2 * 2 ^ 49 + 1) +
    (2 * 2 ^ 192 + 1)) : n ≤ 2 ^ 195 := by omega

/-- **The input bound of `Dec` at `confA`.** -/
theorem nDec_le : nDec hkp confP ≤ 2 ^ 195 :=
  nDec_arith (nDec_le_gen hkp confP fixLen_skEnc_le fixLen_ctEnc_le confP_L_le)

theorem decOffs_le_gen {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) {X : ℕ}
    (h1 : fixLen (skEnc hk c) ≤ X) (h2 : fixLen (ctEnc hk c) ≤ X) (h3 : lPsi (N := N) (K := K) hk ≤ X)
    (h4 : lenPK hk c ≤ X) (h5 : c.d * (N * K) ≤ X) (h6 : Algo.nT k * (N * K) ≤ X)
    (h7 : 2 * k * (N * K) ≤ X) (h8 : N * K ≤ X) : ∀ x ∈ decOffs hk c, x ≤ 4 * X := by
  intro x hx
  simp only [decOffs, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem nTk_eq : Algo.nT kp = 1 + (2 * (2 ^ 26 + 1) + 2 * (2 ^ 26 + 1)) := by
  simp only [Algo.nT]; rw [kp_eq]

/-- **The offsets read by the end of decryption at `confA`.** -/
theorem decOffs_conf : ∀ x ∈ decOffs hkp confP, x ≤ 2 ^ 194 := fun x hx =>
  (decOffs_le_gen hkp confP (X := 2 ^ 192) fixLen_skEnc_le fixLen_ctEnc_le
    (lPsi_le.trans (by norm_num)) (lenPK_le.trans (by norm_num)) (by rw [dNK_conf]; norm_num)
    (by rw [nTk_eq, NK_eq]; norm_num) (rK_le.trans (by norm_num)) (NK_le.trans (by norm_num))
    x hx).trans (by norm_num)

/-- The templates of the end of decryption at `confA`. -/
theorem decTmpl_conf {G : ℕ} (hG : 2 ^ 66 ≤ G) : ∀ x ∈ decTmpl confP, x.2 ≤ G := by
  have h1 : Kp ≤ 2 ^ 26 := by rw [Kp_def]
  have h2 : Np ≤ 2 ^ 34 := by rw [Np_def]
  have h3 := NK_le
  have h4 : 2 * kp ≤ 2 ^ 29 := by rw [kp_eq]; norm_num
  have h5 : confP.d ≤ 2 ^ 62 := by rw [confP_d]
  have h6 : Algo.nT kp ≤ 2 ^ 30 := by rw [nTk_eq]; norm_num
  intro x hx
  simp only [decTmpl, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

/-- The templates of the read-back of `c_f̂` at `confA`. -/
theorem postTmplC_conf : ∀ x ∈ postTmplC Np Kp kp (lenZ confP) (RingBTVW.rowL Np Kp kp)
    (nJ (N := Np) (K := Kp) hkp), x.2 ≤ 2 ^ 157 := by
  have h1 := lenZ_le
  have h2 := rowL_le
  have h3 := nJ_le
  have h4 := kNK_le; have h5 := NK_le; have h6 := rK_le
  have h7 : kp ≤ 2 ^ 28 := by rw [kp_eq]; norm_num
  have h8 : Np ≤ 2 ^ 34 := by rw [Np_def]
  have h9 : Kp ≤ 2 ^ 26 := by rw [Kp_def]
  have h10 : 1 * (2 * kp) * Np ≤ 2 ^ 62 := by rw [kp_eq, Np_def]; norm_num
  intro x hx
  simp only [postTmplC, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

end AdvancedEncryption.RingBTVW.Prog
