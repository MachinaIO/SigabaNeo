import PE.Impl.RingBTVW.Prog.SizeConf
import PE.Impl.RingBTVW.Prog.TightChain

/-!
# The description lengths of `Setup` and `Enc` from their counts (Stage II)

The state counts of the programs of `Setup` and `Enc` depend on their numerals only through the
condition that every count (template length, sampler count) is below `2^240` (`size_setupP_le`,
`size_encP_le`). The counts are closed forms in `N, K, k, d, n_A` (`nRowD_eq`, `nRowC_eq`,
`nBj_eq`, `nR_eqA`, `nE_eqA`, `nJenc_eqA`, …), all below `2^200` at the sizes of `confA`
(`N = 2^36`, `K = 2^27`, `k = 2^27 + 1`, `d = 2^65`, `n_A = 128`, flooding width `768`): the
largest is `nBj = 8 n_A k³ N² K ≈ 2^190` (and the `B_j` field of the input, of the same size).

* `descLen_setupMP_of_counts`, `descLen_encMP_of_counts`: `descLen ≤ 2^300` from counts below
  `M < 2^240`;
* `descLen_setupMP_A`, `descLen_encMP_A`: **`≤ 2^300` at the sizes of `confA`** (hypotheses on the
  values of `Np`, `Kp`, `dp`, `nA`, `confP.w`; while `nA = 10` they hold vacuously).
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.RingBTVW.Params
open AdvancedEncryption.PE

/-! ### Arithmetic -/

theorem descLen_arithA {k S B : ℕ} (h : S ≤ B) :
    6 * S * 3 ^ k * 3 ^ 0 * Machine.entryBits k S 0 ≤ 6 * B * 3 ^ k * (4 + 4 * k + B) := by
  have hs : Nat.size S ≤ S := Nat.size_le.mpr (Nat.lt_two_pow_self)
  unfold Machine.entryBits
  simp only [pow_zero, mul_one, Nat.mul_zero, Nat.add_zero, Nat.size_zero]
  gcongr
  omega

set_option exponentiation.threshold 2000 in
theorem dl_num_setupA : 6 * (2 ^ 24 + 4) * 3 ^ 96 * (4 + 4 * 96 + (2 ^ 24 + 4)) ≤ 2 ^ 300 := by
  norm_num

set_option exponentiation.threshold 2000 in
theorem dl_num_encA : 6 * (2 ^ 24 + 4) * 3 ^ 124 * (4 + 4 * 124 + (2 ^ 24 + 4)) ≤ 2 ^ 300 := by
  norm_num

/-! ### Counts as closed forms in `N, K, k, d, n_A` -/

section Closed

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The attribute bits are `n_A` (whatever their symbol structure). -/
theorem len_AttrA : (Enum.list (α := (Sdw (N := N) hk).Attr)).length = nA := len_fin _

theorem nJenc_eqA : nJenc (N := N) hk = nA * (2 * (2 * k * (k * N))) := by
  simp only [nJenc, Enum.length_prod, len_AttrA, len_Index]

theorem nR_eqA : nR hk c = nA * (2 * k) * c.d := by
  simp only [nR, Enum.length_prod, len_AttrA, len_fin, List.length_finRange]

theorem nE_eqA : nE (N := N) hk = nA * (2 * (2 * k * (k * N))) * (2 * k) * N := by
  simp only [nE, JC, Enum.length_prod, len_AttrA, len_Index, len_col, len_fin]

theorem nTrap_eqA : nTrap k = 1 + (2 * k + 2 * k) := len_trap

end Closed

/-! ### Description lengths from the counts -/

/-- **The description length of `Setup`** from its counts below `M < 2^240`. -/
theorem descLen_setupMP_of_counts {M : ℕ} (hB : M < 2 ^ 240) (h1 : nRowD Np Kp confP.d ≤ M)
    (h2 : nRowC Np Kp kp ≤ M) (h3 : Np ≤ M) (h4 : (Enum.list (α := RingBTVW.Fresh.Col kp)).length * Np ≤ M)
    (h5 : nBj (N := Np) (K := Kp) hkp ≤ M) (h6 : Np * Kp ≤ M) (hK : Kp ≤ M) (hk : kp ≤ M)
    (h2k : 2 * kp ≤ M) (h7 : 2 * kp * (Np * Kp) ≤ M)
    (h8 : 2 * kp * (Np * Kp) + 2 * kp * (Np * Kp) + Np * Kp ≤ M) (h9 : 2 * kp * Np ≤ M) :
    (setupMP hkp confP chiSamplerP).descLen ≤ 2 ^ 300 := by
  have hD := size_setupDet_le hB hK h3 hk h2k h6 h7 h8 h9 (le_trans (Nat.le_add_left 1 Kp) hk)
  rw [descLen_setupMP]
  exact (descLen_arithA (Nat.add_le_add_right (size_setupP_le hB h1 h2 h3 h4 h5 h6 hD) 4)).trans
    dl_num_setupA

/-- **The description length of `Enc`** from its counts below `M < 2^240`. -/
theorem descLen_encMP_of_counts {M : ℕ} (hB : M < 2 ^ 240) (h0 : 2 * RingBTVW.pw.length + 1 ≤ M)
    (p1 : (Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin confP.d)).length * (Np * Kp)) ≤ M)
    (p2 : (Enum.list (α := Fin 1)).length * ((Enum.list (α := TrapCol kp)).length * (Np * Kp)) ≤ M)
    (p3 : (Enum.list (α := (Sdw (N := Np) hkp).Attr × (Sdw (N := Np) hkp).ctBits.Index)).length *
      ((Enum.list (α := Fin 1)).length * ((Enum.list (α := RingBTVW.Fresh.Col kp)).length * (Np * Kp))) ≤ M)
    (hA : nA ≤ M) (h1 : Np * Kp ≤ M)
    (h2 : (Enum.list (α := Fin confP.d)).length * Np ≤ M) (h3 : Np ≤ M)
    (h4 : (Enum.list (α := RingBTVW.Fresh.Col kp)).length * Np ≤ M) (h5 : nR hkp confP ≤ M)
    (h6 : nE (N := Np) hkp ≤ M) (h7 : Kp + confP.w ≤ M) (ht : ∀ p ∈ tmplList hkp confP, p.2 ≤ M) :
    (encMP hkp confP chiSamplerP).descLen ≤ 2 ^ 300 := by
  have hP := size_encParseP_le hB h0 p1 p2 p3 h1 hA
  rw [descLen_encMP]
  exact (descLen_arithA (Nat.add_le_add_right
    (size_encP_le hB hB hP h1 h2 h3 h4 h5 h6 h7 ht) 4)).trans dl_num_encA

/-! ### At the sizes of `confA` -/

section ConfA

variable (hN : Np = 2 ^ 34) (hK : Kp = 2 ^ 26) (hd : confP.d = 2 ^ 62) (hA : nA = 128)
include hN hK

theorem kp_A : kp = 2 ^ 26 + 1 := by rw [kp, hK]

theorem nk_A : Np * Kp = 2 ^ 60 := by rw [hN, hK]; norm_num

include hd hA in
/-- **The description length of `Setup` at the sizes of `confA`.** -/
theorem descLen_setupMP_A : (setupMP hkp confP chiSamplerP).descLen ≤ 2 ^ 300 := by
  have ek := kp_A hN hK
  have enk := nk_A hN hK
  refine descLen_setupMP_of_counts (M := 2 ^ 200) (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [TightS.nRowD_eq, hd, enk]; norm_num
  · rw [TightS.nRowC_eq, ek, enk]; norm_num
  · rw [hN]; norm_num
  · rw [len_col, ek, hN]; norm_num
  · rw [TightS.nBj_eq, hN, hK, ek, hA]; norm_num
  · rw [enk]; norm_num
  · rw [hK]; norm_num
  · rw [ek]; norm_num
  · rw [ek]; norm_num
  · rw [ek, enk]; norm_num
  · rw [ek, enk]; norm_num
  · rw [ek, hN]; norm_num

include hd hA in
/-- **The description length of `Enc` at the sizes of `confA`** (flooding width `768`, a password
of at most `2^20` bits). -/
theorem descLen_encMP_A (hw : confP.w = 768) (hpw : RingBTVW.pw.length ≤ 2 ^ 20) :
    (encMP hkp confP chiSamplerP).descLen ≤ 2 ^ 300 := by
  have ek := kp_A hN hK
  have enk := nk_A hN hK
  have eJ : nJenc (N := Np) hkp = 128 * (2 * (2 * (2 ^ 26 + 1) * ((2 ^ 26 + 1) * 2 ^ 34))) := by
    rw [nJenc_eqA, hA, ek, hN]
  refine descLen_encMP_of_counts (M := 2 ^ 200) (by norm_num) (by omega) ?_ ?_ ?_ (by omega) ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_
  · rw [len_fin, len_fin, hd, enk]; norm_num
  · rw [len_fin, len_trap, ek, enk]; norm_num
  · rw [show (Enum.list (α := (Sdw (N := Np) hkp).Attr × (Sdw (N := Np) hkp).ctBits.Index)).length =
      nJenc (N := Np) hkp from rfl, eJ, len_fin, len_col, ek, enk]; norm_num
  · rw [enk]; norm_num
  · rw [len_fin, hd, hN]; norm_num
  · rw [hN]; norm_num
  · rw [len_col, ek, hN]; norm_num
  · rw [nR_eqA, hA, hd, ek]; norm_num
  · rw [nE_eqA, hA, ek, hN]; norm_num
  · rw [hw, hK]; norm_num
  · intro p hp
    simp only [tmplList, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
    all_goals (try simp only [ctLen, nTrap_eqA, eJ])
    all_goals (try rw [hd])
    all_goals (try rw [hA])
    all_goals (try rw [ek])
    all_goals (try rw [hN])
    all_goals (try rw [hK])
    all_goals norm_num

end ConfA

end AdvancedEncryption.RingBTVW.Prog
