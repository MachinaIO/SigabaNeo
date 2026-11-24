import PE.Impl.DualUse.Prog.CompLib
import PE.Impl.DualUse.Prog.KeyGenCost
import PE.Impl.DualUse.Prog.KeyCfgP
import PE.Impl.DualUse.Prog.SetupL
import PE.Impl.DualUse.Prog.FrontBPCost
import PE.Impl.DualUse.Prog.BfX
import PE.Impl.DualUse.PUCodes

/-!
# The constants of `KeyGen` at `confA`

The lengths that the clocks and the description lengths of `KeyGen` and `Dec` use, at the numbers
of `confA` (`N = 2^36`, `K = 2^27`, `k = K + 1`, `d = 2^65`, `nA = 128`) and with the key-try
configuration `cfP`:

* the cut of the predicates `confP.L = bpLen ≤ 2^49` (`confP_L_le`);
* the words of the scheme: the public key `lenPK` (`lenPK_eq`, `≈ 2^190`), a row `2kNK`
  (`rK_le`, `2^91`), the trapdoor stash `lenT` (`2^92`), the free part of a `W_j` `lenZ`
  (`2^157`), the number `nJ` of the `W_j` (`2^99`), the offsets `offBk`, `offWk`, the dummy key
  (`≤ 2^129`), the input bound `nKG ≤ 2^192`;
* the templates of the read-back (`postTmpl_conf`) and of the key try (`tmplMax_conf`,
  `keyTmplR_conf`).

Every closed form is reached by `rw` with the equation lemmas of the parameters (`Np_def`, `Kp_def`,
`kp_eq`, `confP_d`) and then arithmetic on numerals only.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.DualUse.Params
open AdvancedEncryption.DualUse.Algo AdvancedEncryption.DualUse.Algo.Params
open SigabaNeo.Lattices.Algo
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPWord

set_option maxRecDepth 100000
set_option exponentiation.threshold 3000

/-! ### Generic helpers -/

theorem tmplT_le {n : ℕ} : ∀ (l : List (Fin n × ℕ)) (M X : ℕ), (∀ x ∈ l, x.2 ≤ X) →
    tmplT l M ≤ l.length * ((2 * X + 1) * (4 * M + 12)) + (2 * (M + 1) + 3)
  | [], M, X, _ => by simp [tmplT]
  | x :: l, M, X, h => by
    have h1 : (2 * x.2 + 1) * (4 * M + 12) ≤ (2 * X + 1) * (4 * M + 12) :=
      Nat.mul_le_mul_right _ (by have := h x (by simp); omega)
    have h2 := tmplT_le l M X (fun y hy => h y (by simp [hy]))
    show (2 * x.2 + 1) * (4 * M + 12) + tmplT l M ≤
      (l.length + 1) * ((2 * X + 1) * (4 * M + 12)) + (2 * (M + 1) + 3)
    generalize (2 * x.2 + 1) * (4 * M + 12) = P at *
    generalize (2 * X + 1) * (4 * M + 12) = Q at *
    rw [Nat.add_one_mul]
    generalize l.length * Q = R at *
    omega

theorem tmplMax_le_of {n : ℕ} {X : ℕ} : ∀ l : List (Fin n × ℕ), (∀ x ∈ l, x.2 ≤ X) → tmplMax l ≤ X
  | [], _ => Nat.zero_le _
  | x :: l, h => max_le (h x (by simp)) (tmplMax_le_of l fun y hy => h y (by simp [hy]))

/-! ### The cut -/

theorem confP_L_le : confP.L ≤ 2 ^ 49 := by rw [confP_L]; exact bpLen_le

/-! ### The words at `confA` -/

theorem lenPK_eq : lenPK hkp confP =
    6129982437495116521683020588912456589297838140178825216 := by
  simp only [lenPK, fixLen]; comp_unfold; norm_num

theorem lenPK_le : lenPK hkp confP ≤ 2 ^ 191 := by rw [lenPK_eq]; norm_num

theorem lenDummy_le : ((keyEnc (N := Np) (K := Kp) confP).enc (dummyKey confP)).length ≤ 2 ^ 129 := by
  rw [length_enc_fixLen]; simp only [fixLen]; comp_unfold; norm_num

theorem length_sW_cfP : cfP.sW.length = 2 ^ 26 := by
  show SpW.length = _; rw [length_SpW, Kp_def]

theorem length_powW_cfP : (powW Kp (cfP.B - 1)).length = 2 ^ 26 := by
  rw [powW, length_toBits, Kp_def]

theorem rowL_conf : DualUse.rowL Np Kp kp = 2 * (2 ^ 26 + 1) * (2 ^ 34 * 2 ^ 26) := by
  rw [kp_eq, Np_def, Kp_def]

theorem nJ_conf : nJ (N := Np) (K := Kp) hkp =
    128 * (2 * (2 * (2 ^ 26 + 1) * ((2 ^ 26 + 1) * 2 ^ 34))) := by
  simp only [nJ, DualUse.JIx, SigabaNeo.Encode.Enum.length_prod, len_Attr, len_Index]
  rw [kp_eq, Np_def]

theorem lenZ_conf : lenZ confP = (2 ^ 62 - 1) * (2 * (2 ^ 26 + 1) * (2 ^ 34 * 2 ^ 26)) := by
  simp only [lenZ]; rw [confP_d, rowL_conf]

theorem lenT_conf : lenT Np Kp kp = 2 * (2 ^ 26 + 1) * (2 ^ 34 * 2 ^ 26) + 2 ^ 34 * 2 ^ 26 := by
  simp only [lenT]; rw [rowL_conf, Np_def, Kp_def]

theorem offBk_conf : offBk confP = 1 * (2 ^ 62 * (2 ^ 34 * 2 ^ 26)) +
    1 * ((1 + (2 * (2 ^ 26 + 1) + 2 * (2 ^ 26 + 1))) * (2 ^ 34 * 2 ^ 26)) := by
  simp only [offBk, len_fin, len_trap]; rw [confP_d, kp_eq, Np_def, Kp_def]

theorem offWk_eq {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) :
    offWk hk c = lenPK hk c + c.d * (N * K) + nA * (c.d * DualUse.rowL N K k) := rfl

theorem offWk_conf : offWk hkp confP = lenPK hkp confP + 2 ^ 62 * (2 ^ 34 * 2 ^ 26) +
    nA * (2 ^ 62 * (2 * (2 ^ 26 + 1) * (2 ^ 34 * 2 ^ 26))) := by
  rw [offWk_eq, rowL_conf, confP_d, show Np * Kp = 2 ^ 34 * 2 ^ 26 by rw [Np_def, Kp_def]]

theorem dNK_conf : confP.d * (Np * Kp) = 2 ^ 62 * (2 ^ 34 * 2 ^ 26) := by
  rw [confP_d, Np_def, Kp_def]

theorem rK_le : 2 * kp * (Np * Kp) ≤ 2 ^ 92 := by rw [kp_eq, Np_def, Kp_def]; norm_num

theorem lenTc_le : lenT Np Kp kp ≤ 2 ^ 92 := by rw [lenT_conf]; norm_num
theorem lenZ_le : lenZ confP ≤ 2 ^ 157 := by rw [lenZ_conf]; norm_num
theorem nJ_le : nJ (N := Np) (K := Kp) hkp ≤ 2 ^ 100 := by rw [nJ_conf]; norm_num
theorem offBk_le : offBk confP ≤ 2 ^ 129 := by rw [offBk_conf]; norm_num
theorem offWk_le : offWk hkp confP ≤ 2 ^ 191 := by
  rw [offWk_conf, lenPK_eq, show nA = 128 from rfl]; norm_num

theorem fixLen_msk_le : fixLen (mskEnc hkp confP) ≤ 2 ^ 191 := by
  simp only [fixLen]; comp_unfold; norm_num

theorem nKG_arith {p m L : ℕ} (hp : p = 515) (hm : m ≤ 2 ^ 191) (hL : L ≤ 2 ^ 49) :
    2 * p + 1 + (2 * m + 1) + (2 * L + 1) ≤ 2 ^ 193 := by
  subst hp; omega

theorem nKG_le : nKG hkp confP ≤ 2 ^ 193 := by
  simp only [nKG, DualUse.pw]
  exact nKG_arith DualUse.length_paramsWord_pu fixLen_msk_le confP_L_le

theorem aK_le' {n : ℕ} (h : n ≤ 2 ^ 193) : 8 * (n + 2) ≤ 2 ^ 197 := by omega

theorem aK_le : 8 * (nKG hkp confP + 2) ≤ 2 ^ 197 := aK_le' nKG_le

/-! ### The templates -/

theorem postTmpl_conf : ∀ x ∈ postTmpl Np Kp kp, x.2 ≤ 2 ^ 92 := by
  intro x hx
  simp only [postTmpl, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
    (try rw [kp_eq]) <;> (try rw [Np_def]) <;> (try rw [Kp_def]) <;> norm_num

theorem mBp_le : cfP.m ≤ 2 ^ 130 := by
  show mBp ≤ _
  simp only [mBp, Bp_def, dp_def, Np_def, kp, Kp_def]; norm_num

theorem Bp_le : cfP.B ≤ 2 ^ 30 := by show Bp ≤ _; rw [Bp_def]; norm_num

theorem tmplMax_conf : tmplMax (keyTmpl hkp confP cfP) ≤ 2 ^ 192 := by
  refine tmplMax_le_of _ fun x hx => ?_
  simp only [keyTmpl, List.mem_cons, List.not_mem_nil, or_false] at hx
  have hP := lenPK_le
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
  · rw [Kp_def]; norm_num
  · rw [Np_def]; norm_num
  · rw [Np_def, Kp_def]; norm_num
  · exact Bp_le.trans (by norm_num)
  all_goals first
    | exact mBp_le.trans (by norm_num)
    | (norm_num; done)
    | (simp only [Algo.nT, confP_d, kp, Kp_def, Np_def]; norm_num; done)
    | (rw [lenPK_eq]; (try simp only [Algo.nT, confP_d, kp, Kp_def, Np_def]); norm_num)

theorem keyTmplR_conf {G : ℕ} (hG : 2 ^ 192 ≤ G) : tmplMax (keyTmplR hkp confP cfP) ≤ G := by
  refine tmplMax_le_of _ fun x hx => ?_
  simp only [keyTmplR, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hx | rfl | rfl | rfl
  · exact ((le_tmplMax _ x hx).trans tmplMax_conf).trans hG
  all_goals (dsimp only; refine le_trans ?_ hG; (try rw [kp_eq]); (try rw [Np_def]); (try rw [Kp_def]); norm_num)

end AdvancedEncryption.DualUse.Prog
