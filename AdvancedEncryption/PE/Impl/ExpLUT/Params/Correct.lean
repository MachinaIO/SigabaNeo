import PE.Impl.ExpLUT.Params.Noise

/-!
# Correctness of ExpLUT at the concrete parameters

The experiment of correctness (`correctExp`) at the concrete configuration: `(mpk, msk) ← Setup`
(`setupLaw` with the binary trapdoor law `χT`), `k_F ← KeyGen(msk, F)` (`keyGenLaw`: one try of box
rejection with `Big`, `Small`, `dec = gadDec` and the real trapdoor of `msk`), `ct ← Enc(mpk, x, M)`
(`encLaw` with `χs = χ = CBD(16)` and the flooding law `χfl`, the bit `M` as `⌊q/2⌋ · M`), and the
result `Dec(k_F, ct) = M` (decoding the constant coefficient, `decodeBit`).

**`correct_fail_le`**: for every branching program `F` of length at most `16` that is well formed for
`W = 2^22` (`BP.WF`), every attribute `x` of symbols below `|Σ|` with `F(x) = 0`, and every bit `M`,
decryption fails with probability at most `2^{−128}` (in fact `2^{−130}`, the abort probability of
key generation): every key of `Setup` has its real trapdoor covered by the boxes
(`realTrap_covered`), the coins are within `B_χ = 16` and `B_fl = 2^eFl`, every accepted key is
within `2^{Bk−1}`, and the noise `corrBound` is below `q/4` (`decode_ok`). `correct_ge` is the
same as a lower bound `1 − 2^{−128}` on the probability of success.
-/

namespace AdvancedEncryption.ExpLUT.Params

open SigabaNeo.Lattices Cslib
open scoped ENNReal

/-- A bind is at most `c` at `b` when every branch of the support is (generic). -/
theorem PMF.bind_apply_le {α β : Type*} (p : PMF α) (f : α → PMF β) (b : β) (c : ℝ≥0∞)
    (h : ∀ a ∈ p.support, f a b ≤ c) : p.bind f b ≤ c := by
  rw [PMF.bind_apply]
  calc ∑' a, p a * f a b ≤ ∑' a, p a * c := by
        refine tsum_le_tsum (fun a => ?_)
        by_cases ha : a ∈ p.support
        · gcongr; exact h a ha
        · rw [(PMF.apply_eq_zero_iff p a).mpr ha, zero_mul, zero_mul]
    _ = c := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- `Lemma 8` for the concrete setting (the canonical `H`). -/
theorem lemma8_conf : Lemma8 confS :=
  lemma8_canon confE rfl h2c (binaryDigits (2 ^ en) qc Kc hτc) (binaryDigits_g hτc)

theorem one_le_gfac : 1 ≤ confS.gfac := le_trans (by norm_num) two_le_gfac

theorem one_le_Kkey : 1 ≤ Kkey := Nat.one_le_two_pow

variable {Pos : Type} [Fintype Pos] [DecidableEq Pos]

/-- **The experiment of correctness** at the concrete parameters, for a program `F` (of width
`F.w`), an attribute `x` and a bit `M`: `true` iff decryption returns `M`. -/
noncomputable def correctExp (F : BP Pos) (x : Pos → ℕ) (M : Bool) : PMF Bool :=
  (setupLaw confS Wbc Jc Pos χT).bind fun v =>
    (keyGenLaw Big Small hBig decc helperJ v.2 F).bind fun k =>
      (encLaw confS Wbc Jc Pos χc χc χfl helperJ F.w half v.1 x (msgR M)).map fun ct =>
        decide (decrypt (decodeBit hnc) helperJ v.1 F k ct = M)

/-- **Correctness at the concrete parameters**: decryption fails with probability at most
`2^{−130}` (the abort probability of one try of box rejection). -/
theorem correct_fail_le_130 (F : BP Pos) (hF : F.WF confS.E.W) (hT : F.T ≤ 16) (x : Pos → ℕ)
    (hx : ∀ t, x t < F.nsym) (hFx : F.eval x = 0) (M : Bool) :
    correctExp F x M false ≤ ((2 : ℝ≥0∞) ^ 130)⁻¹ := by
  unfold correctExp
  refine PMF.bind_apply_le _ _ _ _ fun v hv => ?_
  obtain ⟨hmpk, htrap, hTχ⟩ := mem_support_setupLaw hv
  have hTs : ∀ w c, cnorm (v.2.T w c) ≤ 1 := fun w c => χT_short _ (hTχ w c)
  unfold keyGenLaw
  rw [PMF.bind_map, hmpk]
  have hgood := realTrap_good helperJ v.1 F v.2.T htrap
  refine le_trans (decrypt_fail_le confN lemma8_conf helperJ half v.1 F hF rfl x hx hFx (msgR M)
    (χs := χc) (χ := χc) (χfl := χfl) (Bχ := Bχ) (Bfl := Bfl) (K := Kkey) one_le_gfac
    (fun a ha => by rw [confN_nrm]; exact χc_short a ha)
    (fun a ha => by rw [confN_nrm]; exact χfl_short a ha)
    Big Small hBig decc hdecc (realTrap v.2.T) hgood (realTrap_covered v.2.T hTs)
    (fun u hu p => by rw [confN_nrm]; exact Small_short u hu p)
    (fun y ic => by rw [confN_nrm]; exact (decc_short y ic).trans one_le_Kkey)
    (decodeBit hnc) M
    (fun e he => decode_ok hT M e (by rwa [confN_nrm] at he))) ?_
  exact abort_le_of_shift helperJ v.1 F (realTrap v.2.T) fun y p => realShift_le v.2.T hTs y p

/-- **Correctness at the concrete parameters**: decryption fails with probability at most
`2^{−128}`. -/
theorem correct_fail_le (F : BP Pos) (hF : F.WF confS.E.W) (hT : F.T ≤ 16) (x : Pos → ℕ)
    (hx : ∀ t, x t < F.nsym) (hFx : F.eval x = 0) (M : Bool) :
    correctExp F x M false ≤ ((2 : ℝ≥0∞) ^ 128)⁻¹ :=
  (correct_fail_le_130 F hF hT x hx hFx M).trans
    (ENNReal.inv_le_inv.mpr (pow_le_pow_right₀ (by norm_num) (by norm_num)))

/-- The same as a bound on success: `1 − 2^{−128} ≤ P[Dec = M]`. -/
theorem correct_ge (F : BP Pos) (hF : F.WF confS.E.W) (hT : F.T ≤ 16) (x : Pos → ℕ)
    (hx : ∀ t, x t < F.nsym) (hFx : F.eval x = 0) (M : Bool) :
    1 - ((2 : ℝ≥0∞) ^ 128)⁻¹ ≤ correctExp F x M true := by
  have hsum : correctExp F x M false + correctExp F x M true = 1 := by
    rw [← (correctExp F x M).tsum_coe, tsum_fintype, Fintype.sum_bool, add_comm]
  have hfin : correctExp F x M false ≠ ⊤ := PMF.apply_ne_top _ _
  calc 1 - ((2 : ℝ≥0∞) ^ 128)⁻¹ ≤ 1 - correctExp F x M false :=
        tsub_le_tsub_left (correct_fail_le F hF hT x hx hFx M) 1
    _ = correctExp F x M true := by
        rw [← hsum, ENNReal.add_sub_cancel_left hfin]

end AdvancedEncryption.ExpLUT.Params
