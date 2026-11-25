import PE.Impl.ExpLUT.AH.Games
import PE.Impl.ExpLUT.AH.Conf
import PE.Impl.ExpLUT.Prog.KeyBoxW
import PE.Impl.ExpLUT.Params.Correct
/-!
# Correctness of the ExpLUT implementation from the machines' specifications

For an implementation whose machines meet the specifications of package F at the concrete
dimensions `Dc` (`Setup`: `SetupSpec Dc (χbin Dc)`; `Enc`: `EncSpec Dc χc χc χfl`; `KeyGen`:
`KeySpec Dc kbDc L` with the machine's key boxes `kbDc`; `Dec`: `DecSpec Dc L`; `Eval`:
`evalMachineX`) and predicates of at most `L ≥ predLen` bits:

* `decryptLaw_eq`: the law of the PE correctness experiment (`PE.decryptLaw`) of an authorized
  predicate word `C` is the experiment of the laws `setupLawW`, `keyGenLaw` (one try of box
  rejection with `kbDc` and the real trapdoor), `encLawW`, decoded by the machine's `decodeBit`;
* `decryptLaw_fail_le`: decryption fails with probability at most `2^{−130}` (the abort
  probability of key generation, `abort_kbDc`), from Theorem 1 (`decrypt_fail_le`) with the noise
  bound `corrBound_Dc_le` and exact decoding (`decodeBit_half_add`);
* **`correct_of_specs`**: `Correct (univ w8) params impl` (`κ = 128`).

The laws differ from those of `Params.correctExp` (`Jh Dc` has `44` helpers against `43` for
`Jc`, `half = 2^{K−1}`, the machine's `decodeBit`), so the bound is derived again at `Dc` from the
generic lemmas rather than read off `Params.correct_ge`.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.ExpLUT.Params
open scoped ENNReal

/-! ### Decoding -/

/-- **Exact decoding of the machine's `decodeBit`**: `half · μ + e` decodes to `μ` for
`4 ‖e‖ + 4 ≤ 2^K`. -/
theorem decodeBit_half_add (D : Dims) (μ : Bool) (e : Rg D) (C : ℕ) (he : cnorm e ≤ C)
    (hC : 4 * C + 4 ≤ 2 ^ D.K) : decodeBit D (half D * msgR D μ + e) = μ := by
  have hK := D.hK
  set P : ℕ := 2 ^ (D.K - 2) with hP
  have h4 : 2 ^ D.K = 4 * P := by
    rw [hP, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]; congr 1; omega
  have h2 : 2 ^ (D.K - 1) = 2 * P := by
    rw [hP, ← pow_succ']; congr 1; omega
  have hq : (D.q : ℤ) = 4 * P - 1 := by
    simp only [Dims.q]; rw [h4]; have : 1 ≤ 4 * P := by have : 0 < P := Nat.two_pow_pos _; omega
    push_cast [Nat.cast_sub this]; ring
  set c := e.coeffs ⟨0, D.N_pos⟩ with hc
  set n := c.valMinAbs with hn
  have hnC : n.natAbs ≤ C := (zabs_coeffs_le_cnorm e _).trans he
  have hcn : c = (n : ZMod D.q) := (ZMod.coe_valMinAbs c).symm
  have hco : (half D * msgR D μ + e).coeffs ⟨0, D.N_pos⟩ =
      (((if μ then (2 * P : ℤ) else 0) + n : ℤ) : ZMod D.q) := by
    rw [Negacyclic.coeffs_add, Pi.add_apply, ← hc, hcn]
    cases μ
    · simp [msgR]
    · simp only [msgR, ite_true, mul_one, half, Negacyclic.coeffs_algebraMap]
      rw [show (2 : ZMod D.q) ^ (D.K - 1) = ((2 ^ (D.K - 1) : ℕ) : ZMod D.q) by push_cast; rfl, h2]
      push_cast; ring
  unfold decodeBit
  rw [hco]
  have hv := ZMod.val_intCast (n := D.q) ((if μ then (2 * P : ℤ) else 0) + n)
  have hnl : -(C : ℤ) ≤ n := by omega
  have hnu : n ≤ (C : ℤ) := by omega
  have hCP : (4 * C + 4 : ℤ) ≤ 4 * P := by exact_mod_cast h4 ▸ hC
  cases μ
  · simp only [Bool.false_eq_true, ite_false, zero_add] at hv ⊢
    rcases le_or_gt 0 n with h0 | h0
    · rw [Int.emod_eq_of_lt h0 (by omega)] at hv
      apply decide_eq_false; omega
    · rw [← Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)] at hv
      apply decide_eq_false; omega
  · simp only [ite_true] at hv ⊢
    rw [Int.emod_eq_of_lt (by omega) (by omega)] at hv
    apply decide_eq_true; omega

/-! ### Sizes at `Dc` (`44` helpers) -/

theorem card_gen44_le {m k : ℕ} (hm : m + k ≤ 2 ^ 42) (hk : k ≤ 2 ^ 16) :
    2 ^ bc * (m + k) + (2 ^ bc * (44 * (2 * k)) + 2 * k) ≤ 2 ^ 65 := by
  have h1 := Nat.mul_le_mul_left (2 ^ bc) hm
  have h2 := Nat.mul_le_mul_left (2 ^ bc) (Nat.mul_le_mul_left 88 hk)
  have e : 44 * (2 * k) = 88 * k := by ring
  rw [e]
  norm_num at h1 h2 ⊢
  omega

theorem card_KCol_Dc : Fintype.card (KCol (Wb Dc) (Jh Dc) confS.τ confS.E.W) ≤ 2 ^ 65 := by
  rw [card_KCol_gen]
  simp only [Fintype.card_fin, Fintype.card_prod, confS_W, confS_τ]
  exact card_gen44_le mbar_le Kc_le

theorem card_PIdx_Dc : Fintype.card (PIdxD Dc) * 2 ^ en ≤ 2 ^ 89 := by
  have h : Fintype.card (PIdxD Dc) ≤ 2 ^ 65 := by
    simp only [PIdxD, PIdx, Col, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    refine le_trans ?_ (card_gen44_le mbar_le Kc_le)
    have : Dc.mb = mbar := rfl
    have hK : Dc.K = Kc := rfl
    have hb : Dc.b = bc := rfl
    rw [this, hK, hb]
    have := Nat.mul_le_mul_left (2 ^ bc) (Nat.le_add_right mbar Kc)
    nlinarith
  calc Fintype.card (PIdxD Dc) * 2 ^ en ≤ 2 ^ 65 * 2 ^ 24 := Nat.mul_le_mul_right _ h
    _ = 2 ^ 89 := by norm_num

/-- **The noise bound at `Dc`**: `corrBound ≤ 16 + 2^eNoise` for `T ≤ 16`. -/
theorem corrBound_Dc_le {T : ℕ} (hT : T ≤ 16) :
    corrBound confS (Wb Dc) (Jh Dc) T Bχ Bfl Kkey ≤ 16 + 2 ^ eNoise := by
  unfold corrBound
  have hmax : max Bχ (evalBound confS T Bχ Bfl) ≤ 2 ^ (17122 + eFl) :=
    max_le (Bχ_le.trans (pow_le_pow' (by omega))) (evalBound_le hT)
  have hn : confS.E.n ≤ 2 ^ 24 := le_of_eq rfl
  have h := pow_mul_le' card_KCol_Dc (pow_mul_le' (pow_mul_le' hn hmax rfl) (le_refl Kkey) rfl)
    (show 65 + (24 + (17122 + eFl) + (Bk - 1)) = eNoise by unfold eNoise; omega)
  exact Nat.add_le_add_left h 16

theorem four_corrBound_Dc {T : ℕ} (hT : T ≤ 16) :
    4 * corrBound confS (Wb Dc) (Jh Dc) T Bχ Bfl Kkey + 4 ≤ 2 ^ Dc.K := by
  have hc := corrBound_Dc_le hT
  have hp : 32 ≤ 2 ^ eNoise :=
    (show 32 = 2 ^ 5 from rfl).le.trans (pow_le_pow' five_le_eNoise)
  have hQ : 8 * 2 ^ eNoise ≤ 2 ^ Dc.K := by
    have : 8 * 2 ^ eNoise = 2 ^ (eNoise + 3) := by rw [pow_add]; ring
    rw [this]; exact pow_le_pow' eNoise_lt.le
  omega

/-! ### The abort probability of the machine's key boxes -/

theorem kbDc_Big : kbDc.Big = famBig Dc.q Dc.N (PIdxD Dc) Bk hBk_Dc := by
  rw [kbDc_def]; exact kbOf_Big Dc Bk hBk_Dc rSmall

theorem kbDc_Small : kbDc.Small = famBall Dc.q Dc.N (PIdxD Dc) rSmall := by
  rw [kbDc_def]; rfl

theorem abort_prod_Dc :
    Fintype.card (PIdxD Dc) * Dc.N * (4 * coverBound + 1) * 2 ^ 130 ≤ 2 ^ Bk := by
  rw [show Dc.N = 2 ^ en from rfl]
  calc Fintype.card (PIdxD Dc) * 2 ^ en * (4 * coverBound + 1) * 2 ^ 130
      ≤ 2 ^ 89 * 2 ^ (eSh + 3) * 2 ^ 130 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul card_PIdx_Dc four_cover_le)
    _ = 2 ^ (89 + (eSh + 3) + 130) := by rw [pow_add 2 (89 + (eSh + 3)) 130, pow_add 2 89 (eSh + 3)]
    _ ≤ 2 ^ Bk := pow_le_pow' (by rw [eSh_def, Bk_def]; norm_num)

/-- The inner box of the abort bound (opaque, as the other boxes). -/
noncomputable irreducible_def innerDc : Finset (PIdxD Dc → Rg Dc) :=
  famBall Dc.q Dc.N (PIdxD Dc) (2 ^ (Bk - 1) - 1 - 2 * coverBound)

/-- **The abort probability of one try of key generation with `kbDc`**: at most `2^{−130}` for
every trapdoor shifting by at most `coverBound`. -/
theorem abort_kbDc (mpk : MPKt Dc) (F : BP (Pos)) (T : (ZIdx Dc.K (2 ^ Dc.b) → Rg Dc) → PIdxD Dc → Rg Dc)
    (hT : ∀ y p, cnorm (T (gadDec (S := setting Dc) y) p) ≤ coverBound) :
    keyLaw (S := setting Dc) kbDc.Big kbDc.Small kbDc.hBig gadDec (helperMap Dc) mpk F T none ≤
      ((2 : ℝ≥0∞) ^ 130)⁻¹ := by
  have hsub : innerDc ⊆ kbDc.Big :=
    @subset_of_eq Dc.q Dc.N _ (PIdxD Dc) _ _ innerDc kbDc.Big _ Bk hBk_Dc innerDc_def kbDc_Big
      one_le_Bk boxFacts.1
  have hin : ∀ p ∈ innerDc, ∀ y, p - T (gadDec (S := setting Dc) y) ∈ kbDc.Small := fun p hp y =>
    @sub_mem_of_eq Dc.q Dc.N _ (PIdxD Dc) _ _ innerDc kbDc.Small rSmall _ coverBound innerDc_def
      kbDc_Small (by rw [rSmall_def]; exact boxFacts.2.2.1) _ (hT y) p hp
  have h1 := keyLaw_none_le (S := setting Dc) kbDc.Big kbDc.Small kbDc.hBig gadDec (helperMap Dc)
    mpk F T _ hsub hin
  refine le_trans h1 ?_
  have h4 : 4 * coverBound + 1 ≤ 2 ^ Bk :=
    four_cover_le.trans (pow_le_pow' (by rw [eSh_def, Bk_def]; norm_num))
  exact @abort_of_eq Dc.q Dc.N _ (PIdxD Dc) _ _ innerDc kbDc.Big Bk coverBound 130 hBk_Dc innerDc_def kbDc_Big
    one_le_Bk h4 abort_prod_Dc

/-! ### The algorithms of the implementation -/

section Bridge

variable {impl : Impl sig} {L : ℕ}

/-- `Dec` of the implementation on encoded inputs. -/
theorem impl_dec (hD : DecSpec Dc L (impl.machine .dec)) (sk : SKt Dc) (C : List Bool)
    (ct : CTt Dc) (hC : C.length ≤ L) :
    dec (U := univ w8) params impl ((skEnc Dc).enc sk) C ((ctEnc Dc).enc ct) =
      PMF.pure (decOutW Dc sk C ct) := by
  unfold dec
  rw [run_of_machine' impl .dec (paramsWord (univ w8) params)
    [(skEnc Dc).enc sk, C, (ctEnc Dc).enc ct] (PMF.pure ()) (fun _ => [decOutW Dc sk C ct])
    (fun _ => rfl) (by rw [PMF.pure_map]; exact hD.2 sk C ct hC), PMF.pure_map, PMF.pure_map]
  rfl

/-- `KeyGen` of the implementation on a predicate word. -/
theorem impl_keyGen_valid (hK : KeySpec Dc kbDc L (impl.machine .keyGen)) (msk : MSKt Dc)
    (C : List Bool) (hC : C.length ≤ L) (hv : ValidC C) :
    keyGen (U := univ w8) params impl ((mskEnc Dc).enc msk) C =
      (keyGenLaw (S := setting Dc) kbDc.Big kbDc.Small kbDc.hBig gadDec (helperMap Dc) msk
        (bpOf (progOf C))).map fun k => (skEnc Dc).enc (msk.mpk, k) := by
  unfold keyGen
  rw [run_of_machine' impl .keyGen (paramsWord (univ w8) params) [(mskEnc Dc).enc msk, C]
    (keyLawW Dc kbDc msk C) (fun sk => [(skEnc Dc).enc sk]) (fun _ => rfl) (hK msk C hC),
    PMF.map_comp]
  unfold keyLawW
  rw [if_pos hv]
  exact PMF.map_comp _ _ _

/-- **The experiment of correctness at `Dc`** with the machines' laws: `true` iff the decoded bit
of `Dec` is `μ`. -/
noncomputable def corrExpW (C : List Bool) (x : Attribute w8) (μ : Bool) : PMF Bool :=
  (setupLawW Dc (χbin Dc)).bind fun v =>
    (keyGenLaw (S := setting Dc) kbDc.Big kbDc.Small kbDc.hBig gadDec (helperMap Dc) v.2
      (bpOf (progOf C))).bind fun k =>
      (encLawW Dc χc χc χfl v.1 x μ).map fun ct =>
        decide (decodeBit Dc (decryptRaw (helperMap Dc) v.2.mpk (bpOf (progOf C)) k ct) = μ)

/-- **The PE experiment of correctness is `corrExpW`** (through the encodings). -/
theorem decryptLaw_map (hS : SetupSpec Dc (χbin Dc) (impl.machine .setup))
    (hE : EncSpec Dc χc χc χfl (impl.machine .enc)) (hK : KeySpec Dc kbDc L (impl.machine .keyGen))
    (hD : DecSpec Dc L (impl.machine .dec)) (x : Attribute w8) (C : List Bool)
    (hv : ValidC C) (hL : C.length ≤ L) (μ : Bool) :
    (decryptLaw (univ w8) params impl x C μ).map (fun l => decide (l = [μ])) =
      corrExpW C x μ := by
  unfold decryptLaw corrExpW
  rw [impl_setup hS]
  simp only [bind, PMF.bind_map, PMF.map_bind]
  refine congrArg _ (funext fun v => ?_)
  simp only [Function.comp_apply]
  rw [impl_keyGen_valid hK v.2 C hL hv]
  refine (congrArg (PMF.map _) (PMF.bind_map _ _ _)).trans ((PMF.map_bind _ _ _).trans ?_)
  refine congrArg _ (funext fun k => ?_)
  simp only [Function.comp_apply]
  rw [impl_enc hE, PMF.bind_map, PMF.map_bind, ← PMF.bind_pure_comp]
  refine congrArg _ (funext fun ct => ?_)
  simp only [Function.comp_apply]
  rw [impl_dec hD _ C ct hL, PMF.pure_map]
  unfold decOutW
  rw [if_pos hv]
  simp

end Bridge

/-! ### The bound -/

theorem rSmall_le : rSmall ≤ Kkey := by
  rw [rSmall_def]; exact le_trans (Nat.sub_le _ _) (le_trans (Nat.sub_le _ _) le_rfl)

/-- **Decryption fails with probability at most `2^{−130}`** for authorized predicate words. -/
theorem corrExpW_false_le (C : List Bool) (x : Attribute w8) (hout : (progOf C).output x = false)
    (μ : Bool) : corrExpW C x μ false ≤ ((2 : ℝ≥0∞) ^ 130)⁻¹ := by
  unfold corrExpW
  refine Params.PMF.bind_apply_le _ _ _ _ fun v hv => ?_
  obtain ⟨hmpk, htrap, hTχ⟩ := mem_support_setupLawW hv
  have hTs : ∀ w c, cnorm (v.2.T w c) ≤ 1 := fun w c => χbin_short _ (hTχ w c)
  unfold keyGenLaw encLawW
  rw [PMF.bind_map, hmpk]
  have hFx : (bpOf (progOf C)).eval (attrN x) = 0 := by rw [eval_bpOf, hout]; rfl
  refine le_trans (decrypt_fail_le NDc lemma8_conf (helperMap Dc) (half Dc) v.1 (bpOf (progOf C))
    (wf_bpOf _ le_rfl) rfl (attrN x) (attrN_lt _ x) hFx (msgR Dc μ)
    (χs := χc) (χ := χc) (χfl := χfl) (Bχ := Bχ) (Bfl := Bfl) (K := Kkey) one_le_gfac
    (fun a ha => by rw [NDc_nrm]; exact χc_short a ha)
    (fun a ha => by rw [NDc_nrm]; exact χfl_short a ha)
    kbDc.Big kbDc.Small kbDc.hBig gadDec gadZ_gadDec (realTrap v.2.T)
    (realTrap_good (helperMap Dc) v.1 _ v.2.T htrap)
    (fun x' hx' y => kbCover_Dc x' hx' _ fun p => realShift_le_Dc v.2.T hTs y p)
    (fun u hu p => by
      rw [NDc_nrm]; exact ((mem_of_eq_famBall kbDc_Small u).mp hu p).trans rSmall_le)
    (fun y ic => by rw [NDc_nrm]; exact (decc_short y ic).trans one_le_Kkey)
    (decodeBit Dc) μ
    (fun e he => decodeBit_half_add Dc μ e _ (by rwa [NDc_nrm] at he)
      (four_corrBound_Dc le_rfl))) ?_
  exact abort_kbDc v.1 _ _ fun y p => realShift_le_Dc v.2.T hTs y p

/-- **Success with probability at least `1 − 2^{−130}`.** -/
theorem corrExpW_true_ge (C : List Bool) (x : Attribute w8) (hout : (progOf C).output x = false)
    (μ : Bool) : 1 - ((2 : ℝ≥0∞) ^ 130)⁻¹ ≤ corrExpW C x μ true := by
  have hsum : corrExpW C x μ false + corrExpW C x μ true = 1 := by
    rw [← (corrExpW C x μ).tsum_coe, tsum_fintype, Fintype.sum_bool, add_comm]
  have hfin : corrExpW C x μ false ≠ ⊤ := PMF.apply_ne_top _ _
  calc 1 - ((2 : ℝ≥0∞) ^ 130)⁻¹ ≤ 1 - corrExpW C x μ false :=
        tsub_le_tsub_left (corrExpW_false_le C x hout μ) 1
    _ = corrExpW C x μ true := by rw [← hsum, ENNReal.add_sub_cancel_left hfin]

/-! ### Correctness -/

/-- The probability of decrypting `μ` in the PE experiment is that of `true` in `corrExpW`. -/
theorem decryptLaw_apply {impl : Impl sig} {L : ℕ}
    (hS : SetupSpec Dc (χbin Dc) (impl.machine .setup))
    (hE : EncSpec Dc χc χc χfl (impl.machine .enc)) (hK : KeySpec Dc kbDc L (impl.machine .keyGen))
    (hD : DecSpec Dc L (impl.machine .dec)) (x : Attribute w8) (C : List Bool)
    (hv : ValidC C) (hL : C.length ≤ L) (μ : Bool) :
    decryptLaw (univ w8) params impl x C μ [μ] = corrExpW C x μ true := by
  rw [← decryptLaw_map hS hE hK hD x C hv hL μ, PMF.map_apply, tsum_eq_single [μ]]
  · simp
  · intro l hl; simp [hl]

/-- **Correctness of the implementation at `κ = 130`**: for every attribute `x`, every predicate
word `C` authorized for `x` and every bit `μ`, decryption returns `μ` with probability at least
`1 − 2^{−130}`. -/
theorem correct_of_specs_130 {impl : Impl sig} {L : ℕ}
    (hS : SetupSpec Dc (χbin Dc) (impl.machine .setup))
    (hE : EncSpec Dc χc χc χfl (impl.machine .enc)) (hK : KeySpec Dc kbDc L (impl.machine .keyGen))
    (hD : DecSpec Dc L (impl.machine .dec)) (hEv : impl.machine .eval = evalMachineX)
    (hL : predLen ≤ L) (x : Attribute w8) (C : List Bool)
    (hC : Authorized (U := univ w8) params impl C x) (μ : Bool) :
    1 - ((2 : ℝ≥0∞) ^ 130)⁻¹ ≤ decryptLaw (univ w8) params impl x C μ [μ] := by
  obtain ⟨hv, hout⟩ := (authorized_iff impl hEv C x).mp hC
  rw [decryptLaw_apply hS hE hK hD x C hv (hv ▸ hL) μ]
  exact corrExpW_true_ge C x hout μ

/-- **Correctness of the ExpLUT implementation** (`κ = 128`) from the specifications of its
machines at the concrete dimensions `Dc`. -/
theorem correct_of_specs {impl : Impl sig} {L : ℕ}
    (hS : SetupSpec Dc (χbin Dc) (impl.machine .setup))
    (hE : EncSpec Dc χc χc χfl (impl.machine .enc)) (hK : KeySpec Dc kbDc L (impl.machine .keyGen))
    (hD : DecSpec Dc L (impl.machine .dec)) (hEv : impl.machine .eval = evalMachineX)
    (hL : predLen ≤ L) : Correct (univ w8) params impl := by
  intro x C hC μ
  have h := correct_of_specs_130 hS hE hK hD hEv hL x C hC μ
  set p := decryptLaw (univ w8) params impl x C μ [μ]
  have hp1 : p ≤ 1 := PMF.coe_le_one _ _
  have hle : (1 : ℝ≥0∞) - ((2 : ℝ≥0∞) ^ 130)⁻¹ ≤ p := h
  have hr : ((1 : ℝ≥0∞) - ((2 : ℝ≥0∞) ^ 130)⁻¹).toReal ≤ p.toReal :=
    ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top hp1) hle
  have hinv : ((2 : ℝ≥0∞) ^ 130)⁻¹ ≤ 1 :=
    ENNReal.inv_le_one.mpr (one_le_pow₀ (by norm_num))
  rw [ENNReal.toReal_sub_of_le hinv ENNReal.one_ne_top, ENNReal.toReal_one, ENNReal.toReal_inv,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat] at hr
  show 1 - ((2 : ℝ) ^ params.corrBits)⁻¹ ≤ p.toReal
  have h128 : ((2 : ℝ) ^ 130)⁻¹ ≤ ((2 : ℝ) ^ params.corrBits)⁻¹ := by
    show ((2 : ℝ) ^ 130)⁻¹ ≤ ((2 : ℝ) ^ 128)⁻¹
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    exact pow_le_pow_right₀ (by norm_num) (by norm_num)
  linarith

end AdvancedEncryption.ExpLUT.Prog
