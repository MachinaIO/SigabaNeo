import PE.Impl.RingBTVW.AHComps
import PE.Impl.RingBTVW.ReductionCompsBound
import PE.Impl.RingBTVW.Prog.SetupLA
import PE.Impl.RingBTVW.Prog.CompCost
import PE.Impl.RingBTVW.Prog.RedDecodeA
import PE.Impl.RingBTVW.Prog.AuthBPX
import PE.Impl.RingBTVW.Prog.ShellsBP
import PE.Impl.RingBTVW.Params.Advantage
import PE.Impl.RingBTVW.Params.Strength
import PE.Impl.RingBTVW.ImplBP

/-!
# Attribute hiding of the concrete scheme at `confA`

At `confP` (the sizes of `confA`: `N = 2^36`, `K = 2^27`, `k = K + 1`, `d = 2^65`, `nA = 128`,
branching programs), the three reductions are assembled from their component programs (`Comps` at
`R = 254`, the length bounds `CompBoundsP`, the `Bundle`s of `AHComps`) and the constant of each
reduction is bounded through `compConst_le_bp` (`ReductionCompsBound`).

**The components** (all proved): the setups (`SetupLA`: `≤ 2^394` steps, output `≤ 2^195` bits),
the public keys (`≤ 2^458`, `≤ 2^196`), the challenges (`≤ 2^458`, `≤ 2^197`), the SimData programs
(`≤ 2^520`, `≤ 2^259`, `CompCost`), the authorization (`authBPX`: `≤ 2^109`, `≤ 2^18` states,
`AuthBPX`), the decoders (`≤ 2^380` steps, `≤ 2^16` states, `14` tapes, `RedDecodeA`); the packed
secrets are below `2^193` bits.

**The key component** of the reductions is `keyR sdP = keyPF … sdP eF (frontBP confP.L) wfR cfP`:
the SimData program, the front end of branching programs (`frontBP`), the stream block `wfC` of
`implC` behind `tailB` (`wfR`, it drops the bit `f(0)` of the block word) and the simulated key
try. Its law is proved (`law_keyP_spPack`); **its cost is the one hypothesis** here, `KeyRCost Ts
Ls Tk Lk Sk`: for a SimData program of at most `2^Ts` steps leaving at most `2^Ls` bits on a secret
of at most `2^193` bits, at most `2^Tk` steps and `2^Lk` bits per tape; at most `Sk` states for a
SimData program of at most `2^25` states. It is the key-component bound of the `KeyGen` cost
workstream (`time_keyP_confV`/`size_keyP_confV` at `confA`, with `frontBP`); here it is used at
`Ts = 520`, `Ls = 259`, `Tk ≤ 650`, `Lk ≤ 270`, `Sk ≤ 2^198 + 2^196` (the expected size is
`≈ 264 · lenPK ≈ 2^198.05`, the prefixes of the public key).

**The constant**: with these, every reduction's constant is at most `Cst` (`compBound_confA`,
`≈ 2^702.8`: the states of the chain `≈ 55944 · Sz2 ≈ 2^214.6` times `3^298` for the `14 + 254 + 30`
tapes), and `64 · (2^128)² · Cst ≤ 2^965` (`kb_confA`).

* `attributeHiding_conf`: from `KeyRCost` and `HardAt (params3 …) kb`, `HardAt (params5 …) kb`
  with `965 ≤ kb`;
* `attributeHiding_conf_rlwe`: the same at `kb` with the registry's strength: `965 ≤ 1158 ≤
  RingLWE.H` at both instances (`ringLWE_H_registry3/5`, `registry_covers_kb`).
-/

namespace AdvancedEncryption.RingBTVW

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW.Fresh Cslib
  Cslib.Probability SigabaNeo.Tape SigabaNeo.Tape.XProg
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord AdvancedEncryption.PE.Generic
open AdvancedEncryption.RingBTVW.Prog AdvancedEncryption.RingBTVW.Params
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option exponentiation.threshold 3000

instance : NeZero confP.d := dp_ne

/-! ### Statistical terms -/

section Stat

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

/-- **The statistical part from exponents**: attributes at most `2^a`, every term at most
`2^{-(a + s + 3)}`; then `statTerm ≤ 2^{-s}`. -/
theorem statTerm_le_gen {ε : ℝ≥0∞} (a s : ℕ)
    (hA : (Fintype.card PUniv.Attr : ℝ≥0∞) ≤ 2 ^ a)
    (h1 : delta1 (Sdw (N := N) hk) (Fin c.d) ≤ ((2 : ℝ≥0∞) ^ (a + (s + 3)))⁻¹)
    (h6 : delta6 (Sdw (N := N) hk) (Fin c.d) ≤ ((2 : ℝ≥0∞) ^ (a + (s + 3)))⁻¹)
    (hε : ε ≤ ((2 : ℝ≥0∞) ^ (a + (s + 3)))⁻¹) :
    statTerm c hk ε ≤ ((2 : ℝ≥0∞) ^ s)⁻¹ := by
  set x : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ (s + 3))⁻¹
  have m : ∀ {δ : ℝ≥0∞}, δ ≤ ((2 : ℝ≥0∞) ^ (a + (s + 3)))⁻¹ →
      (Fintype.card PUniv.Attr : ℝ≥0∞) * δ ≤ x := fun h =>
    card_mul_le (a := a) (t := s + 3) hA le_rfl h
  unfold statTerm
  calc _ ≤ x + x + x + x + x := by
        gcongr
        exacts [m h1, m hε, m h6, m h1, m h1]
    _ = 5 * x := by ring
    _ ≤ 2 ^ 3 * x := by gcongr; norm_num
    _ = ((2 : ℝ≥0∞) ^ s)⁻¹ := by
        show (2 : ℝ≥0∞) ^ 3 * ((2 : ℝ≥0∞) ^ (s + 3))⁻¹ = _
        rw [Nat.add_comm s 3]; exact two_pow_mul_inv 3 s

/-- **The statistical condition of the hybrid argument from an exponent**: `statTerm ≤ 2^{-s}`
and `λ + 2 ≤ 2 s` give `4 · 2^λ · statTerm² ≤ 1`. -/
theorem stat_of_le {ε : ℝ≥0∞} (s : ℕ) (h : statTerm c hk ε ≤ ((2 : ℝ≥0∞) ^ s)⁻¹)
    (hs : params.secBits + 2 ≤ 2 * s) :
    4 * (2 : ℝ) ^ params.secBits * (statTerm c hk ε).toReal ^ 2 ≤ 1 := by
  have h' := ENNReal.toReal_mono (ENNReal.inv_ne_top.mpr (pow_ne_zero _ two_ne_zero)) h
  rw [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at h'
  have h0 := ENNReal.toReal_nonneg (a := statTerm c hk ε)
  generalize (statTerm c hk ε).toReal = r at *
  have hr : r ^ 2 ≤ (((2 : ℝ) ^ s)⁻¹) ^ 2 := pow_le_pow_left₀ h0 h' 2
  generalize params.secBits = l at *
  calc 4 * (2 : ℝ) ^ l * r ^ 2 ≤ 2 ^ 2 * 2 ^ l * (((2 : ℝ) ^ s)⁻¹) ^ 2 := by
        gcongr; norm_num
    _ = 2 ^ (l + 2) / 2 ^ (2 * s) := by rw [← pow_add, inv_pow, ← pow_mul]; ring_nf
    _ ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact pow_le_pow_right₀ (by norm_num) hs

theorem statTerm_ne_top_of_le {ε : ℝ≥0∞} {s : ℕ} (h : statTerm c hk ε ≤ ((2 : ℝ≥0∞) ^ s)⁻¹) :
    statTerm c hk ε ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.inv_ne_top.mpr (pow_ne_zero _ two_ne_zero)) h

end Stat

/-- **The statistical part at `confP`**: `2^128` attributes, `δ₁, δ₆ ≤ 2^{-370}`, flooding
`ε = 2^{-499}`: `statTerm ≤ 2^{-239}`. -/
theorem statTerm_conf : statTerm confP hkp ((2 : ℝ≥0∞) ^ 499)⁻¹ ≤ ((2 : ℝ≥0∞) ^ 239)⁻¹ := by
  have hle : ∀ {e : ℕ}, 370 ≤ e → ((2 : ℝ≥0∞) ^ e)⁻¹ ≤ ((2 : ℝ≥0∞) ^ (128 + (239 + 3)))⁻¹ :=
    fun he => ENNReal.inv_le_inv.mpr (pow_le_pow_right₀ (by norm_num) (by omega))
  exact statTerm_le_gen (c := confP) 128 239 card_attrP.le (delta1_le.trans (hle le_rfl))
    (delta6_le.trans (hle le_rfl)) (hle (by norm_num))

theorem statTerm_conf_ne_top : statTerm confP hkp ((2 : ℝ≥0∞) ^ 499)⁻¹ ≠ ⊤ :=
  statTerm_ne_top_of_le statTerm_conf

theorem stat_conf :
    4 * (2 : ℝ) ^ params.secBits * (statTerm confP hkp ((2 : ℝ≥0∞) ^ 499)⁻¹).toReal ^ 2 ≤ 1 :=
  stat_of_le 239 statTerm_conf (by show 128 + 2 ≤ 2 * 239; norm_num)

/-! ### Discharged hypotheses of `attributeHiding_of_comps` -/

/-- **The boxes cover the simulated trapdoor** at `confP` (the data are binary, `SimValid`). -/
theorem simCovered_conf : SimCovered hkp confP := fun d hv C _ hev y hy u =>
  (goodTrap_sim d.mpk d.Rm (attrBits d.x) d.W d.Ψ hv.2.2.1 hv.2.2.2 C
    (keyMatrix_simW d hv C hev)).2 y hy u

theorem hχ_conf : χR confP = polyOf (N := Np) (ModuleLWE.coeffLaw (2 ^ Kp) (.cbd 16)) := rfl

theorem hL_conf : bpLen ≤ confP.L := by rw [confP_L]

theorem confP_L_le : confP.L ≤ 2 ^ 49 := by rw [confP_L]; exact bpLen_le

/-! ### The lengths of the answers -/

section Lengths

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000

theorem fixLen_skEnc_le : fixLen (skEnc hkp confP) ≤ 2 ^ 191 := by
  simp only [fixLen, skEnc]; comp_unfold; norm_num

theorem fixLen_ctEnc_le : fixLen (ctEnc hkp confP) ≤ 2 ^ 191 := by
  simp only [fixLen]; comp_unfold; norm_num

theorem lenPK_le : lenPK hkp confP ≤ 2 ^ 191 := by
  simp only [lenPK, fixLen]; comp_unfold; norm_num

end Lengths

theorem length_KGsim_le (d : SimData hkp confP) (C : List Bool) :
    ∀ sk ∈ (KGsim d C).support, sk.length ≤ 2 ^ 191 := by
  intro sk hsk
  unfold KGsim at hsk
  split_ifs at hsk
  · obtain ⟨o, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hsk
    rw [length_enc_fixLen]; exact fixLen_skEnc_le
  · rw [PMF.mem_support_pure_iff] at hsk; subst hsk
    rw [length_enc_fixLen]; exact fixLen_skEnc_le
  · rw [PMF.mem_support_pure_iff] at hsk; subst hsk; simp

/-! ### The key component of the reductions -/

/-- **The `W_f` block of the reductions' key component**: the stream block `wfC` of `implC` behind
`tailB` (the block word of the front end starts with the bit `f(0)`). -/
noncomputable abbrev wfR : XProg 256 := tailB Sub.wfC

theorem wfSpec_wfR : WfSpec hkp confP wfR 512 := wfSpec_tailB Sub.wfSpecS_wfC

/-- **The key component of the reductions** for a SimData program `sdP`: the front end of
branching programs `frontBP confP.L` (framed by `eF`), the block `wfR`, the key try of `cfP`. -/
noncomputable def keyR (sdP : XProg 82) : XProg 256 :=
  keyPF hkp confP sdP eF (frontBP confP.L) wfR cfP

/-- **The cost of the key component of the reductions** (the one hypothesis of this file): for a
SimData program of at most `2^Ts` steps leaving at most `2^Ls` bits (tape `0`) on a packed secret
of at most `2^193` bits, on that secret and a query of at most `confP.L` bits the key component
takes at most `2^Tk` steps and leaves at most `2^Lk` bits on every tape; for a SimData program of
at most `2^25` states it has at most `Sk` states. -/
structure KeyRCost (Ts Ls Tk Lk Sk : ℕ) : Prop where
  time : ∀ {sdP : XProg 82} {a : ℕ}, a ≤ 2 ^ 193 →
    timeBoundT sdP (io2 (R := 80) a 0 0) ≤ 2 ^ Ts →
    lenBoundT sdP (io2 (R := 80) a 0 0) ≤ io2 (2 ^ Ls) 0 0 →
    timeBoundT (keyR sdP) (io2 (R := 254) a confP.L 0) ≤ 2 ^ Tk
  len : ∀ {sdP : XProg 82} {a : ℕ}, a ≤ 2 ^ 193 →
    timeBoundT sdP (io2 (R := 80) a 0 0) ≤ 2 ^ Ts →
    lenBoundT sdP (io2 (R := 80) a 0 0) ≤ io2 (2 ^ Ls) 0 0 →
    lenBoundT (keyR sdP) (io2 (R := 254) a confP.L 0) ≤ io2 (2 ^ Lk) 0 0
  size : ∀ {sdP : XProg 82}, sdP.size ≤ 2 ^ 25 → (keyR sdP).size ≤ Sk

/-- **The authorization component of the reductions** and its interface (`AuthSpec`). -/
abbrev authC : XProg 256 := authBPX

theorem authC_spec : AuthSpec hkp confP authC (2 ^ 49) 109 18 := authSpec_authBPX hkp confP

/-! ### The components of a step -/

section Step

variable {Inst Sec : Type} [Nonempty Inst] {nI nσ : ℕ} (ienc : FixedEnc Inst nI)
  (senc : FixedEnc Sec nσ) (setupI : PUniv.Attr → PMF Sec)
  (viewI : Inst → Sec → PK hkp confP × CT hkp confP) (sdI : Inst → Sec → SimData hkp confP)

/-- The instance words of a step: `true` and the encoding of an instance. -/
def IWof (w : List Bool) : Prop := ∃ i, w = true :: ienc.enc i

/-- The instance of an instance word. -/
noncomputable def instOf : List Bool → Inst := Function.invFun fun i => true :: ienc.enc i

theorem instOf_cons (i : Inst) : instOf ienc (true :: ienc.enc i) = i :=
  Function.leftInverse_invFun (fun a b h => ienc.inj (List.cons_injective h)) i

/-- The setup of the packed challenger (unused by the oracle, which draws from `setupPack`). -/
noncomputable def stOf : PUniv.Attr → PMF (Inst × Sec) :=
  setupPack (instOf ienc) (fun _ => setupI) []

/-- **The components of a step other than the key component at `confP`**, with their laws and
their costs (`R = 254`). -/
structure StepComps where
  setupP : XProg 256
  pubP : XProg 256
  chalP : XProg 256
  sdP : XProg 82
  wf_setup : setupP.WF
  wf_pub : pubP.WF
  wf_chal : chalP.WF
  sd : SdSpec hkp confP sdP (ienc.prod senc).enc (fun p => sdI p.1 p.2) (fun _ => True)
  law_setup : ∀ i x, setupP.law (io2 (R := 254) (true :: ienc.enc i) (PUniv.encAttr x) []) =
    (setupI x).map fun σ => io2 (R := 254) ((ienc.prod senc).enc (i, σ)) [] []
  law_pub : ∀ p, pubP.law (io2 (R := 254) ((ienc.prod senc).enc p) [] []) =
    PMF.pure (io2 (R := 254) ((spPack (stOf ienc setupI) viewI sdI).pub p) [] [])
  law_chal : ∀ p μ, chalP.law (io2 (R := 254) ((ienc.prod senc).enc p) (PUniv.encMsg μ) []) =
    ((spPack (stOf ienc setupI) viewI sdI).chal p μ).map fun ct => io2 (R := 254) ct [] []
  time_setup : ∀ {a b : ℕ}, a ≤ 2 ^ 193 → b ≤ nA →
    timeBoundT setupP (io2 (R := 254) a b 0) ≤ 2 ^ 394
  len_setup : ∀ {a b : ℕ}, a ≤ 2 ^ 193 → b ≤ nA →
    lenBoundT setupP (io2 (R := 254) a b 0) ≤ io2 (2 ^ 195) 0 0
  time_pub : ∀ {a b : ℕ}, a ≤ 2 ^ 195 → b ≤ 2 ^ 195 →
    timeBoundT pubP (io2 (R := 254) a b 0) ≤ 2 ^ 458
  len_pub : ∀ {a b : ℕ}, a ≤ 2 ^ 195 → b ≤ 2 ^ 195 →
    lenBoundT pubP (io2 (R := 254) a b 0) ≤ io2 (2 ^ 196) 0 0
  time_chal : ∀ {a b : ℕ}, a ≤ 2 ^ 193 → b ≤ 2 ^ 193 →
    timeBoundT chalP (io2 (R := 254) a b 0) ≤ 2 ^ 458
  len_chal : ∀ {a b : ℕ}, a ≤ 2 ^ 193 → b ≤ 2 ^ 193 →
    lenBoundT chalP (io2 (R := 254) a b 0) ≤ io2 (2 ^ 197) 0 0
  time_sd : ∀ {a b : ℕ}, a ≤ 2 ^ 193 → b ≤ 2 ^ 193 → timeBoundT sdP (io2 (R := 80) a b 0) ≤ 2 ^ 520
  len_sd : ∀ {a b : ℕ}, a ≤ 2 ^ 193 → b ≤ 2 ^ 193 →
    lenBoundT sdP (io2 (R := 80) a b 0) ≤ io2 (2 ^ 259) 0 0
  size_setup : setupP.size ≤ 2 ^ 25
  size_pub : pubP.size ≤ 2 ^ 25
  size_chal : chalP.size ≤ 2 ^ 25
  size_sd : sdP.size ≤ 2 ^ 25
  nS_le : nI + nσ + 132 ≤ 2 ^ 193

variable {ienc senc setupI viewI sdI}
variable (S : StepComps ienc senc setupI viewI sdI)

/-- **The component programs of a step**, the key component `keyR S.sdP`. -/
noncomputable def StepComps.comps :
    Comps 254 (puCodes (ienc.prod senc)) (spPack (stOf ienc setupI) viewI sdI)
      (setupPack (instOf ienc) fun _ => setupI) (IWof ienc) (fun _ => True) where
  setupP := S.setupP
  pubP := S.pubP
  keyP := keyR S.sdP
  authP := authC
  chalP := S.chalP
  wf_setup := S.wf_setup
  wf_pub := S.wf_pub
  wf_key := wf_keyPF S.sd.wf eF (frontSpec_frontBP confP.L).wf wfSpec_wfR.wf cfP
  wf_auth := authC_spec.wf
  wf_chal := S.wf_chal
  law_setup w x hw := by
    obtain ⟨i, rfl⟩ := hw
    rw [S.law_setup i x, setupPack, PMF.map_comp, instOf_cons]
    rfl
  ok_setup _ _ _ _ _ := trivial
  law_pub σ _ := S.law_pub σ
  law_key σ C _ := law_keyP_spPack (stOf ienc setupI) viewI sdI S.sd frEmb_eF
    (frontSpec_frontBP confP.L) wfSpec_wfR cfP cfP_valid σ trivial C
  law_auth C x := authC_spec.law C x
  law_chal σ μ _ := S.law_chal σ μ

include S in
theorem stateBound_le :
    stateBound (puCodes (ienc.prod senc)) (2 ^ 193) ≤ 2 ^ 193 := by
  have h := S.nS_le
  show max (2 ^ 193) (1 + nA + (nI + nσ) + 3) ≤ 2 ^ 193
  rw [show nA = 128 from rfl]
  generalize (2 : ℕ) ^ 193 = Z at *
  omega

include S in
theorem sigBound_le : sigBound (puCodes (ienc.prod senc)) (2 ^ 193) ≤ 2 ^ 193 := by
  have := stateBound_le S
  unfold sigBound
  omega

variable {Ts Ls Tk Lk Sk : ℕ} (hkey : KeyRCost Ts Ls Tk Lk Sk) (hTs : 520 ≤ Ts) (hLs : 259 ≤ Ls)
include hkey hTs hLs

theorem time_sd_le : timeBoundT S.sdP
    (io2 (R := 80) (sigBound (puCodes (ienc.prod senc)) (2 ^ 193)) 0 0) ≤ 2 ^ Ts :=
  (S.time_sd (sigBound_le S) (by positivity)).trans (Nat.pow_le_pow_right (by norm_num) hTs)

theorem len_sd_le : lenBoundT S.sdP
    (io2 (R := 80) (sigBound (puCodes (ienc.prod senc)) (2 ^ 193)) 0 0) ≤ io2 (2 ^ Ls) 0 0 :=
  (S.len_sd (sigBound_le S) (by positivity)).trans
    (Prog.io2_mono (Nat.pow_le_pow_right (by norm_num) hLs) le_rfl)

/-- **The length bounds of the components of a step.** -/
noncomputable def StepComps.bounds : CompBoundsP S.comps confP.L (2 ^ 193) where
  Ssig := 2 ^ 195
  Lp := 2 ^ 196
  Lk := 2 ^ Lk
  La := 1
  Lc := 2 ^ 197
  len_setup := S.len_setup (stateBound_le S) le_rfl
  len_pub := S.len_pub le_rfl (by positivity)
  len_key := hkey.len (sigBound_le S) (time_sd_le S hkey hTs hLs) (len_sd_le S hkey hTs hLs)
  len_auth := authC_spec.len confP_L_le (le_refl nA)
  len_chal := S.len_chal (sigBound_le S) (by show (1 : ℕ) ≤ 2 ^ 193; norm_num)

omit hkey hTs hLs in
include S in
theorem length_true_enc (i : Inst) : (true :: ienc.enc i).length ≤ 2 ^ 193 := by
  have h := S.nS_le
  rw [List.length_cons, ienc.length]
  generalize (2 : ℕ) ^ 193 = Z at *
  omega

/-- **The bundle of a step.** -/
noncomputable def StepComps.bundle : Bundle hkp confP ienc setupI viewI sdI where
  R := 254
  nS := nI + nσ
  sig := ienc.prod senc
  st := stOf ienc setupI
  inst := instOf ienc
  IW := IWof ienc
  Ok := fun _ => True
  cs := S.comps
  W := 2 ^ 193
  cb := S.bounds hkey hTs hLs
  L := 2 ^ 191
  hpubL σ _ := by
    show ((pkEnc hkp confP).enc _).length ≤ _
    rw [length_enc_fixLen]; exact lenPK_le
  hkeyL σ C _ _ := length_KGsim_le _ C
  hchalL σ μ _ ct hct := by
    rw [show (spPack (stOf ienc setupI) viewI sdI).chal σ μ = PMF.pure _ from rfl,
      PMF.mem_support_pure_iff] at hct
    subst hct
    rw [length_enc_fixLen]; exact fixLen_ctEnc_le
  hinv := instOf_cons ienc
  hIW i := ⟨⟨i, rfl⟩, length_true_enc S i⟩

/-- **The time of the components of a step**: at most `2^651` for `Tk ≤ 650`. -/
theorem compTime_le (hTk : Tk ≤ 650) : compTimeP (S.bounds hkey hTs hLs) ≤ 2 ^ 651 := by
  have h1 := S.time_setup (stateBound_le S) le_rfl
  have h2 := S.time_pub (a := 2 ^ 195) (b := 0) le_rfl (by positivity)
  have h3 := hkey.time (sigBound_le S) (time_sd_le S hkey hTs hLs) (len_sd_le S hkey hTs hLs)
  have h4 := authC_spec.time (a := confP.L) (b := nA) confP_L_le le_rfl
  have h5 := S.time_chal (a := sigBound (puCodes (ienc.prod senc)) (2 ^ 193)) (b := 1)
    (sigBound_le S) (by show (1 : ℕ) ≤ 2 ^ 193; norm_num)
  have hT' : (2 : ℕ) ^ Tk ≤ 2 ^ 650 := Nat.pow_le_pow_right (by norm_num) hTk
  have e : (2 : ℕ) ^ 394 + 2 ^ 458 + 2 ^ 650 + 2 ^ 109 + 2 ^ 458 ≤ 2 ^ 651 := by norm_num
  exact le_trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h1 h2)
    (h3.trans hT')) h4) h5) e

omit hTs hLs in
/-- **The states of the components of a step**, the selection's twice. -/
theorem sizes_le (hSk : Sk ≤ 2 ^ 198 + 2 ^ 196) :
    2 * (S.comps.setupP.size + S.comps.pubP.size) + S.comps.keyP.size + S.comps.authP.size +
      S.comps.chalP.size ≤ 2 ^ 198 + 2 ^ 196 + 2 ^ 28 := by
  have hk := hkey.size S.size_sd
  have h1 := S.size_setup
  have h2 := S.size_pub
  have h4 := authC_spec.size
  have h5 := S.size_chal
  show 2 * (S.setupP.size + S.pubP.size) + (keyR S.sdP).size + authC.size + S.chalP.size ≤ _
  have : 2 * ((2 : ℕ) ^ 25 + 2 ^ 25) + 2 ^ 18 + 2 ^ 25 ≤ 2 ^ 28 := by norm_num
  generalize (2 : ℕ) ^ 198 + 2 ^ 196 = Z at *
  omega

end Step

/-! ### The constant -/

/-- **The numerical bound on the constant at `confP`**: decoder `≤ 2^16` states, `≤ 2^380` steps,
`14` tapes; components `R = 254` tapes, at most `2^198 + 2^196 + 2^28` states (`Sz2`); the cut
`2^49`; the slope `≤ 2^656`. -/
noncomputable def Cst : ℕ :=
  60 * compStatesG 128 1 515 (2 ^ 16) (2 ^ 198 + 2 ^ 196 + 2 ^ 28) (2 ^ 49) 656 * 3 ^ (14 + 254 + 30) *
      (5 + 4 * (14 + 254 + 30) + 215) +
    11 * 2 ^ 380 + 11 * 2 ^ 656 + 24

theorem compBound_confA {Sz2 Sl : ℕ} (hSz : Sz2 ≤ 2 ^ 198 + 2 ^ 196 + 2 ^ 28) (hSl : Sl ≤ 2 ^ 656) :
    compBoundG 128 1 515 (2 ^ 16) (2 ^ 380) 14 254 Sz2 (2 ^ 49) Sl 656 ≤ Cst := by
  have hS : compStatesG 128 1 515 (2 ^ 16) Sz2 (2 ^ 49) 656 ≤
      compStatesG 128 1 515 (2 ^ 16) (2 ^ 198 + 2 ^ 196 + 2 ^ 28) (2 ^ 49) 656 :=
    compStatesG_mono le_rfl hSz le_rfl
  have hS0 : compStatesG 128 1 515 (2 ^ 16) (2 ^ 198 + 2 ^ 196 + 2 ^ 28) (2 ^ 49) 656 < 2 ^ 215 := by
    unfold compStatesG postStatesG glue3; norm_num
  have hz : Nat.size (compStatesG 128 1 515 (2 ^ 16) Sz2 (2 ^ 49) 656) ≤ 215 :=
    Nat.size_le.mpr (hS.trans_lt hS0)
  unfold compBoundG Cst
  gcongr

/-- **The strength from the constant**: `64 · (2^128)² · Cst ≤ 2^965`. -/
theorem kb_confA : 64 * ((2 : ℝ) ^ 128) ^ 2 * (Cst : ℝ) ≤ 2 ^ 965 := by
  have h : 64 * (2 ^ 128) ^ 2 * Cst ≤ 2 ^ 965 := by
    unfold Cst compStatesG postStatesG glue3; norm_num
  exact_mod_cast h

section Step

variable {Inst Sec : Type} [Nonempty Inst] {nI nσ : ℕ} {ienc : FixedEnc Inst nI}
  {senc : FixedEnc Sec nσ} {setupI : PUniv.Attr → PMF Sec}
  {viewI : Inst → Sec → PK hkp confP × CT hkp confP} {sdI : Inst → Sec → SimData hkp confP}
  (S : StepComps ienc senc setupI viewI sdI)
  {Ts Ls Tk Lk Sk : ℕ} (hkey : KeyRCost Ts Ls Tk Lk Sk) (hTs : 520 ≤ Ts) (hLs : 259 ≤ Ls)

/-- **The constant of the reduction of a step**, for a decoder with at most `2^16` states,
`2^380` steps and `14` tapes: at most `Cst` when `Tk ≤ 650`, `Lk ≤ 270`, `Sk ≤ 2^198 + 2^196`. -/
theorem const_le (hTk : Tk ≤ 650) (hLk : Lk ≤ 270) (hSk : Sk ≤ 2 ^ 198 + 2 ^ 196) (P : Machine)
    (hsP : P.states ≤ 2 ^ 16) (htP : P.time ≤ 2 ^ 380) (hpP : P.tapes ≤ 14) :
    (S.bundle hkey hTs hLs).const P ≤ Cst := by
  unfold Bundle.const
  have hX : ∀ {e : ℕ}, e ≤ 270 → (2 : ℕ) ^ e ≤ 2 ^ 270 := fun h =>
    Nat.pow_le_pow_right (by norm_num) h
  have hnS : nI + nσ ≤ 2 ^ 270 := by
    have h := S.nS_le
    have : (2 : ℕ) ^ 193 ≤ 2 ^ 270 := hX (by norm_num)
    omega
  have hcL : confP.L ≤ 2 ^ 270 := confP_L_le.trans (hX (by norm_num))
  have hst : 11 * 2 ^ 651 + 2 ^ 26 * (2 ^ 270 * 2 ^ 270) ≤ (2 : ℕ) ^ 656 := by norm_num
  refine (compConst_le_bp (S.comps) (S.bounds hkey hTs hLs) P (2 ^ 191) (2 ^ 16) (2 ^ 380) 14
    (2 ^ 198 + 2 ^ 196 + 2 ^ 28) (2 ^ 49) (2 ^ 651) (2 ^ 270) 656 hsP htP hpP
    (sizes_le S hkey hSk) (compTime_le S hkey hTs hLs hTk) Nat.one_le_two_pow
    (hX (by norm_num)) (hX (by norm_num)) (hX hLk) (Nat.one_le_two_pow) (hX (by norm_num))
    (hX (by norm_num)) hnS hcL (hX (by norm_num)) confP_L_le (by norm_num) hst).trans ?_
  exact compBound_confA le_rfl hst

end Step

/-! ### The three steps -/

section Steps

/-- **The components of hybrid 3.** -/
noncomputable def step3 : StepComps (inst3Enc (N := Np) (K := Kp) (k := kp)) (sec3Enc hkp confP)
    (setup3 hkp confP) (view3 hkp confP) (sd3 hkp confP) where
  setupP := setup3D
  pubP := pub3L hkp confP
  chalP := chal3L hkp confP
  sdP := sd3P hkp confP
  wf_setup := wf_setup3D
  wf_pub := wf_pub3L hkp confP
  wf_chal := wf_chal3L hkp confP
  sd := sdSpec3 hkp confP Np_pos Kp_pos
  law_setup := law_setup3D
  law_pub p := law_pub3L hkp confP Np_pos Kp_pos _ p
  law_chal p μ := law_chal3L hkp confP Np_pos Kp_pos _ p μ
  time_setup ha hb := time_setup3D_conf ha hb
  len_setup ha hb := len_setup3D_conf ha hb
  time_pub ha hb := time_pub3L_conf ha hb
  len_pub ha hb := len_pub3L_conf ha hb
  time_chal ha hb := time_chal3L_conf ha hb
  len_chal ha hb := len_chal3L_conf ha hb
  time_sd ha hb := time_sd3P_conf ha hb
  len_sd ha hb := len_sd3P_conf ha hb
  size_setup := size_setup3D_conf
  size_pub := size_pub3L_conf.trans (by norm_num)
  size_chal := size_chal3L_conf
  size_sd := size_sd3P_conf
  nS_le := nS3_conf

/-- **The components of hybrid 5.** -/
noncomputable def step5 : StepComps (inst5Enc (N := Np) (K := Kp) (k := kp) confP.d)
    (sec5Enc hkp confP) (setup5 hkp confP) (view5 hkp confP) (sd5 hkp confP) where
  setupP := setup5D
  pubP := pub5L hkp confP
  chalP := chal5L hkp confP
  sdP := sd5P hkp confP
  wf_setup := wf_setup5D
  wf_pub := wf_pub5L hkp confP
  wf_chal := wf_chal5L hkp confP
  sd := sdSpec5 hkp confP Np_pos Kp_pos
  law_setup := law_setup5D
  law_pub p := law_pub5L hkp confP Np_pos Kp_pos _ p
  law_chal p μ := law_chal5L hkp confP Np_pos Kp_pos _ p μ
  time_setup ha hb := time_setup5D_conf ha hb
  len_setup ha hb := len_setup5D_conf ha hb
  time_pub ha hb := time_pub5L_conf ha hb
  len_pub ha hb := len_pub5L_conf ha hb
  time_chal ha hb := time_chal5L_conf ha hb
  len_chal ha hb := len_chal5L_conf ha hb
  time_sd ha hb := time_sd5P_conf ha hb
  len_sd ha hb := len_sd5P_conf ha hb
  size_setup := size_setup5D_conf
  size_pub := size_pub5L_conf.trans (by norm_num)
  size_chal := size_chal5L_conf
  size_sd := size_sd5P_conf
  nS_le := nS5_conf

/-- **The components of the ideal side.** -/
noncomputable def stepI : StepComps (inst3Enc (N := Np) (K := Kp) (k := kp)) (secIEnc hkp confP)
    (setupI hkp confP) (viewI hkp confP) (sdI hkp confP) where
  setupP := setupID
  pubP := pubIL hkp confP
  chalP := chalIL2 hkp confP
  sdP := sdIP hkp confP
  wf_setup := wf_setupID
  wf_pub := wf_pubIL hkp confP
  wf_chal := wf_chalIL2 hkp confP
  sd := sdSpecI hkp confP Np_pos Kp_pos
  law_setup := law_setupID
  law_pub p := law_pubIL hkp confP Np_pos Kp_pos _ p
  law_chal p μ := law_chalIL2 hkp confP Np_pos Kp_pos _ p μ
  time_setup ha hb := time_setupID_conf ha hb
  len_setup ha hb := len_setupID_conf ha hb
  time_pub ha hb := time_pubIL_conf ha hb
  len_pub ha hb := len_pubIL_conf ha hb
  time_chal ha hb := (time_chalIL2_conf ha hb).trans (by norm_num)
  len_chal ha hb := len_chalIL2_conf ha hb
  time_sd ha hb := time_sd3P_conf ha hb
  len_sd ha hb := len_sd3P_conf ha hb
  size_setup := size_setupID_conf
  size_pub := size_pubIL_conf.trans (by norm_num)
  size_chal := size_chalIL2_conf.trans (by norm_num)
  size_sd := size_sdIP_conf
  nS_le := nSI_conf

end Steps

/-! ### Attribute hiding -/

variable {ms : Machines hkp confP}

/-- **Attribute hiding of the concrete scheme** at `confP`, for every choice of the machines
(`impl hkp confP ms`), from the hardness of decision Ring-LWE at the parameters of hybrids 3 and 5
with **`kb ≥ 965`** bits, given the cost of the reductions' key component (`KeyRCost Ts Ls Tk Lk Sk`
with `520 ≤ Ts`, `259 ≤ Ls`, `Tk ≤ 650`, `Lk ≤ 270`, `Sk ≤ 2^198 + 2^196`). Each reduction's
constant is at most `Cst` and `64 · (2^128)² · Cst ≤ 2^965`. -/
theorem attributeHiding_conf {Ts Ls Tk Lk Sk : ℕ} (hkey : KeyRCost Ts Ls Tk Lk Sk)
    (hTs : 520 ≤ Ts) (hLs : 259 ≤ Ls) (hTk : Tk ≤ 650) (hLk : Lk ≤ 270)
    (hSk : Sk ≤ 2 ^ 198 + 2 ^ 196) (kb : ℕ) (hkb : 965 ≤ kb)
    (hard3 : RingLWE.decision.HardAt (params3 Np (2 ^ Kp) kp (.cbd 16)) kb)
    (hard5 : RingLWE.decision.HardAt (params5 Np (2 ^ Kp) kp (Fin confP.d) (.cbd 16)) kb) :
    AttributeHiding PUniv params (impl hkp confP ms) := by
  have hC : ∀ {Inst Sec : Type} [Nonempty Inst] {nI nσ : ℕ} {ienc : FixedEnc Inst nI}
      {senc : FixedEnc Sec nσ} {setupI : PUniv.Attr → PMF Sec}
      {viewI : Inst → Sec → PK hkp confP × CT hkp confP} {sdI : Inst → Sec → SimData hkp confP}
      (S : StepComps ienc senc setupI viewI sdI) (P : Machine), P.states ≤ 2 ^ 16 →
      P.time ≤ 2 ^ 380 → P.tapes ≤ 14 →
      ((S.bundle hkey hTs hLs).const P : ℝ) ≤ (Cst : ℝ) := by
    intro _ _ _ _ _ _ _ _ _ _ S P h1 h2 h3
    exact_mod_cast const_le S hkey hTs hLs hTk hLk hSk P h1 h2 h3
  refine attributeHiding_of_comps_rlwe (fun u => hdecp u) realCovered_conf hL_conf simCovered_conf
    flood_conf statTerm_conf_ne_top stat_conf (.cbd 16) hχ_conf
    (step3.bundle hkey hTs hLs) (step5.bundle hkey hTs hLs) (stepI.bundle hkey hTs hLs) kb
    (Cst : ℝ) (by unfold Cst; positivity)
    (hC step3 _ states_dec3M_confA time_dec3M_confA (le_of_eq tapes_dec3M))
    (hC step5 _ states_dec5M_confA time_dec5M_confA (le_of_eq (tapes_dec5M _)))
    (hC stepI _ states_dec3M_confA time_dec3M_confA (le_of_eq tapes_dec3M)) ?_ hard3 hard5
  rw [show params.secBits = 128 from rfl]
  exact kb_confA.trans (pow_le_pow_right₀ (by norm_num) hkb)

theorem params3_conf : params3 Np (2 ^ Kp) kp (.cbd 16) =
    params3 (2 ^ 34) (2 ^ (2 ^ 26)) (2 ^ 26 + 1) (.cbd 16) := by
  rw [Np_def, kp, Kp_def]

theorem params5_conf : params5 Np (2 ^ Kp) kp (Fin confP.d) (.cbd 16) =
    params5 (2 ^ 34) (2 ^ (2 ^ 26)) (2 ^ 26 + 1) (Fin (2 ^ 62)) (.cbd 16) := by
  show params5 Np (2 ^ Kp) kp (Fin dp) (.cbd 16) = _
  rw [Np_def, kp, Kp_def, dp_def]

/-- **The registry's strength covers the strength needed**: `965 ≤ 1158 ≤ RingLWE.H` at the
parameters of hybrids 3 and 5. -/
theorem registry_covers_kb :
    965 ≤ RingLWE.H (params3 Np (2 ^ Kp) kp (.cbd 16)) ∧
      965 ≤ RingLWE.H (params5 Np (2 ^ Kp) kp (Fin confP.d) (.cbd 16)) := by
  refine ⟨(show 965 ≤ 1158 by norm_num).trans ?_, (show 965 ≤ 1158 by norm_num).trans ?_⟩
  · rw [params3_conf]; exact Strength.ringLWE_H_registry3
  · rw [params5_conf]; exact Strength.ringLWE_H_registry5

/-- **Attribute hiding of the concrete scheme from the registry's decision Ring-LWE**: the
assumption `RingLWE.decision.Holds` gives `HardAt` at `965 ≤ 1158 ≤ RingLWE.H` bits. -/
theorem attributeHiding_conf_registry (hR : RingLWE.decision.Holds) {Ts Ls Tk Lk Sk : ℕ}
    (hkey : KeyRCost Ts Ls Tk Lk Sk) (hTs : 520 ≤ Ts) (hLs : 259 ≤ Ls) (hTk : Tk ≤ 650)
    (hLk : Lk ≤ 270) (hSk : Sk ≤ 2 ^ 198 + 2 ^ 196) :
    AttributeHiding PUniv params (impl hkp confP ms) :=
  attributeHiding_conf hkey hTs hLs hTk hLk hSk 965 le_rfl
    (hR.hardAt (p := params3 Np (2 ^ Kp) kp (.cbd 16)) registry_covers_kb.1)
    (hR.hardAt (p := params5 Np (2 ^ Kp) kp (Fin confP.d) (.cbd 16)) registry_covers_kb.2)

/-- **The cost of the reductions' key component at `confA`** as used here (`KeyRCost` with the
SimData bounds `2^520` steps and `2^259` bits, at most `2^650` steps, `2^270` bits per tape and
`2^198 + 2^196` states). -/
def KeyRConfA : Prop :=
  ∃ Tk Lk Sk : ℕ, KeyRCost 520 259 Tk Lk Sk ∧ Tk ≤ 650 ∧ Lk ≤ 270 ∧ Sk ≤ 2 ^ 198 + 2 ^ 196

/-- **Attribute hiding of the concrete scheme from `kb ≥ 965` bits of decision Ring-LWE** at the
parameters of hybrids 3 and 5, given the cost of the reductions' key component (`KeyRConfA`). -/
theorem attributeHiding_conf_rlwe (hkey : KeyRConfA) (kb : ℕ) (hkb : 965 ≤ kb)
    (hard3 : RingLWE.decision.HardAt (params3 Np (2 ^ Kp) kp (.cbd 16)) kb)
    (hard5 : RingLWE.decision.HardAt (params5 Np (2 ^ Kp) kp (Fin confP.d) (.cbd 16)) kb) :
    AttributeHiding PUniv params (impl hkp confP ms) := by
  obtain ⟨Tk, Lk, Sk, h, hTk, hLk, hSk⟩ := hkey
  exact attributeHiding_conf h le_rfl le_rfl hTk hLk hSk kb hkb hard3 hard5

end AdvancedEncryption.RingBTVW
