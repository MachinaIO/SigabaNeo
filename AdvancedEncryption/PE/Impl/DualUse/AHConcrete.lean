import PE.Impl.DualUse.AHComps
import PE.Impl.DualUse.Prog.SetupL
import PE.Impl.DualUse.Prog.AuthL
import PE.Impl.DualUse.Prog.DecodeCost
import PE.Impl.DualUse.Prog.KeyCostP
import PE.Impl.DualUse.Params.Advantage
import PE.Impl.DualUse.Params.Strength
import PE.Impl.DualUse.ImplP

/-!
# Attribute hiding of the concrete scheme

At the configuration `confP` (`N = 2^34`, `K = 2^25`, `k = K + 1`, `|Wd| = 2^61`), the three
reductions are assembled from their component programs (`Comps` at `R = 254`, the length bounds
`CompBoundsP`, the `Bundle`s of `AHComps`), and the constant of each reduction is bounded through
`compConst_le_two_pow`: **at most `2^2383`**. With `64 · 2^256 · 2^2383 = 2^2645`, attribute hiding
follows from the hardness of decision Ring-LWE at `params3`, `params5` with `kb = 2645 ≤ 2650`
bits, which the registry's strength gives (`ringLWE_H_registry3/5 : 2650 ≤ RingLWE.H`).

**The one input not proven here: the `W_f` block** `wfB` of the key component. It enters through
* its law, `WfSpec hkp confP wfB Wg` (the key component's law needs it), and
* **`WfCost wfB Wg T`**: on its input inside the key component (`wfIn (2^240) (frontL confP.L Wg)`:
  the SimData word on tape `0`, the gate list of a window predicate on tape `1`), at most `2^T`
  steps, every tape at most `2^250` bits afterwards, at most `2^200` states,

for a window width `384 ≤ Wg ≤ 2^200` and **`T ≤ 2370`**. Everything else is discharged: the
statistical terms (`Params/Advantage`, `Params/Stat`), the covering of the simulated trapdoor
(`simCovered_conf`), the laws and costs of the setup, public-key, authorization, challenge,
SimData and decoding components (`SetupL`, `CompCost`, `AuthL`, `DecodeCost`), the key component
around `wfB` (`KeyCostP`).

* `attributeHiding_conf`: from `HardAt (params3 …) kb` and `HardAt (params5 …) kb`, `2645 ≤ kb`;
* `attributeHiding_conf_registry`: from `RingLWE.decision.Holds` (the registry's assumption);
* `attributeHiding_implP_registry`: the same for the compiled implementation `implP`.
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib
  Cslib.Probability SigabaNeo.Tape SigabaNeo.Tape.XProg
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord AdvancedEncryption.PE.Generic
open AdvancedEncryption.DualUse.Prog AdvancedEncryption.DualUse.Params
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option exponentiation.threshold 3000

/-! ### The hypothesis on the `W_f` block -/

/-- **The cost of the `W_f` block** (the input of the key component not proven here): on the word
of the simulation data (at most `2^240` bits, tape `0`) and the gate list of a window predicate
(at most `frontL confP.L Wg` bits, the front end's output bound, tape `1`), every other tape
blank, `wfB` takes at most `2^T` steps and leaves every tape at most `2^250` bits; it has at most
`2^200` states. -/
structure WfCost (wfB : XProg 256) (Wg T : ℕ) : Prop where
  time : timeBoundT wfB (wfIn (2 ^ 240) (frontL confP.L Wg)) ≤ 2 ^ T
  len : ∀ i, lenBoundT wfB (wfIn (2 ^ 240) (frontL confP.L Wg)) i ≤ 2 ^ 250
  size : wfB.size ≤ 2 ^ 200

theorem WfCost.mono {wfB : XProg 256} {Wg T T' : ℕ} (h : WfCost wfB Wg T) (hT : T ≤ T') :
    WfCost wfB Wg T' :=
  ⟨h.time.trans (Nat.pow_le_pow_right (by norm_num) hT), h.len, h.size⟩

instance : NeZero confP.d := dp_ne

/-! ### Discharged hypotheses of `attributeHiding_of_comps` -/

/-- **The boxes cover the simulated trapdoor** at `confP` (the data are binary, `SimValid`). -/
theorem simCovered_conf : SimCovered hkp confP := fun d hv w hev y hy u =>
  (goodTrap_sim d.mpk d.Rm (attrBits d.x) d.W d.Ψ hv.2.2.1 hv.2.2.2 w
    (keyMatrix_simW d hv w hev)).2 y hy u

/-- The statistical part at `confP` with the flooding `ε = 2^{-148}`. -/
theorem statTerm_conf : statTerm confP hkp ((2 : ℝ≥0∞) ^ 148)⁻¹ ≤ ((2 : ℝ≥0∞) ^ 135)⁻¹ := by
  set x : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ 138)⁻¹
  have h1 := date_mul_le delta1_le
  have h6 := date_mul_le delta6_le
  have hε : (Fintype.card PUniv.Attr : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 148)⁻¹ ≤ x := by
    rw [card_date]; exact le_of_eq (two_pow_mul_inv 10 138)
  rw [statTerm_eq_date]
  calc _ ≤ x + x + x + x + x := by gcongr
    _ = 5 * x := by ring
    _ ≤ 2 ^ 3 * x := by gcongr; norm_num
    _ = ((2 : ℝ≥0∞) ^ 135)⁻¹ := two_pow_mul_inv 3 135

theorem statTerm_conf_ne_top : statTerm confP hkp ((2 : ℝ≥0∞) ^ 148)⁻¹ ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.inv_ne_top.mpr (pow_ne_zero _ two_ne_zero)) statTerm_conf

theorem stat_conf :
    4 * (2 : ℝ) ^ params.secBits * (statTerm confP hkp ((2 : ℝ≥0∞) ^ 148)⁻¹).toReal ^ 2 ≤ 1 := by
  have h := ENNReal.toReal_mono (ENNReal.inv_ne_top.mpr (pow_ne_zero _ two_ne_zero)) statTerm_conf
  rw [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at h
  have h0 := ENNReal.toReal_nonneg (a := statTerm confP hkp ((2 : ℝ≥0∞) ^ 148)⁻¹)
  generalize (statTerm confP hkp ((2 : ℝ≥0∞) ^ 148)⁻¹).toReal = s at *
  have hs : s ^ 2 ≤ (((2 : ℝ) ^ 135)⁻¹) ^ 2 := pow_le_pow_left₀ h0 h 2
  have hp : (params.secBits : ℕ) = 128 := rfl
  rw [hp]
  calc 4 * (2 : ℝ) ^ 128 * s ^ 2 ≤ 4 * 2 ^ 128 * (((2 : ℝ) ^ 135)⁻¹) ^ 2 := by gcongr
    _ ≤ 1 := by norm_num

theorem hχ_conf : χR confP = polyOf (N := Np) (ModuleLWE.coeffLaw (2 ^ Kp) (.cbd 16)) := rfl

/-! ### The lengths of the answers -/

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 1000 in
theorem fixLen_skEnc_le : fixLen (skEnc hkp confP) ≤ 2 ^ 200 := by
  simp only [fixLen, skEnc]; comp_unfold; norm_num

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 1000 in
theorem fixLen_ctEnc_le : fixLen (ctEnc hkp confP) ≤ 2 ^ 200 := by
  simp only [fixLen]; comp_unfold; norm_num

theorem length_KGsim_le (d : SimData hkp confP) (C : List Bool) :
    ∀ sk ∈ (KGsim d C).support, sk.length ≤ 2 ^ 200 := by
  intro sk hsk
  unfold KGsim at hsk
  split_ifs at hsk
  · obtain ⟨o, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hsk
    rw [length_enc_fixLen]; exact fixLen_skEnc_le
  · rw [PMF.mem_support_pure_iff] at hsk; subst hsk
    rw [length_enc_fixLen]; exact fixLen_skEnc_le
  · rw [PMF.mem_support_pure_iff] at hsk; subst hsk; simp

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
  time_setup : ∀ {a b : ℕ}, a ≤ 2 ^ 180 → b ≤ 10 → timeBoundT setupP (io2 (R := 254) a b 0) ≤ 2 ^ 403
  len_setup : ∀ {a b : ℕ}, a ≤ 2 ^ 180 → b ≤ 10 →
    lenBoundT setupP (io2 (R := 254) a b 0) ≤ io2 (2 ^ 182) 0 0
  time_pub : ∀ {a b : ℕ}, a ≤ 2 ^ 182 → b ≤ 2 ^ 182 →
    timeBoundT pubP (io2 (R := 254) a b 0) ≤ 2 ^ 425
  len_pub : ∀ {a b : ℕ}, a ≤ 2 ^ 182 → b ≤ 2 ^ 182 →
    lenBoundT pubP (io2 (R := 254) a b 0) ≤ io2 (2 ^ 183) 0 0
  time_chal : ∀ {a b : ℕ}, a ≤ 2 ^ 180 → b ≤ 2 ^ 180 →
    timeBoundT chalP (io2 (R := 254) a b 0) ≤ 2 ^ 440
  len_chal : ∀ {a b : ℕ}, a ≤ 2 ^ 180 → b ≤ 2 ^ 180 →
    lenBoundT chalP (io2 (R := 254) a b 0) ≤ io2 (2 ^ 182) 0 0
  time_sd : ∀ {a b : ℕ}, a ≤ 2 ^ 180 → b ≤ 2 ^ 180 → timeBoundT sdP (io2 (R := 80) a b 0) ≤ 2 ^ 500
  len_sd : ∀ {a b : ℕ}, a ≤ 2 ^ 180 → b ≤ 2 ^ 180 →
    lenBoundT sdP (io2 (R := 80) a b 0) ≤ io2 (2 ^ 240) 0 0
  size_setup : setupP.size ≤ 2 ^ 25
  size_pub : pubP.size ≤ 2 ^ 25
  size_chal : chalP.size ≤ 2 ^ 25
  size_sd : sdP.size ≤ 2 ^ 25
  nS_le : nI + nσ + 14 ≤ 2 ^ 180

variable {ienc senc setupI viewI sdI}
variable (S : StepComps ienc senc setupI viewI sdI) (wfB : XProg 256) (Wg : ℕ)
  (hwf : WfSpec hkp confP wfB Wg)

theorem hL_conf : dateBound ≤ confP.L := by rw [confP_L]

/-- **The authorization component of the reductions** and its interface (`AuthSpec`): the
reductions use only `authC_spec`. -/
abbrev authC : XProg 256 := authL

theorem authC_spec : AuthSpec hkp confP authC (2 ^ 240) 275 19 := authSpec_authL hkp confP hL_conf

/-- **The component programs of a step**, the key component `keyP … sdP wfB Wg cfP`. -/
noncomputable def StepComps.comps :
    Comps 254 (puCodes (ienc.prod senc)) (spPack (stOf ienc setupI) viewI sdI)
      (setupPack (instOf ienc) fun _ => setupI) (IWof ienc) (fun _ => True) where
  setupP := S.setupP
  pubP := S.pubP
  keyP := keyP hkp confP S.sdP wfB Wg cfP
  authP := authC
  chalP := S.chalP
  wf_setup := S.wf_setup
  wf_pub := S.wf_pub
  wf_key := wf_keyP S.sd.wf hwf.wf Wg cfP
  wf_auth := authC_spec.wf
  wf_chal := S.wf_chal
  law_setup w x hw := by
    obtain ⟨i, rfl⟩ := hw
    rw [S.law_setup i x, setupPack, PMF.map_comp, instOf_cons]
    rfl
  ok_setup _ _ _ _ _ := trivial
  law_pub σ _ := S.law_pub σ
  law_key σ C _ := law_keyP_spPack (stOf ienc setupI) viewI sdI S.sd hwf cfP cfP_valid σ trivial C
  law_auth C x := authC_spec.law C x
  law_chal σ μ _ := S.law_chal σ μ

include S in
theorem stateBound_le :
    stateBound (puCodes (ienc.prod senc)) (2 ^ 180) ≤ 2 ^ 180 := by
  have h := S.nS_le
  show max (2 ^ 180) (1 + 10 + (nI + nσ) + 3) ≤ 2 ^ 180
  generalize (2 : ℕ) ^ 180 = Z at *
  omega

include S in
theorem sigBound_le : sigBound (puCodes (ienc.prod senc)) (2 ^ 180) ≤ 2 ^ 180 := by
  have := stateBound_le S
  unfold sigBound
  omega

variable {wfB Wg}
variable {T : ℕ} (hcost : WfCost wfB Wg T) (hW1 : 384 ≤ Wg) (hW2 : Wg ≤ 2 ^ 200)
include hcost hW1 hW2

theorem key_bounds :
    timeBoundT (keyP hkp confP S.sdP wfB Wg cfP)
        (io2 (R := 254) (sigBound (puCodes (ienc.prod senc)) (2 ^ 180)) confP.L 0) ≤
        2 ^ T + 2 ^ 2045 ∧
      lenBoundT (keyP hkp confP S.sdP wfB Wg cfP)
        (io2 (R := 254) (sigBound (puCodes (ienc.prod senc)) (2 ^ 180)) confP.L 0) ≤
        io2 (2 ^ 252) 0 0 :=
  time_keyP_conf (S.time_sd (sigBound_le S) (by positivity)) (S.len_sd (sigBound_le S) (by positivity))
    hW1 hW2 hcost.time hcost.len

/-- **The length bounds of the components of a step.** -/
noncomputable def StepComps.bounds : CompBoundsP (S.comps wfB Wg hwf) confP.L (2 ^ 180) where
  Ssig := 2 ^ 182
  Lp := 2 ^ 183
  Lk := 2 ^ 252
  La := 1
  Lc := 2 ^ 182
  len_setup := S.len_setup (stateBound_le S) le_rfl
  len_pub := S.len_pub le_rfl (by positivity)
  len_key := (key_bounds S hcost hW1 hW2).2
  len_auth := authC_spec.len (confP_L_le.trans (by norm_num)) (le_refl nA)
  len_chal := S.len_chal (sigBound_le S) (by show (1 : ℕ) ≤ 2 ^ 180; norm_num)

omit hcost hW1 hW2 in
include S in
theorem length_true_enc (i : Inst) : (true :: ienc.enc i).length ≤ 2 ^ 180 := by
  have h := S.nS_le
  rw [List.length_cons, ienc.length]
  generalize (2 : ℕ) ^ 180 = Z at *
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
  cs := S.comps wfB Wg hwf
  W := 2 ^ 180
  cb := S.bounds hwf hcost hW1 hW2
  L := 2 ^ 200
  hpubL σ _ := by
    show ((pkEnc hkp confP).enc _).length ≤ _
    rw [length_enc_fixLen, ← lenPK, lenPK_eq]; norm_num
  hkeyL σ C _ _ := length_KGsim_le _ C
  hchalL σ μ _ ct hct := by
    rw [show (spPack (stOf ienc setupI) viewI sdI).chal σ μ = PMF.pure _ from rfl,
      PMF.mem_support_pure_iff] at hct
    subst hct
    rw [length_enc_fixLen]; exact fixLen_ctEnc_le
  hinv := instOf_cons ienc
  hIW i := ⟨⟨i, rfl⟩, length_true_enc S i⟩

/-- **The time of the components of a step**: at most `2^2371` for `T ≤ 2370`. -/
theorem compTime_le (hT : T ≤ 2370) : compTimeP (S.bounds hwf hcost hW1 hW2) ≤ 2 ^ 2371 := by
  have h1 := S.time_setup (stateBound_le S) le_rfl
  have h2 := S.time_pub (a := 2 ^ 182) (b := 0) le_rfl (by positivity)
  have h3 := (key_bounds S hcost hW1 hW2).1
  have h4 := authC_spec.time (a := confP.L) (b := nA) (confP_L_le.trans (by norm_num)) le_rfl
  have h5 := S.time_chal (a := sigBound (puCodes (ienc.prod senc)) (2 ^ 180)) (b := 1)
    (sigBound_le S) (by show (1 : ℕ) ≤ 2 ^ 180; norm_num)
  have hT' : (2 : ℕ) ^ T ≤ 2 ^ 2370 := Nat.pow_le_pow_right (by norm_num) hT
  have hk' := h3.trans (Nat.add_le_add_right hT' (2 ^ 2045))
  exact le_trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h1 h2) hk') h4) h5)
    (by norm_num)

/-- **The constant of the reduction of a step**, for a decoder with at most `2^16` states,
`2^350` steps and `14` tapes: at most `2^2383` when `T ≤ 2370`. -/
theorem const_le (hT : T ≤ 2370) (P : Machine) (hsP : P.states ≤ 2 ^ 16) (htP : P.time ≤ 2 ^ 350)
    (hpP : P.tapes ≤ 14) : (S.bundle hwf hcost hW1 hW2).const P ≤ 2 ^ 2383 := by
  unfold Bundle.const
  have hkey : (keyP hkp confP S.sdP wfB Wg cfP).size ≤ 2 ^ 240 :=
    size_keyP_conf S.sdP S.size_sd wfB hcost.size hW1 hW2
  have hnS : nI + nσ ≤ 2 ^ 252 := by
    have h := S.nS_le
    have : (2 : ℕ) ^ 180 ≤ 2 ^ 252 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    generalize (2 : ℕ) ^ 180 = Z at *
    generalize (2 : ℕ) ^ 252 = Y at *
    omega
  refine (compConst_le_two_pow (S.comps wfB Wg hwf) (S.bounds hwf hcost hW1 hW2) P (2 ^ 200)
    270 2376 14 240 2371 252 20 298 11
    (hsP.trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
    (htP.trans (Nat.pow_le_pow_right (by norm_num) (by norm_num))) hpP
    (S.size_setup.trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
    (S.size_pub.trans (Nat.pow_le_pow_right (by norm_num) (by norm_num))) hkey
    (authC_spec.size.trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
    (S.size_chal.trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
    (compTime_le S hwf hcost hW1 hW2 hT)
    (show (2 : ℕ) ^ 182 ≤ 2 ^ 252 by norm_num) (show (2 : ℕ) ^ 183 ≤ 2 ^ 252 by norm_num)
    (show (2 : ℕ) ^ 252 ≤ 2 ^ 252 from le_rfl) (show (1 : ℕ) ≤ 2 ^ 252 by norm_num)
    (show (2 : ℕ) ^ 182 ≤ 2 ^ 252 by norm_num) (show (2 : ℕ) ^ 180 ≤ 2 ^ 252 by norm_num) hnS
    (confP_L_le.trans (by norm_num)) (show (2 : ℕ) ^ 200 ≤ 2 ^ 252 by norm_num) confP_L_le
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  norm_num

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
  time_pub ha hb := time_pub3L_conf' ha hb
  len_pub ha hb := len_pub3L_conf' ha hb
  time_chal ha hb := (time_chal3L_conf ha hb).trans (by norm_num)
  len_chal ha hb := (len_chal3L_conf ha hb).trans (Prog.io2_mono (by norm_num) le_rfl)
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
  time_pub ha hb := time_pub5L_conf' ha hb
  len_pub ha hb := len_pub5L_conf' ha hb
  time_chal ha hb := time_chal5L_conf ha hb
  len_chal ha hb := (len_chal5L_conf ha hb).trans (Prog.io2_mono (by norm_num) le_rfl)
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
  time_pub ha hb := time_pubIL_conf' ha hb
  len_pub ha hb := len_pubIL_conf' ha hb
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
with `kb ≥ 2645` bits, given a `W_f` block `wfB` meeting its specification at a window width
`384 ≤ Wg ≤ 2^200` and costing at most `2^T` steps, `T ≤ 2370` (`WfCost`). Each reduction's
constant is at most `2^2383`; `64 · 2^256 · 2^2383 = 2^2645`. -/
theorem attributeHiding_conf {wfB : XProg 256} {Wg T : ℕ} (hwf : WfSpec hkp confP wfB Wg)
    (hcost : WfCost wfB Wg T) (hT : T ≤ 2370) (hW1 : 384 ≤ Wg) (hW2 : Wg ≤ 2 ^ 200)
    (kb : ℕ) (hkb : 2645 ≤ kb)
    (hard3 : RingLWE.decision.HardAt (params3 Np (2 ^ Kp) kp (.cbd 16)) kb)
    (hard5 : RingLWE.decision.HardAt (params5 Np (2 ^ Kp) kp (Fin confP.d) (.cbd 16)) kb) :
    AttributeHiding PUniv params (impl hkp confP ms) := by
  have hC : ∀ {Inst Sec : Type} [Nonempty Inst] {nI nσ : ℕ} {ienc : FixedEnc Inst nI}
      {senc : FixedEnc Sec nσ} {setupI : PUniv.Attr → PMF Sec}
      {viewI : Inst → Sec → PK hkp confP × CT hkp confP} {sdI : Inst → Sec → SimData hkp confP}
      (S : StepComps ienc senc setupI viewI sdI) (P : Machine), P.states ≤ 2 ^ 16 →
      P.time ≤ 2 ^ 350 → P.tapes ≤ 14 →
      ((S.bundle hwf hcost hW1 hW2).const P : ℝ) ≤ (2 : ℝ) ^ 2383 := by
    intro _ _ _ _ _ _ _ _ _ _ S P h1 h2 h3
    exact_mod_cast const_le S hwf hcost hW1 hW2 hT P h1 h2 h3
  refine attributeHiding_of_comps_rlwe (fun u => hdecp u) realCovered_conf hL_conf simCovered_conf
    flood_conf statTerm_conf_ne_top stat_conf (.cbd 16) hχ_conf
    (step3.bundle hwf hcost hW1 hW2) (step5.bundle hwf hcost hW1 hW2)
    (stepI.bundle hwf hcost hW1 hW2) kb ((2 : ℝ) ^ 2383) (by positivity)
    (hC step3 _ states_dec3M_conf time_dec3M_conf (le_of_eq tapes_dec3M))
    (hC step5 _ states_dec5M_conf time_dec5M_conf (le_of_eq (tapes_dec5M _)))
    (hC stepI _ states_dec3M_conf time_dec3M_conf (le_of_eq tapes_dec3M)) ?_ hard3 hard5
  calc 64 * ((2 : ℝ) ^ params.secBits) ^ 2 * 2 ^ 2383 = 2 ^ 2645 := by
        rw [show params.secBits = 128 from rfl]; norm_num
    _ ≤ 2 ^ kb := pow_le_pow_right₀ (by norm_num) hkb

theorem params3_conf : params3 Np (2 ^ Kp) kp (.cbd 16) =
    params3 (2 ^ 34) (2 ^ (2 ^ 25)) (2 ^ 25 + 1) (.cbd 16) := by
  rw [Np_def, kp, Kp_def]

theorem params5_conf : params5 Np (2 ^ Kp) kp (Fin confP.d) (.cbd 16) =
    params5 (2 ^ 34) (2 ^ (2 ^ 25)) (2 ^ 25 + 1) (Fin (2 ^ 61)) (.cbd 16) := by
  show params5 Np (2 ^ Kp) kp (Fin dp) (.cbd 16) = _
  rw [Np_def, kp, Kp_def, dp_def]

/-- **Attribute hiding of the concrete scheme from the registry's decision Ring-LWE**: the
assumption `RingLWE.decision.Holds` gives `HardAt` at `RingLWE.H ≥ 2650` bits
(`ringLWE_H_registry3/5`), so at `kb = 2650`. -/
theorem attributeHiding_conf_registry (hR : RingLWE.decision.Holds) {wfB : XProg 256} {Wg T : ℕ}
    (hwf : WfSpec hkp confP wfB Wg) (hcost : WfCost wfB Wg T) (hT : T ≤ 2370) (hW1 : 384 ≤ Wg)
    (hW2 : Wg ≤ 2 ^ 200) :
    AttributeHiding PUniv params (impl hkp confP ms) := by
  have h3 : 2650 ≤ RingLWE.H (params3 Np (2 ^ Kp) kp (.cbd 16)) := by
    rw [params3_conf]; exact Strength.ringLWE_H_registry3
  have h5 : 2650 ≤ RingLWE.H (params5 Np (2 ^ Kp) kp (Fin confP.d) (.cbd 16)) := by
    rw [params5_conf]; exact Strength.ringLWE_H_registry5
  exact attributeHiding_conf hwf hcost hT hW1 hW2 2650 (by norm_num)
    (hR.hardAt (p := params3 Np (2 ^ Kp) kp (.cbd 16)) h3)
    (hR.hardAt (p := params5 Np (2 ^ Kp) kp (Fin confP.d) (.cbd 16)) h5)

/-- **Attribute hiding of the compiled implementation** `implP` at `confP`, from the registry's
decision Ring-LWE and the `W_f` block of the key component of the reductions. -/
theorem attributeHiding_implP_registry (hR : RingLWE.decision.Holds) (X : ChiSampler confP)
    {bfX cfX : XProg 256} {W W' : ℕ} (hbf : BfSpec hkp confP bfX W) (hcfX : CfSpec hkp confP cfX W')
    (hK2 : 2 ≤ Kp) {wfB : XProg 256} {Wg T : ℕ}
    (hwf : WfSpec hkp confP wfB Wg) (hcost : WfCost wfB Wg T) (hT : T ≤ 2370) (hW1 : 384 ≤ Wg)
    (hW2 : Wg ≤ 2 ^ 200) :
    AttributeHiding PUniv params (implP hkp confP X hbf hcfX cfP cfP_valid hK2) :=
  attributeHiding_conf_registry hR hwf hcost hT hW1 hW2

end AdvancedEncryption.DualUse
