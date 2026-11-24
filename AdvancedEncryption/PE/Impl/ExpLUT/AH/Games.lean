import PE.Impl.ExpLUT.AH.Unif
import PE.Impl.ExpLUT.GameChain
import PE.Impl.ExpLUT.SimKeys
import PE.Impl.ExpLUT.Prog.Eval
import PE.Impl.ExpLUT.Prog.Samplers
import PE.Impl.Game.Bridge
import PE.Impl.Game.Coins
import PE.Impl.Game.UntilBad

/-!
# The experiments of the implementation as experiments of the hybrids (package G)

For an implementation whose machines meet the specifications of package F (`ImplSpec`: `Setup`
realizes `setupLawW D (χbin D)`, `Enc` realizes `encLawW`, `KeyGen` realizes `keyLawW D kb` on
predicate words of at most `L` bits and answers the empty word on longer ones, `Eval` is
`evalMachineX`) and a simulator outputting the encoding of a ciphertext with independent `unifW`
entries (`SimSpec`):

* `real_eq_gameV`: the observable law of `PE.real` is the experiment `gameV` of package D with the
  secret law `realVW` (the machines' `Setup`, `Enc` of `0`) and the ideal key oracle `KGiW`
  (real keys have the ideal law on the support of `Setup` when the real trapdoor is covered,
  `RealCovW`); `realVW_close`: `realVW` is within `epsSetup` of package D's `hyb0`;
* `ideal_eq_gameV0`: the observable law of `PE.ideal` is the experiment `gameV0` (challenge `ct`
  itself, no shift) of the secret law `idealVW` (the machines' `Setup`, the simulator's `ctUW`);
  `gameV0_close`: within `|Attr| (epsSetup + epsCT)` of `gameV0` at package D's `Setup` and `ctU`,
  which is `gameV` at `idealView` (`gameV0_idealV_eq`: a uniform ciphertext absorbs the shift).
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open scoped ENNReal

instance fintypeAttr8 : Fintype (univ w8).Attr := inferInstanceAs (Fintype (Attribute w8))
instance decEqAttr8 : DecidableEq (univ w8).Attr := inferInstanceAs (DecidableEq (Attribute w8))

variable (D : Dims) (kb : KeyBoxes D) (L : ℕ)

/-! ### The specifications of the implementation -/

/-- `KeyGen` answers the empty word on predicate words longer than `L`. -/
def KeyLongSpec (M : Machine) : Prop :=
  ∀ (msk : MSKt D) (C : List Bool), ¬ C.length ≤ L →
    M.run (encodeTuple [pwW, (mskEnc D).enc msk, C]) = PMF.pure (encodeTuple [])

/-- **The machines of the implementation meet the specifications.** -/
structure ImplSpec (impl : Impl sig) (χs χ χfl : PMF (Rg D)) : Prop where
  setup : SetupSpec D (χbin D) (impl.machine .setup)
  enc : EncSpec D χs χ χfl (impl.machine .enc)
  key : KeySpec D kb L (impl.machine .keyGen)
  keyLong : KeyLongSpec D L (impl.machine .keyGen)
  eval : impl.machine .eval = evalMachineX

/-- **The simulator's specification**: the encoding of a ciphertext with independent `unifW`
entries. -/
def SimSpec (Sim : Machine) : Prop :=
  ∀ mpk : MPKt D, Sim.run (encodeTuple [pwW, (mpkEnc D).enc mpk]) =
    (ctUW D).map fun ct => encodeTuple [(ctEnc D).enc ct]

theorem decodeTuple_one_nil' : decodeTuple 1 (encodeTuple []) = [[]] := by
  unfold decodeTuple
  rw [dif_neg]
  · rfl
  · rintro ⟨xs, hl, he⟩
    match xs, hl with
    | [y], _ =>
      have := congrArg List.length he
      simp [encodeTuple, Turing.MultiTapeTM.length_frame] at this

theorem run_of_machine' {Alg : Type} {sig : Alg → AlgSig} (impl : Impl sig) (a : Alg)
    (pw : List Bool) (xs : List (List Bool)) {β : Type} (μ : PMF β)
    (outs : β → List (List Bool)) (hlen : ∀ v, (outs v).length = (sig a).outputs.length)
    (h : (impl.machine a).run (encodeTuple (pw :: xs)) = μ.map fun v => encodeTuple (outs v)) :
    impl.run a pw xs = μ.map outs := by
  unfold Impl.run
  rw [h, PMF.map_comp]
  congr 1
  funext v
  simp only [Function.comp_apply, ← hlen v, decodeTuple_encodeTuple]

/-- The binary law of the machines is package D's `bitLaw`. -/
theorem χbin_eq_bitLaw : χbin D = (bitLaw : PMF (Rg D)) := by
  unfold χbin bitLaw
  rw [show (fun u : List Bool => if u.headD false = true then (1 : Rg D) else 0) =
      bitVal ∘ (fun u : List Bool => u.headD false) from funext fun u => by
        rcases u with _ | ⟨a, t⟩
        · rfl
        · cases a <;> rfl, ← PMF.map_comp]
  congr 1
  unfold BitString.uniformList
  rw [PMF.map_comp]
  have e : (fun r : Fin 1 → Bool => (List.ofFn r).headD false) = (Equiv.funUnique (Fin 1) Bool) :=
    funext fun r => by simp [Equiv.funUnique]
  rw [show ((fun u : List Bool => u.headD false) ∘ List.ofFn) =
    (fun r : Fin 1 → Bool => (List.ofFn r).headD false) from rfl, e]
  exact Cslib.Probability.PMF.uniformOfFintype_map_equiv _

/-! ### The key oracles -/

/-- `KeyGen`'s answer on the encoding of `msk`. -/
noncomputable def KGreal (msk : MSKt D) (C : List Bool) : PMF (List Bool) :=
  if C.length ≤ L then (keyLawW D kb msk C).map (skEnc D).enc else PMF.pure []

open Classical in
/-- **The ideal key oracle**: the ideal key law of `M_F` (a function of `mpk`) for predicate words,
the zero key for the other short words, the empty word for long ones. -/
noncomputable def KGiW (mpk : MPKt D) (C : List Bool) : PMF (List Bool) :=
  if C.length ≤ L then
    if ValidC C then
      (idealKeyLaw (S := setting D) kb.Big kb.Small kb.hBig gadDec (helperMap D) mpk
        (bpOf (progOf C))).map fun o => (skEnc D).enc (mpk, keyOfOutput o)
    else PMF.pure ((skEnc D).enc (mpk, 0))
  else PMF.pure []

/-- The real trapdoor of every key of the machines' `Setup` is covered by the boxes. -/
def RealCovW : Prop :=
  ∀ v ∈ (setupLawW D (χbin D)).support, ∀ C : List Bool, ValidC C →
    ∀ x' ∈ kb.Small, ∀ y, x' + (show PIdx (Wb D) (Jh D) D.K (2 ^ D.b) → Rg D from
      realTrap (J := Jh D) (S := setting D) v.2.T (gadDec y)) ∈ kb.Big

variable {D kb L}

/-- **Real keys have the ideal law** on the support of the machines' `Setup`. -/
theorem KGreal_eq_KGiW (hcov : RealCovW D kb) (v : MPKt D × MSKt D)
    (hv : v ∈ (setupLawW D (χbin D)).support) (C : List Bool) :
    KGreal D kb L v.2 C = KGiW D kb L v.1 C := by
  obtain ⟨hm, hT, -⟩ := mem_support_setupLawW hv
  unfold KGreal KGiW keyLawW
  split_ifs with hL hw
  · have e := keyLaw_eq_ideal (S := setting D) kb.Big kb.Small kb.hBig gadDec gadZ_gadDec
      (helperMap D) v.1 (bpOf (progOf C)) _ (realTrap_good (helperMap D) v.1 _ v.2.T hT)
      (hcov v hv C hw)
    simp only [keyGenLaw, hm, e]
    exact (congrArg (PMF.map _) (PMF.map_comp _ _ _)).trans (PMF.map_comp _ _ _)
  · rw [PMF.pure_map, hm]
  · rfl

variable (D kb L)

open Classical in
/-- The flag of the experiment. -/
noncomputable def authW (impl : Impl sig) (C : List Bool) (x : Attribute w8) : Bool :=
  decide (Authorized (U := univ w8) params impl C x)

/-! ### The real experiment -/

/-- The secret law of the real experiment: the machines' `Setup` and `Enc` of `0`. -/
noncomputable def realVW (χs χ χfl : PMF (Rg D)) (x : Attribute w8) : PMF (MPKt D × CTt D) :=
  (setupLawW D (χbin D)).bind fun v => (encLawW D χs χ χfl v.1 x false).map fun ct => (v.1, ct)

/-- The experiment of the hybrids at the dimensions `D`. -/
noncomputable abbrev GV (impl : Impl sig) (A : Machine 3) (V : Attribute w8 → PMF (MPKt D × CTt D)) :=
  gameV (univ w8) (half D) (msgR D) (mpkEnc D).enc (ctEnc D).enc (KGiW D kb L) (authW impl)
    (A.machine.runOracle A.time (paramsWord (univ w8) params)) V

variable {D kb L}

theorem impl_setup {impl : Impl sig} (h : SetupSpec D (χbin D) (impl.machine .setup)) :
    PE.setup (U := univ w8) params impl =
      (setupLawW D (χbin D)).map fun v => ((mpkEnc D).enc v.1, (mskEnc D).enc v.2) := by
  unfold PE.setup
  rw [run_of_machine' impl .setup (paramsWord (univ w8) params) [] (setupLawW D (χbin D))
    (fun v => [(mpkEnc D).enc v.1, (mskEnc D).enc v.2]) (fun _ => rfl) h, PMF.map_comp]
  rfl

theorem impl_keyGen {impl : Impl sig} (hK : KeySpec D kb L (impl.machine .keyGen))
    (hKl : KeyLongSpec D L (impl.machine .keyGen)) (msk : MSKt D) (C : List Bool) :
    keyGen (U := univ w8) params impl ((mskEnc D).enc msk) C = KGreal D kb L msk C := by
  unfold keyGen KGreal
  split_ifs with hC
  · rw [run_of_machine' impl .keyGen (paramsWord (univ w8) params) [(mskEnc D).enc msk, C]
      (keyLawW D kb msk C) (fun sk => [(skEnc D).enc sk]) (fun _ => rfl) (hK msk C hC),
      PMF.map_comp]
    rfl
  · unfold Impl.run
    rw [show (impl.machine Alg.keyGen).run (encodeTuple [paramsWord (univ w8) params,
      (mskEnc D).enc msk, C]) = PMF.pure (encodeTuple []) from hKl msk C hC, PMF.pure_map,
      PMF.pure_map]
    have : (sig Alg.keyGen).outputs.length = 1 := rfl
    rw [this, decodeTuple_one_nil']
    rfl

theorem impl_enc {impl : Impl sig} {χs χ χfl : PMF (Rg D)}
    (h : EncSpec D χs χ χfl (impl.machine .enc)) (mpk : MPKt D) (x : Attribute w8) (μ : Bool) :
    enc (U := univ w8) params impl ((mpkEnc D).enc mpk) x μ =
      (encLawW D χs χ χfl mpk x μ).map (ctEnc D).enc := by
  unfold enc
  rw [run_of_machine' impl .enc (paramsWord (univ w8) params)
    [(mpkEnc D).enc mpk, (univ w8).encAttr x, (univ w8).encMsg μ] (encLawW D χs χ χfl mpk x μ)
    (fun ct => [(ctEnc D).enc ct]) (fun _ => rfl) (by exact h mpk x μ), PMF.map_comp]
  rfl


/-! ### The real experiment is the experiment of `realVW` -/

variable (D kb L)

/-- The challenge of the implementation, through the encodings. -/
noncomputable def CHreal (χs χ χfl : PMF (Rg D)) (mpk : MPKt D) (x : Attribute w8) (μ : Bool) :
    PMF (List Bool) :=
  (encLawW D χs χ χfl mpk x μ).map (ctEnc D).enc

/-- The challenger of the implementation as a generic challenger. -/
noncomputable def realSpec (impl : Impl sig) (χs χ χfl : PMF (Rg D)) :=
  Generic.implSpec (U := univ w8) params impl (mpkEnc D).enc (setupLawW D (χbin D))
    (KGreal D kb L) (CHreal D χs χ χfl)

/-- The challenge with given coins. -/
noncomputable def gReal (σ : Attribute w8 × MPKt D × MSKt D) (μ : Bool)
    (r : EncCoins (setting D) (Wb D) (Jh D) Pos) : List Bool :=
  (ctEnc D).enc (encrypt (helperMap D) wSt (half D) σ.2.1 (attrN σ.1) (msgR D μ) r)

/-- The secret `(mpk, ct₀)` of the hybrids from the secret with the coins. -/
noncomputable def toView (σ : (Attribute w8 × MPKt D × MSKt D) ×
    EncCoins (setting D) (Wb D) (Jh D) Pos) : MPKt D × CTt D :=
  (σ.1.2.1, encrypt (helperMap D) wSt (half D) σ.1.2.1 (attrN σ.1.1) 0 σ.2)

theorem msgR_false : msgR D false = 0 := by simp [msgR]

variable {D kb L}

/-- **The real experiment is the experiment of the secret law `realVW`** with the ideal key
oracle. -/
theorem real_eq_gameV [Nonempty (Wb D)] {impl : Impl sig} {χs χ χfl : PMF (Rg D)}
    (hI : ImplSpec D kb L impl χs χ χfl) (hcov : RealCovW D kb) (A : Machine 3) :
    (PE.real (univ w8) params impl A).map (fun r => (r.1, r.2.attr, r.2.msg, r.2.bad)) =
      GV D kb L impl A (realVW D χs χ χfl) := by
  have b1 := Generic.game_eq_generic params impl (mpkEnc D).enc (mskEnc D).enc
    (setupLawW D (χbin D)) (KGreal D kb L) (CHreal D χs χ χfl) (enc params impl)
    (impl_setup hI.setup) (impl_keyGen hI.key hI.keyLong) (fun mpk x μ => impl_enc hI.enc mpk x μ) A
  unfold PE.real
  rw [b1]
  unfold Machine.runWith GV gameV
  have hchal : ∀ σ μ, (realSpec D kb L impl χs χ χfl).chal σ μ =
      (encCoinsLaw (setting D) (Wb D) (Jh D) Pos χs χ χfl).map (gReal D σ μ) := by
    intro σ μ
    show (encLawW D χs χ χfl σ.2.1 σ.1 μ).map (ctEnc D).enc = _
    unfold encLawW encLaw
    rw [PMF.map_comp]
    rfl
  rw [show Generic.implSpec (U := univ w8) params impl (mpkEnc D).enc (setupLawW D (χbin D))
      (KGreal D kb L) (CHreal D χs χ χfl) = realSpec D kb L impl χs χ χfl from rfl,
    Generic.runWith_eagerCoins (realSpec D kb L impl χs χ χfl) _ (gReal D) hchal]
  set prog := A.machine.runOracle A.time (paramsWord (univ w8) params)
  set eag := Generic.eagerCoins (realSpec D kb L impl χs χ χfl)
    (encCoinsLaw (setting D) (Wb D) (Jh D) Pos χs χ χfl) (gReal D)
  set sp3 := (specV (univ w8) (half D) (msgR D) (mpkEnc D).enc (ctEnc D).enc (KGiW D kb L)
    (authW impl) (realVW D χs χ χfl)).comap (toView D) eag.setup
  have hsupp : ∀ x, ∀ σ ∈ (eag.setup x).support, ∃ v ∈ (setupLawW D (χbin D)).support,
      σ.1 = (x, v) := by
    intro x σ hσ
    simp only [eag, Generic.eagerCoins, realSpec, Generic.implSpec, PMF.mem_support_bind_iff,
      PMF.mem_support_map_iff] at hσ
    obtain ⟨σ₀, ⟨v, hv, rfl⟩, r, -, rfl⟩ := hσ
    exact ⟨v, hv, rfl⟩
  have hcongr := Generic.runWith_congr_support eag sp3 rfl (fun _ _ _ => rfl)
    (fun x σ hσ => by
      obtain ⟨v, hv, hσ1⟩ := hsupp x σ hσ
      rcases σ with ⟨⟨x', v'⟩, r⟩
      simp only [Prod.mk.injEq] at hσ1
      obtain ⟨-, rfl⟩ := hσ1
      funext C
      exact (KGreal_eq_KGiW hcov v' hv C).symm)
    (fun x σ _ => by
      funext μ
      show PMF.pure ((ctEnc D).enc (shiftCT (half D) (msgR D μ) (toView D σ).2)) =
        PMF.pure ((ctEnc D).enc (encrypt (helperMap D) wSt (half D) σ.1.2.1 (attrN σ.1.1)
          (msgR D μ) σ.2))
      rw [encrypt_shift (helperMap D) wSt (half D) _ _ (msgR D μ)]
      rfl)
    rfl prog
  rw [← hcongr]
  have hcomap := Generic.runWith_comap
    (specV (univ w8) (half D) (msgR D) (mpkEnc D).enc (ctEnc D).enc (KGiW D kb L) (authW impl)
      (realVW D χs χ χfl)) (toView D) prog eag.setup (fun x => by
      show (eag.setup x).map (toView D) = realVW D χs χ χfl x
      simp only [eag, Generic.eagerCoins, realSpec, Generic.implSpec, PMF.bind_map, realVW,
        encLawW, encLaw]
      refine (PMF.map_bind _ _ _).trans ?_
      refine congrArg (PMF.bind _) (funext fun v => ?_)
      rw [msgR_false]
      exact (PMF.map_comp _ _ _).trans
        (PMF.map_comp (encrypt (helperMap D) wSt (half D) v.1 (attrN x) 0) _ (fun ct => (v.1, ct))).symm)
  rw [← hcomap, PMF.map_comp]
  rfl

/-- **The real secret law is close to package D's `hyb0`** (the machines' near-uniform public
matrices). -/
theorem realVW_close (χs χ χfl : PMF (Rg D)) (x : Attribute w8) :
    CloseTo (realVW D χs χ χfl x)
      (hyb0 (Wb := Wb D) (helperMap D) wSt (half D) χs χ χfl (attrN x)) (epsSetup D) := by
  unfold realVW hyb0 encLawW
  rw [χbin_eq_bitLaw, msgR_false]
  exact (closeTo_setupLaw D bitLaw).symm.bind_left _

/-! ### The ideal experiment -/

variable (D kb L)

/-- The challenger of the ideal side with the challenge `ct` itself (no shift). -/
noncomputable def specV0 (impl : Impl sig) (V : Attribute w8 → PMF (MPKt D × CTt D)) :
    Generic.Spec (univ w8) (MPKt D × CTt D) where
  setup := V
  pub σ := (mpkEnc D).enc σ.1
  key σ := KGiW D kb L σ.1
  chal σ _ := PMF.pure ((ctEnc D).enc σ.2)
  auth := authW impl

/-- Its observable experiment. -/
noncomputable def GV0 (impl : Impl sig) (A : Machine 3) (V : Attribute w8 → PMF (MPKt D × CTt D)) :=
  (ProbOracleComp.runWith (Generic.oracle (specV0 D kb L impl V))
    (A.machine.runOracle A.time (paramsWord (univ w8) params))
    ({} : Generic.GState (univ w8) (MPKt D × CTt D))).map Generic.obs

/-- The secret law of the ideal experiment: the machines' `Setup` and the simulator's ciphertext. -/
noncomputable def idealVW (_x : Attribute w8) : PMF (MPKt D × CTt D) :=
  (setupLawW D (χbin D)).bind fun v => (ctUW D).map fun ct => (v.1, ct)

/-- The simulator's challenge through the encodings. -/
noncomputable def CHideal (_ : MPKt D) (_ : Attribute w8) (_ : Bool) : PMF (List Bool) :=
  (ctUW D).map (ctEnc D).enc

/-- The ideal challenger as a generic challenger. -/
noncomputable def idealSpec (impl : Impl sig) :=
  Generic.implSpec (U := univ w8) params impl (mpkEnc D).enc (setupLawW D (χbin D))
    (KGreal D kb L) (CHideal D)

variable {D kb L}

theorem simulate_eq {Sim : Machine} (hSim : SimSpec D Sim) (mpk : MPKt D) :
    simulate (univ w8) params Sim ((mpkEnc D).enc mpk) = (ctUW D).map (ctEnc D).enc := by
  unfold simulate
  rw [show Sim.run (encodeTuple [paramsWord (univ w8) params, (mpkEnc D).enc mpk]) = _ from
    hSim mpk, PMF.map_comp]
  refine congrArg (fun f => PMF.map f (ctUW D)) (funext fun ct => ?_)
  show (decodeTuple 1 (encodeTuple [(ctEnc D).enc ct])).getD 0 [] = _
  have h := decodeTuple_encodeTuple [(ctEnc D).enc ct]
  simp only [List.length_singleton] at h
  rw [h]
  rfl

/-- **The ideal experiment is the experiment of the secret law `idealVW`** (challenge unshifted). -/
theorem ideal_eq_gameV0 {impl : Impl sig} {χs χ χfl : PMF (Rg D)}
    (hI : ImplSpec D kb L impl χs χ χfl) (hcov : RealCovW D kb) {Sim : Machine}
    (hSim : SimSpec D Sim) (A : Machine 3) :
    (PE.ideal (univ w8) params impl Sim A).map (fun r => (r.1, r.2.attr, r.2.msg, r.2.bad)) =
      GV0 D kb L impl A (idealVW D) := by
  have b1 := Generic.game_eq_generic params impl (mpkEnc D).enc (mskEnc D).enc
    (setupLawW D (χbin D)) (KGreal D kb L) (CHideal D)
    (fun mpk (_ : Attribute w8) (_ : Bool) => simulate (univ w8) params Sim mpk)
    (impl_setup hI.setup) (impl_keyGen hI.key hI.keyLong) (fun mpk _ _ => simulate_eq hSim mpk) A
  unfold PE.ideal
  refine b1.trans ?_
  unfold Machine.runWith GV0
  have hchal : ∀ σ μ, (idealSpec D kb L impl).chal σ μ =
      (ctUW D).map (fun ct => (ctEnc D).enc ct) := fun _ _ => rfl
  rw [show Generic.implSpec (U := univ w8) params impl (mpkEnc D).enc (setupLawW D (χbin D))
      (KGreal D kb L) (CHideal D) = idealSpec D kb L impl from rfl,
    Generic.runWith_eagerCoins (idealSpec D kb L impl) (ctUW D) (fun _ _ ct => (ctEnc D).enc ct)
      hchal]
  set prog := A.machine.runOracle A.time (paramsWord (univ w8) params)
  set eag := Generic.eagerCoins (idealSpec D kb L impl) (ctUW D) (fun _ _ ct => (ctEnc D).enc ct)
  let toV : (Attribute w8 × MPKt D × MSKt D) × CTt D → MPKt D × CTt D := fun σ => (σ.1.2.1, σ.2)
  set sp3 := (specV0 D kb L impl (idealVW D)).comap toV eag.setup
  have hsupp : ∀ x, ∀ σ ∈ (eag.setup x).support, ∃ v ∈ (setupLawW D (χbin D)).support,
      σ.1 = (x, v) := by
    intro x σ hσ
    simp only [eag, Generic.eagerCoins, idealSpec, Generic.implSpec, PMF.mem_support_bind_iff,
      PMF.mem_support_map_iff] at hσ
    obtain ⟨σ₀, ⟨v, hv, rfl⟩, r, -, rfl⟩ := hσ
    exact ⟨v, hv, rfl⟩
  have hcongr := Generic.runWith_congr_support eag sp3 rfl (fun _ _ _ => rfl)
    (fun x σ hσ => by
      obtain ⟨v, hv, hσ1⟩ := hsupp x σ hσ
      rcases σ with ⟨⟨x', v'⟩, r⟩
      simp only [Prod.mk.injEq] at hσ1
      obtain ⟨-, rfl⟩ := hσ1
      funext C
      exact (KGreal_eq_KGiW hcov v' hv C).symm)
    (fun _ _ _ => rfl) rfl prog
  rw [← hcongr]
  have hcomap := Generic.runWith_comap (specV0 D kb L impl (idealVW D)) toV prog eag.setup
    (fun x => by
      show (eag.setup x).map toV = idealVW D x
      simp only [eag, Generic.eagerCoins, idealSpec, Generic.implSpec, PMF.bind_map, idealVW]
      refine (PMF.map_bind _ _ _).trans ?_
      refine congrArg (PMF.bind _) (funext fun v => ?_)
      exact (PMF.map_comp _ _ _).trans rfl)
  rw [← hcomap, PMF.map_comp]
  rfl

/-- A statistical step of the unshifted experiment. -/
theorem gameV0_close {impl : Impl sig} (A : Machine 3) {V V' : Attribute w8 → PMF (MPKt D × CTt D)}
    {ε : ℝ≥0∞} (h : ∀ x, CloseTo (V x) (V' x) ε) :
    CloseTo (GV0 D kb L impl A V) (GV0 D kb L impl A V') (Fintype.card (Attribute w8) * ε) := by
  unfold GV0
  have := Generic.closeTo_runWith_setup (specV0 D kb L impl V)
    (A.machine.runOracle A.time (paramsWord (univ w8) params)) V' (fun _ => ε) h
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
  exact this.map _

/-- **The ideal secret law is close to package D's ideal view.** -/
theorem idealVW_close (x : Attribute w8) :
    CloseTo (idealVW D x) (idealView (S := setting D) (Wb := Wb D) (J := Jh D) (Pos := Pos))
      (epsSetup D + epsCT D) := by
  unfold idealVW idealView
  rw [χbin_eq_bitLaw]
  exact (closeTo_setupLaw D bitLaw).symm.bind fun v _ => (closeTo_ctU_ctUW D).symm.map _

/-- **A uniform ciphertext absorbs the shift**: the unshifted experiment of the ideal view is the
experiment `gameV` of package D at the ideal view. -/
theorem gameV0_idealView_eq [Nonempty (Wb D)] (impl : Impl sig) (A : Machine 3) :
    GV0 D kb L impl A (fun _ => idealView (S := setting D) (Wb := Wb D) (J := Jh D) (Pos := Pos)) =
      GV D kb L impl A (fun _ => idealView (S := setting D) (Wb := Wb D) (J := Jh D) (Pos := Pos)) := by
  let lazyI : Generic.Spec (univ w8) (MPKt D) :=
    { setup := fun _ => (setupLaw (setting D) (Wb D) (Jh D) Pos bitLaw).map Prod.fst
      pub := (mpkEnc D).enc
      key := KGiW D kb L
      chal := fun _ _ => (ctU (setting D) (Wb D) (Jh D) Pos).map (ctEnc D).enc
      auth := authW impl }
  set prog := A.machine.runOracle A.time (paramsWord (univ w8) params)
  have h1 := Generic.runWith_eagerCoins lazyI (ctU (setting D) (Wb D) (Jh D) Pos)
    (fun _ _ ct => (ctEnc D).enc ct) (fun _ _ => rfl) prog
  have h2 := Generic.runWith_eagerCoins lazyI (ctU (setting D) (Wb D) (Jh D) Pos)
    (fun _ μ ct => (ctEnc D).enc (shiftCT (half D) (msgR D μ) ct))
    (fun _ μ => by
      show (ctU (setting D) (Wb D) (Jh D) Pos).map (ctEnc D).enc = _
      conv_lhs => rw [← ctU_shift (half D) (msgR D μ), PMF.map_comp]
      rfl) prog
  have e1 : Generic.eagerCoins lazyI (ctU (setting D) (Wb D) (Jh D) Pos)
      (fun _ _ ct => (ctEnc D).enc ct) =
      specV0 D kb L impl (fun _ => idealView (S := setting D) (Wb := Wb D) (J := Jh D) (Pos := Pos)) := by
    unfold Generic.eagerCoins specV0 idealView
    simp only [lazyI, PMF.bind_map]
    rfl
  have e2 : Generic.eagerCoins lazyI (ctU (setting D) (Wb D) (Jh D) Pos)
      (fun _ μ ct => (ctEnc D).enc (shiftCT (half D) (msgR D μ) ct)) =
      specV (univ w8) (half D) (msgR D) (mpkEnc D).enc (ctEnc D).enc (KGiW D kb L) (authW impl)
        (fun _ => idealView (S := setting D) (Wb := Wb D) (J := Jh D) (Pos := Pos)) := by
    unfold Generic.eagerCoins specV idealView
    simp only [lazyI, PMF.bind_map]
    rfl
  unfold GV0 GV gameV
  rw [← e1, ← h1, h2]
  exact congrArg (fun sp => PMF.map Generic.obs (ProbOracleComp.runWith (Generic.oracle sp) prog {})) e2

end AdvancedEncryption.ExpLUT.Prog
