import PE.Impl.DualUse.GameChain
import PE.Impl.Game.Bridge
import PE.Impl.Game.Coins

/-!
# The real experiment is the first hybrid

The observable law of `PE.real` for the implementation is the experiment `gameV (V0)` of the
hybrids, with the key oracle answering the ideal key law of `mpk` (`KGi`): the challenger's
secret becomes `(mpk, ct₀)` by drawing the coins of the challenge at the selection
(`Generic.runWith_eagerCoins`), real keys have the ideal law when the real trapdoor is covered
(`DualUse.keyLaw_eq_ideal`), and the challenge for `μ` is the shift of `ct₀`.
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib
  Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)
variable {ms : Machines hk c}

open Classical in
/-- **The ideal key oracle**: the ideal key law of `mpk` for window predicates of at most `L` bits,
the zero key for the other short words, and the empty word for long ones. -/
noncomputable def KGi (mpk : PK hk c) (C : List Bool) : PMF (List Bool) :=
  if C.length ≤ c.L then
    if ∃ w : Window, winWord w = C then
      (idealKeyLaw c.Big c.Small c.hBig c.dec mpk (keyMatrix mpk (predC C))).map
        fun o => (skEnc hk c).enc (mpk, keyOfOutput o)
    else PMF.pure ((skEnc hk c).enc (mpk, dummyKey c))
  else PMF.pure []

open Classical in
/-- The flag of the experiment: the query is authorized for the selected attribute. -/
noncomputable def authI (C : List Bool) (x : Date) : Bool :=
  decide (Authorized (U := PUniv) params (impl hk c) C x)

/-- **Long predicates are never authorized**: `Eval` rejects inputs longer than `L`. -/
theorem authI_long (C : List Bool) (x : Date) (hC : c.L < C.length) : authI hk c C x = false := by
  unfold authI
  rw [decide_eq_false_iff_not]
  intro h
  obtain ⟨h1, -, -⟩ := (win_authorized_iff (impl hk c) rfl C x).mp h
  have := (length_le_encodeTuple (C := C)
    (xs := [paramsWord PUniv params, C, encDate x]) (by simp)).trans h1
  omega

/-- The real trapdoor is covered for every key of `Setup` and every window predicate. -/
def RealCovered : Prop :=
  ∀ v ∈ (setupM hk c).support, ∀ w : Window,
    GoodTrap c.Big c.Small c.dec v.1 (keyMatrix v.1 (predC (winWord w)))
      (realTrap (S := Sdw (N := N) hk) (trapMat v.2.2.1 v.2.2.2) (keyMatrix v.1 (predC (winWord w))))

variable {hk c}

/-- **Real keys have the ideal law** for every key of `Setup`. -/
theorem KGreal_eq_KGi (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u)
    (hcov : RealCovered hk c) (v : PK hk c × SKey hk c) (hv : v ∈ (setupM hk c).support)
    (C : List Bool) : KGreal hk c v.2 C = KGi hk c v.1 C := by
  obtain ⟨-, hm⟩ := msk_trapdoor _ v hv
  unfold KGreal KGi
  split_ifs with hL hw
  · obtain ⟨w, rfl⟩ := hw
    rw [keyM_eq hk c v.2 _ ⟨w, rfl⟩, hm,
      keyLaw_eq_ideal c.Big c.Small c.hBig c.dec hdec v.1 _ _ (hcov v hv w), PMF.map_comp]
    rfl
  · rw [keyM_of_not hk c v.2 C hw, hm, PMF.pure_map]
  · rfl

/-- The law of `(mpk, ct₀)` from `Setup` and the coins of `Enc` is the real view. -/
theorem setup_coins_eq_V0 (x : Date) :
    ((setupM hk c).bind fun v => (coinsM hk c).map fun r =>
      (v.1, encrypt v.1 (bitsOf x) false r)) = V0 hk c x := by
  unfold setupM setupLaw V0 realGame realView inst3Real coinsM
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind, PMF.bind_map, PMF.map_bind]
  refine congrArg (PMF.bind _) (funext fun B₀ => ?_)
  refine congrArg (PMF.bind _) (funext fun a => ?_)
  refine congrArg (PMF.bind _) (funext fun t => ?_)
  refine congrArg (PMF.bind _) (funext fun e => ?_)
  simp only [Function.comp_def, PMF.pure_bind, trapRow_eq_toB₁]
  rfl

variable (hk c)

/-- The challenge of the implementation, through the encodings. -/
noncomputable def CHreal (mpk : PK hk c) (x : Date) (μ : Bool) : PMF (List Bool) :=
  (encM hk c mpk x μ).map (ctEnc hk c).enc

/-- The challenger of the implementation, as a generic challenger. -/
noncomputable def realSpec :=
  Generic.implSpec (U := PUniv) params (impl hk c) (pkEnc hk c).enc (setupM hk c)
    (KGreal hk c) (CHreal hk c)

/-- The challenge with given coins. -/
noncomputable def gReal (σ : Date × PK hk c × SKey hk c) (μ : Bool)
    (r : EncCoins (Sdw (N := N) hk) (Fin c.d) (TrapCol k)) : List Bool :=
  (ctEnc hk c).enc (encrypt σ.2.1 (bitsOf σ.1) μ r)

/-- The secret `(mpk, ct₀)` of the hybrids from the secret with the coins. -/
noncomputable def toView (σ : (Date × PK hk c × SKey hk c) ×
    EncCoins (Sdw (N := N) hk) (Fin c.d) (TrapCol k)) : PK hk c × CT hk c :=
  (σ.1.2.1, encrypt σ.1.2.1 (bitsOf σ.1.1) false σ.2)

variable {hk c}

/-- **The real experiment is the experiment of the first hybrid.** -/
theorem real_eq_gameV (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u)
    (hcov : RealCovered hk c) (A : Machine 3) :
    (PE.real PUniv params (impl hk c ms) A).map (fun r => (r.1, r.2.attr, r.2.msg, r.2.bad)) =
      gameV hk c (pkEnc hk c).enc (ctEnc hk c).enc (KGi hk c) (authI hk c) A (V0 hk c) := by
  -- the generic challenger of the implementation
  have b1 := Generic.game_eq_generic params (impl hk c ms) (pkEnc hk c).enc (mskEnc hk c).enc
    (setupM hk c) (KGreal hk c) (CHreal hk c) (enc params (impl hk c ms)) (impl_setup hk c)
    (impl_keyGen hk c) (fun mpk x μ => impl_enc hk c mpk x μ) A
  unfold PE.real
  rw [b1]
  unfold Machine.runWith gameV Machine.runWith
  -- the coins of the challenge at the selection
  have hchal : ∀ σ μ, (realSpec hk c).chal σ μ = (coinsM hk c).map (gReal hk c σ μ) := by
    intro σ μ
    show (encM hk c σ.2.1 σ.1 μ).map (ctEnc hk c).enc = _
    unfold encM
    rw [PMF.map_comp]
    rfl
  rw [show Generic.implSpec (U := PUniv) params (impl hk c ms) (pkEnc hk c).enc (setupM hk c)
      (KGreal hk c) (CHreal hk c) = realSpec hk c from rfl,
    Generic.runWith_eagerCoins (realSpec hk c) (coinsM hk c) (gReal hk c) hchal]
  set prog := A.machine.runOracle A.time (paramsWord PUniv params)
  set eag := Generic.eagerCoins (realSpec hk c) (coinsM hk c) (gReal hk c)
  set sp3 := (specV hk c (pkEnc hk c).enc (ctEnc hk c).enc (KGi hk c) (authI hk c) (V0 hk c)).comap
    (toView hk c) eag.setup
  -- the two challengers agree on the support of the secret
  have hsupp : ∀ x, ∀ σ ∈ (eag.setup x).support, ∃ v ∈ (setupM hk c).support, σ.1 = (x, v) := by
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
      exact (KGreal_eq_KGi hdec hcov v' hv C).symm)
    (fun x σ _ => by
      funext μ
      show PMF.pure ((ctEnc hk c).enc (shiftCT hk c μ (toView hk c σ).2)) =
        PMF.pure ((ctEnc hk c).enc (encrypt σ.1.2.1 (bitsOf σ.1.1) μ σ.2))
      rw [encrypt_shift hk c _ _ μ]
      rfl)
    rfl prog
  rw [← hcongr]
  -- the secret `(mpk, ct₀)`
  have hcomap := Generic.runWith_comap
    (specV hk c (pkEnc hk c).enc (ctEnc hk c).enc (KGi hk c) (authI hk c) (V0 hk c)) (toView hk c)
    prog eag.setup (fun x => by
      show (eag.setup x).map (toView hk c) = V0 hk c x
      refine Eq.trans ?_ (setup_coins_eq_V0 (hk := hk) (c := c) x)
      simp only [eag, Generic.eagerCoins, realSpec, Generic.implSpec, PMF.bind_map]
      refine (PMF.map_bind _ _ _).trans ?_
      refine congrArg (PMF.bind _) (funext fun v => ?_)
      simp only [Function.comp_def]
      exact PMF.map_comp _ _ _)
  rw [← hcomap, PMF.map_comp]
  rfl

end AdvancedEncryption.DualUse
