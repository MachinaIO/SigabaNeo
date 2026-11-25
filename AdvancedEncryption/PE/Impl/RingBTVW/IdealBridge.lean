import PE.Impl.RingBTVW.RealBridge

/-!
# The simulator and the ideal experiment

The simulator outputs the encoding of a uniform ciphertext (`simMachine`, from fair coins). The
observable law of `PE.ideal` for it is the experiment `gameV (VI0)` of the ideal side
(`ideal_eq_gameV`): the challenge does not depend on the message, and a uniform ciphertext
shifted by `μ · ⌊q/2⌋` is uniform (`ctU_shift`).
-/

namespace AdvancedEncryption.RingBTVW

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW.Fresh Cslib
  Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)
variable {ms : Machines hk c}

/-- The simulator's ciphertext. -/
noncomputable abbrev ctUc : PMF (CT hk c) := ctU (Sdw (N := N) hk) (Fin c.d) (TrapCol k)

/-- The uniform ciphertext is realized by fair coins. -/
theorem bitLaw_ctU : ∃ m, BitLaw (ctUc hk c) m := by
  unfold ctUc ctU
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure]
  exact ⟨_, BitLaw.bind (BitLaw.uniform_fun (BitLaw.uniform_fun (BitLaw.uniform_fun
      (BitLaw.uniform_ring N K)))) fun Ψ =>
    BitLaw.bind (BitLaw.uniform_fun (BitLaw.uniform_fun (BitLaw.uniform_ring N K))) fun c₀ =>
    BitLaw.bind (BitLaw.uniform_fun (BitLaw.uniform_fun (BitLaw.uniform_ring N K))) fun c₁ =>
    BitLaw.bind (BitLaw.uniform_fun (BitLaw.uniform_fun (BitLaw.uniform_fun
      (BitLaw.uniform_ring N K)))) fun cj =>
    BitLaw.bind (BitLaw.uniform_ring N K) fun κ => BitLaw.pure _⟩

theorem exists_simMachine : ∃ M : Machine, ∀ mpk : PK hk c,
    M.run (encodeTuple [pw, (pkEnc hk c).enc mpk]) =
      (ctUc hk c).map fun ct => encodeTuple [(ctEnc hk c).enc ct] := by
  obtain ⟨m, g, hg⟩ := bitLaw_ctU hk c
  obtain ⟨M, hM⟩ := Machine.exists_finiteAlg (A := PK hk c) (fun mpk => [pw, (pkEnc hk c).enc mpk])
    (fun a b h => by
      simp only [List.cons.injEq, and_true, true_and] at h
      exact (pkEnc hk c).inj h) m (fun _ w => [(ctEnc hk c).enc (g w)])
  refine ⟨M, fun mpk => ?_⟩
  rw [hM mpk, hg, PMF.map_comp]
  rfl

/-- **The simulator**: the encoding of a uniform ciphertext. -/
noncomputable def simMachine : Machine := Classical.choose (exists_simMachine hk c)

/-- The simulator's challenge in the experiment. -/
theorem simulate_eq (mpk : PK hk c) :
    simulate PUniv params (simMachine hk c) ((pkEnc hk c).enc mpk) =
      (ctUc hk c).map (ctEnc hk c).enc := by
  unfold simulate
  rw [show encodeTuple [paramsWord PUniv params, (pkEnc hk c).enc mpk] =
    encodeTuple [pw, (pkEnc hk c).enc mpk] from rfl,
    show (simMachine hk c).run (encodeTuple [pw, (pkEnc hk c).enc mpk]) = _ from
      Classical.choose_spec (exists_simMachine hk c) mpk, PMF.map_comp]
  refine congrArg (fun f => PMF.map f (ctUc hk c)) (funext fun ct => ?_)
  show (decodeTuple 1 (encodeTuple [(ctEnc hk c).enc ct])).getD 0 [] = _
  have h := decodeTuple_encodeTuple [(ctEnc hk c).enc ct]
  simp only [List.length_singleton] at h
  rw [h]
  rfl

/-- **A uniform ciphertext shifted by the message is uniform.** -/
theorem ctU_shift (μ : Bool) : (ctUc hk c).map (shiftCT hk c μ) = ctUc hk c := by
  unfold ctUc ctU
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure,
    PMF.map_bind, PMF.pure_map]
  refine congrArg (PMF.bind _) (funext fun Ψ => ?_)
  refine congrArg (PMF.bind _) (funext fun c₀ => ?_)
  refine congrArg (PMF.bind _) (funext fun c₁ => ?_)
  refine congrArg (PMF.bind _) (funext fun cj => ?_)
  exact bind_uniform_equiv (Equiv.addRight (if μ then (Sdw (N := N) hk).half else 0))
    (fun κ => PMF.pure ({ Ψ := Ψ, c₀ := c₀, c₁ := c₁, cj := cj, κ := κ } : CT hk c))

/-- The public key of `Setup`. -/
theorem setupM_fst : (setupM hk c).map Prod.fst =
    mpkU (Sdw (N := N) hk) (Fin c.d) (TrapCol k) (lawB₁r hk c) := by
  unfold setupM setupLaw mpkU lawB₁r inst3Real
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure,
    PMF.map_bind, PMF.pure_map, PMF.bind_bind, PMF.pure_bind, PMF.bind_map]
  refine congrArg (PMF.bind _) (funext fun B₀ => ?_)
  refine congrArg (PMF.bind _) (funext fun a => ?_)
  refine congrArg (PMF.bind _) (funext fun t => ?_)
  refine congrArg (PMF.bind _) (funext fun e => ?_)
  simp only [Function.comp_def, PMF.pure_bind, trapRow_eq_toB₁]

/-- The simulator's challenge, through the encodings. -/
noncomputable def CHideal (_ : PK hk c) (_ : PUniv.Attr) (_ : Bool) : PMF (List Bool) :=
  (ctUc hk c).map (ctEnc hk c).enc

/-- The ideal challenger as a generic challenger. -/
noncomputable def idealSpec :=
  Generic.implSpec (U := PUniv) params (impl hk c) (pkEnc hk c).enc (setupM hk c)
    (KGreal hk c) (CHideal hk c)

/-- The simulator's challenge, written as a shift of the uniform ciphertext. -/
noncomputable def gIdeal (_ : PUniv.Attr × PK hk c × SKey hk c) (μ : Bool) (ct : CT hk c) : List Bool :=
  (ctEnc hk c).enc (shiftCT hk c μ ct)

variable {hk c}

/-- **The ideal experiment is the experiment of the ideal view.** -/
theorem ideal_eq_gameV (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u)
    (hcov : RealCovered hk c) [NeZero c.d] (A : Machine 3) :
    (PE.ideal PUniv params (impl hk c ms) (simMachine hk c) A).map
        (fun r => (r.1, r.2.attr, r.2.msg, r.2.bad)) =
      gameV hk c (pkEnc hk c).enc (ctEnc hk c).enc (KGi hk c) (authI hk c) A (VI0 hk c) := by
  have b1 := Generic.game_eq_generic params (impl hk c ms) (pkEnc hk c).enc (mskEnc hk c).enc
    (setupM hk c) (KGreal hk c) (CHideal hk c)
    (fun mpk (_ : PUniv.Attr) (_ : PUniv.Msg) =>
      simulate PUniv params (simMachine hk c) mpk) (impl_setup hk c)
    (impl_keyGen hk c) (fun mpk _ _ => simulate_eq hk c mpk) A
  unfold PE.ideal
  rw [b1]
  unfold Machine.runWith gameV Machine.runWith
  have hchal : ∀ σ μ, (idealSpec hk c).chal σ μ = (ctUc hk c).map (gIdeal hk c σ μ) := by
    intro σ μ
    show (ctUc hk c).map (ctEnc hk c).enc = _
    conv_lhs => rw [← ctU_shift hk c μ, PMF.map_comp]
    rfl
  rw [show Generic.implSpec (U := PUniv) params (impl hk c ms) (pkEnc hk c).enc (setupM hk c)
      (KGreal hk c) (CHideal hk c) = idealSpec hk c from rfl,
    Generic.runWith_eagerCoins (idealSpec hk c) (ctUc hk c) (gIdeal hk c) hchal]
  set prog := A.machine.runOracle A.time (paramsWord PUniv params)
  set eag := Generic.eagerCoins (idealSpec hk c) (ctUc hk c) (gIdeal hk c)
  let toV : (PUniv.Attr × PK hk c × SKey hk c) × CT hk c → PK hk c × CT hk c := fun σ => (σ.1.2.1, σ.2)
  set sp3 := (specV hk c (pkEnc hk c).enc (ctEnc hk c).enc (KGi hk c) (authI hk c) (VI0 hk c)).comap
    toV eag.setup
  have hsupp : ∀ x, ∀ σ ∈ (eag.setup x).support, ∃ v ∈ (setupM hk c).support, σ.1 = (x, v) := by
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
      exact (KGreal_eq_KGi hdec hcov v' hv C).symm)
    (fun _ _ _ => rfl) rfl prog
  rw [← hcongr]
  have hcomap := Generic.runWith_comap
    (specV hk c (pkEnc hk c).enc (ctEnc hk c).enc (KGi hk c) (authI hk c) (VI0 hk c)) toV
    prog eag.setup (fun x => by
      show (eag.setup x).map toV = VI0 hk c x
      unfold VI0 idealView
      rw [← setupM_fst, PMF.bind_map]
      simp only [eag, Generic.eagerCoins, idealSpec, Generic.implSpec, PMF.bind_map]
      refine (PMF.map_bind _ _ _).trans ?_
      refine congrArg (PMF.bind _) (funext fun v => ?_)
      simp only [Function.comp_def]
      exact PMF.map_comp _ _ _)
  rw [← hcomap, PMF.map_comp]
  rfl

end AdvancedEncryption.RingBTVW
