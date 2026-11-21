import PE.Impl.DualUse.Codec

/-!
# The machines of the dual-use scheme for date windows

`Setup`, `Enc` and `KeyGen` are machines realizing the scheme's laws exactly
(`Machine.exists_finiteAlg'`), `Dec` a deterministic machine computing the scheme's decryption,
and `Eval` the evaluation of window predicates. Keys and ciphertexts are written with the explicit
encodings of `DualUse.Codec`. Inputs that encode no valid value are answered by the empty tuple.
`correct_of_scheme`: the implementation is correct as soon as the scheme decrypts correctly with
probability at least `1 − 2^{-κ}` for every window predicate whose last gate is `false` on `x`.
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

open SigabaNeo.Encode

/-! ### The machines -/

theorem exists_setupMachine : ∃ M : Machine, M.run (encodeTuple [pw]) =
    (setupM hk c).map fun v => encodeTuple [(pkEnc hk c).enc v.1, (mskEnc hk c).enc v.2] := by
  obtain ⟨m, g, hg⟩ := bitLaw_setup (S := Sdw (N := N) hk) (Wd := Fin c.d) c.hχ
  obtain ⟨M, hM⟩ := Machine.exists_finiteAlg (A := Unit) (fun _ => [pw]) (fun _ _ _ => rfl) m
    (fun _ w => [(pkEnc hk c).enc (g w).1, (mskEnc hk c).enc (g w).2])
  exact ⟨M, by rw [hM (), setupM, hg, PMF.map_comp]; rfl⟩

/-- The machine of `Setup`. -/
noncomputable def setupMachine : Machine := Classical.choose (exists_setupMachine hk c)

theorem exists_encMachine : ∃ M : Machine, ∀ (mpk : PK hk c) (x : Date) (b : Bool),
    M.run (encodeTuple [pw, (pkEnc hk c).enc mpk, encDate x, [b]]) =
      (encM hk c mpk x b).map fun ct => encodeTuple [(ctEnc hk c).enc ct] := by
  obtain ⟨m, g, hg⟩ := bitLaw_coins (S := Sdw (N := N) hk) (Wd := Fin c.d) c.hχ c.w
  obtain ⟨M, hM⟩ := Machine.exists_finiteAlg (A := PK hk c × Date × Bool)
    (fun a => [pw, (pkEnc hk c).enc a.1, encDate a.2.1, [a.2.2]]) (fun a a' h => by
      simp only [List.cons.injEq, and_true, true_and] at h
      exact Prod.ext ((pkEnc hk c).inj h.1) (Prod.ext (encDate.injective h.2.1)
        h.2.2)) m
    (fun a w => [(ctEnc hk c).enc (encrypt a.1 (bitsOf a.2.1) a.2.2 (g w))])
  refine ⟨M, fun mpk x b => ?_⟩
  rw [hM (mpk, x, b), encM, PMF.map_comp, coinsM, hg, PMF.map_comp]
  rfl

/-- The machine of `Enc`. -/
noncomputable def encMachine : Machine := Classical.choose (exists_encMachine hk c)

theorem exists_keyMachine : ∃ M : Machine,
    (∀ (msk : SKey hk c) (C : List Bool), C.length ≤ c.L →
      M.run (encodeTuple [pw, (mskEnc hk c).enc msk, C]) =
        (keyM hk c msk C).map fun sk => encodeTuple [(skEnc hk c).enc sk]) ∧
    ∀ (msk : SKey hk c) (C : List Bool), ¬ C.length ≤ c.L →
      M.run (encodeTuple [pw, (mskEnc hk c).enc msk, C]) = PMF.pure (encodeTuple []) := by
  classical
  obtain ⟨g, hg⟩ := BitLaw.uniformOfFinset_map c.mB c.emb
  obtain ⟨M, hM, hM'⟩ := Machine.exists_finiteAlg' (A := SKey hk c × ShortWord c.L)
    (fun a => [pw, (mskEnc hk c).enc a.1, a.2.1]) (fun a a' h => by
      simp only [List.cons.injEq, and_true, true_and] at h
      exact Prod.ext ((mskEnc hk c).inj h.1) (Subtype.ext h.2)) c.mB
    (fun a w => [(skEnc hk c).enc (keyTry hk c a.1 a.2.1 (g w))])
  refine ⟨M, fun msk C hC => ?_, fun msk C hC => hM' _ ?_⟩
  · rw [hM (msk, ⟨C, hC⟩), keyM, PMF.map_comp]
    change _ = PMF.map _ (PMF.uniformOfFinset (Finset.univ.map c.emb) _)
    rw [hg, PMF.map_comp]
    simp only [Function.comp_def]
  · rintro ⟨a, ha⟩
    simp only [List.cons.injEq, and_true] at ha
    exact hC (ha.2.2 ▸ a.2.2)

/-- The machine of `KeyGen`. -/
noncomputable def keyMachine : Machine := Classical.choose (exists_keyMachine hk c)

theorem exists_decMachine : ∃ M : Machine, M.Deterministic ∧
    ∀ (sk : SK hk c) (C : List Bool) (ct : CT hk c), C.length ≤ c.L →
      M.run (encodeTuple [pw, (skEnc hk c).enc sk, C, (ctEnc hk c).enc ct]) =
        PMF.pure (encodeTuple [decM hk c sk C ct]) := by
  obtain ⟨M, hdet, hM⟩ := Machine.exists_finiteAlg_det (A := SK hk c × ShortWord c.L × CT hk c)
    (fun a => [pw, (skEnc hk c).enc a.1, a.2.1.1, (ctEnc hk c).enc a.2.2]) (fun a a' h => by
      simp only [List.cons.injEq, and_true, true_and] at h
      exact Prod.ext ((skEnc hk c).inj h.1) (Prod.ext (Subtype.ext h.2.1)
        ((ctEnc hk c).inj h.2.2)))
    (fun a => decM hk c a.1 a.2.1.1 a.2.2)
  exact ⟨M, hdet, fun sk C ct hC => hM (sk, ⟨C, hC⟩, ct)⟩

/-- The machine of `Dec`. -/
noncomputable def decMachine : Machine := Classical.choose (exists_decMachine hk c)

/-- **The implementation.** -/
noncomputable def impl : Impl PE.sig where
  machine
    | .setup => setupMachine hk c
    | .enc => encMachine hk c
    | .keyGen => keyMachine hk c
    | .dec => decMachine hk c
    | .eval => winEvalMachine c.L
  deterministic a h := by
    cases a
    all_goals first
      | exact absurd h (by decide)
      | exact (Classical.choose_spec (exists_decMachine hk c)).1
      | exact winEvalMachine_deterministic _

/-! ### The laws of the algorithms -/

theorem decodeTuple_one_nil : decodeTuple 1 (encodeTuple []) = [[]] := by
  unfold decodeTuple
  rw [dif_neg]
  · rfl
  · rintro ⟨xs, hl, he⟩
    match xs, hl with
    | [y], _ =>
      have := congrArg List.length he
      simp [encodeTuple, Turing.MultiTapeTM.length_frame] at this

/-- `Setup` outputs the encodings of `(mpk, msk)`. -/
theorem impl_setup : PE.setup (U := dateUniverse) params (impl hk c) =
    (setupM hk c).map fun v => ((pkEnc hk c).enc v.1, (mskEnc hk c).enc v.2) := by
  unfold PE.setup
  rw [run_of_machine (impl hk c) .setup (paramsWord dateUniverse params) [] (setupM hk c)
    (fun v => [(pkEnc hk c).enc v.1, (mskEnc hk c).enc v.2]) (fun _ => rfl)
    (Classical.choose_spec (exists_setupMachine hk c)), PMF.map_comp]
  rfl

/-- The answer of `KeyGen` on every predicate word. -/
noncomputable def KGreal (msk : SKey hk c) (C : List Bool) : PMF (List Bool) :=
  if C.length ≤ c.L then (keyM hk c msk C).map (skEnc hk c).enc else PMF.pure []

/-- `KeyGen` answers `KGreal`. -/
theorem impl_keyGen (msk : SKey hk c) (C : List Bool) :
    keyGen (U := dateUniverse) params (impl hk c) ((mskEnc hk c).enc msk) C = KGreal hk c msk C := by
  unfold keyGen KGreal
  split_ifs with hC
  · rw [run_of_machine (impl hk c) .keyGen (paramsWord dateUniverse params)
      [(mskEnc hk c).enc msk, C] (keyM hk c msk C) (fun sk => [(skEnc hk c).enc sk])
      (fun _ => rfl) ((Classical.choose_spec (exists_keyMachine hk c)).1 msk C hC), PMF.map_comp]
    rfl
  · unfold Impl.run
    have h := (Classical.choose_spec (exists_keyMachine hk c)).2 msk C hC
    change (PMF.map _ (PMF.map _ ((keyMachine hk c).run _))) = _
    rw [show (keyMachine hk c).run (encodeTuple [paramsWord dateUniverse params,
      (mskEnc hk c).enc msk, C]) = PMF.pure (encodeTuple []) from h, PMF.pure_map, PMF.pure_map]
    have : (sig Alg.keyGen).outputs.length = 1 := rfl
    rw [this, decodeTuple_one_nil]
    rfl

/-- `Enc` outputs the encoding of the ciphertext. -/
theorem impl_enc (mpk : PK hk c) (x : Date) (b : Bool) :
    enc (U := dateUniverse) params (impl hk c) ((pkEnc hk c).enc mpk) x b =
      (encM hk c mpk x b).map (ctEnc hk c).enc := by
  unfold enc
  rw [run_of_machine (impl hk c) .enc (paramsWord dateUniverse params)
    [(pkEnc hk c).enc mpk, dateUniverse.encAttr x, dateUniverse.encMsg b] (encM hk c mpk x b)
    (fun ct => [(ctEnc hk c).enc ct]) (fun _ => rfl)
    (Classical.choose_spec (exists_encMachine hk c) mpk x b), PMF.map_comp]
  rfl

/-! ### Correctness -/

/-- **Correctness from the scheme**: the implementation is correct if the scheme decrypts
correctly with probability at least `1 − 2^{-κ}` for every window predicate whose last gate is
`false` on `x`. -/
theorem correct_of_scheme
    (hscheme : ∀ (x : Date) (w : Window), (winWord w).length ≤ c.L →
      evalGates (encDate x, parse (winWord w)) = false → ∀ b : Bool,
        1 - ((2 : ℝ) ^ params.corrBits)⁻¹ ≤
          (((setupM hk c).bind fun v => (keyM hk c v.2 (winWord w)).bind fun sk =>
            (encM hk c v.1 x b).map fun ct => decM hk c sk (winWord w) ct) [b]).toReal) :
    Correct dateUniverse params (impl hk c) := by
  have hauth : ∀ C (x : Date), Authorized (U := dateUniverse) params (impl hk c) C x →
      C.length ≤ c.L ∧ (∃ w : Window, winWord w = C) ∧ evalGates (encDate x, parse C) = false := by
    intro C x h
    obtain ⟨h1, h2, h3⟩ := (win_authorized_iff (impl hk c) rfl C x).mp h
    exact ⟨(length_le_encodeTuple (by simp)).trans h1, h2, h3⟩
  refine correct_of_laws (U := dateUniverse) params (impl hk c) (pkEnc hk c).enc (mskEnc hk c).enc
    (skEnc hk c).enc (ctEnc hk c).enc (setupM hk c) (keyM hk c) (encM hk c) (decM hk c) ?_ ?_ ?_ ?_ ?_
  · unfold PE.setup
    rw [run_of_machine (impl hk c) .setup (paramsWord dateUniverse params) [] (setupM hk c)
      (fun v => [(pkEnc hk c).enc v.1, (mskEnc hk c).enc v.2]) (fun _ => rfl)
      (Classical.choose_spec (exists_setupMachine hk c)), PMF.map_comp]
    rfl
  · intro msk C x hC
    unfold keyGen
    rw [run_of_machine (impl hk c) .keyGen (paramsWord dateUniverse params) [(mskEnc hk c).enc msk, C] (keyM hk c msk C) (fun sk => [(skEnc hk c).enc sk])
      (fun _ => rfl) ((Classical.choose_spec (exists_keyMachine hk c)).1 msk C (hauth C x hC).1),
      PMF.map_comp]
    rfl
  · intro mpk x b
    unfold enc
    rw [run_of_machine (impl hk c) .enc (paramsWord dateUniverse params)
      [(pkEnc hk c).enc mpk, dateUniverse.encAttr x, dateUniverse.encMsg b] (encM hk c mpk x b) (fun ct => [(ctEnc hk c).enc ct])
      (fun _ => rfl) (Classical.choose_spec (exists_encMachine hk c) mpk x b), PMF.map_comp]
    rfl
  · intro sk C ct x hC
    unfold dec
    rw [run_of_machine (impl hk c) .dec (paramsWord dateUniverse params) [(skEnc hk c).enc sk, C, (ctEnc hk c).enc ct]
      (PMF.pure (decM hk c sk C ct))
      (fun r => [r]) (fun _ => rfl) (by
        rw [PMF.pure_map]
        exact (Classical.choose_spec (exists_decMachine hk c)).2 sk C ct (hauth C x hC).1),
      PMF.pure_map, PMF.pure_map]
    rfl
  · intro x C hC b
    obtain ⟨h1, ⟨w, rfl⟩, h3⟩ := hauth C x hC
    exact hscheme x w h1 h3 b

/-- **Expressiveness.** -/
theorem expressive (hL : dateBound ≤ c.L) : Expressive dateUniverse params (impl hk c) :=
  expressive_win (impl hk c) rfl hL

end AdvancedEncryption.DualUse
