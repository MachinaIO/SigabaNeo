import PE.Impl.Game.Generic

/-!
# The experiment of an implementation as an experiment with an abstract secret

If `Setup` outputs the encodings of `(mpk, msk) ← setupM`, `KeyGen` answers `KG msk C` on the
encoding of `msk` and the challenge on the encoding of `mpk` is `CH mpk x μ`, the experiment
`PE.game` has the same observable law as the generic experiment whose secret is
`(x, mpk, msk)` (`game_eq_generic`).
-/

namespace AdvancedEncryption.PE.Generic

open SigabaNeo Cslib

variable {U : Universe} (p : Params) (impl : Impl sig)
  {MPK MSK : Type} (encMPK : MPK → List Bool) (encMSK : MSK → List Bool)
  (setupM : PMF (MPK × MSK)) (KG : MSK → List Bool → PMF (List Bool))
  (CH : MPK → U.Attr → U.Msg → PMF (List Bool))

open Classical in
/-- The challenger of an implementation, with the secret `(x, mpk, msk)`. -/
noncomputable def implSpec : Spec U (U.Attr × MPK × MSK) where
  setup x := setupM.map (x, ·)
  pub σ := encMPK σ.2.1
  key σ C := KG σ.2.2 C
  chal σ μ := CH σ.2.1 σ.1 μ
  auth C x := decide (Authorized p impl C x)

/-- The state of `PE.game` represented by a generic state. -/
def toGameState (s : GState U (U.Attr × MPK × MSK)) : GameState U :=
  { attr := s.attr, mpk := (s.sec.map fun σ => encMPK σ.2.1).getD [],
    msk := (s.sec.map fun σ => encMSK σ.2.2).getD [], msg := s.msg, bad := s.bad }

/-- The secret is present exactly after the selection, and records the selected attribute. -/
def Inv (s : GState U (U.Attr × MPK × MSK)) : Prop :=
  match s.attr, s.sec with
  | none, none => True
  | some x, some σ => σ.1 = x
  | _, _ => False

variable (challenge : List Bool → U.Attr → U.Msg → PMF (List Bool))
  (hsetup : setup (U := U) p impl = setupM.map fun v => (encMPK v.1, encMSK v.2))
  (hkey : ∀ msk C, keyGen (U := U) p impl (encMSK msk) C = KG msk C)
  (hch : ∀ mpk x μ, challenge (encMPK mpk) x μ = CH mpk x μ)

include hsetup hkey hch in
/-- One answer of the generic oracle, represented, is the answer of `PE.oracle`. -/
theorem bridge_step (q : Fin 3 × List Bool) (s : GState U (U.Attr × MPK × MSK)) (hs : Inv s) :
    (oracle (implSpec p impl encMPK setupM KG CH) q s).map
        (fun r => (r.1, toGameState encMPK encMSK r.2)) =
      PE.oracle p impl challenge q (toGameState encMPK encMSK s) := by
  rcases s with ⟨attr, sec, msg, bad⟩
  by_cases hq : q.1 = selectOp
  · rcases attr with _ | x
    · rcases sec with _ | σ
      · rcases hd : decode U.encAttr q.2 with _ | x
        · simp [oracle, oracleWith, PE.oracle, hq, hd, toGameState]
        · simp only [oracle, oracleWith, PE.oracle, hq, hd, if_true, toGameState, hsetup,
            implSpec, PMF.map_comp]
          rfl
      · exact absurd hs (by simp [Inv])
    · rcases sec with _ | σ
      · exact absurd hs (by simp [Inv])
      · simp [oracle, oracleWith, PE.oracle, hq, toGameState]
  · by_cases hk : q.1 = keyGenOp
    · rcases attr with _ | x
      · rcases sec with _ | σ
        · simp [oracle, oracleWith, PE.oracle, hq, hk, toGameState, selectOp, keyGenOp]
        · exact absurd hs (by simp [Inv])
      · rcases sec with _ | σ
        · exact absurd hs (by simp [Inv])
        · simp only [Inv] at hs
          simp only [oracle, oracleWith, PE.oracle, hq, hk, if_true, if_false, toGameState,
            show (keyGenOp : Fin 3) ≠ selectOp by decide, ite_false,
            implSpec, PMF.map_comp, Option.map_some, Option.getD_some, hkey, hs]
          rfl
    · rcases attr with _ | x
      · rcases sec with _ | σ
        · simp [oracle, oracleWith, PE.oracle, hq, hk, toGameState]
        · exact absurd hs (by simp [Inv])
      · rcases sec with _ | σ
        · exact absurd hs (by simp [Inv])
        · simp only [Inv] at hs
          rcases msg with _ | μ₀ <;> rcases hd : decode U.encMsg q.2 with _ | μ
          all_goals simp only [oracle, oracleWith, PE.oracle, hq, hk, if_false, toGameState, ite_false,
            implSpec, PMF.map_comp, Option.map_some, Option.getD_some, hd, hs, hch, PMF.pure_map]
          all_goals rfl

omit hsetup hkey hch in
/-- The generic oracle keeps the invariant. -/
theorem inv_step (q : Fin 3 × List Bool) (s : GState U (U.Attr × MPK × MSK)) (hs : Inv s) :
    ∀ a s', (a, s') ∈ (oracle (implSpec p impl encMPK setupM KG CH) q s).support → Inv s' := by
  intro a s' h
  rcases s with ⟨attr, sec, msg, bad⟩
  unfold oracle oracleWith at h
  split_ifs at h with hq hk
  · split at h
    · rw [PMF.mem_support_map_iff] at h
      obtain ⟨σ, hσ, he⟩ := h
      simp only [implSpec, PMF.mem_support_map_iff] at hσ
      obtain ⟨v, -, rfl⟩ := hσ
      cases he
      simp [Inv]
    · rw [PMF.mem_support_pure_iff] at h; cases h; exact hs
  · split at h
    · rw [PMF.mem_support_map_iff] at h
      obtain ⟨sk, -, he⟩ := h
      cases he
      exact hs
    · rw [PMF.mem_support_pure_iff] at h; cases h; exact hs
  · split at h
    · rw [PMF.mem_support_map_iff] at h
      obtain ⟨ct, -, he⟩ := h
      cases he
      exact hs
    · rw [PMF.mem_support_pure_iff] at h; cases h; exact hs

include hsetup hkey hch in
/-- **The experiment of the implementation** has the observable law of the generic experiment. -/
theorem game_eq_generic (A : Machine 3) :
    (game p impl challenge A).map (fun r => (r.1, r.2.attr, r.2.msg, r.2.bad)) =
      (A.runWith (oracle (implSpec p impl encMPK setupM KG CH)) (paramsWord U p) {}).map obs := by
  have h := ProbOracleComp.runWith_map_state_of_invariant
    (oracle (implSpec p impl encMPK setupM KG CH)) (PE.oracle p impl challenge)
    (toGameState encMPK encMSK) Inv (inv_step p impl encMPK setupM KG CH)
    (fun q s hs => bridge_step p impl encMPK encMSK setupM KG CH challenge hsetup hkey hch q s hs)
    (A.machine.runOracle A.time (paramsWord U p)) {} trivial
  have h' := congrArg (PMF.map fun r : List Bool × GameState U => (r.1, r.2.attr, r.2.msg, r.2.bad)) h
  rw [PMF.map_comp] at h'
  unfold game Machine.runWith
  rw [← show toGameState encMPK encMSK ({} : GState U (U.Attr × MPK × MSK)) = {} from rfl, ← h']
  rfl

end AdvancedEncryption.PE.Generic
