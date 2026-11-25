import PE.Impl.Game.Generic

/-!
# Eager coins of the challenge

A challenger whose challenge is `g σ μ r` for fresh coins `r ← coins` runs the same experiment
as the challenger that draws `r` together with its secret at the selection and keeps it
(`runWith_eagerCoins`): the challenge is answered at most once.
-/

namespace AdvancedEncryption.PE.Generic

open SigabaNeo Cslib Cslib.Probability

variable {U : Universe} {Sig Coins : Type} (sp : Spec U Sig) (coins : PMF Coins)
  (g : Sig → U.Msg → Coins → List Bool)

/-- The challenger keeping the coins of the challenge in its secret. -/
noncomputable def eagerCoins : Spec U (Sig × Coins) where
  setup x := (sp.setup x).bind fun σ => coins.map (σ, ·)
  pub σ := sp.pub σ.1
  key σ := sp.key σ.1
  chal σ μ := PMF.pure (g σ.1 μ σ.2)
  auth := sp.auth

/-- A state with another secret. -/
def withSec {S S' : Type} (s : GState U S) (sec : Option S') : GState U S' :=
  { attr := s.attr, sec := sec, msg := s.msg, bad := s.bad }

/-- Forget the coins. -/
def dropCoins (s : GState U (Sig × Coins)) : GState U Sig := withSec s (s.sec.map Prod.fst)

variable (hchal : ∀ σ μ, sp.chal σ μ = coins.map (g σ μ))

/-- After the challenge the coins are not read: the two challengers agree. -/
theorem runWith_after_challenge {α : Type}
    (program : ProbOracleComp (fun _ : Fin 3 × List Bool => List Bool) α)
    (s : GState U (Sig × Coins)) (hs : s.msg.isSome) :
    (ProbOracleComp.runWith (oracle (eagerCoins sp coins g)) program s).map
        (fun r => (r.1, dropCoins r.2)) =
      ProbOracleComp.runWith (oracle sp) program (dropCoins s) := by
  refine ProbOracleComp.runWith_map_state_of_invariant (oracle (eagerCoins sp coins g))
    (oracle sp) dropCoins (fun s => s.msg.isSome) ?_ ?_ program s hs
  · intro q s hs a s' h
    rcases s with ⟨attr, sec, msg, bad⟩
    simp only at hs
    obtain ⟨μ, rfl⟩ := Option.isSome_iff_exists.mp hs
    unfold oracle oracleWith at h
    split_ifs at h with hq hk
    · split at h
      · simp only [PMF.mem_support_map_iff] at h
        obtain ⟨σ, -, he⟩ := h; cases he; rfl
      · rw [PMF.mem_support_pure_iff] at h; cases h; rfl
    · split at h
      · simp only [PMF.mem_support_map_iff] at h
        obtain ⟨sk, -, he⟩ := h; cases he; rfl
      · rw [PMF.mem_support_pure_iff] at h; cases h; rfl
    · split at h
      all_goals first
        | (rw [PMF.mem_support_pure_iff] at h; cases h; rfl)
        | simp_all
  · intro q s hs
    rcases s with ⟨attr, sec, msg, bad⟩
    simp only at hs
    obtain ⟨μ, rfl⟩ := Option.isSome_iff_exists.mp hs
    by_cases hq : q.1 = selectOp
    · rcases attr with _ | x
      · rcases hd : decode U.encAttr q.2 with _ | x
        · simp [oracle, oracleWith, hq, hd, dropCoins, withSec]
        · simp only [oracle, oracleWith, hq, hd, if_true, eagerCoins, PMF.map_bind, PMF.map_comp,
            dropCoins, withSec]
          rw [PMF.map]
          refine congrArg (PMF.bind _) (funext fun σ => ?_)
          simp only [Function.comp_def, Option.map_some]
          exact PMF.map_const coins _
      · simp [oracle, oracleWith, hq, dropCoins, withSec]
    · by_cases hk : q.1 = keyGenOp
      · rcases attr with _ | x <;> rcases sec with _ | ⟨σ, r⟩ <;>
          simp [oracle, oracleWith, hq, hk, dropCoins, withSec, eagerCoins, PMF.map_comp,
            Function.comp_def, selectOp, keyGenOp]
      · rcases attr with _ | x <;> rcases sec with _ | ⟨σ, r⟩ <;>
          simp [oracle, oracleWith, hq, hk, dropCoins, withSec]

/-- The eager state of a lazy state before the challenge: fresh coins next to the secret. -/
noncomputable def eLaw (s : GState U Sig) : PMF (GState U (Sig × Coins)) :=
  match s.sec with
  | some σ => coins.map fun r => withSec s (some (σ, r))
  | none => PMF.pure (withSec s none)

theorem obs_withSec {α S S' : Type} (a : α) (s : GState U S) (sec : Option S') :
    obs (a, withSec s sec) = obs (a, s) := rfl

theorem eLaw_bind_const {β : Type} (s : GState U Sig) (b : PMF β) :
    (eLaw coins s).bind (fun _ => b) = b := by
  unfold eLaw; split <;> simp [PMF.bind_const]

include hchal in
/-- **Before the challenge**, the lazy experiment is the eager one averaged over the coins. -/
theorem runWith_before_challenge {α : Type}
    (program : ProbOracleComp (fun _ : Fin 3 × List Bool => List Bool) α) :
    ∀ s : GState U Sig, s.msg = none →
      (ProbOracleComp.runWith (oracle sp) program s).map obs =
        (eLaw coins s).bind fun s' =>
          (ProbOracleComp.runWith (oracle (eagerCoins sp coins g)) program s').map obs := by
  induction program using ProbOracleComp.induction with
  | pure a =>
    intro s hs
    simp only [ProbOracleComp.runWith_pure, PMF.pure_map]
    unfold eLaw; split
    · rw [PMF.bind_map]; simp only [Function.comp_def, obs, withSec]; rw [PMF.bind_const]
    · simp [obs, withSec]
  | sample_bind n cont ih =>
    intro s hs
    simp only [ProbOracleComp.runWith_sample_bind, PMF.map_bind]
    rw [PMF.bind_comm]
    exact congrArg (PMF.bind _) (funext fun i => ih i s hs)
  | query_bind q cont ih =>
    intro s hs
    rcases s with ⟨attr, sec, msg, bad⟩
    simp only at hs
    subst hs
    simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query, PMF.map_bind]
    -- answers that keep the state
    have keep : ∀ (s : GState U Sig), s.msg = none →
        oracle sp q s = PMF.pure ([], s) →
        (∀ s' ∈ (eLaw coins s).support, oracle (eagerCoins sp coins g) q s' = PMF.pure ([], s')) →
        ((oracle sp q s).bind fun x =>
          (ProbOracleComp.runWith (oracle sp) (cont x.1) x.2).map obs) =
          (eLaw coins s).bind fun s' => (oracle (eagerCoins sp coins g) q s').bind fun x =>
            (ProbOracleComp.runWith (oracle (eagerCoins sp coins g)) (cont x.1) x.2).map obs := by
      intro s hs h1 h2
      rw [h1, PMF.pure_bind, ih [] s hs]
      refine PMF.bind_congr_on_support _ _ _ fun s' hs' => ?_
      rw [h2 s' hs', PMF.pure_bind]
    by_cases hq : q.1 = selectOp
    · rcases attr with _ | x
      · rcases hd : decode U.encAttr q.2 with _ | x
        · refine keep _ rfl (by simp [oracle, oracleWith, hq, hd]) fun s' hs' => ?_
          unfold eLaw at hs'
          split at hs' <;> simp only [PMF.mem_support_map_iff, PMF.mem_support_pure_iff] at hs'
          · obtain ⟨r, -, rfl⟩ := hs'; simp [oracle, oracleWith, hq, hd, withSec]
          · subst hs'; simp [oracle, oracleWith, hq, hd, withSec]
        · have h1 : oracle sp q { attr := none, sec := sec, msg := none, bad := bad } =
              (sp.setup x).map fun σ => (sp.pub σ,
                ({ attr := some x, sec := some σ, msg := none, bad := bad } : GState U Sig)) := by
            simp [oracle, oracleWith, hq, hd]
          have h2 : ∀ s' ∈ (eLaw coins
              ({ attr := none, sec := sec, msg := none, bad := bad } : GState U Sig)).support,
              oracle (eagerCoins sp coins g) q s' =
                ((sp.setup x).bind fun σ => coins.map (σ, ·)).map fun σr => (sp.pub σr.1,
                  ({ attr := some x, sec := some σr, msg := none, bad := bad } :
                    GState U (Sig × Coins))) := by
            intro s' hs'
            unfold eLaw at hs'
            split at hs' <;> simp only [PMF.mem_support_map_iff, PMF.mem_support_pure_iff] at hs'
            · obtain ⟨r, -, rfl⟩ := hs'
              simp [oracle, oracleWith, hq, hd, eagerCoins, withSec]
            · subst hs'
              simp [oracle, oracleWith, hq, hd, eagerCoins, withSec]
          rw [h1, PMF.bind_map]
          conv_rhs => rw [PMF.bind_congr_on_support _ _ _ fun s' hs' => by rw [h2 s' hs'],
            eLaw_bind_const, PMF.bind_map, PMF.bind_bind]
          refine congrArg (PMF.bind _) (funext fun σ => ?_)
          simp only [Function.comp_def]
          rw [ih (sp.pub σ) _ rfl]
          simp only [eLaw, PMF.bind_map]
          rfl
      · refine keep _ rfl (by simp [oracle, oracleWith, hq]) fun s' hs' => ?_
        unfold eLaw at hs'
        split at hs' <;> simp only [PMF.mem_support_map_iff, PMF.mem_support_pure_iff] at hs'
        · obtain ⟨r, -, rfl⟩ := hs'; simp [oracle, oracleWith, hq, withSec]
        · subst hs'; simp [oracle, oracleWith, hq, withSec]
    · -- the answers that keep the state, by the shape of the state
      have keepAll : ∀ (hpure : oracle sp q { attr := attr, sec := sec, msg := none, bad := bad } =
            PMF.pure ([], { attr := attr, sec := sec, msg := none, bad := bad }))
          (hpure' : ∀ sec' : Option (Sig × Coins), oracle (eagerCoins sp coins g) q
            (withSec ({ attr := attr, sec := sec, msg := none, bad := bad } : GState U Sig) sec') =
              PMF.pure ([], withSec ({ attr := attr, sec := sec, msg := none, bad := bad } :
                GState U Sig) sec')), _ := fun hpure hpure' =>
        keep _ rfl hpure fun s' hs' => by
          unfold eLaw at hs'
          split at hs' <;> simp only [PMF.mem_support_map_iff, PMF.mem_support_pure_iff] at hs'
          · obtain ⟨r, -, rfl⟩ := hs'; exact hpure' _
          · subst hs'; exact hpure' _
      by_cases hk : q.1 = keyGenOp
      · rcases attr with _ | x
        · exact keepAll (by simp [oracle, oracleWith, hq, hk, selectOp, keyGenOp])
            (fun sec' => by
              cases sec' <;> simp [oracle, oracleWith, hq, hk, withSec, selectOp, keyGenOp])
        · rcases sec with _ | σ
          · exact keep _ rfl (by simp [oracle, oracleWith, hq, hk, selectOp, keyGenOp])
              fun s' hs' => by
                simp only [eLaw, PMF.mem_support_pure_iff] at hs'
                subst hs'
                simp [oracle, oracleWith, hq, hk, withSec, selectOp, keyGenOp]
          · -- a key: its law does not read the coins
            have h1 : oracle sp q { attr := some x, sec := some σ, msg := none, bad := bad } =
                (sp.key σ q.2).map fun sk =>
                  (sk, ({ attr := some x, sec := some σ, msg := none, bad := bad || sp.auth q.2 x } : GState U Sig)) := by
              simp [oracle, oracleWith, hq, hk, selectOp, keyGenOp]
            have h2 : ∀ r, oracle (eagerCoins sp coins g) q
                (withSec ({ attr := some x, sec := some σ, msg := none, bad := bad } : GState U Sig)
                  (some (σ, r))) =
                (sp.key σ q.2).map fun sk =>
                  (sk, withSec ({ attr := some x, sec := some σ, msg := none, bad := bad || sp.auth q.2 x } : GState U Sig) (some (σ, r))) := by
              intro r
              simp [oracle, oracleWith, hq, hk, withSec, eagerCoins, selectOp, keyGenOp]
            rw [h1, PMF.bind_map]
            simp only [eLaw, PMF.bind_map, Function.comp_def, h2]
            conv_rhs => rw [PMF.bind_comm]
            refine congrArg (PMF.bind _) (funext fun sk => ?_)
            rw [ih sk _ rfl]
            simp only [eLaw, PMF.bind_map]
            rfl
      · rcases attr with _ | x
        · exact keepAll (by simp [oracle, oracleWith, hq, hk])
            (fun sec' => by cases sec' <;> simp [oracle, oracleWith, hq, hk, withSec])
        · rcases sec with _ | σ
          · exact keep _ rfl (by simp [oracle, oracleWith, hq, hk])
              fun s' hs' => by
                simp only [eLaw, PMF.mem_support_pure_iff] at hs'
                subst hs'
                simp [oracle, oracleWith, hq, hk, withSec]
          · rcases hd : decode U.encMsg q.2 with _ | μ
            · exact keep _ rfl (by simp [oracle, oracleWith, hq, hk, hd])
                fun s' hs' => by
                  simp only [eLaw, PMF.mem_support_map_iff] at hs'
                  obtain ⟨r, -, rfl⟩ := hs'
                  simp [oracle, oracleWith, hq, hk, hd, withSec]
            · -- the challenge: the eager coins are the lazy ones
              have h1 : oracle sp q { attr := some x, sec := some σ, msg := none, bad := bad } =
                  (coins.map (g σ μ)).map fun ct =>
                    (ct, ({ attr := some x, sec := some σ, msg := some μ, bad := bad } : GState U Sig)) := by
                simp [oracle, oracleWith, hq, hk, hd, hchal]
              have h2 : ∀ r, oracle (eagerCoins sp coins g) q
                  (withSec ({ attr := some x, sec := some σ, msg := none, bad := bad } : GState U Sig)
                    (some (σ, r))) =
                  PMF.pure (g σ μ r, withSec ({ attr := some x, sec := some σ, msg := some μ, bad := bad } : GState U Sig) (some (σ, r))) := by
                intro r
                simp [oracle, oracleWith, hq, hk, hd, withSec, eagerCoins]
              rw [h1, PMF.map_comp, PMF.bind_map]
              simp only [eLaw, PMF.bind_map, Function.comp_def, h2, PMF.pure_bind]
              refine congrArg (PMF.bind coins) (funext fun r => ?_)
              have hq3 := runWith_after_challenge sp coins g (cont (g σ μ r))
                (withSec ({ attr := some x, sec := some σ, msg := some μ, bad := bad } : GState U Sig)
                  (some (σ, r))) rfl
              have hd3 : dropCoins (withSec ({ attr := some x, sec := some σ, msg := some μ, bad := bad } : GState U Sig) (some (σ, r))) =
                  ({ attr := some x, sec := some σ, msg := some μ, bad := bad } : GState U Sig) := rfl
              rw [hd3] at hq3
              rw [← hq3, PMF.map_comp]
              rfl

include hchal in
/-- **Eager coins**: the challenger may draw the coins of the challenge with its secret. -/
theorem runWith_eagerCoins {α : Type}
    (program : ProbOracleComp (fun _ : Fin 3 × List Bool => List Bool) α) :
    (ProbOracleComp.runWith (oracle sp) program ({} : GState U Sig)).map obs =
      (ProbOracleComp.runWith (oracle (eagerCoins sp coins g)) program {}).map obs := by
  rw [runWith_before_challenge sp coins g hchal program {} rfl]
  simp only [eLaw, PMF.pure_bind]
  rfl

end AdvancedEncryption.PE.Generic
