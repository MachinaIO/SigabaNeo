import PE
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.Product

/-!
# The attribute-hiding experiment with an abstract secret

The experiment of `PE.AttributeHiding` with the challenger's secret abstracted (`Spec`): at the
selection of `x` a secret `σ` is drawn from `setup x`, the adversary gets `pub σ`, key queries are
answered by `key σ C` and the challenge by `chal σ μ`; `auth C x` raises the flag `bad`.

**Eager setup** (`runWith_eager`): drawing the secret at the selection is the same as drawing a
table of secrets, one for every attribute, before the run and reading the entry of the selected
attribute. Each attribute is selected at most once, so the experiment is a fixed kernel applied to
the table (`Cslib.Probability.PMF.bind_pi_update`).
-/

namespace AdvancedEncryption.PE.Generic

open SigabaNeo Cslib Cslib.Probability

variable (U : Universe) (Sig : Type)

/-- The state of the experiment. -/
structure GState where
  /-- The selected attribute. -/
  attr : Option U.Attr := none
  /-- The challenger's secret. -/
  sec : Option Sig := none
  /-- The challenge message. -/
  msg : Option U.Msg := none
  /-- Some key query was authorized for the selected attribute. -/
  bad : Bool := false

/-- The challenger, with an abstract secret. -/
structure Spec where
  /-- The law of the secret for the selected attribute. -/
  setup : U.Attr → PMF Sig
  /-- The public key given to the adversary. -/
  pub : Sig → List Bool
  /-- The answer to a key query. -/
  key : Sig → List Bool → PMF (List Bool)
  /-- The challenge ciphertext. -/
  chal : Sig → U.Msg → PMF (List Bool)
  /-- The query `C` is authorized for `x` (raises `bad`). -/
  auth : List Bool → U.Attr → Bool

variable {U Sig}

open Classical in
/-- The oracle, with the secret of the selection drawn from `sel x`. -/
noncomputable def oracleWith (sp : Spec U Sig) (sel : U.Attr → PMF Sig) :
    Fin 3 × List Bool → StateT (GState U Sig) PMF (List Bool) := fun q s =>
  if q.1 = selectOp then
    match s.attr, decode U.encAttr q.2 with
    | none, some x => (sel x).map fun σ => (sp.pub σ, { s with attr := some x, sec := some σ })
    | _, _ => PMF.pure ([], s)
  else if q.1 = keyGenOp then
    match s.attr, s.sec with
    | some x, some σ => (sp.key σ q.2).map fun sk => (sk, { s with bad := s.bad || sp.auth q.2 x })
    | _, _ => PMF.pure ([], s)
  else
    match s.attr, s.sec, s.msg, decode U.encMsg q.2 with
    | some _, some σ, none, some μ => (sp.chal σ μ).map fun ct => (ct, { s with msg := some μ })
    | _, _, _, _ => PMF.pure ([], s)

/-- The oracle of the experiment. -/
noncomputable def oracle (sp : Spec U Sig) := oracleWith sp sp.setup

/-- The oracle reading the secret from a table. -/
noncomputable def oracleTab (sp : Spec U Sig) (tab : U.Attr → Sig) :=
  oracleWith sp fun x => PMF.pure (tab x)

/-! ### Eager setup -/

section Eager

variable [Fintype U.Attr] [DecidableEq U.Attr] [Finite Sig] (sp : Spec U Sig)

/-- The law of the table given the state: the selected entry is the secret, the others fresh. -/
noncomputable def tabLaw (s : GState U Sig) : PMF (U.Attr → Sig) :=
  match s.attr, s.sec with
  | some x, some σ => PMF.pi (Function.update sp.setup x (PMF.pure σ))
  | _, _ => PMF.pi sp.setup

/-- The oracle on the state with the table. -/
noncomputable def oracleE (q : Fin 3 × List Bool) :
    StateT (GState U Sig × (U.Attr → Sig)) PMF (List Bool) := fun st =>
  (oracleTab sp st.2 q st.1).map fun r => (r.1, (r.2, st.2))

theorem oracleWith_of_ne {sel sel' : U.Attr → PMF Sig} (q : Fin 3 × List Bool)
    (hq : q.1 ≠ selectOp) (s : GState U Sig) : oracleWith sp sel q s = oracleWith sp sel' q s := by
  simp [oracleWith, hq]

/-- The answers other than the selection keep the attribute and the secret. -/
theorem oracleWith_keep {sel : U.Attr → PMF Sig} (q : Fin 3 × List Bool) (hq : q.1 ≠ selectOp)
    (s : GState U Sig) : ∀ r ∈ (oracleWith sp sel q s).support,
      r.2.attr = s.attr ∧ r.2.sec = s.sec := by
  intro r hr
  unfold oracleWith at hr
  rw [if_neg hq] at hr
  split_ifs at hr with hk
  · split at hr
    · rw [PMF.mem_support_map_iff] at hr
      obtain ⟨sk, -, rfl⟩ := hr
      exact ⟨rfl, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hr; rw [hr]; exact ⟨rfl, rfl⟩
  · split at hr
    · rw [PMF.mem_support_map_iff] at hr
      obtain ⟨ct, -, rfl⟩ := hr
      exact ⟨rfl, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hr; rw [hr]; exact ⟨rfl, rfl⟩

theorem tabLaw_congr {s s' : GState U Sig} (h : s'.attr = s.attr ∧ s'.sec = s.sec) :
    tabLaw sp s' = tabLaw sp s := by
  unfold tabLaw; rw [h.1, h.2]

/-- **One step of the simulation** of the lazy experiment by the eager one. -/
theorem eager_step (q : Fin 3 × List Bool) (s : GState U Sig) :
    (oracle sp q s).bind (fun r => (tabLaw sp r.2).map fun t => (r.1, (r.2, t))) =
      ((tabLaw sp s).map fun t => (s, t)).bind (oracleE sp q) := by
  rw [PMF.bind_map]
  by_cases hq : q.1 = selectOp
  · rcases s with ⟨attr, sec, msg, bad⟩
    rcases attr with _ | x
    · rcases hd : decode U.encAttr q.2 with _ | x
      · simp only [oracle, oracleE, oracleTab, oracleWith, hq, hd, if_true, tabLaw,
          Function.comp_def, PMF.pure_map, PMF.pure_bind]
        exact (PMF.bind_pure_comp _ _).symm
      · -- the selection: draw the secret, or read the table
        simp only [oracle, oracleE, oracleTab, oracleWith, hq, hd, if_true, tabLaw,
          Function.comp_def, PMF.bind_map, PMF.pure_map]
        exact Cslib.Probability.PMF.bind_pi_update sp.setup x
          (fun σ t => PMF.pure (sp.pub σ,
            ({ attr := some x, sec := some σ, msg := msg, bad := bad } : GState U Sig), t))
    · rcases sec with _ | σ <;>
      · simp only [oracle, oracleE, oracleTab, oracleWith, hq, if_true, tabLaw,
          Function.comp_def, PMF.pure_map, PMF.pure_bind]
        exact (PMF.bind_pure_comp _ _).symm
  · -- the other queries do not use the table
    have hind : ∀ t, oracleTab sp t q s = oracle sp q s := fun t =>
      oracleWith_of_ne sp q hq s
    simp only [oracleE, Function.comp_def, hind]
    calc ((oracle sp q s).bind fun r => PMF.map (fun t => (r.1, r.2, t)) (tabLaw sp r.2))
        = (oracle sp q s).bind fun r => (tabLaw sp s).bind fun t => PMF.pure (r.1, r.2, t) :=
          PMF.bind_congr_on_support _ _ _ fun r hr => by
            rw [tabLaw_congr sp (oracleWith_keep sp q hq s r hr)]; rfl
      _ = (tabLaw sp s).bind fun t => (oracle sp q s).bind fun r => PMF.pure (r.1, r.2, t) :=
          PMF.bind_comm _ _ _
      _ = _ := rfl

/-- The run of the eager oracle with a fixed table, forgetting the table. -/
theorem runWith_oracleE {α : Type}
    (program : ProbOracleComp (fun _ : Fin 3 × List Bool => List Bool) α) (s : GState U Sig)
    (t : U.Attr → Sig) :
    (ProbOracleComp.runWith (oracleE sp) program (s, t)).map (fun r => (r.1, r.2.1)) =
      ProbOracleComp.runWith (oracleTab sp t) program s := by
  refine ProbOracleComp.runWith_map_state_of_invariant (oracleE sp) (oracleTab sp t)
    (fun st => st.1) (fun st => st.2 = t) ?_ ?_ program (s, t) rfl
  · intro q st hst a st' h
    simp only [oracleE, PMF.mem_support_map_iff] at h
    obtain ⟨r, -, hr⟩ := h
    rw [← hst]
    exact (congrArg (fun p => p.2.2) hr).symm
  · intro q st hst
    simp only [oracleE, PMF.map_comp]
    rw [← hst]
    simp only [Function.comp_def]
    exact PMF.map_id _

/-- **Eager setup**: the experiment draws a table of secrets before the run. -/
theorem runWith_eager {α : Type}
    (program : ProbOracleComp (fun _ : Fin 3 × List Bool => List Bool) α) :
    ProbOracleComp.runWith (oracle sp) program ({} : GState U Sig) =
      (PMF.pi sp.setup).bind fun t => ProbOracleComp.runWith (oracleTab sp t) program {} := by
  have h := ProbOracleComp.runWith_simulation (oracle sp) (oracleE sp)
    (fun s => (tabLaw sp s).map fun t => (s, t)) (fun q s => by
      rw [← eager_step sp q s]
      refine congrArg (PMF.bind _) (funext fun r => ?_)
      obtain ⟨a, s'⟩ := r
      show PMF.map (fun x => (a, x)) (PMF.map (fun t => (s', t)) (tabLaw sp s')) = _
      rw [PMF.map_comp]; rfl) program {}
  have h' := congrArg (PMF.map fun r : α × (GState U Sig × (U.Attr → Sig)) => (r.1, r.2.1)) h
  rw [PMF.map_bind, PMF.map_bind] at h'
  have lhs : (ProbOracleComp.runWith (oracle sp) program ({} : GState U Sig)).bind
      (fun r => PMF.map (fun r : α × (GState U Sig × (U.Attr → Sig)) => (r.1, r.2.1))
        (PMF.map (fun x => (r.1, x)) ((tabLaw sp r.2).map fun t => (r.2, t)))) =
      ProbOracleComp.runWith (oracle sp) program {} := by
    conv_rhs => rw [← PMF.bind_pure (ProbOracleComp.runWith (oracle sp) program {})]
    refine congrArg (PMF.bind _) (funext fun r => ?_)
    rw [PMF.map_comp, PMF.map_comp]
    exact PMF.map_const (tabLaw sp r.2) r
  rw [lhs] at h'
  rw [h', tabLaw, PMF.bind_map]
  · refine congrArg (PMF.bind _) (funext fun t => ?_)
    exact runWith_oracleE sp program {} t

end Eager

end AdvancedEncryption.PE.Generic
