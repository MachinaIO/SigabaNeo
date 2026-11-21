import PE
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.Product
import SigabaNeo.Lib.Lattices.Stat

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

/-- The answers other than the selection do not read the law of the secret. -/
theorem oracleWith_of_ne (sp : Spec U Sig) {sel sel' : U.Attr → PMF Sig} (q : Fin 3 × List Bool)
    (hq : q.1 ≠ selectOp) (s : GState U Sig) : oracleWith sp sel q s = oracleWith sp sel' q s := by
  simp [oracleWith, hq]

/-- The answers other than the selection keep the attribute and the secret. -/
theorem oracleWith_keep (sp : Spec U Sig) {sel : U.Attr → PMF Sig} (q : Fin 3 × List Bool) (hq : q.1 ≠ selectOp)
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

/-- The table oracle does not read the law of the secret. -/
theorem oracleTab_setup (setup' : U.Attr → PMF Sig) (t : U.Attr → Sig) :
    oracleTab { sp with setup := setup' } t = oracleTab sp t := rfl

/-- **A statistical change of the secret**: if the law of the secret moves by at most `ε x` for
every attribute `x`, the experiment moves by at most `∑ x, ε x`. -/
theorem closeTo_runWith_setup {α : Type}
    (program : ProbOracleComp (fun _ : Fin 3 × List Bool => List Bool) α)
    (setup' : U.Attr → PMF Sig) (ε : U.Attr → ENNReal)
    (h : ∀ x, CloseTo (sp.setup x) (setup' x) (ε x)) :
    CloseTo (ProbOracleComp.runWith (oracle sp) program ({} : GState U Sig))
      (ProbOracleComp.runWith (oracle { sp with setup := setup' }) program {}) (∑ x, ε x) := by
  rw [runWith_eager, runWith_eager]
  simp only [oracleTab_setup]
  exact (SigabaNeo.Lattices.closeTo_pi _ _ ε h).bind_left _

end Eager

/-! ### What the adversary and the distinguisher see -/

/-- The observable part of a run: the output, the attribute, the message and the flag. -/
def obs {α : Type} (r : α × GState U Sig) : α × Option U.Attr × Option U.Msg × Bool :=
  (r.1, r.2.attr, r.2.msg, r.2.bad)

/-! ### Changing the representation of the secret -/

section Represent

variable {Sig' : Type} (sp : Spec U Sig) (f : Sig' → Sig)

/-- The challenger reading its secret through `f`. -/
noncomputable def Spec.comap (setup' : U.Attr → PMF Sig') : Spec U Sig' where
  setup := setup'
  pub := sp.pub ∘ f
  key := sp.key ∘ f
  chal := sp.chal ∘ f
  auth := sp.auth

/-- The state with the secret mapped. -/
def mapSec (s : GState U Sig') : GState U Sig :=
  { attr := s.attr, sec := s.sec.map f, msg := s.msg, bad := s.bad }

/-- **Representation of the secret**: a challenger that reads its secret `σ'` only through
`f σ'` runs the experiment of the image law. -/
theorem runWith_comap {α : Type}
    (program : ProbOracleComp (fun _ : Fin 3 × List Bool => List Bool) α)
    (setup' : U.Attr → PMF Sig') (hsetup : ∀ x, (setup' x).map f = sp.setup x) :
    (ProbOracleComp.runWith (oracle (sp.comap f setup')) program ({} : GState U Sig')).map
        (fun r => (r.1, mapSec f r.2)) =
      ProbOracleComp.runWith (oracle sp) program {} := by
  refine ProbOracleComp.runWith_map_state (oracle (sp.comap f setup')) (oracle sp) (mapSec f)
    ?_ program {}
  intro q s
  rcases s with ⟨attr, sec, msg, bad⟩
  by_cases hq : q.1 = selectOp
  · rcases attr with _ | x
    · rcases hd : decode U.encAttr q.2 with _ | x
      · simp [oracle, oracleWith, hq, hd, mapSec]
      · simp only [oracle, oracleWith, hq, hd, if_true, PMF.map_comp, mapSec]
        rw [← hsetup x, PMF.map_comp]
        rfl
    · simp [oracle, oracleWith, hq, mapSec]
  · by_cases hk : q.1 = keyGenOp
    · rcases attr with _ | x <;> rcases sec with _ | σ <;>
        simp [oracle, oracleWith, hq, hk, mapSec, Spec.comap, PMF.map_comp, Function.comp_def,
          selectOp, keyGenOp]
    · rcases attr with _ | x <;> rcases sec with _ | σ <;> rcases msg with _ | μ <;>
        rcases hd : decode U.encMsg q.2 with _ | μ' <;>
        simp [oracle, oracleWith, hq, hk, hd, mapSec, Spec.comap, PMF.map_comp, Function.comp_def]

/-! ### A shared instance -/

variable {Inst : Type} (inst : PMF Inst) (F : U.Attr → Inst → PMF Sig)

/-- The challenger drawing an instance `i` at the selection and the secret from `F x i`, keeping
`i`. -/
noncomputable def shared : Spec U (Inst × Sig) :=
  sp.comap Prod.snd fun x => inst.bind fun i => (F x i).map (i, ·)

/-- The challenger with the instance `i` fixed. -/
noncomputable def atInst (i : Inst) : Spec U (Inst × Sig) :=
  sp.comap Prod.snd fun x => (F x i).map (i, ·)

/-- The law of the instance given the state. -/
noncomputable def instLaw (s : GState U (Inst × Sig)) : PMF Inst :=
  match s.attr, s.sec with
  | some _, some σ => PMF.pure σ.1
  | _, _ => inst

/-- The oracle with the instance in the state. -/
noncomputable def oracleI (q : Fin 3 × List Bool) :
    StateT (GState U (Inst × Sig) × Inst) PMF (List Bool) := fun st =>
  (oracle (atInst sp F st.2) q st.1).map fun r => (r.1, (r.2, st.2))

theorem share_step (q : Fin 3 × List Bool) (s : GState U (Inst × Sig)) :
    (oracle (shared sp inst F) q s).bind (fun r => (instLaw inst r.2).map fun i => (r.1, (r.2, i))) =
      ((instLaw inst s).map fun i => (s, i)).bind (oracleI sp F q) := by
  rw [PMF.bind_map]
  rcases s with ⟨attr, sec, msg, bad⟩
  by_cases hq : q.1 = selectOp
  · rcases attr with _ | x
    · rcases hd : decode U.encAttr q.2 with _ | x
      · simp only [oracle, oracleI, oracleWith, hq, hd, if_true, instLaw, Function.comp_def,
          PMF.pure_map, PMF.pure_bind]
        exact (PMF.bind_pure_comp _ _).symm
      · simp only [oracle, oracleI, oracleWith, hq, hd, if_true, instLaw, Function.comp_def,
          PMF.bind_map, PMF.pure_map, shared, atInst, Spec.comap, PMF.bind_bind, PMF.map_bind]
        refine congrArg (PMF.bind inst) (funext fun i => ?_)
        simp only [PMF.bind_map, PMF.map_comp, Function.comp_def, PMF.pure_map]
        rw [PMF.map]
        rfl
    · rcases sec with _ | ⟨i, σ⟩ <;>
      · simp only [oracle, oracleI, oracleWith, hq, if_true, instLaw, Function.comp_def,
          PMF.pure_map, PMF.pure_bind]
        try exact (PMF.bind_pure_comp _ _).symm
  · have hind : ∀ i, oracle (atInst sp F i) q = oracle (shared sp inst F) q := fun i =>
      funext fun s => by simp only [oracle, oracleWith, if_neg hq]; rfl
    simp only [oracleI, Function.comp_def, hind]
    calc ((oracle (shared sp inst F) q { attr := attr, sec := sec, msg := msg, bad := bad }).bind
          fun r => PMF.map (fun i => (r.1, r.2, i)) (instLaw inst r.2))
        = (oracle (shared sp inst F) q { attr := attr, sec := sec, msg := msg, bad := bad }).bind
            fun r => (instLaw inst { attr := attr, sec := sec, msg := msg, bad := bad }).bind
              fun i => PMF.pure (r.1, r.2, i) :=
          PMF.bind_congr_on_support _ _ _ fun r hr => by
            have hk := oracleWith_keep _ q hq _ r hr
            simp only [instLaw, hk.1, hk.2]; rfl
      _ = _ := PMF.bind_comm _ _ _

theorem runWith_oracleI {α : Type}
    (program : ProbOracleComp (fun _ : Fin 3 × List Bool => List Bool) α)
    (s : GState U (Inst × Sig)) (i : Inst) :
    (ProbOracleComp.runWith (oracleI sp F) program (s, i)).map (fun r => (r.1, r.2.1)) =
      ProbOracleComp.runWith (oracle (atInst sp F i)) program s := by
  refine ProbOracleComp.runWith_map_state_of_invariant (oracleI sp F) (oracle (atInst sp F i))
    (fun st => st.1) (fun st => st.2 = i) ?_ ?_ program (s, i) rfl
  · intro q st hst a st' h
    simp only [oracleI, PMF.mem_support_map_iff] at h
    obtain ⟨r, -, hr⟩ := h
    rw [← hst]
    exact (congrArg (fun p => p.2.2) hr).symm
  · intro q st hst
    simp only [oracleI, PMF.map_comp]
    rw [← hst]
    simp only [Function.comp_def]
    exact PMF.map_id _

/-- **A shared instance**: the experiment that draws the instance at the selection is the
average over the instance of the experiments with the instance fixed. -/
theorem runWith_shared {α : Type}
    (program : ProbOracleComp (fun _ : Fin 3 × List Bool => List Bool) α) :
    ProbOracleComp.runWith (oracle (shared sp inst F)) program ({} : GState U (Inst × Sig)) =
      inst.bind fun i => ProbOracleComp.runWith (oracle (atInst sp F i)) program {} := by
  have h := ProbOracleComp.runWith_simulation (oracle (shared sp inst F)) (oracleI sp F)
    (fun s => (instLaw inst s).map fun i => (s, i)) (fun q s => by
      rw [← share_step sp inst F q s]
      refine congrArg (PMF.bind _) (funext fun r => ?_)
      obtain ⟨a, s'⟩ := r
      show PMF.map (fun x => (a, x)) (PMF.map (fun i => (s', i)) (instLaw inst s')) = _
      rw [PMF.map_comp]; rfl) program {}
  have h' := congrArg
    (PMF.map fun r : α × (GState U (Inst × Sig) × Inst) => (r.1, r.2.1)) h
  rw [PMF.map_bind, PMF.map_bind] at h'
  have lhs : (ProbOracleComp.runWith (oracle (shared sp inst F)) program
      ({} : GState U (Inst × Sig))).bind
      (fun r => PMF.map (fun r : α × (GState U (Inst × Sig) × Inst) => (r.1, r.2.1))
        (PMF.map (fun x => (r.1, x)) ((instLaw inst r.2).map fun i => (r.2, i)))) =
      ProbOracleComp.runWith (oracle (shared sp inst F)) program {} := by
    conv_rhs => rw [← PMF.bind_pure (ProbOracleComp.runWith (oracle (shared sp inst F)) program {})]
    refine congrArg (PMF.bind _) (funext fun r => ?_)
    rw [PMF.map_comp, PMF.map_comp]
    exact PMF.map_const (instLaw inst r.2) r
  rw [lhs] at h'
  rw [h', instLaw, PMF.bind_map]
  refine congrArg (PMF.bind _) (funext fun i => ?_)
  exact runWith_oracleI sp F program {} i

end Represent

end AdvancedEncryption.PE.Generic
