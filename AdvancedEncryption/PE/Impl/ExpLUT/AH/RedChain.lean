import PE.Impl.ExpLUT.AH.Final
import PE.Impl.ExpLUT.AH.CircBridge
import PE.Impl.DualUse.Prog.Post
import PE.Impl.Game.HandlersPCost
import SigabaNeo.Lib.Machines.Inline.InitStructCost
import SigabaNeo.Lib.Machines.Inline.InitPerQuery

/-!
# The reduction machine from component programs (package G2, plumbing)

The reduction machine of the circular Ring-LWE step is the chain (as `DualUse.reductionP`)

`P.andThenLin (((A.inlineOracleInit H w₀ E Q Lₐ).andThenLin Post).andThenGuard Dm)`

with the generic handlers `Generic.handlersP` of component programs (`Generic.Comps`) for the
machines' reduction challenger `specRedW` (`AH/RedGame`), whose secret is drawn from the instance
word kept in the handlers' state (`setupR`: a law `setupS` representing `redSecW` of the decoded
instance through `f`, `spS`), the
post-processing `Generic.Post` (`[false]` when the flag is up, else `true :: viewObs8 o`) and the
distinguisher `Dm` behind a guard.

* `w8Codes`: the codes of the universe `univ w8` (128-bit attributes, onto: `encAttribute_onto`;
  one message bit);
* `acceptProb_redM8`: the acceptance of the chain, for any handlers serving an oracle whose
  observations from the start state of a word are a given game;
* `RedComps`: **the data of a reduction from components** — the decoder `P` (instance word to
  state word `dw w`, read back by `instOf`), the components `cs` with their length bounds `cb`
  (key queries cut at `L`), the bound `Lₐ` on the answers;
* **`redMachine_of_comps`**: such data give `RedMachine D kb L (circParamsD D) impl (χcbd D)
  (χcbd D) χfl C A Dm` for every `A`, `Dm`, with `C = redConst` (`chainConst` of the chain);
  `redConst_le_two_pow`: a power-of-two bound from bounds on the parts (`chainConst_le_two_pow`).
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Generic
open SigabaNeo.Inline
open scoped ENNReal

/-! ### The codes of `univ w8` -/

/-- **The attribute encoding is onto the words of 128 bits** (an injection between sets of
`2^128` elements). -/
theorem encAttribute_onto (w : Width) (l : List Bool) (hl : l.length = 128) :
    ∃ x, encAttribute w x = l := by
  classical
  let f : Attribute w → List.Vector Bool 128 := fun x => ⟨encAttribute w x, length_encAttribute w x⟩
  have hf : Function.Injective f := fun a b h =>
    (encAttribute w).injective (congrArg Subtype.val h)
  have hc : Fintype.card (Attribute w) = Fintype.card (List.Vector Bool 128) := by
    rw [card_vector, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Fintype.card_bool,
      ← pow_mul, w.bits_mul_len]
  obtain ⟨x, hx⟩ := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hc⟩).2 ⟨l, hl⟩
  exact ⟨x, congrArg Subtype.val hx⟩

/-- **The codes of the universe `w8`**, for a fixed-length encoding of the secret. -/
def w8Codes {Sig : Type} {nS : ℕ} (sig : FixedEnc Sig nS) : Codes (univ w8) Sig where
  nA := 128
  nM := 1
  nS := nS
  sig := sig
  len_attr x := length_encAttribute w8 x
  len_msg μ := rfl
  full_attr w hw := encAttribute_onto w8 w hw
  full_msg w hw := by
    match w, hw with
    | [b], _ => exact ⟨b, rfl⟩

/-! ### The chain and its acceptance -/

/-- The observations of a run. -/
abbrev Ob8 := List Bool × Option (univ w8).Attr × Option (univ w8).Msg × Bool

theorem guardK_postG (Dm : Machine) (ob : Ob8) :
    (Dm.guardK (postG ob)) [true] = DcB Dm ob true := by
  unfold postG DcB
  rcases hb : ob.2.2.2
  · simp only [Bool.false_eq_true, ite_false, Machine.guardK_true]
    rw [PMF.map_apply, tsum_eq_single [true]]
    · simp [viewObs8]
    · intro b hb; simp [hb]
  · simp

variable {m : ℕ}

/-- **The reduction machine**: the decoder `P`, the inlined adversary against the handlers `H`
(per-query clock `q₀ + q₁ |b|`, answers of at most `Lₐ` bits, states of at most `E` bits), the
post-processing `Post` and the guarded distinguisher `Dm`. -/
noncomputable def redM8 (P Post : Machine) (A : Machine 3) (H : Fin 3 → Routine (m + 3))
    (E q₀ q₁ La : ℕ) (Dm : Machine) : Machine :=
  P.andThenLin (((A.inlineOracleInit H (paramsWord (univ w8) params) E (q₀ + q₁ * 3) La).andThenLin
    Post).andThenGuard Dm)

/-- **Acceptance of the reduction machine**: when the handlers serve an oracle `orc` whose
observations from the start state `s₀ w` of the state word of `w` are the game `G w`. -/
theorem acceptProb_redM8 {σ : Type} (P Post : Machine) (A : Machine 3)
    (H : Fin 3 → Routine (m + 3)) (orc : Fin 3 × List Bool → StateT σ PMF (List Bool))
    (enc : σ → List Bool) (InvS : σ → Prop) (E q₀ q₁ La : ℕ)
    (hH : HandlesP A H orc enc InvS q₀ q₁ La) (hE : ∀ s, InvS s → (enc s).length ≤ E)
    (obsOf : List Bool → σ → Ob8) (Dm : Machine) (μ : PMF (List Bool)) (s₀ : List Bool → σ)
    (hs₀ : ∀ w ∈ μ.support, InvS (s₀ w))
    (hP : ∀ w ∈ μ.support, P.run w = PMF.pure (enc (s₀ w)))
    (hPost : ∀ o s, o.length ≤ A.time → InvS s →
      Post.run (pairOut o (enc s)) = PMF.pure (postG (obsOf o s)))
    (G : List Bool → PMF Ob8)
    (hgame : ∀ w ∈ μ.support,
      (A.runWith orc (paramsWord (univ w8) params) (s₀ w)).map (fun r => obsOf r.1 r.2) = G w) :
    (redM8 P Post A H E q₀ q₁ La Dm).acceptProb μ =
      ((μ.bind fun w => (G w).bind (DcB Dm)) true).toReal := by
  unfold redM8
  rw [Machine.acceptProb_andThenLin_andThenGuard]
  congr 1
  rw [PMF.bind_bind, PMF.bind_bind, PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun w => ?_
  by_cases hw : w ∈ μ.support
  · congr 1
    rw [hP w hw, PMF.pure_bind, Machine.run_andThenLin,
      Machine.run_inlineOracleInitP A H _ orc enc InvS E q₀ q₁ La hH hE (s₀ w) (hs₀ w hw) _ rfl,
      PMF.bind_map, PMF.bind_bind]
    have h1 : ((A.runWith orc (paramsWord (univ w8) params) (s₀ w)).bind
        fun r => (Post.run (pairOut r.1 (enc r.2))).bind Dm.guardK) =
        (((A.runWith orc (paramsWord (univ w8) params) (s₀ w)).map
          (fun r => obsOf r.1 r.2))).bind (fun ob => Dm.guardK (postG ob)) := by
      rw [PMF.bind_map]
      refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ (fun r hr => ?_)
      obtain ⟨hlen, hinv⟩ := A.runWith_support_inv orc InvS
        (fun o b s hb hs r hr => (hH.inv o b s hb hs r hr).1) _ (s₀ w) (hs₀ w hw) r hr
      simp only [Function.comp_apply, hPost r.1 r.2 hlen hinv, PMF.pure_bind]
    rw [Function.comp_def] at *
    rw [h1, hgame w hw, PMF.bind_apply, PMF.bind_apply]
    refine tsum_congr fun ob => ?_
    rw [guardK_postG]
  · rw [(PMF.apply_eq_zero_iff _ _).mpr hw, zero_mul, zero_mul]

/-! ### The challenger of the handlers -/

variable (D : Dims) (kb : KeyBoxes D) (L : ℕ)

variable {Sig : Type} (f : Sig → RSec D) (setupS : CInst D → Attribute w8 → PMF Sig)

/-- **The challenger of the handlers**: `specRedW` reading its secret through `f` (the handlers'
secret type `Sig` is finite and encoded with a fixed length, unlike `RSec D`). -/
noncomputable def spS (impl : Impl sig) (χfl : PMF (Rg D)) (i₀ : CInst D) : Spec (univ w8) Sig :=
  (specRedW D kb L impl χfl i₀).comap f (setupS i₀)

/-- **The secret of the selection for the state word `w`**: `setupS` of the instance
`instOf w`. -/
noncomputable def setupR (instOf : List Bool → CInst D) (w : List Bool) : (univ w8).Attr → PMF Sig :=
  setupS (instOf w)

/-- **The handlers' oracle has the observations of the machines' reduction experiment** of the
instance of the state word, when `setupS` represents the machines' reduction secret through `f`. -/
theorem obs_oracleW_red (impl : Impl sig) (χfl : PMF (Rg D))
    (hS : ∀ i x, (setupS i x).map f = redSecW D χfl x i) (instOf : List Bool → CInst D)
    (i₀ : CInst D) (A : Machine 3) (w : List Bool) :
    (A.runWith (oracleW (spS D kb L f setupS impl χfl i₀) (setupR D setupS instOf))
        (paramsWord (univ w8) params) (w, {})).map (fun r => Generic.obs (r.1, r.2.2)) =
      redGameW D kb L impl χfl A (instOf w) := by
  have h1 := ProbOracleComp.runWith_map_state
    (Generic.oracle (spS D kb L f setupS impl χfl (instOf w)))
    (oracleW (spS D kb L f setupS impl χfl i₀) (setupR D setupS instOf)) (fun s => (w, s))
    (fun q s => rfl) (A.machine.runOracle A.time (paramsWord (univ w8) params))
    ({} : Generic.GState (univ w8) Sig)
  have h2 := Generic.runWith_comap (specRedW D kb L impl χfl (instOf w)) f
    (A.machine.runOracle A.time (paramsWord (univ w8) params)) (setupS (instOf w))
    (fun x => hS (instOf w) x)
  unfold Machine.runWith redGameW
  rw [← h1, PMF.map_comp]
  rw [← h2, PMF.map_comp]
  rfl

/-- **Long key queries**: answered by the empty word and never authorized, when `predLen ≤ L`. -/
theorem longKeys_red {impl : Impl sig} (hEval : impl.machine .eval = evalMachineX)
    (hL : predLen ≤ L) (χfl : PMF (Rg D)) (i₀ : CInst D) (Ok : Sig → Prop) :
    LongKeys (spS D kb L f setupS impl χfl i₀) Ok L [] where
  key σ C _ hC := by
    show KGsim D kb L (f σ) C = PMF.pure []
    unfold KGsim
    simp only [show ¬ C.length ≤ L by omega, ↓reduceIte]
  auth C x hC := by
    show authW impl C x = false
    unfold authW
    rw [decide_eq_false_iff_not]
    intro h
    have := ((authorized_iff impl hEval C x).mp h).1
    omega

/-! ### Reductions from components -/

/-- The length of the words of a fixed-length encoding. -/
def _root_.SigabaNeo.Encode.FixedEnc.len {β : Type} {n : ℕ} (_ : FixedEnc β n) : ℕ := n

theorem length_fixedEnc_enc {β : Type} {n : ℕ} (e : FixedEnc β n) (b : β) :
    (e.enc b).length = e.len := e.length b

/-- **The data of a reduction from components**: a fixed-length encoding `senc` of the secret, the
decoder `P` turning the word of every instance `i` into the state word `dw (enc D i)` (not
starting with `false`, at most `W` bits, admissible: `IW`) whose instance is read back by
`instOf`, the components `cs` (on `R + 2` tapes) of the handlers of the challenger `specRedW`
with the secret of `setupR`, their length bounds `cb` (key queries cut at `L`), and a bound `La`
on the answers. -/
structure RedComps (impl : Impl sig) (χfl : PMF (Rg D)) where
  /-- The scratch tapes of the components. -/
  R : ℕ
  /-- The secret of the handlers. -/
  Sig : Type
  /-- The machines' reduction secret it represents. -/
  f : Sig → RSec D
  /-- Its law, for an instance and an attribute. -/
  setupS : CInst D → Attribute w8 → PMF Sig
  map_setupS : ∀ i x, (setupS i x).map f = redSecW D χfl x i
  /-- The length of the encoded secret. -/
  nS : ℕ
  /-- The encoding of the secret. -/
  senc : FixedEnc Sig nS
  /-- The admissible state words. -/
  IW : List Bool → Prop
  /-- The admissible secrets. -/
  Ok : Sig → Prop
  /-- A bound on the state words. -/
  W : ℕ
  /-- The instance of a state word. -/
  instOf : List Bool → CInst D
  /-- The components. -/
  cs : Comps R (w8Codes senc) (spS D kb L f setupS impl χfl (instOf [])) (setupR D setupS instOf) IW Ok
  /-- Their length bounds, key queries cut at `L`. -/
  cb : CompBoundsP cs L W
  /-- The decoder. -/
  P : Machine
  /-- The state word of an instance word. -/
  dw : List Bool → List Bool
  run_P : ∀ i : CInst D, P.run (enc D i) = PMF.pure (dw (enc D i))
  instOf_dw : ∀ i : CInst D, instOf (dw (enc D i)) = i
  iw : ∀ i : CInst D, IW (dw (enc D i)) ∧ (dw (enc D i)).length ≤ W ∧
    (dw (enc D i)).head? ≠ some false
  /-- A bound on the answers. -/
  La : ℕ
  pubL : (mpkEnc D).len ≤ La
  keyL : (skEnc D).len ≤ La
  chalL : (ctEnc D).len ≤ La

variable {D kb L}

namespace RedComps

variable {impl : Impl sig} {χfl : PMF (Rg D)} (rc : RedComps D kb L impl χfl)

/-- The handlers of the components. -/
noncomputable def H : Fin 3 → Routine (rc.R + 5 + 3) :=
  handlersP (w8Codes rc.senc) rc.cs L [] rc.W

/-- The bound on the encoded states. -/
def E : ℕ := stateBound (w8Codes rc.senc) rc.W

/-- **The reduction machine of the components.** -/
noncomputable def machine (A : Machine 3) (Dm : Machine) : Machine :=
  redM8 rc.P (Post A.time rc.E 128 1) A rc.H rc.E (handlerQ0 rc.cb []) (handlerQ1 (w8Codes rc.senc) L [])
    rc.La Dm

/-- **The constant of the reduction of the components.** -/
noncomputable def const : ℕ :=
  chainConst rc.P (Post 0 0 128 1) rc.H (handlerQ0 rc.cb [] + handlerQ1 (w8Codes rc.senc) L [] * 3)
    rc.La rc.E (postA rc.E 128 1 + postB rc.E 128 1) (paramsWord (univ w8) params).length

theorem hgame (A : Machine 3) (w : List Bool) :
    (A.runWith (oracleW (spS D kb L rc.f rc.setupS impl χfl (rc.instOf [])) (setupR D rc.setupS rc.instOf))
        (paramsWord (univ w8) params) (w, {})).map (fun r => Generic.obs (r.1, r.2.2)) =
      redGameW D kb L impl χfl A (rc.instOf w) :=
  obs_oracleW_red D kb L rc.f rc.setupS impl χfl rc.map_setupS rc.instOf (rc.instOf []) A w

theorem length_KGsim' (σ : RSec D) (C : List Bool) :
    ∀ sk ∈ (KGsim D kb L σ C).support, sk.length ≤ (skEnc D).len := by
  intro sk hsk
  unfold KGsim at hsk
  split_ifs at hsk
  · obtain ⟨o, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hsk
    exact le_of_eq ((skEnc D).length _)
  · rw [PMF.mem_support_pure_iff] at hsk; subst hsk
    exact le_of_eq ((skEnc D).length _)
  · rw [PMF.mem_support_pure_iff] at hsk; subst hsk; exact Nat.zero_le _

/-- **The handlers of the components serve the oracle**, per query. -/
theorem handles (hEval : impl.machine .eval = evalMachineX) (hL : predLen ≤ L) (A : Machine 3) :
    HandlesP A rc.H (oracleW (spS D kb L rc.f rc.setupS impl χfl (rc.instOf [])) (setupR D rc.setupS rc.instOf))
      (w8Codes rc.senc).encState (InvS rc.IW rc.W rc.Ok) (handlerQ0 rc.cb [])
      (handlerQ1 (w8Codes rc.senc) L []) rc.La :=
  handlesP rc.cs L [] (longKeys_red D kb L rc.f rc.setupS hEval hL χfl (rc.instOf []) rc.Ok) rc.cb A rc.La
    (fun σ _ => le_trans (le_of_eq ((mpkEnc D).length _)) rc.pubL)
    (fun σ C _ _ sk hsk => le_trans (length_KGsim' (rc.f σ) C sk hsk) rc.keyL)
    (Nat.zero_le _)
    (fun σ μ _ ct hct => by
      rw [(PMF.mem_support_pure_iff _ _).mp hct]
      exact le_trans (le_of_eq ((ctEnc D).length _)) rc.chalL)

theorem support_map_enc {ν : PMF (CInst D)} :
    ∀ w ∈ (ν.map (enc D)).support, ∃ i, w = enc D i := by
  intro w hw
  obtain ⟨i, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hw
  exact ⟨i, rfl⟩

/-- **Acceptance of the reduction of the components** on a law of instance words. -/
theorem acceptProb_machine (hEval : impl.machine .eval = evalMachineX) (hL : predLen ≤ L)
    (A : Machine 3) (Dm : Machine) (ν : PMF (CInst D)) :
    (rc.machine A Dm).acceptProb (ν.map (enc D)) =
      ((ν.bind fun i => (redGameW D kb L impl χfl A i).bind (DcB Dm)) true).toReal := by
  have hE : ∀ s, InvS rc.IW rc.W rc.Ok s → ((w8Codes rc.senc).encState s).length ≤ rc.E :=
    fun s h => length_encState_le h
  have key := acceptProb_redM8 rc.P (Post A.time rc.E 128 1) A rc.H
    (oracleW (spS D kb L rc.f rc.setupS impl χfl (rc.instOf [])) (setupR D rc.setupS rc.instOf))
    (w8Codes rc.senc).encState (InvS rc.IW rc.W rc.Ok) rc.E (handlerQ0 rc.cb [])
    (handlerQ1 (w8Codes rc.senc) L []) rc.La (rc.handles hEval hL A) hE
    (fun o s => Generic.obs (o, s.2)) Dm (ν.map (enc D)) (fun w => (rc.dw w, {}))
    (fun w hw => by
      obtain ⟨i, rfl⟩ := support_map_enc w hw
      exact ⟨(rc.iw i).1, (rc.iw i).2.1, (rc.iw i).2.2, Or.inl rfl⟩)
    (fun w hw => by
      obtain ⟨i, rfl⟩ := support_map_enc w hw
      rw [rc.run_P i, Codes.encState_init])
    (fun o s ho hs => run_post (w8Codes rc.senc) A.time rc.E o s ho
      (postOK_of_invS _ hs (hE s hs)))
    (fun w => redGameW D kb L impl χfl A (rc.instOf (rc.dw w)))
    (fun w _ => rc.hgame A (rc.dw w))
  refine key.trans ?_
  rw [PMF.bind_map]
  simp only [Function.comp_def, rc.instOf_dw]

/-- **Cost of the reduction of the components.** -/
theorem cost_machine (A : Machine 3) (Dm : Machine) :
    ((rc.machine A Dm).cost : ℝ) ≤ (rc.const : ℝ) * ((A.cost + Dm.cost : ℕ) : ℝ) ^ 2 := by
  have h := Machine.cost_chain_le rc.P (Post A.time rc.E 128 1) Dm A rc.H
    (paramsWord (univ w8) params) rc.E (handlerQ0 rc.cb [] + handlerQ1 (w8Codes rc.senc) L [] * 3)
    rc.La _ (time_post_le _ _ _ _ _ (by unfold Machine.cost; omega) A.one_le_cost)
  have e : chainConst rc.P (Post A.time rc.E 128 1) rc.H
      (handlerQ0 rc.cb [] + handlerQ1 (w8Codes rc.senc) L [] * 3) rc.La rc.E
      (postA rc.E 128 1 + postB rc.E 128 1) (paramsWord (univ w8) params).length = rc.const := by
    unfold const chainConst chainStates chainTapes
    rw [states_post A.time 0 rc.E 0, tapes_post A.time 0 rc.E 0]
  rw [e] at h
  have h' : (rc.machine A Dm).cost ≤ rc.const * (A.cost * Dm.cost) := by
    rw [← mul_assoc]; exact h
  have hq : A.cost * Dm.cost ≤ (A.cost + Dm.cost) ^ 2 := by nlinarith
  have := h'.trans (Nat.mul_le_mul_left _ hq)
  exact_mod_cast this

end RedComps

/-- **The reduction machines from components**: for every adversary and distinguisher, the
machine of the components accepts the words of real and uniform circular Ring-LWE instances at
`circParamsD D` with the acceptances of the machines' reduction experiment, at a cost at most
`const · (cost A + cost Dm)²`. -/
theorem redMachine_of_comps {impl : Impl sig} {χfl : PMF (Rg D)}
    (rc : RedComps D kb L impl χfl) (hEval : impl.machine .eval = evalMachineX)
    (hL : predLen ≤ L) {C : ℝ} (hC : (rc.const : ℝ) ≤ C) (A : Machine 3) (Dm : Machine) :
    RedMachine D kb L (circParamsD D) impl (χcbd D) (χcbd D) χfl C A Dm := by
  refine ⟨rc.machine A Dm, ?_, ?_, ?_⟩
  · rw [realLaw_circParamsD, rc.acceptProb_machine hEval hL]
    rfl
  · rw [idealLaw_circParamsD, rc.acceptProb_machine hEval hL]
    rfl
  · exact (rc.cost_machine A Dm).trans (mul_le_mul_of_nonneg_right hC (by positivity))

end AdvancedEncryption.ExpLUT.Prog
