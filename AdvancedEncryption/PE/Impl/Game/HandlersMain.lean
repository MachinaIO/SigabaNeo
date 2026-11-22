import PE.Impl.Game.HandlersLaw

/-!
# The handlers serve the oracle (`Handles`)

`handles`: the compiled handler programs (`handlers`, one routine per channel, `R + 8` tapes,
i.e. `m = R + 5` scratch tapes) satisfy the hypothesis `SigabaNeo.Handles` of oracle inlining
for the oracle `oracleW sp setupW` with the state encoding `Codes.encState` on the states `InvS`,
with the clock `handlerTime` and answers of at most `L` bits.

The routines are compiled with the per-tape bounds `ℓ₀ = (T, 0, stateBound, 0, …)`: queries of
at most `T` bits (for the inlining, `T = A.time`) and state words of at most
`stateBound W = max W (nM + nA + nS + 3)` bits.
-/

namespace AdvancedEncryption.PE.Generic

open SigabaNeo SigabaNeo.Tape Cslib Cslib.Probability

variable {U : Universe} {Sig : Type} {R : ℕ}

/-- Per-tape bounds of the glue tapes: query, answer and state, the others `0`. -/
def bvec (b a t : ℕ) : Fin 8 → ℕ :=
  fun j => if j = 0 then b else if j = 1 then a else if j = 2 then t else 0

/-- The bound on the state words. -/
def stateBound (cd : Codes U Sig) (W : ℕ) : ℕ := max W (cd.nM + cd.nA + cd.nS + 3)

/-- The per-tape bounds of the start of a handler. -/
def startBound (cd : Codes U Sig) (T W : ℕ) : Fin (R + 8) → ℕ := ext8 (bvec T 0 (stateBound cd W)) 0

variable {cd : Codes U Sig} {sp : Spec U Sig} {setupW : List Bool → U.Attr → PMF Sig}
  {IW : List Bool → Prop} {Ok : Sig → Prop}

variable (cd) in
/-- The handler program of a channel. -/
def handlerProg (cs : Comps R cd sp setupW IW Ok) (o : Fin 3) : XProg (R + 8) :=
  if o = selectOp then selH cd cs.setupP cs.pubP
  else if o = keyGenOp then keyH cd cs.keyP cs.authP else chalH cd cs.chalP

variable (cd) in
/-- **The handlers**: the compiled programs with the start bounds. -/
noncomputable def handlers (cs : Comps R cd sp setupW IW Ok) (T W : ℕ) :
    Fin 3 → Routine (R + 5 + 3) :=
  fun o => Routine.ofXProg (handlerProg cd cs o) (startBound cd T W)

variable (cd) in
/-- **The clock of the handlers**: the largest per-tape time bound of the three programs. -/
def handlerTime (cs : Comps R cd sp setupW IW Ok) (T W : ℕ) : ℕ :=
  max (XProg.timeBoundT (selH cd cs.setupP cs.pubP) (startBound cd T W))
    (max (XProg.timeBoundT (keyH cd cs.keyP cs.authP) (startBound cd T W))
      (XProg.timeBoundT (chalH cd cs.chalP) (startBound cd T W)))

theorem fin3_cases (o : Fin 3) : o = selectOp ∨ o = keyGenOp ∨ o = challengeOp := by
  fin_cases o <;> simp [selectOp, keyGenOp, challengeOp]

theorem handlerProg_sel (cs : Comps R cd sp setupW IW Ok) :
    handlerProg cd cs selectOp = selH cd cs.setupP cs.pubP := by simp [handlerProg]

theorem handlerProg_key (cs : Comps R cd sp setupW IW Ok) :
    handlerProg cd cs keyGenOp = keyH cd cs.keyP cs.authP := by
  simp [handlerProg, selectOp, keyGenOp]

theorem handlerProg_chal (cs : Comps R cd sp setupW IW Ok) :
    handlerProg cd cs challengeOp = chalH cd cs.chalP := by
  simp [handlerProg, selectOp, keyGenOp, challengeOp]

/-! ### Well-formedness -/

section WF

variable (cs : Comps R cd sp setupW IW Ok)

theorem wf_skipG : (skipG (R := R)).WF := trivial

theorem wf_testLen (n : ℕ) {s f : XProg (R + 8)} (hs : s.WF) (hf : f.WF) : (testLen n s f).WF :=
  ⟨⟨trivial, trivial, Prog.wf_dropN _ _⟩, hf, trivial, hs, trivial, hf⟩

theorem wf_handlerProg (o : Fin 3) : (handlerProg cd cs o).WF := by
  rcases fin3_cases o with rfl | rfl | rfl
  · rw [handlerProg_sel]
    have h : (testLen cd.nA (selCore cd cs.setupP cs.pubP) skipG).WF :=
      wf_testLen _ ⟨trivial, cs.wf_setup, trivial, cs.wf_pub, trivial,
        Prog.wf_prependN _ _ _ _ _, Prog.wf_consN _ _ _⟩ trivial
    exact ⟨h, h, trivial⟩
  · rw [handlerProg_key]
    exact ⟨trivial, trivial, ⟨trivial, trivial, Prog.wf_moveFront _ _ _ _, Prog.wf_moveFront _ _ _ _⟩,
      ⟨trivial, trivial⟩, cs.wf_key, ⟨trivial, trivial⟩, cs.wf_auth, ⟨⟨trivial, trivial⟩, trivial⟩,
      trivial, Prog.wf_prependN _ _ _ _ _, Prog.wf_prependN _ _ _ _ _, trivial, trivial, trivial⟩
  · rw [handlerProg_chal]
    exact ⟨trivial, trivial, ⟨trivial, trivial⟩, ⟨trivial, trivial, trivial⟩,
      wf_testLen _ ⟨⟨trivial, Prog.wf_dropN _ _, Prog.wf_moveFront _ _ _ _⟩, ⟨trivial, trivial⟩,
        cs.wf_chal, Prog.wf_prependN _ _ _ _ _, trivial, Prog.wf_prependN _ _ _ _ _, trivial,
        trivial, trivial, trivial⟩ ⟨trivial, trivial, trivial⟩⟩

end WF

/-! ### The law on the served states -/

section Main

variable (cs : Comps R cd sp setupW IW Ok)

theorem encState_of_inv {W : ℕ} {st : List Bool × GState U Sig} (h : InvS IW W Ok st) :
    (st.2 = {} ∧ cd.encState st = st.1) ∨
      ∃ x σ, st.2.attr = some x ∧ st.2.sec = some σ ∧ Ok σ ∧
        cd.encState st = cd.selWord st.2.bad st.2.msg x σ := by
  rcases h.2.2.2 with h0 | ⟨x, σ, hx, hσ, hOk⟩
  · left; refine ⟨h0, ?_⟩
    obtain ⟨w, s⟩ := st
    simp only at h0
    subst h0
    rfl
  · right; refine ⟨x, σ, hx, hσ, hOk, ?_⟩
    obtain ⟨w, s⟩ := st
    simp only at hx hσ
    simp [Codes.encState, hx, hσ]

theorem length_encState_le {W : ℕ} {st : List Bool × GState U Sig} (h : InvS IW W Ok st) :
    (cd.encState st).length ≤ stateBound cd W := by
  rcases encState_of_inv (cd := cd) h with ⟨-, he⟩ | ⟨x, σ, -, -, -, he⟩
  · rw [he]; exact h.2.1.trans (le_max_left _ _)
  · rw [he, cd.length_selWord]; exact le_max_right _ _

/-- **The handler programs act as the oracle** on the served states. -/
theorem law_handlerProg {W : ℕ} (o : Fin 3) (b : List Bool) (st : List Bool × GState U Sig)
    (h : InvS IW W Ok st) :
    XProg.law (handlerProg cd cs o) (ext8 (vec b [] (cd.encState st)) []) =
      (oracleW sp setupW (o, b) st).map (fun r => ext8 (vec b r.1 (cd.encState r.2)) []) := by
  obtain ⟨w, s⟩ := st
  rcases encState_of_inv (cd := cd) h with ⟨h0, he⟩ | ⟨x, σ, hx, hσ, hOk, -⟩
  · simp only at h0 he
    subst h0
    rw [he]
    rcases fin3_cases o with rfl | rfl | rfl
    · rw [handlerProg_sel]; exact law_selH_init cs w b h.1 h.2.2.1
    · rw [handlerProg_key]; exact law_keyH_init cs w b h.2.2.1
    · rw [handlerProg_chal]; exact law_chalH_init cs w b h.2.2.1
  · rcases fin3_cases o with rfl | rfl | rfl
    · rw [handlerProg_sel]; exact law_selH_sel cs w b hx hσ
    · rw [handlerProg_key]; exact law_keyH_sel cs w b hx hσ hOk
    · rw [handlerProg_chal]; exact law_chalH_sel cs w b hx hσ hOk

include cs in
/-- The oracle keeps the served states, with answers of at most `L` bits. -/
theorem inv_oracleW {W T L : ℕ} (hpubL : ∀ σ, Ok σ → (sp.pub σ).length ≤ L)
    (hkeyL : ∀ σ C, Ok σ → C.length ≤ T → ∀ sk ∈ (sp.key σ C).support, sk.length ≤ L)
    (hchalL : ∀ σ μ, Ok σ → ∀ ct ∈ (sp.chal σ μ).support, ct.length ≤ L)
    (o : Fin 3) (b : List Bool) (st : List Bool × GState U Sig) (hb : b.length ≤ T)
    (h : InvS IW W Ok st) :
    ∀ r ∈ (oracleW sp setupW (o, b) st).support, InvS IW W Ok r.2 ∧ r.1.length ≤ L := by
  obtain ⟨w, s⟩ := st
  have hpure : ∀ r ∈ (PMF.pure ([], (w, s)) : PMF (List Bool × (List Bool × GState U Sig))).support,
      InvS IW W Ok r.2 ∧ r.1.length ≤ L := by
    intro r hr
    rw [PMF.mem_support_pure_iff] at hr
    subst hr
    exact ⟨h, by simp⟩
  have hkeep : ∀ s' : GState U Sig, s'.attr = s.attr → s'.sec = s.sec →
      (∃ x σ, s.attr = some x ∧ s.sec = some σ ∧ Ok σ) → InvS IW W Ok (w, s') := by
    rintro s' ha hs ⟨x, σ, hx, hσ, hOk⟩
    exact ⟨h.1, h.2.1, h.2.2.1, Or.inr ⟨x, σ, ha.trans hx, hs.trans hσ, hOk⟩⟩
  rcases h.2.2.2 with h0 | ⟨x, σ, hx, hσ, hOk⟩
  · simp only at h0
    subst h0
    rcases fin3_cases o with rfl | rfl | rfl
    · by_cases hbn : b.length = cd.nA
      · obtain ⟨x, rfl⟩ := cd.full_attr b hbn
        rw [oracleW_sel_init]
        intro r hr
        rw [PMF.mem_support_map_iff] at hr
        obtain ⟨σ, hσ, rfl⟩ := hr
        have hOk := cs.ok_setup w x h.1 σ hσ
        exact ⟨⟨h.1, h.2.1, h.2.2.1, Or.inr ⟨x, σ, rfl, rfl, hOk⟩⟩, hpubL σ hOk⟩
      · rw [oracleW_sel_init_none _ _ _ (cd.decode_attr_none hbn)]; exact hpure
    · rw [oracleW_key_init]; exact hpure
    · rw [oracleW_chal_init]; exact hpure
  · rcases fin3_cases o with rfl | rfl | rfl
    · rw [oracleW_sel_sel _ _ _ _ hx]; exact hpure
    · rw [oracleW_key_sel _ _ _ _ hx hσ]
      intro r hr
      rw [PMF.mem_support_map_iff] at hr
      obtain ⟨sk, hsk, rfl⟩ := hr
      exact ⟨hkeep _ rfl rfl ⟨x, σ, hx, hσ, hOk⟩, hkeyL σ b hOk hb sk hsk⟩
    · cases hm : s.msg with
      | some μ => rw [oracleW_chal_sel_used _ _ _ _ hx hσ hm]; exact hpure
      | none =>
        by_cases hbn : b.length = cd.nM
        · obtain ⟨μ, rfl⟩ := cd.full_msg b hbn
          rw [oracleW_chal_sel_fresh _ _ _ _ hx hσ hm]
          intro r hr
          rw [PMF.mem_support_map_iff] at hr
          obtain ⟨ct, hct, rfl⟩ := hr
          exact ⟨hkeep _ rfl rfl ⟨x, σ, hx, hσ, hOk⟩, hchalL σ μ hOk ct hct⟩
        · rw [oracleW_chal_sel_none _ _ _ (cd.decode_msg_none hbn)]; exact hpure

/-- **The handlers serve the oracle.** For an oracle machine `A`, the handlers compiled for queries
of at most `A.time` bits and instance words of at most `W` bits satisfy `Handles` for the oracle
`oracleW sp setupW`, the encoding `encState`, the served states `InvS IW W Ok`, the clock
`handlerTime` and answers of at most `L` bits. -/
theorem handles (A : Machine 3) (W L : ℕ) (hpubL : ∀ σ, Ok σ → (sp.pub σ).length ≤ L)
    (hkeyL : ∀ σ C, Ok σ → C.length ≤ A.time → ∀ sk ∈ (sp.key σ C).support, sk.length ≤ L)
    (hchalL : ∀ σ μ, Ok σ → ∀ ct ∈ (sp.chal σ μ).support, ct.length ≤ L) :
    Handles A (handlers cd cs A.time W) (oracleW sp setupW) cd.encState (InvS IW W Ok)
      (handlerTime cd cs A.time W) L where
  time_le o := by
    show XProg.timeBoundT (handlerProg cd cs o) (startBound cd A.time W) ≤ _
    rcases fin3_cases o with rfl | rfl | rfl
    · rw [handlerProg_sel]; exact le_max_left _ _
    · rw [handlerProg_key]; exact (le_max_left _ _).trans (le_max_right _ _)
    · rw [handlerProg_chal]; exact (le_max_right _ _).trans (le_max_right _ _)
  runs o b st hb h := by
    have hfits : Fits (Inline.layout (m := R + 5) b [] (cd.encState st))
        (startBound (R := R) cd A.time W) := by
      rw [layout_eq]
      refine fits_ext8 fun j => ?_
      simp only [vec, bvec]
      split_ifs
      · exact hb
      · simp
      · exact length_encState_le h
      · simp
    have hr := Routine.runs_ofXProg (handlerProg cd cs o) (wf_handlerProg cs o)
      (startBound cd A.time W) _ hfits
    rw [layout_eq, law_handlerProg cs o b st h] at hr
    simp only [layout_eq]
    exact hr
  inv o b st hb h := inv_oracleW cs hpubL hkeyL hchalL o b st hb h

end Main

end AdvancedEncryption.PE.Generic
