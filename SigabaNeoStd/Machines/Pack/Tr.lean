import SigabaNeoStd.Machines.Pack.Translate

/-!
# The packing translation and its law

`tr lay kit σ d p` (see `SigabaNeoStd.Machines.Pack.Translate` for the scheme) and
**`sim_tr`**: it simulates `p` placed by `σ` among the logical tapes, provided the wide loops nest
at most `D - d` deep (`OkX`, implied by `d + XProg.loopDepth p ≤ D`, `okX_of_loopDepth`) and the
workspace has at least `3` tapes (every primitive mentions at most three).
-/

namespace SigabaNeo.Tape.Pack

open Cslib Cslib.Probability Function

variable {K c w D : ℕ} (lay : Layout c w D) (kit : Kit K c lay.st)

/-! ### Narrowness -/

/-- A `Prog` leaf mentioning at most `w` (and at least one) tapes. -/
def NarrowP {k : ℕ} (w : ℕ) (q : Prog k) : Prop :=
  q.tapes.dedup.length ≤ w ∧ 0 < q.tapes.dedup.length

instance {k : ℕ} (w : ℕ) (q : Prog k) : Decidable (NarrowP w q) := by
  unfold NarrowP; infer_instance

/-- The restriction of a narrow `Prog` leaf, as a leaf group. -/
def leafP {k : ℕ} (σ : Fin k ↪ Fin K) (q : Prog k) (h : NarrowP w q) : ZProg c :=
  leaf lay kit ((Prog.listEmb _ (List.nodup_dedup _)).trans σ) h.1
    (XProg.prog (Prog.localize _ h.2 q))

/-- `leafP` if the leaf is narrow, otherwise `alt`. -/
def orNarrow {k : ℕ} (σ : Fin k ↪ Fin K) (q : Prog k) (alt : ZProg c) : ZProg c :=
  if h : NarrowP w q then leafP lay kit σ q h else alt

/-- The clearing of the test tape. -/
def clrT : ZProg c := .xp (.prog (.prim (.clear lay.T)))

/-- The test of a segment: read it onto the test tape, branch, clear the test tape. -/
def testZ (j : Fin K) (bit : Bool) (p q : ZProg c) : ZProg c :=
  .seq (.ph (kit.get j lay.T))
    (if bit then .ifBit lay.T (.seq (clrT lay) p) (.seq (clrT lay) q)
     else .ifBlank lay.T (.seq (clrT lay) p) (.seq (clrT lay) q))

/-- A wide loop at depth `d` (a no-op if `d ≥ D`, excluded by `OkX`). -/
def loopAt (j : Fin K) (d : ℕ) (body : ZProg c) : ZProg c :=
  if hd : d < D then loopZ (lay := lay) (kit := kit) j ⟨d, hd⟩ body else skipZ (lay := lay)

/-- **The translation of a plain program** (wide case). -/
def trP {k : ℕ} (σ : Fin k ↪ Fin K) : ℕ → Prog k → ZProg c
  | _, .prim a => orNarrow lay kit σ (.prim a) (skipZ (lay := lay))
  | _, .coin i => orNarrow lay kit σ (.coin i) (skipZ (lay := lay))
  | d, .seq p q => orNarrow lay kit σ (.seq p q) (.seq (trP σ d p) (trP σ d q))
  | d, .ifBlank i p q =>
    orNarrow lay kit σ (.ifBlank i p q) (testZ lay kit (σ i) false (trP σ d p) (trP σ d q))
  | d, .ifBit i p q =>
    orNarrow lay kit σ (.ifBit i p q) (testZ lay kit (σ i) true (trP σ d p) (trP σ d q))
  | d, .loop i b => orNarrow lay kit σ (.loop i b) (loopAt lay kit (σ i) d (trP σ (d + 1) b))

/-- `leaf` if the program is narrow (`k ≤ w`), otherwise `alt`. -/
def orLeaf {k : ℕ} (σ : Fin k ↪ Fin K) (p : XProg k) (alt : ZProg c) : ZProg c :=
  if h : k ≤ w then leaf lay kit σ h p else alt

/-- **The packing translation.** -/
def tr : {k : ℕ} → (Fin k ↪ Fin K) → ℕ → XProg k → ZProg c
  | _, σ, d, .prog q => orLeaf lay kit σ (.prog q) (trP lay kit σ d q)
  | _, σ, d, .frame e q => orLeaf lay kit σ (.frame e q) (tr (e.trans σ) d q)
  | _, σ, d, .seq p q => orLeaf lay kit σ (.seq p q) (.seq (tr σ d p) (tr σ d q))
  | _, σ, d, .ifBlank i p q =>
    orLeaf lay kit σ (.ifBlank i p q) (testZ lay kit (σ i) false (tr σ d p) (tr σ d q))
  | _, σ, d, .ifBit i p q =>
    orLeaf lay kit σ (.ifBit i p q) (testZ lay kit (σ i) true (tr σ d p) (tr σ d q))
  | _, σ, d, .loop i b => orLeaf lay kit σ (.loop i b) (loopAt lay kit (σ i) d (tr σ (d + 1) b))

/-! ### Depth conditions -/

/-- The wide loops of a plain program nest at most `D - d` deep. -/
def OkP {k : ℕ} (w D : ℕ) : ℕ → Prog k → Prop
  | _, .prim _ | _, .coin _ => True
  | d, .seq p q | d, .ifBlank _ p q | d, .ifBit _ p q => OkP w D d p ∧ OkP w D d q
  | d, .loop _ b => d < D ∧ OkP w D (d + 1) b

/-- The wide loops of a framed program nest at most `D - d` deep. -/
def OkX (w D : ℕ) : {k : ℕ} → ℕ → XProg k → Prop
  | k, d, .prog q => k ≤ w ∨ OkP w D d q
  | k, d, .frame _ q => k ≤ w ∨ OkX w D d q
  | k, d, .seq p q | k, d, .ifBlank _ p q | k, d, .ifBit _ p q =>
    k ≤ w ∨ (OkX w D d p ∧ OkX w D d q)
  | k, d, .loop _ b => k ≤ w ∨ (d < D ∧ OkX w D (d + 1) b)

/-- The loop nesting depth of a plain program. -/
def Prog.loopDepth {k : ℕ} : Prog k → ℕ
  | .prim _ | .coin _ => 0
  | .seq p q | .ifBlank _ p q | .ifBit _ p q => max (Prog.loopDepth p) (Prog.loopDepth q)
  | .loop _ b => Prog.loopDepth b + 1

/-- The loop nesting depth of a framed program. -/
def XProg.loopDepth : {k : ℕ} → XProg k → ℕ
  | _, .prog q => Prog.loopDepth q
  | _, .frame _ q => XProg.loopDepth q
  | _, .seq p q | _, .ifBlank _ p q | _, .ifBit _ p q =>
    max (XProg.loopDepth p) (XProg.loopDepth q)
  | _, .loop _ b => XProg.loopDepth b + 1

theorem okP_of_loopDepth {k : ℕ} : ∀ (d : ℕ) (q : Prog k), d + Prog.loopDepth q ≤ D → OkP w D d q
  | _, .prim _, _ | _, .coin _, _ => trivial
  | d, .seq p q, h | d, .ifBlank _ p q, h | d, .ifBit _ p q, h => by
    simp only [Prog.loopDepth] at h
    exact ⟨okP_of_loopDepth d p (by omega), okP_of_loopDepth d q (by omega)⟩
  | d, .loop _ b, h => by
    simp only [Prog.loopDepth] at h
    exact ⟨by omega, okP_of_loopDepth (d + 1) b (by omega)⟩

theorem okX_of_loopDepth : ∀ {k : ℕ} (d : ℕ) (p : XProg k), d + XProg.loopDepth p ≤ D →
    OkX w D d p
  | _, d, .prog q, h => Or.inr (okP_of_loopDepth d q h)
  | _, d, .frame _ q, h => Or.inr (okX_of_loopDepth d q h)
  | _, d, .seq p q, h | _, d, .ifBlank _ p q, h | _, d, .ifBit _ p q, h => by
    simp only [XProg.loopDepth] at h
    exact Or.inr ⟨okX_of_loopDepth d p (by omega), okX_of_loopDepth d q (by omega)⟩
  | _, d, .loop _ b, h => by
    simp only [XProg.loopDepth] at h
    exact Or.inr ⟨by omega, okX_of_loopDepth (d + 1) b (by omega)⟩

/-! ### Laws -/

variable {lay kit}

theorem sim_testZ {d : ℕ} (j : Fin K) (bit : Bool) {p q : ZProg c}
    {μ ν : Store K → PMF (Store K)} (hp : Sim lay d p μ) (hq : Sim lay d q ν) :
    Sim lay d (testZ lay kit j bit p q)
      (fun S => if bit then (if (S j).head? = some true then μ S else ν S)
        else (if S j = [] then μ S else ν S)) := by
  cases bit
  · exact sim_ifBlank j hp hq
  · exact sim_ifBit j hp hq

theorem sim_loopAt {d : ℕ} (j : Fin K) (hd : d < D) {body : ZProg c}
    {μ : Store K → PMF (Store K)} (hb : Sim lay (d + 1) body μ) :
    Sim lay d (loopAt lay kit j d body)
      (fun S => XProg.kIter (fun S => μ (tailAt j S)) (S j).length S) := by
  rw [loopAt, dif_pos hd]
  exact sim_loopZ j ⟨d, hd⟩ rfl hb

theorem sim_leafP {d k : ℕ} (σ : Fin k ↪ Fin K) (q : Prog k) (h : NarrowP w q) :
    Sim lay d (leafP lay kit σ q h) (lift σ q.law) := by
  refine sim_congr (sim_leaf _ h.1 _) fun S => ?_
  simp only [lift, XProg.law_prog]
  rw [Prog.law_localize _ (List.nodup_dedup _) h.2 q (fun t ht => List.mem_dedup.mpr ht)
    (fun j => S (σ j)), PMF.map_comp]
  congr 1
  funext a
  exact (embedF_trans _ σ S a).symm

theorem narrowP_prim {k : ℕ} (hw : 3 ≤ w) (a : Prim k) : NarrowP w (.prim a) := by
  refine ⟨(List.dedup_sublist _).length_le.trans ((Prim.length_tapes_le a).trans hw), ?_⟩
  apply List.length_pos_iff.mpr
  intro h
  have h' : a.tapes = [] := by
    rw [← List.dedup_eq_nil]; exact h
  cases a <;> simp [Prim.tapes] at h'

theorem narrowP_coin {k : ℕ} (hw : 3 ≤ w) (i : Fin k) : NarrowP w (.coin i) := by
  refine ⟨by simp [Prog.tapes]; omega, by simp [Prog.tapes]⟩

theorem sim_orNarrow {d k : ℕ} (σ : Fin k ↪ Fin K) (q : Prog k) {alt : ZProg c}
    (halt : ¬ NarrowP w q → Sim lay d alt (lift σ q.law)) :
    Sim lay d (orNarrow lay kit σ q alt) (lift σ q.law) := by
  unfold orNarrow
  split_ifs with h
  · exact sim_leafP σ q h
  · exact halt h

/-- **The translation of a plain program simulates it.** -/
theorem sim_trP (hw : 3 ≤ w) {k : ℕ} (σ : Fin k ↪ Fin K) :
    ∀ (d : ℕ) (q : Prog k), OkP w D d q → Sim lay d (trP lay kit σ d q) (lift σ q.law)
  | _, .prim a, _ => sim_orNarrow σ _ fun h => absurd (narrowP_prim hw a) h
  | _, .coin i, _ => sim_orNarrow σ _ fun h => absurd (narrowP_coin hw i) h
  | d, .seq p q, ⟨hp, hq⟩ => sim_orNarrow σ _ fun _ =>
    sim_congr (sim_seq (sim_trP hw σ d p hp) (sim_trP hw σ d q hq)) fun S => by
      rw [show (Prog.seq p q).law = fun s => (p.law s).bind q.law from
        funext fun s => Prog.law_seq p q s, lift_bind]
  | d, .ifBlank i p q, ⟨hp, hq⟩ => sim_orNarrow σ _ fun _ =>
    sim_congr (sim_testZ (σ i) false (sim_trP hw σ d p hp) (sim_trP hw σ d q hq)) fun S => by
      simp only [lift, Prog.law_ifBlank, Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> rfl
  | d, .ifBit i p q, ⟨hp, hq⟩ => sim_orNarrow σ _ fun _ =>
    sim_congr (sim_testZ (σ i) true (sim_trP hw σ d p hp) (sim_trP hw σ d q hq)) fun S => by
      simp only [lift, Prog.law_ifBit, ↓reduceIte]
      split_ifs <;> rfl
  | d, .loop i b, ⟨hd, hb⟩ => sim_orNarrow σ _ fun _ =>
    sim_congr (sim_loopAt (σ i) hd (sim_trP hw σ (d + 1) b hb)) fun S =>
      (lift_loopP σ i b S).symm

theorem XProg.law_ifBlank' {k : ℕ} (i : Fin k) (p q : XProg k) (s : Store k) :
    (XProg.ifBlank i p q).law s = if s i = [] then p.law s else q.law s := by
  simp only [XProg.law, XProg.denote]; split_ifs <;> rfl

theorem XProg.law_ifBit' {k : ℕ} (i : Fin k) (p q : XProg k) (s : Store k) :
    (XProg.ifBit i p q).law s = if (s i).head? = some true then p.law s else q.law s := by
  simp only [XProg.law, XProg.denote]; split_ifs <;> rfl

theorem sim_orLeaf {d k : ℕ} (σ : Fin k ↪ Fin K) (p : XProg k) {alt : ZProg c}
    (halt : ¬ k ≤ w → Sim lay d alt (lift σ p.law)) :
    Sim lay d (orLeaf lay kit σ p alt) (lift σ p.law) := by
  unfold orLeaf
  split_ifs with h
  · exact sim_leaf σ h p
  · exact halt h

/-- **The packing translation simulates the framed program.** -/
theorem sim_tr (hw : 3 ≤ w) : ∀ {k : ℕ} (σ : Fin k ↪ Fin K) (d : ℕ) (p : XProg k),
    OkX w D d p → Sim lay d (tr lay kit σ d p) (lift σ p.law)
  | _, σ, d, .prog q, h => sim_orLeaf σ _ fun hk =>
    sim_congr (sim_trP hw σ d q (h.resolve_left hk)) fun S => rfl
  | _, σ, d, .frame e q, h => sim_orLeaf σ _ fun hk =>
    sim_congr (sim_tr hw (e.trans σ) d q (h.resolve_left hk)) fun S => (lift_frame σ e q S).symm
  | _, σ, d, .seq p q, h => sim_orLeaf σ _ fun hk =>
    have h' := h.resolve_left hk
    sim_congr (sim_seq (sim_tr hw σ d p h'.1) (sim_tr hw σ d q h'.2)) fun S => by
      rw [show (XProg.seq p q).law = fun s => (p.law s).bind q.law from
        funext fun s => XProg.law_seq p q s, lift_bind]
  | _, σ, d, .ifBlank i p q, h => sim_orLeaf σ _ fun hk =>
    have h' := h.resolve_left hk
    sim_congr (sim_testZ (σ i) false (sim_tr hw σ d p h'.1) (sim_tr hw σ d q h'.2)) fun S => by
      simp only [lift, XProg.law_ifBlank', Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> rfl
  | _, σ, d, .ifBit i p q, h => sim_orLeaf σ _ fun hk =>
    have h' := h.resolve_left hk
    sim_congr (sim_testZ (σ i) true (sim_tr hw σ d p h'.1) (sim_tr hw σ d q h'.2)) fun S => by
      simp only [lift, XProg.law_ifBit', ↓reduceIte]
      split_ifs <;> rfl
  | _, σ, d, .loop i b, h => sim_orLeaf σ _ fun hk =>
    have h' := h.resolve_left hk
    sim_congr (sim_loopAt (σ i) h'.1 (sim_tr hw σ (d + 1) b h'.2)) fun S =>
      (lift_loop σ i b S).symm

/-- **The packing translation at the top**: on the packed store of `S`, with all the other tapes
blank, the translation of `p` ends in the packed store of a store drawn from the law of `p`. -/
theorem law_tr (hw : 3 ≤ w) (p : XProg K) (hp : OkX w D 0 p) (P : Store c) (S : Store K)
    (hP : ∀ x, x ≠ lay.st → P x = []) (hS : P lay.st = pkW S) :
    (tr lay kit (Function.Embedding.refl _) 0 p).law P =
      (p.law S).map (fun S' => update P lay.st (pkW S')) := by
  rw [sim_tr hw _ 0 p hp P S (fun x hx _ => hP x hx) hS, lift, PMF.map_comp]
  congr 1
  funext a
  simp only [Function.comp_apply]
  congr 2
  funext x
  exact embedF_apply_self (Function.Embedding.refl _) S a x

end SigabaNeo.Tape.Pack
