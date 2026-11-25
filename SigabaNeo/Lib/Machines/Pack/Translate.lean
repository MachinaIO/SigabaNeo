import SigabaNeo.Lib.Machines.Pack.ZProg
import SigabaNeo.Lib.Machines.Pack.Seg
import SigabaNeo.Lib.Machines.Pack.Restrict

/-!
# Packing the logical tapes of a framed program onto a few physical tapes

`tr lay kit σ d p : ZProg c` runs the framed program `p : XProg k` on a machine with `c` tapes
(`lay : Layout c w D`), where the logical store `S : Store K` is kept *packed* on the store tape
`lay.st` (`pkW S`), `σ : Fin k ↪ Fin K` places the tapes of `p` among the logical tapes, and `d` is
the nesting depth of the enclosing *wide* loops. The segment phases `kit.get j t` (`t := S j`) and
`kit.put j t` (`S j := t`, `t := []`) are abstract here (`Kit`): only their store functions matter
for the law.

* a **narrow** program (`k ≤ w`) is a *leaf group*: get its `k` segments onto the workspace tapes
  `lay.W`, run its own compiled machine there (`xp (frame _ p)`: the existing compiler, unchanged),
  put the segments back (`leaf`);
* a wide `frame e q` is `q` placed by `e.trans σ`;
* a wide `Prog` leaf is restricted to the tapes it mentions when they are at most `w`
  (`Prog.localize`), and otherwise translated construct by construct (`trP`);
* `seq` is `seq`; `ifBlank i`, `ifBit i` read the segment `σ i` onto the test tape `lay.T`;
  `loop i body` reads the segment `σ i` onto the counter tape `lay.F d` and loops on it, each round
  dropping the first bit of the segment (`tailZ`) before the body.

**`sim_tr`**: on every physical store `P` whose store tape holds `pkW S` and whose other tapes are
blank (except the counters of the enclosing loops),
`(tr lay kit σ d p).law P = ((p.law (S ∘ σ)).map (embedF σ S)).map (fun S' => update P st (pkW S'))`.
-/

namespace SigabaNeo.Tape.Pack

open Cslib Cslib.Probability Function

variable {K c w D : ℕ}

/-! ### Layout and segment phases -/

/-- The physical tapes: the store, the test tape, the workspace and the loop counters. -/
structure Layout (c w D : ℕ) where
  /-- The store tape. -/
  st : Fin c
  /-- The test tape. -/
  T : Fin c
  /-- The workspace. -/
  W : Fin w ↪ Fin c
  /-- The loop counters. -/
  F : Fin D ↪ Fin c
  hTst : T ≠ st
  hWst : ∀ j, W j ≠ st
  hWT : ∀ j, W j ≠ T
  hFst : ∀ d, F d ≠ st
  hFT : ∀ d, F d ≠ T
  hWF : ∀ j d, W j ≠ F d

/-- The segment phases, specified by their store functions on packed stores. -/
structure Kit (K c : ℕ) (st : Fin c) where
  /-- `t := S j`. -/
  get : Fin K → Fin c → Phase c
  /-- `S j := t`, `t := []`. -/
  put : Fin K → Fin c → Phase c
  get_f : ∀ (j : Fin K) (t : Fin c) (P : Store c) (S : Store K), t ≠ st → P st = pkW S →
    (get j t).f P = update P t (S j)
  put_f : ∀ (j : Fin K) (t : Fin c) (P : Store c) (S : Store K), t ≠ st → P st = pkW S →
    (put j t).f P = update (update P st (pkW (update S j (P t)))) t []

variable (lay : Layout c w D)

/-- The physical stores of depth `d`: blank except the store tape and the counters of the `d`
enclosing loops. -/
def Clean (d : ℕ) (P : Store c) : Prop :=
  ∀ x, x ≠ lay.st → (∀ e : Fin D, (e : ℕ) < d → x ≠ lay.F e) → P x = []

/-- `q` simulates the logical kernel `μ` at depth `d`. -/
def Sim (d : ℕ) (q : ZProg c) (μ : Store K → PMF (Store K)) : Prop :=
  ∀ P S, Clean lay d P → P lay.st = pkW S →
    q.law P = (μ S).map (fun S' => update P lay.st (pkW S'))

/-- The law of a framed program placed by `σ` among the logical tapes. -/
noncomputable def lift {k : ℕ} (σ : Fin k ↪ Fin K) (L : Store k → PMF (Store k)) :
    Store K → PMF (Store K) :=
  fun S => (L (fun j => S (σ j))).map (embedF σ S)

/-! ### Store lemmas -/

variable {lay}

theorem Clean.update_st {d : ℕ} {P : Store c} (h : Clean lay d P) (u : List Bool) :
    Clean lay d (update P lay.st u) := by
  intro x hx hF
  rw [update_of_ne hx]
  exact h x hx hF

theorem Clean.T {d : ℕ} {P : Store c} (h : Clean lay d P) : P lay.T = [] :=
  h _ lay.hTst fun e _ => (lay.hFT e).symm

theorem Clean.W {d : ℕ} {P : Store c} (h : Clean lay d P) (j : Fin w) : P (lay.W j) = [] :=
  h _ (lay.hWst j) fun e _ => lay.hWF j e

theorem Clean.F {d : ℕ} {P : Store c} (h : Clean lay d P) (e : Fin D) (he : d ≤ e) :
    P (lay.F e) = [] :=
  h _ (lay.hFst e) fun e' he' h' => by
    have := lay.F.injective h'
    subst this
    omega

theorem update_self_of_eq {α : Type} {n : ℕ} (P : Fin n → α) (x : Fin n) (a : α) (h : P x = a) :
    update P x a = P := by
  rw [← h, update_eq_self]

theorem update_update_of_eq {α : Type} {n : ℕ} (P : Fin n → α) {a b : Fin n} (hab : b ≠ a)
    (v w : α) (h : P b = w) : update (update P a v) b w = update P a v := by
  rw [update_comm hab.symm, update_self_of_eq _ _ _ h]

/-! ### Sequencing -/

theorem sim_seq {d : ℕ} {p q : ZProg c} {μ ν : Store K → PMF (Store K)} (hp : Sim lay d p μ)
    (hq : Sim lay d q ν) : Sim lay d (.seq p q) (fun S => (μ S).bind ν) := by
  intro P S hP hS
  rw [ZProg.law_seq, hp P S hP hS, PMF.bind_map, PMF.map_bind]
  congr 1
  funext S'
  simp only [Function.comp_apply]
  rw [hq _ S' (hP.update_st _) (by simp)]
  congr 1
  funext S''
  simp

theorem sim_congr {d : ℕ} {q : ZProg c} {μ ν : Store K → PMF (Store K)} (h : Sim lay d q μ)
    (he : ∀ S, μ S = ν S) : Sim lay d q ν := by
  intro P S hP hS
  rw [h P S hP hS, he]

/-! ### Folds of updates -/

/-- A fold of updates at distinct places. -/
theorem foldl_update_spec {α ι : Type} {n : ℕ} (e : ι → Fin n) (he : Injective e) (v : ι → α) :
    ∀ (L : List ι), L.Nodup → ∀ (P : Fin n → α),
      (∀ j ∈ L, (L.foldl (fun P j => update P (e j) (v j)) P) (e j) = v j) ∧
      (∀ x, (∀ j ∈ L, e j ≠ x) → (L.foldl (fun P j => update P (e j) (v j)) P) x = P x)
  | [], _, P => ⟨by simp, fun _ _ => rfl⟩
  | j₀ :: L, hL, P => by
    obtain ⟨hj₀, hL'⟩ := List.nodup_cons.mp hL
    obtain ⟨ih1, ih2⟩ := foldl_update_spec e he v L hL' (update P (e j₀) (v j₀))
    refine ⟨fun j hj => ?_, fun x hx => ?_⟩
    · rcases List.mem_cons.mp hj with rfl | hj
      · rw [List.foldl_cons, ih2 _ (fun j' hj' h => hj₀ (by rw [← he h]; exact hj')), update_self]
      · exact ih1 j hj
    · rw [List.foldl_cons, ih2 x (fun j hj => hx j (List.mem_cons_of_mem _ hj)),
        update_of_ne (fun h => hx j₀ (List.mem_cons_self) h.symm)]

/-- A fold of updates over all the positions of an embedding is the embedding of the values. -/
theorem foldl_update_finRange {α : Type} {m n : ℕ} (e : Fin m ↪ Fin n) (v : Fin m → α)
    (P : Fin n → α) :
    (List.finRange m).foldl (fun P j => update P (e j) (v j)) P = embedF e P v := by
  obtain ⟨h1, h2⟩ := foldl_update_spec e e.injective v _ (List.nodup_finRange m) P
  funext x
  rcases embedF_cases e P v x with ⟨hx, h⟩ | ⟨j, rfl, h⟩
  · rw [h, h2 x]
    rintro j - rfl
    rw [partialInv_self] at hx
    simp at hx
  · rw [h, h1 j (List.mem_finRange j)]

/-! ### Sequences of phases -/

/-- `ps₀; ps₁; …; q`. -/
def seqL : List (ZProg c) → ZProg c → ZProg c
  | [], q => q
  | p :: ps, q => .seq p (seqL ps q)

theorem law_seqL_ph (Ps : List (Phase c)) (q : ZProg c) (P : Store c) :
    (seqL (Ps.map ZProg.ph) q).law P = q.law (Ps.foldl (fun P Ph => Ph.f P) P) := by
  induction Ps generalizing P with
  | nil => rfl
  | cons Ph Ps ih =>
    simp only [List.map_cons, seqL, List.foldl_cons]
    rw [ZProg.law_seq, ZProg.law_ph, PMF.pure_bind, ih]

/-- A no-op (clears the blank test tape). -/
def skipZ : ZProg c := .xp (.prog (.prim (.clear lay.T)))

theorem law_skipZ {d : ℕ} {P : Store c} (hP : Clean lay d P) : (skipZ (lay := lay)).law P =
    PMF.pure P := by
  rw [skipZ, ZProg.law_xp, XProg.law_prim]
  simp only [Prim.apply]
  rw [update_self_of_eq _ _ _ hP.T]

/-! ### Leaf groups -/

variable (lay) (kit : Kit K c lay.st)

/-- The workspace tapes of a narrow program. -/
def wsE {m : ℕ} (h : m ≤ w) : Fin m ↪ Fin c := (Fin.castLEEmb h).trans lay.W

theorem wsE_apply {m : ℕ} (h : m ≤ w) (j : Fin m) : wsE lay h j = lay.W (Fin.castLE h j) := rfl

theorem wsE_ne_st {m : ℕ} (h : m ≤ w) (j : Fin m) : wsE lay h j ≠ lay.st := lay.hWst _

/-- **A leaf group**: get the segments, run the compiled narrow program on the workspace, put the
segments back. -/
def leaf {m : ℕ} (σ : Fin m ↪ Fin K) (h : m ≤ w) (p : XProg m) : ZProg c :=
  seqL ((List.finRange m).map fun j => .ph (kit.get (σ j) (wsE lay h j)))
    (.seq (.xp (.frame (wsE lay h) p))
      (seqL ((List.finRange m).map fun j => .ph (kit.put (σ j) (wsE lay h j))) (skipZ (lay := lay))))

variable {lay kit}

theorem gets_fold {m : ℕ} (σ : Fin m ↪ Fin K) (h : m ≤ w) (S : Store K) :
    ∀ (L : List (Fin m)) (P : Store c), P lay.st = pkW S →
      L.foldl (fun P j => (kit.get (σ j) (wsE lay h j)).f P) P =
        L.foldl (fun P j => update P (wsE lay h j) (S (σ j))) P
  | [], _, _ => rfl
  | j :: L, P, hP => by
    rw [List.foldl_cons, List.foldl_cons, kit.get_f _ _ P S (wsE_ne_st lay h j) hP]
    exact gets_fold σ h S L _ (by rw [update_of_ne (wsE_ne_st lay h j).symm, hP])

theorem puts_fold {m : ℕ} (σ : Fin m ↪ Fin K) (h : m ≤ w) (v : Fin m → List Bool) :
    ∀ (L : List (Fin m)), L.Nodup → ∀ (P : Store c) (S : Store K), P lay.st = pkW S →
      (∀ j ∈ L, P (wsE lay h j) = v j) →
      L.foldl (fun P j => (kit.put (σ j) (wsE lay h j)).f P) P =
        update (L.foldl (fun P j => update P (wsE lay h j) []) P) lay.st
          (pkW (L.foldl (fun S j => update S (σ j) (v j)) S))
  | [], _, P, S, hP, _ => by simp [← hP]
  | j :: L, hL, P, S, hP, hv => by
    obtain ⟨hj, hL'⟩ := List.nodup_cons.mp hL
    rw [List.foldl_cons, List.foldl_cons, List.foldl_cons, kit.put_f _ _ P S (wsE_ne_st lay h j) hP,
      hv j List.mem_cons_self]
    rw [puts_fold σ h v L hL' _ (update S (σ j) (v j))
      (by rw [update_of_ne (wsE_ne_st lay h j).symm, update_self])
      (fun j' hj' => by
        rw [update_of_ne (fun h' => hj (by
            have := (wsE lay h).injective h'; subst this; exact hj')),
          update_of_ne (wsE_ne_st lay h j')]
        exact hv j' (List.mem_cons_of_mem _ hj'))]
    -- moving the store update out of the fold
    have key : ∀ (L : List (Fin m)) (Q : Store c) (u : List Bool),
        L.foldl (fun P j => update P (wsE lay h j) []) (update Q lay.st u) =
          update (L.foldl (fun P j => update P (wsE lay h j) []) Q) lay.st u := by
      intro L
      induction L with
      | nil => intro Q u; rfl
      | cons j L ih =>
        intro Q u
        rw [List.foldl_cons, List.foldl_cons, update_comm (wsE_ne_st lay h j).symm, ih]
    rw [update_comm (wsE_ne_st lay h j).symm, key, update_idem]

/-- **The leaf group simulates its narrow program.** -/
theorem sim_leaf {d m : ℕ} (σ : Fin m ↪ Fin K) (h : m ≤ w) (p : XProg m) :
    Sim lay d (leaf lay kit σ h p) (lift σ p.law) := by
  intro P S hP hS
  rw [leaf]
  have hg : ((List.finRange m).map fun j => ZProg.ph (kit.get (σ j) (wsE lay h j))) =
      ((List.finRange m).map fun j => kit.get (σ j) (wsE lay h j)).map ZProg.ph := by
    simp [List.map_map]
  have hp' : ((List.finRange m).map fun j => ZProg.ph (kit.put (σ j) (wsE lay h j))) =
      ((List.finRange m).map fun j => kit.put (σ j) (wsE lay h j)).map ZProg.ph := by
    simp [List.map_map]
  rw [hg, law_seqL_ph, List.foldl_map, gets_fold σ h S _ P hS, foldl_update_finRange]
  rw [ZProg.law_seq, ZProg.law_xp, XProg.law_frame, embedF_comp_self, PMF.bind_map]
  simp only [lift, PMF.map_comp]
  rw [← PMF.bind_pure_comp]
  congr 1
  funext a
  simp only [Function.comp_apply]
  rw [hp', law_seqL_ph, List.foldl_map, embedF_embedF]
  have hst : embedF (wsE lay h) P a lay.st = pkW S := by
    rcases embedF_cases (wsE lay h) P a lay.st with ⟨-, h'⟩ | ⟨j, hj, -⟩
    · rw [h', hS]
    · exact absurd hj (wsE_ne_st lay h j)
  rw [puts_fold σ h a _ (List.nodup_finRange m) _ S hst
    (fun j _ => embedF_apply_self _ _ _ j), foldl_update_finRange, foldl_update_finRange,
    embedF_embedF]
  have hblank : embedF (wsE lay h) P (fun _ => []) = P := by
    funext x
    rcases embedF_cases (wsE lay h) P (fun _ => []) x with ⟨-, h'⟩ | ⟨j, rfl, h'⟩
    · exact h'
    · rw [h']; exact (hP.W _).symm
  rw [hblank, law_skipZ (hP.update_st _)]

/-! ### Logical laws placed by an embedding -/

theorem embedF_trans {k m : ℕ} (e : Fin m ↪ Fin k) (σ : Fin k ↪ Fin K) (S : Store K)
    (a : Store m) : embedF σ S (embedF e (fun j => S (σ j)) a) = embedF (e.trans σ) S a := by
  rw [XProg.embedF_eq_extend, XProg.embedF_eq_extend, XProg.embedF_eq_extend]
  funext x
  by_cases hx : ∃ i, σ i = x
  · obtain ⟨i, rfl⟩ := hx
    rw [σ.injective.extend_apply]
    by_cases hi : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [e.injective.extend_apply]
      exact ((e.trans σ).injective.extend_apply a S j).symm
    · rw [Function.extend_apply' _ _ _ hi, Function.extend_apply']
      rintro ⟨j, hj⟩
      exact hi ⟨j, σ.injective hj⟩
  · rw [Function.extend_apply' _ _ _ hx, Function.extend_apply']
    rintro ⟨j, hj⟩
    exact hx ⟨e j, hj⟩

theorem lift_frame {k m : ℕ} (σ : Fin k ↪ Fin K) (e : Fin m ↪ Fin k) (q : XProg m) (S : Store K) :
    lift σ (XProg.frame e q).law S = lift (e.trans σ) q.law S := by
  simp only [lift, XProg.law_frame, PMF.map_comp]
  congr 1
  funext a
  exact embedF_trans e σ S a

theorem lift_bind {k : ℕ} (σ : Fin k ↪ Fin K) (L₁ L₂ : Store k → PMF (Store k)) (S : Store K) :
    lift σ (fun s => (L₁ s).bind L₂) S = (lift σ L₁ S).bind (lift σ L₂) := by
  simp only [lift, PMF.map_bind, PMF.bind_map]
  congr 1
  funext a
  simp only [Function.comp_apply, lift]
  rw [show (fun j => embedF σ S a (σ j)) = a from embedF_comp_self σ S a]
  congr 1
  funext b
  exact (embedF_embedF σ S a b).symm

/-! ### Segment rounds -/

variable (lay kit)

/-- Drop the first bit of the segment `j` (through the test tape). -/
def tailZ (j : Fin K) : ZProg c :=
  .seq (.ph (kit.get j lay.T)) (.seq (.xp (.prog (.prim (.tail lay.T)))) (.ph (kit.put j lay.T)))

variable {lay kit}

theorem sim_tailZ {d : ℕ} (j : Fin K) : Sim lay d (tailZ lay kit j) (fun S => PMF.pure (tailAt j S)) := by
  intro P S hP hS
  rw [tailZ, ZProg.law_seq, ZProg.law_ph, PMF.pure_bind, ZProg.law_seq, ZProg.law_xp,
    XProg.law_prim, PMF.pure_bind, ZProg.law_ph, kit.get_f _ _ P S lay.hTst hS, PMF.pure_map]
  simp only [Prim.apply, update_self, update_idem]
  rw [kit.put_f _ _ _ S lay.hTst (by rw [update_of_ne lay.hTst.symm, hS]), update_self,
    update_comm lay.hTst, update_idem, update_update_of_eq _ lay.hTst _ _ hP.T]
  rfl

/-! ### Branches -/

theorem sim_ifBlank {d : ℕ} (j : Fin K) {p q : ZProg c} {μ ν : Store K → PMF (Store K)}
    (hp : Sim lay d p μ) (hq : Sim lay d q ν) :
    Sim lay d (.seq (.ph (kit.get j lay.T)) (.ifBlank lay.T (.seq (.xp (.prog (.prim (.clear lay.T)))) p)
      (.seq (.xp (.prog (.prim (.clear lay.T)))) q)))
      (fun S => if S j = [] then μ S else ν S) := by
  intro P S hP hS
  rw [ZProg.law_seq, ZProg.law_ph, PMF.pure_bind, kit.get_f _ _ P S lay.hTst hS,
    ZProg.law_ifBlank, update_self]
  have hb : ∀ r : ZProg c, (ZProg.seq (.xp (.prog (.prim (.clear lay.T)))) r).law
      (update P lay.T (S j)) = r.law P := by
    intro r
    rw [ZProg.law_seq, ZProg.law_xp, XProg.law_prim, PMF.pure_bind]
    simp only [Prim.apply, update_idem]
    rw [update_self_of_eq _ _ _ hP.T]
  dsimp only
  by_cases hj : S j = []
  · rw [if_pos hj, hb, hp P S hP hS, if_pos hj]
  · rw [if_neg hj, hb, hq P S hP hS, if_neg hj]

theorem sim_ifBit {d : ℕ} (j : Fin K) {p q : ZProg c} {μ ν : Store K → PMF (Store K)}
    (hp : Sim lay d p μ) (hq : Sim lay d q ν) :
    Sim lay d (.seq (.ph (kit.get j lay.T)) (.ifBit lay.T (.seq (.xp (.prog (.prim (.clear lay.T)))) p)
      (.seq (.xp (.prog (.prim (.clear lay.T)))) q)))
      (fun S => if (S j).head? = some true then μ S else ν S) := by
  intro P S hP hS
  rw [ZProg.law_seq, ZProg.law_ph, PMF.pure_bind, kit.get_f _ _ P S lay.hTst hS,
    ZProg.law_ifBit, update_self]
  have hb : ∀ r : ZProg c, (ZProg.seq (.xp (.prog (.prim (.clear lay.T)))) r).law
      (update P lay.T (S j)) = r.law P := by
    intro r
    rw [ZProg.law_seq, ZProg.law_xp, XProg.law_prim, PMF.pure_bind]
    simp only [Prim.apply, update_idem]
    rw [update_self_of_eq _ _ _ hP.T]
  dsimp only
  by_cases hj : (S j).head? = some true
  · rw [if_pos hj, hb, hp P S hP hS, if_pos hj]
  · rw [if_neg hj, hb, hq P S hP hS, if_neg hj]

/-! ### Loops -/

theorem ZProg.law_loop_iter {σ' : Type} (i : Fin c) (body : ZProg c) (G : σ' → Store c)
    (Kn : σ' → PMF σ')
    (h : ∀ a w, body.law (update (G a) i w) = (Kn a).map fun a' => update (G a') i w)
    (a : σ') (w : List Bool) :
    (ZProg.loop i body).law (update (G a) i w) =
      (XProg.kIter Kn w.length a).map fun a' => update (G a') i [] := by
  have key : ∀ j, ProbComp.eval (OracleComp.iterate j (fun t => body.denote (tailAt i t))
      (update (G a) i w)) =
      (XProg.kIter Kn j a).map fun a' => update (G a') i (w.drop j) := by
    intro j
    induction j with
    | zero => simp [XProg.kIter]
    | succ j ih =>
      rw [OracleComp.iterate_succ, ProbComp.eval_bind, ih, XProg.kIter, PMF.bind_map, PMF.map_bind]
      congr 1
      funext a'
      simp only [Function.comp_apply, tailAt, update_self, update_idem]
      have := h a' (w.drop j).tail
      simp only [ZProg.law] at this
      rw [this, List.tail_drop]
  show ProbComp.eval (ZProg.denote (ZProg.loop i body) (update (G a) i w)) = _
  simp only [ZProg.denote, update_self]
  rw [key, List.drop_length]

/-- The loop on the segment `j` with the counter tape `lay.F e` (`e` the depth). -/
def loopZ (j : Fin K) (e : Fin D) (body : ZProg c) : ZProg c :=
  .seq (.ph (kit.get j (lay.F e))) (.loop (lay.F e) (.seq (tailZ lay kit j) body))

theorem sim_loopZ {d : ℕ} (j : Fin K) (e : Fin D) (he : (e : ℕ) = d) {body : ZProg c}
    {μ : Store K → PMF (Store K)} (hb : Sim lay (d + 1) body μ) :
    Sim lay d (loopZ (lay := lay) (kit := kit) j e body)
      (fun S => XProg.kIter (fun S => μ (tailAt j S)) (S j).length S) := by
  intro P S hP hS
  have hFst : lay.F e ≠ lay.st := lay.hFst e
  rw [loopZ, ZProg.law_seq, ZProg.law_ph, PMF.pure_bind, kit.get_f _ _ P S hFst hS]
  have hP0 : P = update P lay.st (pkW S) := (update_self_of_eq _ _ _ hS).symm
  let G : Store K → Store c := fun S' => update P lay.st (pkW S')
  have hG : update P (lay.F e) (S j) = update (G S) (lay.F e) (S j) := by
    simp only [G]; rw [← hP0]
  rw [hG, ZProg.law_loop_iter (lay.F e) _ G (fun S => μ (tailAt j S))]
  · congr 1
    funext S'
    simp only [G]
    rw [update_update_of_eq _ hFst _ _ (hP.F e (by omega))]
  · intro S' wd
    have hsb := sim_seq (sim_tailZ (lay := lay) (kit := kit) (d := d + 1) j) hb
    have hcl : Clean lay (d + 1) (update (G S') (lay.F e) wd) := by
      intro x hx hF
      rw [update_of_ne (hF e (by omega))]
      simp only [G]
      rw [update_of_ne hx]
      exact hP x hx fun e' he' => hF e' (by omega)
    rw [hsb _ S' hcl (by rw [update_of_ne hFst.symm]; simp [G])]
    simp only [PMF.pure_bind]
    congr 1
    funext S''
    simp only [G]
    rw [update_comm hFst.symm, update_idem, update_comm hFst]

theorem lift_loop {k : ℕ} (σ : Fin k ↪ Fin K) (i : Fin k) (body : XProg k) (S : Store K) :
    lift σ (XProg.loop i body).law S =
      XProg.kIter (fun S => lift σ body.law (tailAt (σ i) S)) (S (σ i)).length S := by
  simp only [lift]
  rw [XProg.law_loop_kIter, kIter_map_embed]
  congr 1
  funext t
  have h1 : (fun j => tailAt (σ i) t (σ j)) = tailAt i (fun j => t (σ j)) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [tailAt]
    · simp [tailAt, update_of_ne hj, update_of_ne (σ.injective.ne hj)]
  rw [h1]
  congr 1
  funext b
  exact (embedF_update_range σ t i _ b).symm

theorem lift_loopP {k : ℕ} (σ : Fin k ↪ Fin K) (i : Fin k) (body : Prog k) (S : Store K) :
    lift σ (Prog.loop i body).law S =
      XProg.kIter (fun S => lift σ body.law (tailAt (σ i) S)) (S (σ i)).length S := by
  have : (Prog.loop i body).law = (XProg.loop i (XProg.prog body)).law := by
    funext s; rw [Prog.law_loop_kIter, XProg.law_loop_kIter]; rfl
  rw [this, lift_loop]
  rfl

end SigabaNeo.Tape.Pack
