import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMHandler

/-!
# `mid` of the key component, phase M1 (generic part): a `RingVM` handler with a stash

The handlers `RedIO.ringIO1` (`pubP`, `chalP`) clear every tape, so the words the key component
still needs (the raw secret, the predicate `C`, the public key) cannot survive a plain call.
**`ringIOS`** is `ringIO1` with three *stash* register tapes `tWd 197`, `tWd 198`, `tWd 199`
(`= 244, 245, 246`) carried through:

* the stash is parked on the operation-area tapes `10`, `11`, `12` while `preP` builds the
  templates (`preP` never touches them: `law_preP_park`), then moved into the stash registers;
* the code runs on the registers `initW1 …` updated at the stash registers; a code that never
  mentions a register (`usesR c r = false`) commutes with its update
  (**`exec_update_of_usesR`**);
* the exit copies the output register to tape `0` and clears every tape but `0` and the stash.

**`law_ringIOS`**: `law (ringIOS …) (stash3 (io2 a b []) v₁ v₂ v₃) =
pure (stash3 (io2 (exec c (initW1 …) ro) [] []) v₁ v₂ v₃)`; **`wf_ringIOS`**.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace SigabaNeo.Tape.RingVM.Handler
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.RingVM Cslib
open SigabaNeo.Tape.RingVM.Handler
open scoped SigabaNeo.Tape.Prog

/-! ### Codes that never mention a register -/

/-- `c` mentions the register `r` (as an operand, a destination, a counter or a test). -/
def usesR (r : Fin 200) : Code → Bool
  | .add d a b | .sub d a b | .mul d a b => d == r || a == r || b == r
  | .canon d a | .neg d a => d == r || a == r
  | .digit d a t | .rotB d a t | .aut d a t | .rhoJ d a t => d == r || a == r || t == r
  | .mv d s c => d == r || s == r || c == r
  | .cp d s => d == r || s == r
  | .drop t c => t == r || c == r
  | .clr t | .tl t => t == r
  | .rep c body => c == r || usesR r body
  | .seq p q => usesR r p || usesR r q
  | .ifb t p q => t == r || usesR r p || usesR r q
  | .nop => false

theorem upd_upd_comm {w : St} {d r : Fin 200} (h : d ≠ r) (x v : List Bool) :
    Function.update (Function.update w r v) d x = Function.update (Function.update w d x) r v :=
  (Function.update_comm h x v w).symm

/-- **A code that never mentions `r` commutes with an update of `r`.** -/
theorem exec_update_of_usesR (N K : ℕ) (r : Fin 200) (v : List Bool) :
    ∀ (c : Code), usesR r c = false → ∀ w : St,
      exec N K c (Function.update w r v) = Function.update (exec N K c w) r v := by
  intro c
  induction c with
  | add d a b | sub d a b | mul d a b =>
    intro h w
    simp only [usesR, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
    obtain ⟨⟨hd, ha⟩, hb⟩ := h
    simp only [exec, Function.update_of_ne ha, Function.update_of_ne hb]
    exact upd_upd_comm hd _ _
  | canon d a | neg d a =>
    intro h w
    simp only [usesR, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
    obtain ⟨hd, ha⟩ := h
    simp only [exec, Function.update_of_ne ha]
    exact upd_upd_comm hd _ _
  | digit d a t | rotB d a t | aut d a t | rhoJ d a t =>
    intro h w
    simp only [usesR, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
    obtain ⟨⟨hd, ha⟩, ht⟩ := h
    simp only [exec, Function.update_of_ne ha, Function.update_of_ne ht]
    exact upd_upd_comm hd _ _
  | mv d s c =>
    intro h w
    simp only [usesR, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
    obtain ⟨⟨hd, hs⟩, hc⟩ := h
    simp only [exec]
    split_ifs
    · rfl
    · rw [Function.update_of_ne hs, Function.update_of_ne hc, Function.update_of_ne hd,
        upd_upd_comm hs, upd_upd_comm hd]
  | cp d s =>
    intro h w
    simp only [usesR, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
    obtain ⟨hd, hs⟩ := h
    simp only [exec, Function.update_of_ne hs]
    exact upd_upd_comm hd _ _
  | drop t c =>
    intro h w
    simp only [usesR, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
    obtain ⟨ht, hc⟩ := h
    simp only [exec]
    split_ifs
    · rfl
    · rw [Function.update_of_ne ht, Function.update_of_ne hc]
      exact upd_upd_comm ht _ _
  | clr t =>
    intro h w
    simp only [usesR, beq_eq_false_iff_ne, ne_eq] at h
    exact upd_upd_comm h _ _
  | tl t =>
    intro h w
    simp only [usesR, beq_eq_false_iff_ne, ne_eq] at h
    simp only [exec, Function.update_of_ne h]
    exact upd_upd_comm h _ _
  | rep c body ih =>
    intro h w
    simp only [usesR, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
    obtain ⟨hc, hb⟩ := h
    simp only [exec, Function.update_of_ne hc]
    generalize (w c).length = n
    induction n generalizing w with
    | zero => rfl
    | succ n ihn =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      have e : exec N K body (Function.update (Function.update w r v) c
          ((Function.update w r v) c).tail) =
          Function.update (exec N K body (Function.update w c (w c).tail)) r v := by
        rw [Function.update_of_ne hc, upd_upd_comm hc, ih hb]
      rw [e, ihn]
  | seq p q ihp ihq =>
    intro h w
    simp only [usesR, Bool.or_eq_false_iff] at h
    simp only [exec, ihp h.1, ihq h.2]
  | ifb t p q ihp ihq =>
    intro h w
    simp only [usesR, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
    obtain ⟨⟨ht, hp⟩, hq⟩ := h
    simp only [exec, Function.update_of_ne ht]
    split_ifs
    · exact ihp hp w
    · exact ihq hq w
  | nop => intro _ _; rfl

/-! ### The stash -/

/-- The stash registers. -/
def sR1 : Fin 200 := 197
def sR2 : Fin 200 := 198
def sR3 : Fin 200 := 199

/-- The parking tapes (operation area, untouched by `preP`). -/
def pk1 : Fin 247 := 10
def pk2 : Fin 247 := 11
def pk3 : Fin 247 := 12

/-- Three words on three tapes. -/
def put3 (t1 t2 t3 : Fin 247) (s : Store 247) (v1 v2 v3 : List Bool) : Store 247 :=
  Function.update (Function.update (Function.update s t1 v1) t2 v2) t3 v3

/-- The stash on its register tapes. -/
abbrev stash3 (s : Store 247) (v1 v2 v3 : List Bool) : Store 247 :=
  put3 (tWd sR1) (tWd sR2) (tWd sR3) s v1 v2 v3

/-- The stash parked. -/
abbrev park3 (s : Store 247) (v1 v2 v3 : List Bool) : Store 247 := put3 pk1 pk2 pk3 s v1 v2 v3

/-- The stash in the registers. -/
def stW (w : St) (v1 v2 v3 : List Bool) : St :=
  Function.update (Function.update (Function.update w sR1 v1) sR2 v2) sR3 v3

theorem put3_apply (t1 t2 t3 : Fin 247) (s : Store 247) (v1 v2 v3 : List Bool) (t : Fin 247) :
    put3 t1 t2 t3 s v1 v2 v3 t =
      if t = t3 then v3 else if t = t2 then v2 else if t = t1 then v1 else s t := by
  simp only [put3, Function.update_apply]

/-- Park: move the stash registers' tapes to the parking tapes. -/
def parkP : Tape.Prog 247 :=
  Prog.cp pk1 (tWd sR1) ⨾ Prog.clr (tWd sR1) ⨾ Prog.cp pk2 (tWd sR2) ⨾ Prog.clr (tWd sR2) ⨾
    Prog.cp pk3 (tWd sR3) ⨾ Prog.clr (tWd sR3)

/-- Unpark: move the parking tapes into the stash registers. -/
def unparkP : Tape.Prog 247 :=
  Prog.cp (tWd sR1) pk1 ⨾ Prog.clr pk1 ⨾ Prog.cp (tWd sR2) pk2 ⨾ Prog.clr pk2 ⨾
    Prog.cp (tWd sR3) pk3 ⨾ Prog.clr pk3

/-- All tapes but `0` and the stash. -/
def postTapesS : List (Fin 247) :=
  (List.finRange 247).filter fun t => t ≠ 0 ∧ t ≠ tWd sR1 ∧ t ≠ tWd sR2 ∧ t ≠ tWd sR3

/-- **The exit**: register `ro` to tape `0`, everything but the stash cleared. -/
def postS (ro : Fin 200) : Tape.Prog 247 := Prog.cp 0 (tWd ro) ⨾ clrL postTapesS

/-- **The handler with a stash.** -/
noncomputable def ringIOS (N K : ℕ) (ra rb ro r1 : Fin 200) (tm : Fin 200 → ℕ) (c : Code) :
    XProg 247 :=
  .seq (.prog parkP) (.seq (preP N K ra rb tm) (.seq (.prog (.prim (.cons (tWd r1) true)))
    (.seq (.prog unparkP) (.seq (compile c) (.prog (postS ro))))))

/-! ### Semantics -/

theorem coinFree_parkP : parkP.CoinFree := rfl
theorem coinFree_unparkP : unparkP.CoinFree := rfl

theorem coinFree_postS (ro : Fin 200) : (postS ro).CoinFree := by
  simpa only [postS, Prog.CoinFree, Prog.coinFreeB, Bool.true_and] using coinFree_clrL postTapesS

theorem io2_tWd (a b : List Bool) (x : Fin 200) : io2 (R := 245) a b [] (tWd x) = [] := by
  have h0 : (tWd x).val ≠ 0 := by simp [tWd]
  have h1 : (tWd x).val ≠ 1 := by simp [tWd]; omega
  simp [io2, h0, h1]

theorem run_parkP (s : Store 247) (v1 v2 v3 : List Bool)
    (h1 : s pk1 = []) (h2 : s pk2 = []) (h3 : s pk3 = [])
    (e1 : s (tWd sR1) = []) (e2 : s (tWd sR2) = []) (e3 : s (tWd sR3) = []) :
    parkP.run (stash3 s v1 v2 v3) = park3 s v1 v2 v3 := by
  simp only [parkP, Prog.run_seq, Prog.run_copy, Prog.run_clear]
  funext t
  simp only [put3, Function.update_apply]
  by_cases a1 : t = tWd sR1 <;> by_cases a2 : t = tWd sR2 <;> by_cases a3 : t = tWd sR3 <;>
    by_cases b1 : t = pk1 <;> by_cases b2 : t = pk2 <;> by_cases b3 : t = pk3 <;>
    simp_all [sR1, sR2, sR3, pk1, pk2, pk3, tWd] <;> omega

theorem run_unparkP (w : St) (N K : ℕ) (v1 v2 v3 : List Bool) :
    unparkP.run (park3 (enc N K w) v1 v2 v3) = enc N K (stW w v1 v2 v3) := by
  simp only [stW, ← enc_update_tWd]
  simp only [unparkP, Prog.run_seq, Prog.run_copy, Prog.run_clear]
  funext t
  have hp1 : enc N K w pk1 = [] := by simp [enc, encO, pk1]
  have hp2 : enc N K w pk2 = [] := by simp [enc, encO, pk2]
  have hp3 : enc N K w pk3 = [] := by simp [enc, encO, pk3]
  simp only [put3, Function.update_apply]
  by_cases a1 : t = tWd sR1 <;> by_cases a2 : t = tWd sR2 <;> by_cases a3 : t = tWd sR3 <;>
    by_cases b1 : t = pk1 <;> by_cases b2 : t = pk2 <;> by_cases b3 : t = pk3 <;>
    simp_all [sR1, sR2, sR3, pk1, pk2, pk3, tWd] <;> omega

theorem run_postS (ro : Fin 200) (hro1 : ro ≠ sR1) (hro2 : ro ≠ sR2) (hro3 : ro ≠ sR3)
    (N K : ℕ) (w : St) (v1 v2 v3 : List Bool) :
    (postS ro).run (enc N K (stW w v1 v2 v3)) =
      stash3 (io2 (R := 245) (w ro) [] []) v1 v2 v3 := by
  rw [postS, Prog.run_seq, Prog.run_copy, run_clrL]
  have d12 : tWd sR1 ≠ tWd sR2 := by decide
  have d13 : tWd sR1 ≠ tWd sR3 := by decide
  have d23 : tWd sR2 ≠ tWd sR3 := by decide
  have r12 : sR1 ≠ sR2 := by decide
  have r13 : sR1 ≠ sR3 := by decide
  have r23 : sR2 ≠ sR3 := by decide
  funext t
  have er : enc N K (stW w v1 v2 v3) (tWd ro) = w ro := by
    rw [enc_tWd]; simp [stW, Function.update_apply, hro1, hro2, hro3]
  by_cases h0 : t = 0
  · subst h0
    have hm : (0 : Fin 247) ∉ postTapesS := by simp [postTapesS]
    rw [if_neg hm, Function.update_self, er]
    simp [put3, io2, Function.update_apply, sR1, sR2, sR3, tWd]
  by_cases hs3 : t = tWd sR3
  · subst hs3
    have hm : tWd sR3 ∉ postTapesS := by simp [postTapesS]
    rw [if_neg hm, Function.update_of_ne h0, enc_tWd]
    simp [put3, stW]
  by_cases hs2 : t = tWd sR2
  · subst hs2
    have hm : tWd sR2 ∉ postTapesS := by simp [postTapesS]
    rw [if_neg hm, Function.update_of_ne h0, enc_tWd]
    simp [put3, stW, Function.update_apply, d23, r23]
  by_cases hs1 : t = tWd sR1
  · subst hs1
    have hm : tWd sR1 ∉ postTapesS := by simp [postTapesS]
    rw [if_neg hm, Function.update_of_ne h0, enc_tWd]
    simp [put3, stW, Function.update_apply, d12, d13, r12, r13]
  · have hm : t ∈ postTapesS := by simp [postTapesS, h0, hs1, hs2, hs3]
    rw [if_pos hm]
    have e0 : t.val ≠ 0 := fun h => h0 (Fin.ext h)
    simp only [put3, Function.update_apply, hs1, hs2, hs3, if_false, io2, e0]
    split_ifs <;> rfl

/-! ### `preP` never touches the parking tapes -/

/-- The store after `preP`, for any input. -/
def preF (N K : ℕ) (ra rb : Fin 200) (tm : Fin 200 → ℕ) (s : Store 247) : Store 247 :=
  Function.update (tmplsS (tList N K ra rb tm) ((inP ra rb).run s)) tOn
    (List.replicate ((tmplsS (tList N K ra rb tm) ((inP ra rb).run s)) tNK).length true)

theorem tWd_ne_tOn' (x : Fin 200) : tOn ≠ tWd x := fun h => by
  have := congrArg Fin.val h; simp [tWd, tOn] at this; omega

theorem tWd_ne_cT' (x : Fin 200) : cT ≠ tWd x := fun h => by
  have := congrArg Fin.val h; simp [tWd, cT] at this; omega

theorem tList_ne_tOn {N K : ℕ} {ra rb : Fin 200} {tm : Fin 200 → ℕ} :
    ∀ p ∈ tList N K ra rb tm, p.1 ≠ tOn := by
  intro p hp
  rcases mem_tList.mp hp with rfl | rfl | rfl | ⟨r', -, -, rfl⟩
  · dsimp only; decide
  · dsimp only; decide
  · dsimp only; decide
  · exact fun h => tWd_ne_tOn' r' h.symm

theorem law_preP_gen (N K : ℕ) (ra rb : Fin 200) (tm : Fin 200 → ℕ) (s : Store 247)
    (hc : s cT = []) (hon : s tOn = []) :
    (preP N K ra rb tm).law s = PMF.pure (preF N K ra rb tm s) := by
  have hi : ∀ t, t ≠ 0 → t ≠ 1 → (∀ x : Fin 200, t ≠ tWd x) → (inP ra rb).run s t = s t := by
    intro t h0 h1 hx
    simp only [inP, Prog.run_seq, Prog.run_copy, Prog.run_clear, Function.update_apply, h0, h1,
      hx, if_false]
  have hcT : (inP ra rb).run s cT = [] := by
    rw [hi cT (by decide) (by decide) fun x => tWd_ne_cT' x]; exact hc
  have hOn0 : (inP ra rb).run s tOn = [] := by
    rw [hi tOn (by decide) (by decide) fun x => tWd_ne_tOn' x]; exact hon
  rw [preP, XProg.law_seq, XProg.law_prog, Prog.law_eq_run_of_coinFree _ (coinFree_inP ra rb),
    PMF.pure_bind, XProg.law_seq, law_tmplsP cT _ _ hcT tList_ne_cT, PMF.pure_bind,
    XProg.law_prog, Prog.law_eq_run_of_coinFree _ coinFree_onesC,
    run_onesP _ (by rw [tmplsS_apply_of_not_mem _ _ _ fun q hq he => tList_ne_cT q hq he]; exact hcT)
      (by rw [tmplsS_apply_of_not_mem _ _ _ fun q hq he => tList_ne_tOn q hq he]; exact hOn0)]
  rfl

theorem tmplsS_update {k : ℕ} (l : List (Fin k × ℕ)) (s : Store k) (t : Fin k) (v : List Bool)
    (h : ∀ p ∈ l, p.1 ≠ t) :
    tmplsS l (Function.update s t v) = Function.update (tmplsS l s) t v := by
  induction l generalizing s with
  | nil => rfl
  | cons p l ih =>
    simp only [tmplsS, List.foldl_cons]
    rw [show l.foldl _ _ = tmplsS l _ from rfl, show l.foldl _ _ = tmplsS l _ from rfl,
      Function.update_comm (h p (by simp)).symm, ih _ (fun q hq => h q (by simp [hq]))]

/-- The parking tapes are no template tapes and no register tapes. -/
theorem park_ok (t : Fin 247) (ht : t = pk1 ∨ t = pk2 ∨ t = pk3) :
    t ≠ 0 ∧ t ≠ 1 ∧ t ≠ tOn ∧ t ≠ cT ∧ t ≠ tNK ∧ (∀ x : Fin 200, t ≠ tWd x) ∧
      ∀ {N K : ℕ} {ra rb : Fin 200} {tm : Fin 200 → ℕ}, ∀ p ∈ tList N K ra rb tm, p.1 ≠ t := by
  have hx : ∀ x : Fin 200, t ≠ tWd x := fun x h => by
    rcases ht with rfl | rfl | rfl <;>
    · have := congrArg Fin.val h; simp [tWd, pk1, pk2, pk3] at this; omega
  refine ⟨by rcases ht with rfl | rfl | rfl <;> decide, by rcases ht with rfl | rfl | rfl <;> decide,
    by rcases ht with rfl | rfl | rfl <;> decide, by rcases ht with rfl | rfl | rfl <;> decide,
    by rcases ht with rfl | rfl | rfl <;> decide, hx, ?_⟩
  intro N K ra rb tm p hp
  rcases mem_tList.mp hp with rfl | rfl | rfl | ⟨r', -, -, rfl⟩
  · show tK ≠ t; rcases ht with rfl | rfl | rfl <;> decide
  · show tN ≠ t; rcases ht with rfl | rfl | rfl <;> decide
  · show tNK ≠ t; rcases ht with rfl | rfl | rfl <;> decide
  · exact fun h => hx r' h.symm

theorem preF_update (N K : ℕ) (ra rb : Fin 200) (tm : Fin 200 → ℕ) (s : Store 247)
    (t : Fin 247) (ht : t = pk1 ∨ t = pk2 ∨ t = pk3) (v : List Bool) :
    preF N K ra rb tm (Function.update s t v) = Function.update (preF N K ra rb tm s) t v := by
  obtain ⟨h0, h1, hOn, -, hNK, hx, hl⟩ := park_ok t ht
  have hi : (inP ra rb).run (Function.update s t v) = Function.update ((inP ra rb).run s) t v := by
    simp only [inP, Prog.run_seq, Prog.run_copy, Prog.run_clear]
    have a1 := hx ra
    have a2 := hx rb
    funext x
    simp only [Function.update_apply]
    by_cases e : x = t
    · subst e; simp [h0, h1, a1, a2]
    · simp only [e, if_false]
      split_ifs <;> simp_all
  rw [preF, preF, hi, tmplsS_update _ _ _ _ fun p hp => hl p hp,
    Function.update_of_ne (Ne.symm hNK), Function.update_comm (Ne.symm hOn)]

/-- **`preP` with a parked stash.** -/
theorem pmf_pure_inj' {α : Type} {a b : α} (h : PMF.pure a = PMF.pure b) : a = b := by
  have := congrArg (fun p : PMF α => p a) h
  simp only [PMF.pure_apply, if_true] at this
  by_contra hne
  rw [if_neg hne] at this
  exact one_ne_zero this

theorem law_preP_park (N K : ℕ) {ra rb : Fin 200} (hab : ra ≠ rb) (tm : Fin 200 → ℕ)
    (a b v1 v2 v3 : List Bool) :
    (preP N K ra rb tm).law (park3 (io2 (R := 245) a b []) v1 v2 v3) =
      PMF.pure (park3 (enc N K (initW ra rb tm a b)) v1 v2 v3) := by
  have hc : io2 (R := 245) a b [] cT = [] := by simp [io2, cT]
  have hon : io2 (R := 245) a b [] tOn = [] := by simp [io2, tOn]
  have e := law_preP N K hab tm a b
  rw [law_preP_gen N K ra rb tm _ hc hon] at e
  have e' := pmf_pure_inj' e
  rw [law_preP_gen]
  · simp only [park3, put3]
    rw [preF_update _ _ _ _ _ _ pk3 (Or.inr (Or.inr rfl)),
      preF_update _ _ _ _ _ _ pk2 (Or.inr (Or.inl rfl)),
      preF_update _ _ _ _ _ _ pk1 (Or.inl rfl), e']
  · simp [put3, Function.update_apply, pk1, pk2, pk3, cT, io2]
  · simp [put3, Function.update_apply, pk1, pk2, pk3, tOn, io2]

/-! ### The law of the handler -/

theorem stW_exec (N K : ℕ) (c : Code) (h1 : usesR sR1 c = false) (h2 : usesR sR2 c = false)
    (h3 : usesR sR3 c = false) (w : St) (v1 v2 v3 : List Bool) :
    exec N K c (stW w v1 v2 v3) = stW (exec N K c w) v1 v2 v3 := by
  rw [stW, exec_update_of_usesR N K _ _ c h3, exec_update_of_usesR N K _ _ c h2,
    exec_update_of_usesR N K _ _ c h1, stW]

/-- **The law of the stash handler.** -/
theorem law_ringIOS {N K : ℕ} (hN : 0 < N) (hK : 0 < K) {ra rb : Fin 200} (hab : ra ≠ rb)
    (ro r1 : Fin 200) (h1a : r1 ≠ ra) (h1b : r1 ≠ rb) (hro1 : ro ≠ sR1) (hro2 : ro ≠ sR2)
    (hro3 : ro ≠ sR3) (tm : Fin 200 → ℕ) (c : Code) (hc1 : usesR sR1 c = false)
    (hc2 : usesR sR2 c = false) (hc3 : usesR sR3 c = false) (a b v1 v2 v3 : List Bool) :
    (ringIOS N K ra rb ro r1 tm c).law (stash3 (io2 (R := 245) a b []) v1 v2 v3) =
      PMF.pure (stash3 (io2 (R := 245) (exec N K c (initW1 ra rb r1 tm a b) ro) [] []) v1 v2 v3) := by
  have hp1 : io2 (R := 245) a b [] pk1 = [] := by simp [io2, pk1]
  have hp2 : io2 (R := 245) a b [] pk2 = [] := by simp [io2, pk2]
  have hp3 : io2 (R := 245) a b [] pk3 = [] := by simp [io2, pk3]
  rw [ringIOS, XProg.law_seq, XProg.law_prog, Prog.law_eq_run_of_coinFree _ coinFree_parkP,
    run_parkP _ _ _ _ hp1 hp2 hp3 (io2_tWd _ _ _) (io2_tWd _ _ _) (io2_tWd _ _ _), PMF.pure_bind,
    XProg.law_seq, law_preP_park N K hab tm, PMF.pure_bind, XProg.law_seq, XProg.law_prim,
    PMF.pure_bind]
  have h : Prim.apply (.cons (tWd r1) true) (park3 (enc N K (initW ra rb tm a b)) v1 v2 v3) =
      park3 (enc N K (initW1 ra rb r1 tm a b)) v1 v2 v3 := by
    obtain ⟨-, -, -, -, -, hx1, -⟩ := park_ok pk1 (Or.inl rfl)
    obtain ⟨-, -, -, -, -, hx2, -⟩ := park_ok pk2 (Or.inr (Or.inl rfl))
    obtain ⟨-, -, -, -, -, hx3, -⟩ := park_ok pk3 (Or.inr (Or.inr rfl))
    show Function.update (park3 _ v1 v2 v3) (tWd r1) (true :: park3 _ v1 v2 v3 (tWd r1)) = _
    have e1 : park3 (enc N K (initW ra rb tm a b)) v1 v2 v3 (tWd r1) = initW ra rb tm a b r1 := by
      simp only [put3, Function.update_apply, (hx3 r1).symm, (hx2 r1).symm, (hx1 r1).symm,
        if_false, enc_tWd]
    have e2 : enc N K (initW1 ra rb r1 tm a b) = Function.update (enc N K (initW ra rb tm a b))
        (tWd r1) (true :: initW ra rb tm a b r1) := by
      rw [enc_update_tWd]; simp [initW1, initW, h1a, h1b]
    rw [e1, e2]
    have b1 := hx1 r1
    have b2 := hx2 r1
    have b3 := hx3 r1
    funext x
    simp only [put3, Function.update_apply]
    split_ifs <;> simp_all
  rw [h, XProg.law_seq, XProg.law_prog, Prog.law_eq_run_of_coinFree _ coinFree_unparkP,
    run_unparkP, PMF.pure_bind, XProg.law_seq, law_compile hN hK, PMF.pure_bind,
    stW_exec N K c hc1 hc2 hc3, XProg.law_prog, Prog.law_eq_run_of_coinFree _ (coinFree_postS ro),
    run_postS ro hro1 hro2 hro3]

/-- **The stash handler is well formed.** -/
theorem wf_ringIOS (N K : ℕ) (ra rb ro r1 : Fin 200) (tm : Fin 200 → ℕ) (c : Code)
    (hc : loopOkB c = true) : (ringIOS N K ra rb ro r1 tm c).WF :=
  ⟨⟨trivial, trivial, trivial, trivial, trivial, trivial⟩, wf_preP N K ra rb tm, trivial,
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩, wf_compile c hc, trivial, wf_clrL _⟩

end SigabaNeo.Tape.RingVM.Handler