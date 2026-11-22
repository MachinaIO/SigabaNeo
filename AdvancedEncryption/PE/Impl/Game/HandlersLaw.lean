import PE.Impl.Game.Handlers

/-!
# The laws of the handlers

The handlers of `PE.Impl.Game.Handlers` act on the layout `(b, [], encState st, blank …)` as the
oracle `oracleW` (`law_selH`, `law_keyH`, `law_chalH`).
-/

namespace AdvancedEncryption.PE.Generic

open SigabaNeo SigabaNeo.Tape Cslib Cslib.Probability

variable {U : Universe} {Sig : Type} {R : ℕ}

theorem ite_pos' {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

theorem ite_neg' {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by simp [h]

/-! ### Glue stores -/

/-- The glue store with query `b`, answer `a` and state `t`. -/
def vec (b a t : List Bool) : Store 8 :=
  fun j => if j = 0 then b else if j = 1 then a else if j = 2 then t else []

@[simp] theorem ext8_gt {α : Type} (v : Fin 8 → α) (d : α) (j : Fin 8) :
    ext8 (R := R) v d (gt j) = v j := congrFun (glue_restrict v d) j

theorem layout_eq (b a t : List Bool) :
    (Inline.layout (m := R + 5) b a t : Fin (R + 8) → List Bool) = ext8 (vec b a t) [] := by
  funext l
  have h0 : ∀ h : l.val < 8, ((⟨l.val, h⟩ : Fin 8) = 0 ↔ l.val = 0) := fun h => Fin.ext_iff
  have h1 : ∀ h : l.val < 8, ((⟨l.val, h⟩ : Fin 8) = 1 ↔ l.val = 1) := fun h => Fin.ext_iff
  have h2 : ∀ h : l.val < 8, ((⟨l.val, h⟩ : Fin 8) = 2 ↔ l.val = 2) := fun h => Fin.ext_iff
  simp only [Inline.layout, ext8, vec]
  by_cases hl : l.val < 8
  · simp only [hl, dite_true, h0 hl, h1 hl, h2 hl]
  · have a0 : l.val ≠ 0 := by omega
    have a1 : l.val ≠ 1 := by omega
    have a2 : l.val ≠ 2 := by omega
    simp only [hl, dite_false, a0, a1, a2, ite_false]

theorem law_skipG (v : Store 8) : XProg.law (skipG (R := R)) (ext8 v []) = PMF.pure (ext8 v []) :=
  law_glue_pure (by rw [Prog.law_prim, Prog.apply_copy_self])

theorem law_seq_glue {P : Prog 8} {q : XProg (R + 8)} {v w : Store 8} (h : P.law v = PMF.pure w) :
    XProg.law (.seq (glue P) q) (ext8 v []) = XProg.law q (ext8 w []) :=
  XProg.law_seq_pure (law_glue_pure h)

theorem law_seq_comp (p q : Fin 8) (hpq : p ≠ q) (c : XProg (R + 2)) (rest : XProg (R + 8))
    (v : Store 8) {β : Type} (μ : PMF β) (out : β → List Bool)
    (hc : XProg.law c (io2 (v p) (v q) []) = μ.map (fun r => io2 (out r) [] [])) :
    XProg.law (.seq (comp p q hpq c) rest) (ext8 v []) =
      μ.bind (fun r => XProg.law rest (ext8 (Function.update (Function.update v q []) p (out r)) [])) := by
  rw [XProg.law_seq, law_comp p q hpq c v μ out hc, PMF.bind_map]
  rfl

theorem law_seq_comp_pure (p q : Fin 8) (hpq : p ≠ q) (c : XProg (R + 2)) (rest : XProg (R + 8))
    (v : Store 8) (o : List Bool) (hc : XProg.law c (io2 (v p) (v q) []) = PMF.pure (io2 o [] [])) :
    XProg.law (.seq (comp p q hpq c) rest) (ext8 v []) =
      XProg.law rest (ext8 (Function.update (Function.update v q []) p o) []) := by
  rw [law_seq_comp p q hpq c rest v (PMF.pure ()) (fun _ => o) (by rw [hc, PMF.pure_map]),
    PMF.pure_bind]

/-- **The length test.** -/
theorem law_testLen (n : ℕ) (succ fail : XProg (R + 8)) (v : Store 8) (h3 : v 3 = []) :
    XProg.law (testLen n succ fail) (ext8 v []) =
      if (v 0).length = n then XProg.law succ (ext8 v []) else XProg.law fail (ext8 v []) := by
  have hv : ∀ w, Function.update v 3 w = v → True := fun _ _ => trivial
  have hupd : Function.update v 3 [] = v := by rw [← h3]; exact Function.update_eq_self 3 v
  rw [testLen, law_seq_glue (w := Function.update v 3 ((true :: v 0).drop n)) (by
    rw [lenPrep, Prog.law_seq_pure (Prog.law_prim _ _), Prog.law_seq_pure (Prog.law_prim _ _),
      Prog.law_dropN]
    simp [Prim.apply])]
  rw [XProg.law_ifBlank]
  simp only [ext8_gt, Function.update_self]
  by_cases hd : (true :: v 0).drop n = []
  · have hn : (v 0).length ≠ n := by
      intro h; rw [List.drop_eq_nil_iff] at hd; simp at hd; omega
    simp only [hd, hn, ↓reduceIte, hupd]
  · simp only [hd, ↓reduceIte]
    have hn1 : n ≤ (v 0).length := by
      rw [List.drop_eq_nil_iff] at hd; simp at hd; omega
    rw [law_seq_glue (w := Function.update v 3 ((v 0).drop n)) (by
      rw [Prog.law_prim]
      congr 1
      funext j
      simp only [Prim.apply, Function.update_apply]
      split_ifs
      · rw [List.tail_drop]
        cases n with
        | zero => simp
        | succ n => simp [List.drop_succ_cons]
      · rfl), XProg.law_ifBlank]
    simp only [ext8_gt, Function.update_self]
    by_cases hb : (v 0).drop n = []
    · have hn : (v 0).length = n := by
        rw [List.drop_eq_nil_iff] at hb; omega
      simp only [hb, hn, ↓reduceIte, hupd]
    · have hn : (v 0).length ≠ n := by
        intro h; apply hb; simp [← h]
      simp only [hb, hn, ↓reduceIte]
      rw [law_seq_glue (w := v) (by
        rw [Prog.law_prim]
        congr 1
        funext j
        simp only [Prim.apply, Function.update_apply]
        split_ifs with hj
        · subst hj; exact h3.symm
        · rfl)]

/-! ### The oracle on the two kinds of states -/

section Oracle

variable (sp : Spec U Sig) (setupW : List Bool → U.Attr → PMF Sig) (w : List Bool)

theorem oracleW_sel_init (x : U.Attr) :
    oracleW sp setupW (selectOp, U.encAttr x) (w, {}) =
      (setupW w x).map fun σ => (sp.pub σ, (w, ({ attr := some x, sec := some σ } : GState U Sig))) := by
  simp only [oracleW, oracle, oracleWith, ↓reduceIte, Codes.decode_attr, PMF.map_comp]
  rfl

theorem oracleW_sel_init_none {b : List Bool} (hb : decode U.encAttr b = none) :
    oracleW sp setupW (selectOp, b) (w, {}) = PMF.pure ([], (w, {})) := by
  simp only [oracleW, oracle, oracleWith, ↓reduceIte, hb, PMF.pure_map]

theorem oracleW_sel_sel (b : List Bool) {s : GState U Sig} {x : U.Attr} (hs : s.attr = some x) :
    oracleW sp setupW (selectOp, b) (w, s) = PMF.pure ([], (w, s)) := by
  simp only [oracleW, oracle, oracleWith, ↓reduceIte, hs, PMF.pure_map]

theorem oracleW_key_init (b : List Bool) :
    oracleW sp setupW (keyGenOp, b) (w, {}) = PMF.pure ([], (w, {})) := by
  simp [oracleW, oracle, oracleWith, selectOp, keyGenOp]

theorem oracleW_key_sel (b : List Bool) {s : GState U Sig} {x : U.Attr} {σ : Sig}
    (hx : s.attr = some x) (hσ : s.sec = some σ) :
    oracleW sp setupW (keyGenOp, b) (w, s) =
      (sp.key σ b).map fun sk => (sk, (w, { s with bad := s.bad || sp.auth b x })) := by
  simp [oracleW, oracle, oracleWith, selectOp, keyGenOp, hx, hσ, PMF.map_comp, Function.comp_def]

theorem oracleW_chal_init (b : List Bool) :
    oracleW sp setupW (challengeOp, b) (w, {}) = PMF.pure ([], (w, {})) := by
  simp [oracleW, oracle, oracleWith, selectOp, keyGenOp, challengeOp]

theorem oracleW_chal_sel_fresh (μ : U.Msg) {s : GState U Sig} {x : U.Attr} {σ : Sig}
    (hx : s.attr = some x) (hσ : s.sec = some σ) (hm : s.msg = none) :
    oracleW sp setupW (challengeOp, U.encMsg μ) (w, s) =
      (sp.chal σ μ).map fun ct => (ct, (w, { s with msg := some μ })) := by
  simp [oracleW, oracle, oracleWith, selectOp, keyGenOp, challengeOp, hx, hσ, hm,
    Codes.decode_msg, PMF.map_comp, Function.comp_def]

theorem oracleW_chal_sel_used (b : List Bool) {s : GState U Sig} {x : U.Attr} {σ μ : _}
    (hx : s.attr = some x) (hσ : s.sec = some σ) (hm : s.msg = some μ) :
    oracleW sp setupW (challengeOp, b) (w, s) = PMF.pure ([], (w, s)) := by
  simp [oracleW, oracle, oracleWith, selectOp, keyGenOp, challengeOp, hx, hσ, hm]

theorem oracleW_chal_sel_none {b : List Bool} (hb : decode U.encMsg b = none) {s : GState U Sig} :
    oracleW sp setupW (challengeOp, b) (w, s) = PMF.pure ([], (w, s)) := by
  simp only [oracleW, oracle, oracleWith, selectOp, keyGenOp, challengeOp, hb]
  split_ifs <;> split <;> simp_all

end Oracle

/-! ### The selection -/

section Sel

variable {cd : Codes U Sig} {sp : Spec U Sig} {setupW : List Bool → U.Attr → PMF Sig}
  {IW : List Bool → Prop} {Ok : Sig → Prop} (cs : Comps R cd sp setupW IW Ok)

theorem law_buildSel (v : Store 8) (h0 : (v 0).length = cd.nA) (h4 : v 4 = []) (h5 : v 5 = []) :
    (buildSel cd).law v = PMF.pure (Function.update (Function.update v 3 [])
      2 (List.replicate (cd.nM + 3) false ++ (v 0 ++ v 2))) := by
  rw [buildSel, Prog.law_seq_pure (Prog.law_prim _ _), Prog.law_seq_pure (Prog.law_prependN cd.nA
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) _
      (by simpa [Prim.apply] using h0) (by simpa [Prim.apply] using h4)
      (by simpa [Prim.apply] using h5)), Prog.law_consN]
  congr 1
  funext j
  fin_cases j <;> simp [Prim.apply]

theorem law_selCore (w : List Bool) (x : U.Attr) (hw : IW w) :
    XProg.law (selCore cd cs.setupP cs.pubP) (ext8 (vec (U.encAttr x) [] w) []) =
      (setupW w x).map fun σ =>
        ext8 (vec (U.encAttr x) (sp.pub σ) (cd.selWord false none x σ)) [] := by
  rw [selCore, law_seq_glue (Prog.law_prim _ _)]
  rw [law_seq_comp 2 4 _ cs.setupP _ _ (setupW w x) (fun σ => cd.sig.enc σ) (by
    convert cs.law_setup w x hw using 3 <;> simp [Prim.apply, vec])]
  rw [← PMF.bind_pure_comp]
  refine PMF.bind_congr_on_support _ _ _ fun σ hσ => ?_
  rw [law_seq_glue (Prog.law_prim _ _)]
  rw [law_seq_comp_pure 1 4 _ cs.pubP _ _ (sp.pub σ) (by
    convert cs.law_pub σ (cs.ok_setup w x hw σ hσ) using 3 <;> simp [Prim.apply, vec])]
  rw [law_glue_pure (law_buildSel _ (by simp [Prim.apply, vec, cd.len_attr])
    (by simp [Prim.apply, vec]) (by simp [Prim.apply, vec]))]
  simp only [Function.comp_apply]
  congr 2
  funext j
  fin_cases j <;> simp [Prim.apply, vec, Codes.selWord, Codes.msgWord,
    List.replicate_succ]

theorem head_selWord (bad : Bool) (m : Option U.Msg) (x : U.Attr) (σ : Sig) :
    (cd.selWord bad m x σ).head? = some false := rfl

theorem eq_nil_of_head {w : List Bool} (h1 : w.head? ≠ some false) (h2 : ¬ w.head? = some true) :
    w = [] := by
  cases w with
  | nil => rfl
  | cons c w => cases c <;> simp_all

theorem law_selH_init (w b : List Bool) (hw : IW w) (hh : w.head? ≠ some false) :
    XProg.law (selH cd cs.setupP cs.pubP) (ext8 (vec b [] w) []) =
      (oracleW sp setupW (selectOp, b) (w, {})).map
        (fun r => ext8 (vec b r.1 (cd.encState r.2)) []) := by
  have hinit : XProg.law (testLen cd.nA (selCore cd cs.setupP cs.pubP) skipG)
      (ext8 (vec b [] w) []) = (oracleW sp setupW (selectOp, b) (w, {})).map
        (fun r => ext8 (vec b r.1 (cd.encState r.2)) []) := by
    rw [law_testLen _ _ _ _ (by simp [vec])]
    split_ifs with hb
    · obtain ⟨x, rfl⟩ := cd.full_attr b (by simpa [vec] using hb)
      rw [law_selCore cs w x hw, oracleW_sel_init, PMF.map_comp]
      rfl
    · rw [law_skipG, oracleW_sel_init_none _ _ _ (cd.decode_attr_none (by simpa [vec] using hb)),
        PMF.pure_map]
      rfl
  simp only [selH]
  rw [XProg.law_ifBit]
  split_ifs with h1
  · exact hinit
  · rw [XProg.law_ifBlank, ite_pos' (by simpa [vec] using eq_nil_of_head hh (by simpa [vec] using h1))]
    exact hinit

theorem law_selH_sel (w b : List Bool) {s : GState U Sig} {x : U.Attr} {σ : Sig}
    (hx : s.attr = some x) (hσ : s.sec = some σ) :
    XProg.law (selH cd cs.setupP cs.pubP) (ext8 (vec b [] (cd.encState (w, s))) []) =
      (oracleW sp setupW (selectOp, b) (w, s)).map
        (fun r => ext8 (vec b r.1 (cd.encState r.2)) []) := by
  have he : cd.encState (w, s) = cd.selWord s.bad s.msg x σ := by
    simp [Codes.encState, hx, hσ]
  simp only [selH]
  rw [XProg.law_ifBit, ite_neg' (by simp [vec, he, head_selWord]), XProg.law_ifBlank,
    ite_neg' (by simp [vec, he, Codes.selWord]), law_skipG, oracleW_sel_sel _ _ _ _ hx, PMF.pure_map]

end Sel

/-! ### Key queries -/

section Key

variable {cd : Codes U Sig} {sp : Spec U Sig} {setupW : List Bool → U.Attr → PMF Sig}
  {IW : List Bool → Prop} {Ok : Sig → Prop} (cs : Comps R cd sp setupW IW Ok)

theorem law_parseSel (v : Store 8) (c bad : Bool) (mw xa es : List Bool)
    (hmw : mw.length = cd.nM + 1) (hxa : xa.length = cd.nA)
    (h2 : v 2 = c :: bad :: (mw ++ (xa ++ es))) (h3 : v 3 = []) (h5 : v 5 = []) (h7 : v 7 = []) :
    (parseSel cd).law v = PMF.pure (Function.update (Function.update (Function.update
      (Function.update v 2 es) 4 [bad]) 3 mw) 5 xa) := by
  rw [parseSel, Prog.law_seq_pure (Prog.law_prim _ _), Prog.law_seq_pure (Prog.law_prim _ _),
    Prog.law_seq_pure (Prog.law_moveFront _ (by decide) (by decide) (by decide) _
      (by simp [Prim.apply, h7])),
    Prog.law_moveFront _ (by decide) (by decide) (by decide) _ (by simp [Prim.apply, h7])]
  congr 1
  funext j
  fin_cases j <;> simp [Prim.apply, h2, h3, h5, List.drop_left' hmw,
    List.take_left' hmw, List.drop_left' hxa, List.take_left' hxa]

theorem law_rebuildK (v : Store 8) (bad' : Bool) (mw xa es : List Bool)
    (hmw : mw.length = cd.nM + 1) (hxa : xa.length = cd.nA)
    (h2 : v 2 = es) (h3 : v 3 = mw) (h4 : v 4 = [bad']) (h5 : v 5 = xa) (h7 : v 7 = []) :
    (rebuildK cd).law v = PMF.pure (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update v 2 (false :: bad' :: (mw ++ (xa ++ es))))
        3 []) 4 []) 5 []) 6 []) 7 []) := by
  rw [rebuildK, Prog.law_seq_pure (Prog.law_prim _ _),
    Prog.law_seq_pure (Prog.law_prependN cd.nA (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) _ (by simp [Prim.apply, h5, hxa]) (by simp [Prim.apply])
      (by simp [Prim.apply, h7])),
    Prog.law_seq_pure (Prog.law_prependN (cd.nM + 1) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) _ (by simp [Prim.apply, h3, hmw]) (by simp [Prim.apply])
      (by simp [Prim.apply, h7])),
    Prog.law_seq_pure (Prog.law_prim _ _), Prog.law_seq_pure (Prog.law_prim _ _), Prog.law_prim]
  congr 1
  funext j
  fin_cases j <;> simp [Prim.apply, h2, h3, h4, h5, h7]

theorem law_setBad (v : Store 8) (bad a : Bool) (h4 : v 4 = [bad]) (h6 : v 6 = [a]) :
    XProg.law (.ifBit (gt 6) (glue setBad) (skipG (R := R))) (ext8 v []) =
      PMF.pure (ext8 (Function.update v 4 [bad || a]) []) := by
  rw [XProg.law_ifBit]
  cases a
  · rw [ite_neg' (by simp [h6]), law_skipG, Bool.or_false, ← h4, Function.update_eq_self]
  · rw [ite_pos' (by simp [h6]), law_glue_pure (by
      rw [setBad, Prog.law_seq_pure (Prog.law_prim _ _), Prog.law_prim]), Bool.or_true]
    congr 2
    funext j
    simp only [Prim.apply, Function.update_apply]
    split_ifs <;> rfl

theorem law_seq_pure_X {p q : XProg (R + 8)} {s t : Store (R + 8)} (hp : XProg.law p s = PMF.pure t) :
    XProg.law (.seq p q) s = XProg.law q t := XProg.law_seq_pure hp

theorem law_keySel (b : List Bool) (bad : Bool) (m : Option U.Msg) (x : U.Attr) (σ : Sig)
    (hσ : Ok σ) :
    XProg.law (keySel cd cs.keyP cs.authP) (ext8 (vec b [] (cd.selWord bad m x σ)) []) =
      (sp.key σ b).map fun sk =>
        ext8 (vec b sk (cd.selWord (bad || sp.auth b x) m x σ)) [] := by
  rw [keySel, law_seq_glue (law_parseSel _ false bad (cd.msgWord m) (U.encAttr x) (cd.sig.enc σ)
    (cd.length_msgWord m) (cd.len_attr x) (by simp [vec, Codes.selWord]) (by simp [vec])
    (by simp [vec]) (by simp [vec]))]
  rw [law_seq_glue (Prog.law_seq_pure (Prog.law_prim _ _) |>.trans (Prog.law_prim _ _))]
  rw [law_seq_comp 1 6 _ cs.keyP _ _ (sp.key σ b) id (by
    convert cs.law_key σ b hσ using 3 <;> simp [Prim.apply, vec])]
  rw [← PMF.bind_pure_comp]
  congr 1
  funext sk
  rw [law_seq_glue (Prog.law_seq_pure (Prog.law_prim _ _) |>.trans (Prog.law_prim _ _))]
  rw [law_seq_comp_pure 6 7 _ cs.authP _ _ [sp.auth b x] (by
    convert cs.law_auth b x using 3 <;> simp [Prim.apply, vec])]
  rw [law_seq_pure_X (law_setBad _ bad (sp.auth b x) (by simp [Prim.apply, vec])
    (by simp [Prim.apply, vec]))]
  rw [law_glue_pure (law_rebuildK _ (bad || sp.auth b x) (cd.msgWord m) (U.encAttr x) (cd.sig.enc σ)
    (cd.length_msgWord m) (cd.len_attr x) (by simp [Prim.apply, vec])
    (by simp [Prim.apply, vec])
    (by simp [Prim.apply, vec])
    (by simp [Prim.apply, vec])
    (by simp [Prim.apply, vec]))]
  simp only [Function.comp_apply, id]
  congr 2
  funext j
  fin_cases j <;> simp [Prim.apply, vec, Codes.selWord]

theorem law_keyH_init (w b : List Bool) (hh : w.head? ≠ some false) :
    XProg.law (keyH cd cs.keyP cs.authP) (ext8 (vec b [] w) []) =
      (oracleW sp setupW (keyGenOp, b) (w, {})).map
        (fun r => ext8 (vec b r.1 (cd.encState r.2)) []) := by
  rw [oracleW_key_init, PMF.pure_map, keyH, XProg.law_ifBit]
  split_ifs with h1
  · exact law_skipG _
  · rw [XProg.law_ifBlank, ite_pos' (by simpa [vec] using eq_nil_of_head hh (by simpa [vec] using h1))]
    exact law_skipG _

theorem law_keyH_sel (w b : List Bool) {s : GState U Sig} {x : U.Attr} {σ : Sig}
    (hx : s.attr = some x) (hσ : s.sec = some σ) (hOk : Ok σ) :
    XProg.law (keyH cd cs.keyP cs.authP) (ext8 (vec b [] (cd.encState (w, s))) []) =
      (oracleW sp setupW (keyGenOp, b) (w, s)).map
        (fun r => ext8 (vec b r.1 (cd.encState r.2)) []) := by
  have he : cd.encState (w, s) = cd.selWord s.bad s.msg x σ := by
    simp [Codes.encState, hx, hσ]
  rw [keyH, XProg.law_ifBit, ite_neg' (by simp [vec, he, head_selWord]), XProg.law_ifBlank,
    ite_neg' (by simp [vec, he, Codes.selWord]), he, law_keySel cs b s.bad s.msg x σ hOk,
    oracleW_key_sel _ _ _ _ hx hσ, PMF.map_comp]
  congr 1
  funext sk
  simp [Codes.encState, hx, hσ]

end Key

/-! ### The challenge -/

section Chal

variable {cd : Codes U Sig} {sp : Spec U Sig} {setupW : List Bool → U.Attr → PMF Sig}
  {IW : List Bool → Prop} {Ok : Sig → Prop} (cs : Comps R cd sp setupW IW Ok)

theorem law_restoreC (v : Store 8) (bad : Bool) (h4 : v 4 = [bad]) :
    restoreC.law v = PMF.pure (Function.update (Function.update v 2 (false :: bad :: v 2)) 4 []) := by
  rw [restoreC, Prog.law_seq_pure (Prog.law_prim _ _), Prog.law_seq_pure (Prog.law_prim _ _),
    Prog.law_prim]
  congr 1
  funext j
  fin_cases j <;> simp [Prim.apply, h4]

theorem law_parseC (v : Store 8) (xa es : List Bool) (hxa : xa.length = cd.nA)
    (h2 : v 2 = false :: (List.replicate cd.nM false ++ (xa ++ es))) (h5 : v 5 = []) (h7 : v 7 = []) :
    (parseC cd).law v = PMF.pure (Function.update (Function.update v 2 es) 5 xa) := by
  rw [parseC, Prog.law_seq_pure (Prog.law_prim _ _), Prog.law_seq_pure (Prog.law_dropN _ _ _),
    Prog.law_moveFront _ (by decide) (by decide) (by decide) _ (by simp [Prim.apply, h7])]
  have hr : (List.replicate cd.nM false).length = cd.nM := List.length_replicate
  congr 1
  funext j
  fin_cases j <;> simp [Prim.apply, h2, h5, List.drop_left' hr, List.drop_left' hxa,
    List.take_left' hxa]

theorem law_rebuildC (v : Store 8) (bad : Bool) (b xa es : List Bool) (hb : b.length = cd.nM)
    (hxa : xa.length = cd.nA) (h0 : v 0 = b) (h2 : v 2 = es) (h4 : v 4 = [bad])
    (h5 : v 5 = xa) (h6 : v 6 = []) (h7 : v 7 = []) :
    (rebuildC cd).law v = PMF.pure (Function.update (Function.update (Function.update
      (Function.update v 2 (false :: bad :: true :: (b ++ (xa ++ es)))) 3 []) 4 []) 5 []) := by
  rw [rebuildC, Prog.law_seq_pure (Prog.law_prependN cd.nA (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) _ (by simp [h5, hxa]) h6 h7),
    Prog.law_seq_pure (Prog.law_prim _ _),
    Prog.law_seq_pure (Prog.law_prependN cd.nM (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) _ (by simp [Prim.apply, h0, hb]) (by simp [Prim.apply, h6])
      (by simp [Prim.apply, h7])),
    Prog.law_seq_pure (Prog.law_prim _ _), law_restoreC _ bad (by simp [Prim.apply, h4])]
  congr 1
  funext j
  fin_cases j <;> simp [Prim.apply, h0, h2, h5, h6, h7]

theorem law_chalH_init (w b : List Bool) (hh : w.head? ≠ some false) :
    XProg.law (chalH cd cs.chalP) (ext8 (vec b [] w) []) =
      (oracleW sp setupW (challengeOp, b) (w, {})).map
        (fun r => ext8 (vec b r.1 (cd.encState r.2)) []) := by
  rw [oracleW_chal_init, PMF.pure_map, chalH, XProg.law_ifBit]
  split_ifs with h1
  · exact law_skipG _
  · rw [XProg.law_ifBlank, ite_pos' (by simpa [vec] using eq_nil_of_head hh (by simpa [vec] using h1))]
    exact law_skipG _

theorem law_chalH_sel (w b : List Bool) {s : GState U Sig} {x : U.Attr} {σ : Sig}
    (hx : s.attr = some x) (hσ : s.sec = some σ) (hOk : Ok σ) :
    XProg.law (chalH cd cs.chalP) (ext8 (vec b [] (cd.encState (w, s))) []) =
      (oracleW sp setupW (challengeOp, b) (w, s)).map
        (fun r => ext8 (vec b r.1 (cd.encState r.2)) []) := by
  have he : cd.encState (w, s) = cd.selWord s.bad s.msg x σ := by
    simp [Codes.encState, hx, hσ]
  have hes : ∀ s' : GState U Sig, s'.attr = some x → s'.sec = some σ →
      cd.encState (w, s') = cd.selWord s'.bad s'.msg x σ := fun s' h1 h2 => by
    simp [Codes.encState, h1, h2]
  rw [chalH, XProg.law_ifBit, ite_neg' (by simp [vec, he, head_selWord]), XProg.law_ifBlank,
    ite_neg' (by simp [vec, he, Codes.selWord]), he, chalSel,
    law_seq_glue (Prog.law_seq_pure (Prog.law_prim _ _) |>.trans (Prog.law_prim _ _)),
    XProg.law_ifBit]
  cases hm : s.msg with
  | some μ =>
    rw [ite_pos' (by simp [Prim.apply, vec, Codes.selWord, Codes.msgWord]),
      law_glue_pure (law_restoreC _ s.bad (by simp [Prim.apply, vec, Codes.selWord])),
      oracleW_chal_sel_used _ _ _ _ hx hσ hm, PMF.pure_map, he, hm]
    congr 2
    funext j
    fin_cases j <;> simp [Prim.apply, vec, Codes.selWord]
  | none =>
    rw [ite_neg' (by simp [Prim.apply, vec, Codes.selWord, Codes.msgWord]),
      law_testLen _ _ _ _ (by simp [Prim.apply, vec])]
    split_ifs with hb
    · obtain ⟨μ, hμ⟩ := cd.full_msg b (by simpa [Prim.apply, vec] using hb)
      subst hμ
      rw [chalFresh, law_seq_glue (law_parseC _ (U.encAttr x) (cd.sig.enc σ) (cd.len_attr x)
          (by simp [Prim.apply, vec, Codes.selWord, Codes.msgWord]) (by simp [Prim.apply, vec])
          (by simp [Prim.apply, vec])),
        law_seq_glue (Prog.law_seq_pure (Prog.law_prim _ _) |>.trans (Prog.law_prim _ _)),
        law_seq_comp 1 6 _ cs.chalP _ _ (sp.chal σ μ) id (by
          convert cs.law_chal σ μ hOk using 3 <;> simp [Prim.apply, vec]),
        oracleW_chal_sel_fresh _ _ _ _ hx hσ hm, PMF.map_comp, ← PMF.bind_pure_comp]
      congr 1
      funext ct
      rw [law_glue_pure (law_rebuildC _ s.bad (U.encMsg μ) (U.encAttr x) (cd.sig.enc σ)
        (cd.len_msg μ) (cd.len_attr x) (by simp [Prim.apply, vec]) (by simp [Prim.apply, vec])
        (by simp [Prim.apply, vec, Codes.selWord]) (by simp [Prim.apply, vec])
        (by simp [Prim.apply, vec]) (by simp [Prim.apply, vec]))]
      simp only [Function.comp_apply, id]
      rw [hes { s with msg := some μ } hx hσ]
      congr 2
      funext j
      fin_cases j <;> simp [Prim.apply, vec, Codes.selWord, Codes.msgWord]
    · rw [law_glue_pure (law_restoreC _ s.bad (by simp [Prim.apply, vec, Codes.selWord])),
        oracleW_chal_sel_none _ _ _ (cd.decode_msg_none (by simpa [Prim.apply, vec] using hb)),
        PMF.pure_map, he, hm]
      congr 2
      funext j
      fin_cases j <;> simp [Prim.apply, vec, Codes.selWord, Codes.msgWord]

end Chal

end AdvancedEncryption.PE.Generic
