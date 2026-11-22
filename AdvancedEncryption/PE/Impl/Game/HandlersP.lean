import PE.Impl.Game.HandlersCost
import SigabaNeo.Lib.Machines.Inline.PerQuery

/-!
# Handlers with per-query time bounds

The handlers of `PE.Impl.Game.Handlers` feed the whole query to the components `keyP` and
`authP`, so their time bound depends on the query bound `T` through the components' time bounds,
in an arbitrary way. Here the key handler (`keyHP`) first cuts the query at a constant `K₀`
(`cutQ`): when the query is longer than `K₀` it answers the fixed word `kL` without changing the
state (key queries longer than `K₀` are answered by `kL` and never authorized: `LongKeys`), and
otherwise the components only see the cut query, whose syntactic bound is `K₀`.

The selection and challenge handlers are those of `PE.Impl.Game.Handlers`.

## Main results

* `law_handlerProgP`: the handler programs act as the oracle `oracleW sp setupW` on the served
  states;
* `time_handlerProgP`: started with a query of at most `T` bits, every handler program takes at
  most `handlerQ0 cb + handlerQ1 cd K₀ kL * T` steps, where `handlerQ0` and `handlerQ1` do not
  depend on `T` (only on the codes, `K₀`, `kL`, `W` and the components' bounds at `K₀`,
  `CompBoundsP`);
* `handlesP`: the handlers satisfy `SigabaNeo.HandlesP` with `q₀ = handlerQ0 cb`,
  `q₁ = handlerQ1 cd K₀ kL`, for every oracle machine `A`.
-/

namespace AdvancedEncryption.PE.Generic

open SigabaNeo SigabaNeo.Tape Cslib Cslib.Probability

variable {U : Universe} {Sig : Type} {R : ℕ}

/-! ### The programs -/

section Programs

/-- Write the word `u` on the answer tape `1` (blank before). -/
def writeA : List Bool → Prog 8
  | [] => .prim (.copy 0 0)
  | b :: u => .seq (writeA u) (.prim (.cons 1 b))

/-- `U := take K₀ b` (through the answer tape, which keeps `drop K₀ b`). -/
def cutQ (K₀ : ℕ) : Prog 8 := .seq (.prim (.copy 1 0)) (Prog.moveFront K₀ 1 6 7)

/-- A long query: clear the cut and answer `u`. -/
def longK (u : List Bool) : Prog 8 := .seq (.prim (.clear 1)) (.seq (.prim (.clear 6)) (writeA u))

/-- The arguments of `keyP`: `A := S`, `U := take K₀ b`. -/
def keyArgP (K₀ : ℕ) : Prog 8 :=
  .seq (.prim (.clear 6)) (.seq (cutQ K₀) (.seq (.prim (.clear 1)) (.prim (.copy 1 2))))

variable (cd : Codes U Sig)

/-- A short key query on a selected state, the cut query on `U`: the authorization first, then the
key. -/
def keyShortP (K₀ : ℕ) (keyP authP : XProg (R + 2)) : XProg (R + 8) :=
  .seq (glue (parseSel cd))
    (.seq (glue (.prim (.copy 7 5)))
      (.seq (comp 6 7 (by decide) authP)
        (.seq (.ifBit (gt 6) (glue setBad) skipG)
          (.seq (glue (keyArgP K₀))
            (.seq (comp 1 6 (by decide) keyP) (glue (rebuildK cd)))))))

/-- A key query on a selected state: cut the query at `K₀`; a longer query is answered by `kL`. -/
def keySelP (K₀ : ℕ) (kL : List Bool) (keyP authP : XProg (R + 2)) : XProg (R + 8) :=
  .seq (glue (cutQ K₀)) (.ifBlank (gt 1) (keyShortP cd K₀ keyP authP) (glue (longK kL)))

/-- **The handler of the key queries**, with the cut `K₀` and the answer `kL` to long queries. -/
def keyHP (K₀ : ℕ) (kL : List Bool) (keyP authP : XProg (R + 2)) : XProg (R + 8) :=
  .ifBit (gt 2) skipG (.ifBlank (gt 2) skipG (keySelP cd K₀ kL keyP authP))

end Programs

theorem law_writeA : ∀ (u : List Bool) (v : Store 8), v 1 = [] →
    (writeA u).law v = PMF.pure (Function.update v 1 u)
  | [], v, h => by
    rw [writeA, Prog.law_prim, Prog.apply_copy_self, ← h, Function.update_eq_self]
  | b :: u, v, h => by
    rw [writeA, Prog.law_seq_pure (law_writeA u v h), Prog.law_prim]
    simp [Prim.apply]

theorem loopFree_writeA : ∀ u : List Bool, (writeA u).LoopFree
  | [] => trivial
  | _ :: u => ⟨loopFree_writeA u, trivial⟩

theorem wf_writeA : ∀ u : List Bool, (writeA u).WF
  | [] => trivial
  | _ :: u => ⟨wf_writeA u, trivial⟩

theorem pcount_writeA : ∀ u : List Bool, (writeA u).pcount = u.length + 1
  | [] => rfl
  | _ :: u => by simp [writeA, Prog.pcount, pcount_writeA u]

theorem law_cutQ (K₀ : ℕ) (v : Store 8) (h7 : v 7 = []) :
    (cutQ K₀).law v = PMF.pure (Function.update (Function.update v 1 ((v 0).drop K₀)) 6
      (v 6 ++ (v 0).take K₀)) := by
  rw [cutQ, Prog.law_seq_pure (Prog.law_prim _ _),
    Prog.law_moveFront _ (by decide) (by decide) (by decide) _ (by simp [Prim.apply, h7])]
  congr 1
  funext j
  simp only [Prim.apply, Function.update_apply]
  split_ifs <;> simp_all

/-! ### The law -/

section Key

variable {cd : Codes U Sig} {sp : Spec U Sig} {setupW : List Bool → U.Attr → PMF Sig}
  {IW : List Bool → Prop} {Ok : Sig → Prop} (cs : Comps R cd sp setupW IW Ok)

/-- Key queries longer than `K₀` are answered by the fixed word `kL` and never authorized. -/
structure LongKeys (sp : Spec U Sig) (Ok : Sig → Prop) (K₀ : ℕ) (kL : List Bool) : Prop where
  key : ∀ σ C, Ok σ → K₀ < C.length → sp.key σ C = PMF.pure kL
  auth : ∀ C x, K₀ < C.length → sp.auth C x = false

theorem law_keyShortP (K₀ : ℕ) (b : List Bool) (hb : b.length ≤ K₀) (bad : Bool)
    (m : Option U.Msg) (x : U.Attr) (σ : Sig) (hσ : Ok σ) :
    XProg.law (keyShortP cd K₀ cs.keyP cs.authP)
        (ext8 (Function.update (vec b [] (cd.selWord bad m x σ)) 6 b) []) =
      (sp.key σ b).map fun sk =>
        ext8 (vec b sk (cd.selWord (bad || sp.auth b x) m x σ)) [] := by
  have hd : b.drop K₀ = [] := List.drop_eq_nil_of_le hb
  have ht : b.take K₀ = b := List.take_of_length_le hb
  rw [keyShortP, law_seq_glue (law_parseSel _ false bad (cd.msgWord m) (U.encAttr x)
    (cd.sig.enc σ) (cd.length_msgWord m) (cd.len_attr x) (by simp [vec, Codes.selWord])
    (by simp [vec]) (by simp [vec]) (by simp [vec]))]
  rw [law_seq_glue (Prog.law_prim _ _)]
  rw [law_seq_comp_pure 6 7 _ cs.authP _ _ [sp.auth b x] (by
    convert cs.law_auth b x using 3 <;> simp [Prim.apply, vec])]
  rw [law_seq_pure_X (law_setBad _ bad (sp.auth b x) (by simp [Prim.apply, vec])
    (by simp [Prim.apply, vec]))]
  rw [law_seq_glue (P := keyArgP K₀) (by
    rw [keyArgP, Prog.law_seq_pure (Prog.law_prim _ _),
      Prog.law_seq_pure (law_cutQ K₀ _ (by simp [Prim.apply, vec])),
      Prog.law_seq_pure (Prog.law_prim _ _), Prog.law_prim])]
  rw [law_seq_comp 1 6 _ cs.keyP _ _ (sp.key σ b) id (by
    convert cs.law_key σ b hσ using 3 <;> simp [Prim.apply, vec, hd, ht])]
  rw [← PMF.bind_pure_comp]
  congr 1
  funext sk
  rw [law_glue_pure (law_rebuildK _ (bad || sp.auth b x) (cd.msgWord m) (U.encAttr x)
    (cd.sig.enc σ) (cd.length_msgWord m) (cd.len_attr x) (by simp [Prim.apply, vec])
    (by simp [Prim.apply, vec])
    (by simp [Prim.apply, vec])
    (by simp [Prim.apply, vec])
    (by simp [Prim.apply, vec]))]
  simp only [Function.comp_apply, id]
  congr 2
  funext j
  fin_cases j <;> simp [Prim.apply, vec, Codes.selWord]

theorem law_keySelP (K₀ : ℕ) (kL : List Bool) (hlong : LongKeys sp Ok K₀ kL) (b : List Bool)
    (bad : Bool) (m : Option U.Msg) (x : U.Attr) (σ : Sig) (hσ : Ok σ) :
    XProg.law (keySelP cd K₀ kL cs.keyP cs.authP) (ext8 (vec b [] (cd.selWord bad m x σ)) []) =
      (sp.key σ b).map fun sk =>
        ext8 (vec b sk (cd.selWord (bad || sp.auth b x) m x σ)) [] := by
  rw [keySelP, law_seq_glue (law_cutQ K₀ _ (by simp [vec])), XProg.law_ifBlank]
  simp only [ext8_gt, Function.update_apply, show (1 : Fin 8) ≠ 6 by decide, ite_true, ite_false]
  by_cases hb : b.length ≤ K₀
  · have hd : b.drop K₀ = [] := List.drop_eq_nil_of_le hb
    have ht : b.take K₀ = b := List.take_of_length_le hb
    simp only [vec, ite_true, hd, ite_true]
    rw [← law_keyShortP cs K₀ b hb bad m x σ hσ]
    congr 2
    funext j
    simp only [Function.update_apply, vec]
    split_ifs <;> simp_all
  · have hd : b.drop K₀ ≠ [] := by
      intro h; rw [List.drop_eq_nil_iff] at h; omega
    simp only [vec, ite_true, hd, ite_false]
    rw [hlong.key σ b hσ (by omega), hlong.auth b x (by omega), Bool.or_false, PMF.pure_map,
      law_glue_pure (P := longK kL) (by
        rw [longK, Prog.law_seq_pure (Prog.law_prim _ _), Prog.law_seq_pure (Prog.law_prim _ _),
          law_writeA kL _ (by simp [Prim.apply])])]
    congr 2
    funext j
    fin_cases j <;> simp [Prim.apply, vec]

theorem law_keyHP_init (K₀ : ℕ) (kL : List Bool) (w b : List Bool) (hh : w.head? ≠ some false) :
    XProg.law (keyHP cd K₀ kL cs.keyP cs.authP) (ext8 (vec b [] w) []) =
      (oracleW sp setupW (keyGenOp, b) (w, {})).map
        (fun r => ext8 (vec b r.1 (cd.encState r.2)) []) := by
  rw [oracleW_key_init, PMF.pure_map, keyHP, XProg.law_ifBit]
  split_ifs with h1
  · exact law_skipG _
  · rw [XProg.law_ifBlank, ite_pos' (by simpa [vec] using eq_nil_of_head hh (by simpa [vec] using h1))]
    exact law_skipG _

theorem law_keyHP_sel (K₀ : ℕ) (kL : List Bool) (hlong : LongKeys sp Ok K₀ kL) (w b : List Bool)
    {s : GState U Sig} {x : U.Attr} {σ : Sig}
    (hx : s.attr = some x) (hσ : s.sec = some σ) (hOk : Ok σ) :
    XProg.law (keyHP cd K₀ kL cs.keyP cs.authP) (ext8 (vec b [] (cd.encState (w, s))) []) =
      (oracleW sp setupW (keyGenOp, b) (w, s)).map
        (fun r => ext8 (vec b r.1 (cd.encState r.2)) []) := by
  have he : cd.encState (w, s) = cd.selWord s.bad s.msg x σ := by
    simp [Codes.encState, hx, hσ]
  rw [keyHP, XProg.law_ifBit, ite_neg' (by simp [vec, he, head_selWord]), XProg.law_ifBlank,
    ite_neg' (by simp [vec, he, Codes.selWord]), he,
    law_keySelP cs K₀ kL hlong b s.bad s.msg x σ hOk,
    oracleW_key_sel _ _ _ _ hx hσ, PMF.map_comp]
  congr 1
  funext sk
  simp [Codes.encState, hx, hσ]

end Key

/-! ### The handlers -/

variable {cd : Codes U Sig} {sp : Spec U Sig} {setupW : List Bool → U.Attr → PMF Sig}
  {IW : List Bool → Prop} {Ok : Sig → Prop}

variable (cd) in
/-- The handler program of a channel, with the cut `K₀` of the key queries. -/
def handlerProgP (cs : Comps R cd sp setupW IW Ok) (K₀ : ℕ) (kL : List Bool) (o : Fin 3) :
    XProg (R + 8) :=
  if o = selectOp then selH cd cs.setupP cs.pubP
  else if o = keyGenOp then keyHP cd K₀ kL cs.keyP cs.authP else chalH cd cs.chalP

variable (cd) in
/-- **The handlers with per-query time bounds**: the compiled programs. Their clock (`time`) is
the one for queries of `0` bits; the halting bound of a query `b` is that of the per-tape bounds
for `|b|` (`handlesP`). -/
noncomputable def handlersP (cs : Comps R cd sp setupW IW Ok) (K₀ : ℕ) (kL : List Bool) (W : ℕ) :
    Fin 3 → Routine (R + 5 + 3) :=
  fun o => Routine.ofXProg (handlerProgP cd cs K₀ kL o) (startBound cd 0 W)

section Main

variable (cs : Comps R cd sp setupW IW Ok) (K₀ : ℕ) (kL : List Bool)

theorem handlerProgP_sel : handlerProgP cd cs K₀ kL selectOp = selH cd cs.setupP cs.pubP := by
  simp [handlerProgP]

theorem handlerProgP_key :
    handlerProgP cd cs K₀ kL keyGenOp = keyHP cd K₀ kL cs.keyP cs.authP := by
  simp [handlerProgP, selectOp, keyGenOp]

theorem handlerProgP_chal : handlerProgP cd cs K₀ kL challengeOp = chalH cd cs.chalP := by
  simp [handlerProgP, selectOp, keyGenOp, challengeOp]

theorem wf_handlerProgP (o : Fin 3) : (handlerProgP cd cs K₀ kL o).WF := by
  rcases fin3_cases o with rfl | rfl | rfl
  · rw [handlerProgP_sel, ← handlerProg_sel cs]; exact wf_handlerProg cs _
  · rw [handlerProgP_key]
    have hps : (parseSel cd).WF :=
      ⟨trivial, trivial, Prog.wf_moveFront _ _ _ _, Prog.wf_moveFront _ _ _ _⟩
    have hrb : (rebuildK cd).WF :=
      ⟨trivial, Prog.wf_prependN _ _ _ _ _, Prog.wf_prependN _ _ _ _ _, trivial, trivial, trivial⟩
    simp only [keyHP, keySelP, keyShortP, skipG, glue, comp, cutQ, keyArgP, longK,
      setBad, XProg.WF, Prog.WF, true_and, and_true, hps, hrb, Prog.wf_moveFront, wf_writeA,
      cs.wf_auth, cs.wf_key, and_self]
  · rw [handlerProgP_chal, ← handlerProg_chal cs]; exact wf_handlerProg cs _

/-- **The handler programs act as the oracle** on the served states. -/
theorem law_handlerProgP (hlong : LongKeys sp Ok K₀ kL) {W : ℕ} (o : Fin 3) (b : List Bool)
    (st : List Bool × GState U Sig) (h : InvS IW W Ok st) :
    XProg.law (handlerProgP cd cs K₀ kL o) (ext8 (vec b [] (cd.encState st)) []) =
      (oracleW sp setupW (o, b) st).map (fun r => ext8 (vec b r.1 (cd.encState r.2)) []) := by
  rcases fin3_cases o with rfl | rfl | rfl
  · rw [handlerProgP_sel, ← handlerProg_sel cs]; exact law_handlerProg cs _ b st h
  · rw [handlerProgP_key]
    obtain ⟨w, s⟩ := st
    rcases encState_of_inv (cd := cd) h with ⟨h0, he⟩ | ⟨x, σ, hx, hσ, hOk, -⟩
    · simp only at h0 he
      subst h0
      rw [he]
      exact law_keyHP_init cs K₀ kL w b h.2.2.1
    · exact law_keyHP_sel cs K₀ kL hlong w b hx hσ hOk
  · rw [handlerProgP_chal, ← handlerProg_chal cs]; exact law_handlerProg cs _ b st h

end Main

end AdvancedEncryption.PE.Generic
