import PE.Impl.ExpLUT.Prog.KeyEvalCodec
/-! Executable fixed-field extraction for the EvalPK input registers. -/
set_option backward.isDefEq.respectTransparency false

namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib

/-- Read a fixed slice of a saved source through scratch29/30. -/
def readFieldC (src dst : Fin 64) (off len : ℕ) : Code :=
  .seq (.cp 29 src) <| .seq (natC 30 rB1 off) <| .seq (.drop 29 30) <|
  .seq (natC 30 rB1 len) (takeC dst 29 30)

theorem wf_readFieldC (src dst : Fin 64) (off len : ℕ) :
    (readFieldC src dst off len).WFc :=
  ⟨trivial, natC_wfc _ _ _, trivial, natC_wfc _ _ _, trivial, trivial⟩

theorem readFieldC_frame (src dst : Fin 64) (off len : ℕ) (r : Fin 64)
    (h29 : r ≠ 29) (h30 : r ≠ 30) (hd : r ≠ dst) :
    (readFieldC src dst off len).writes r = false := by
  simp [readFieldC, takeC, Code.writes, natC_writes _ _ _ r h30,
    Ne.symm h29, Ne.symm hd]

theorem exec_readFieldC {N K : ℕ} (src dst : Fin 64) (hd29 : dst ≠ 29) (hd30 : dst ≠ 30)
    (pre field tail : List Bool) (w : St) (hs : w src = pre ++ field ++ tail)
    (hb : w rB1 = [false]) :
    exec N K (readFieldC src dst pre.length field.length) w dst = field := by
  rw [readFieldC, exec_seq, exec_seq, exec_natC _ _ (by decide) _ _ (by simpa using hb),
    exec_seq, exec_seq, exec_natC _ _ (by decide) _ _ (by simpa using hb)]
  rw [exec_takeC _ _ _ (by tauto) _ field.length (by simp)]
  simp only [Function.update_self, exec_cp, exec_drop, Fin.reduceEq, ↓reduceIte,
    Function.update_apply, List.length_replicate, hs]
  rw [List.append_assoc, List.drop_left, takeD_eq_take (by simp)]
  simp

/-- Read block j from a concatenation whose block lengths are ns. -/
def readBlockC (src dst : Fin 64) (ns : List ℕ) (j : ℕ) : Code :=
  readFieldC src dst (ns.take j).sum (ns.getD j 0)

theorem exec_readBlockC {N K : ℕ} (src dst : Fin 64) (hd29 : dst ≠ 29) (hd30 : dst ≠ 30)
    (blocks : List (List Bool)) (j : ℕ) (hj : j < blocks.length) (w : St)
    (hs : w src = blocks.flatten) (hb : w rB1 = [false]) :
    exec N K (readBlockC src dst (blocks.map List.length) j) w dst = blocks[j] := by
  have he : blocks.flatten = (blocks.take j).flatten ++ blocks[j] ++ (blocks.drop (j + 1)).flatten := by
    conv_lhs => rw [← List.take_append_drop j blocks, List.flatten_append]
    rw [drop_cons_getElem blocks hj, List.flatten_cons, List.append_assoc]
  have hl : (blocks.take j).flatten.length = ((blocks.map List.length).take j).sum := by
    rw [List.length_flatten, List.map_take]
  have hj' : (blocks.map List.length).getD j 0 = blocks[j].length := by
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  rw [readBlockC, ← hl, hj']
  exact exec_readFieldC src dst hd29 hd30 _ _ _ w (hs.trans he) hb

/-- Public-key fields in their wire order. -/
def publicFields (D : Dims) (mpk : MPKt D) : List (List Bool) :=
  [(matE D (Fin 2) (BCol (Wb D) D.K)).enc mpk.B,
   (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc mpk.H,
   (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc mpk.a,
   (matE D (Fin 2) (Col D.K)).enc mpk.A0,
   (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K)
     (matE D (Fin 2) (Col D.K)))).enc mpk.Ain,
   (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K)
     (matE D (Fin 2) (Col D.K)))).enc mpk.Aaut,
   (vecE D (Fin 2)).enc mpk.d]

noncomputable def publicFieldLengths (D : Dims) : List ℕ :=
  [codecSize (matE D (Fin 2) (BCol (Wb D) D.K)),
   codecSize (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))),
   codecSize (FixedEnc.fun (α := Pos) (vecE D (Col D.K))),
   codecSize (matE D (Fin 2) (Col D.K)),
   codecSize (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K)
     (matE D (Fin 2) (Col D.K)))),
   codecSize (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K)
     (matE D (Fin 2) (Col D.K)))), codecSize (vecE D (Fin 2))]

theorem publicFields_lengths (D : Dims) (mpk : MPKt D) :
    (publicFields D mpk).map List.length = publicFieldLengths D := by
  simp only [publicFields, publicFieldLengths, List.map_cons, List.map_nil, FixedEnc.length, codecSize]

theorem publicFields_flatten (D : Dims) (mpk : MPKt D) :
    (publicFields D mpk).flatten = (mpkEnc D).enc mpk := by
  simp only [publicFields, List.flatten_cons, List.flatten_nil, List.append_nil,
    mpkEnc, FixedEnc.comap, FixedEnc.prod]

/-- Read a public-key field while preserving the saved MPK on17. -/
noncomputable def readPublicFieldC (D : Dims) (dst : Fin 64) (j : ℕ) : Code :=
  readBlockC 17 dst (publicFieldLengths D) j

theorem exec_readPublicFieldC (D : Dims) (mpk : MPKt D) (dst : Fin 64)
    (hd29 : dst ≠ 29) (hd30 : dst ≠ 30) (j : ℕ) (hj : j < 7) (w : St)
    (hs : w 17 = (mpkEnc D).enc mpk) (hb : w rB1 = [false]) :
    exec D.N D.K (readPublicFieldC D dst j) w dst = (publicFields D mpk)[j]'(by simpa [publicFields] using hj) := by
  rw [readPublicFieldC, ← publicFields_lengths D mpk]
  exact exec_readBlockC 17 dst hd29 hd30 (publicFields D mpk) j
    (by simpa [publicFields] using hj) w (hs.trans (publicFields_flatten D mpk).symm) hb

/-- Load H2, A04, Ain0, and Aaut1 from the saved MPK17. -/
noncomputable def evalFieldsC (D : Dims) : Code :=
  .seq (readPublicFieldC D 2 1) <| .seq (readPublicFieldC D 4 3) <|
  .seq (readPublicFieldC D 0 4) (readPublicFieldC D 1 5)

theorem wf_evalFieldsC (D : Dims) : (evalFieldsC D).WFc :=
  ⟨wf_readFieldC _ _ _ _, wf_readFieldC _ _ _ _,
    wf_readFieldC _ _ _ _, wf_readFieldC _ _ _ _⟩

theorem readPublicFieldC_frame (D : Dims) (dst : Fin 64) (j : ℕ) (r : Fin 64)
    (h29 : r ≠ 29) (h30 : r ≠ 30) (hd : r ≠ dst) :
    (readPublicFieldC D dst j).writes r = false :=
  readFieldC_frame _ _ _ _ _ h29 h30 hd

theorem evalFieldsC_frame (D : Dims) (r : Fin 64)
    (h0 : r ≠ 0) (h1 : r ≠ 1) (h2 : r ≠ 2) (h4 : r ≠ 4)
    (h29 : r ≠ 29) (h30 : r ≠ 30) :
    (evalFieldsC D).writes r = false := by
  simp only [evalFieldsC, Code.writes,
    readPublicFieldC_frame D 2 1 r h29 h30 h2,
    readPublicFieldC_frame D 4 3 r h29 h30 h4,
    readPublicFieldC_frame D 0 4 r h29 h30 h0,
    readPublicFieldC_frame D 1 5 r h29 h30 h1, Bool.or_self]

/-- All four evaluator fields are loaded without modifying the saved public key. -/
theorem exec_evalFieldsC (D : Dims) (mpk : MPKt D) (w : St)
    (hs : w 17 = (mpkEnc D).enc mpk) (hb : w rB1 = [false]) :
    let v := exec D.N D.K (evalFieldsC D) w
    v 2 = (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc mpk.H ∧
    v 4 = (matE D (Fin 2) (Col D.K)).enc mpk.A0 ∧
    v 0 = (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K)
      (matE D (Fin 2) (Col D.K)))).enc mpk.Ain ∧
    v 1 = (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K)
      (matE D (Fin 2) (Col D.K)))).enc mpk.Aaut := by
  let w1 := exec D.N D.K (readPublicFieldC D 2 1) w
  have f1 (r : Fin 64) (h29 : r ≠ 29) (h30 : r ≠ 30) (hd : r ≠ 2) :
      w1 r = w r := exec_writes _ _ _
    (readPublicFieldC_frame D 2 1 r h29 h30 hd)
  have s1 : w1 17 = (mpkEnc D).enc mpk :=
    (f1 17 (by decide) (by decide) (by decide)).trans hs
  have b1 : w1 rB1 = [false] :=
    (f1 rB1 (by decide) (by decide) (by decide)).trans hb
  have e1 := exec_readPublicFieldC D mpk 2 (by decide) (by decide) 1
    (by decide) w hs hb
  let w2 := exec D.N D.K (readPublicFieldC D 4 3) w1
  have f2 (r : Fin 64) (h29 : r ≠ 29) (h30 : r ≠ 30) (hd : r ≠ 4) :
      w2 r = w1 r := exec_writes _ _ _
    (readPublicFieldC_frame D 4 3 r h29 h30 hd)
  have s2 : w2 17 = (mpkEnc D).enc mpk :=
    (f2 17 (by decide) (by decide) (by decide)).trans s1
  have b2 : w2 rB1 = [false] :=
    (f2 rB1 (by decide) (by decide) (by decide)).trans b1
  have e2 := exec_readPublicFieldC D mpk 4 (by decide) (by decide) 3
    (by decide) w1 s1 b1
  let w3 := exec D.N D.K (readPublicFieldC D 0 4) w2
  have f3 (r : Fin 64) (h29 : r ≠ 29) (h30 : r ≠ 30) (hd : r ≠ 0) :
      w3 r = w2 r := exec_writes _ _ _
    (readPublicFieldC_frame D 0 4 r h29 h30 hd)
  have s3 : w3 17 = (mpkEnc D).enc mpk :=
    (f3 17 (by decide) (by decide) (by decide)).trans s2
  have b3 : w3 rB1 = [false] :=
    (f3 rB1 (by decide) (by decide) (by decide)).trans b2
  have e3 := exec_readPublicFieldC D mpk 0 (by decide) (by decide) 4
    (by decide) w2 s2 b2
  let w4 := exec D.N D.K (readPublicFieldC D 1 5) w3
  have f4 (r : Fin 64) (h29 : r ≠ 29) (h30 : r ≠ 30) (hd : r ≠ 1) :
      w4 r = w3 r := exec_writes _ _ _
    (readPublicFieldC_frame D 1 5 r h29 h30 hd)
  have s4 : w4 17 = (mpkEnc D).enc mpk :=
    (f4 17 (by decide) (by decide) (by decide)).trans s3
  have b4 : w4 rB1 = [false] :=
    (f4 rB1 (by decide) (by decide) (by decide)).trans b3
  have e4 := exec_readPublicFieldC D mpk 1 (by decide) (by decide) 5
    (by decide) w3 s3 b3
  change w4 2 = _ ∧ w4 4 = _ ∧ w4 0 = _ ∧ w4 1 = _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [f4 2 (by decide) (by decide) (by decide), f3 2 (by decide) (by decide) (by decide), f2 2 (by decide) (by decide) (by decide)]
    exact e1
  · rw [f4 4 (by decide) (by decide) (by decide), f3 4 (by decide) (by decide) (by decide)]
    exact e2
  · rw [f4 0 (by decide) (by decide) (by decide)]
    exact e3
  · exact e4

end AdvancedEncryption.ExpLUT.Prog
