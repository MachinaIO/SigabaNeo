import PE.Impl.ExpLUT.Prog.KeyPublicMachine
import PE.Impl.ExpLUT.Prog.KeyDecompose

/-! Target-vector generation from the public key's encoded d field. -/
namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM length_encRM)

/-- The length carried by a fixed codec, without encoding any data. -/
def codecSize {α : Type} {n : ℕ} (_e : FixedEnc α n) : ℕ := n

noncomputable def mpkDOffset (D : Dims) : ℕ := codecSize (mpkEnc D) - 2 * (D.N * D.K)

theorem vecE_fin2 (D : Dims) (d : Fin 2 → Rg D) :
    (vecE D (Fin 2)).enc d = encRM D.N D.K (d 0) ++ encRM D.N D.K (d 1) := by
  simp [vecE, FixedEnc.fun, FixedEnc.encList, enum_fin2, rEnc]

/-- The final public-key field has a data-independent offset. -/
theorem mpkEnc_dSuffix (D : Dims) (mpk : MPKt D) :
    ∃ pre, pre.length = mpkDOffset D ∧
      (mpkEnc D).enc mpk = pre ++ (vecE D (Fin 2)).enc mpk.d := by
  let pre := (matE D (Fin 2) (BCol (Wb D) D.K)).enc mpk.B ++
    (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc mpk.H ++
    (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc mpk.a ++
    (matE D (Fin 2) (Col D.K)).enc mpk.A0 ++
    (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K)
      (matE D (Fin 2) (Col D.K)))).enc mpk.Ain ++
    (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K)
      (matE D (Fin 2) (Col D.K)))).enc mpk.Aaut
  have he : (mpkEnc D).enc mpk = pre ++ (vecE D (Fin 2)).enc mpk.d := by
    simp only [mpkEnc, FixedEnc.comap, FixedEnc.prod, pre, List.append_assoc]
  refine ⟨pre, ?_, he⟩
  have hl : ((mpkEnc D).enc mpk).length = codecSize (mpkEnc D) := (mpkEnc D).length mpk
  rw [he, List.length_append, vecE_fin2] at hl
  simp only [List.length_append, length_encRM] at hl
  unfold mpkDOffset
  omega

/-- Read d0 into register3, from an MPK saved on14. -/
noncomputable def targetHeadC (D : Dims) : Code :=
  .seq (.cp 0 14) <| .seq (natC 2 rB1 (mpkDOffset D)) <|
  .seq (.drop 0 2) <| .seq (.cp 3 rZ) (.mvR 3 0)

theorem wf_targetHeadC (D : Dims) : (targetHeadC D).WFc :=
  ⟨trivial, natC_wfc _ _ _, trivial, trivial, trivial⟩

theorem targetHeadC_frame (D : Dims) (r : Fin 64)
    (h0 : r ≠ 0) (h2 : r ≠ 2) (h3 : r ≠ 3) : (targetHeadC D).writes r = false := by
  simp [targetHeadC, Code.writes, natC_writes _ _ _ r h2, Ne.symm h0, Ne.symm h3]

theorem exec_targetHeadC (D : Dims) (mpk : MPKt D) (w : St)
    (hm : w 14 = (mpkEnc D).enc mpk) (hb : w rB1 = [false])
    (hz : w rZ = encRM D.N D.K 0) :
    exec D.N D.K (targetHeadC D) w 3 = encRM D.N D.K (mpk.d 0) := by
  obtain ⟨pre, hl, he⟩ := mpkEnc_dSuffix D mpk
  rw [targetHeadC, exec_seq, exec_seq,
    exec_natC _ _ (by decide) _ _ (by simpa using hb)]
  vm_simp
  simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, hm, he, hz,
    List.length_replicate, ← hl, List.drop_left, vecE_fin2]
  simp

/-- A distinguished first coordinate followed by a constant tail. -/
theorem enum_head_tail {α : Type} (n : ℕ) (hn : 0 < n) (a z : α) :
    (Enum.list (α := Fin n)).map (fun i ↦ if i.val = 0 then a else z) =
      a :: List.replicate (n - 1) z := by
  change (List.finRange n).map _ = _
  apply List.ext_getElem
  · simp only [List.length_map, List.length_finRange, List.length_cons, List.length_replicate]
    omega
  · intro j hj hj'
    simp only [List.getElem_map, List.getElem_finRange]
    cases j with
    | zero => simp
    | succ j => simp

/-- The target is d0 in row zero and zero in every subsequent row. -/
theorem keyTarget_list (D : Dims) (mpk : MPKt D) :
    Enum.list.map (keyTarget mpk) = mpk.d 0 :: List.replicate ((setting D).E.W - 1) 0 := by
  have he : keyTarget mpk = fun i : Fin (setting D).E.W ↦
      if i.val = 0 then mpk.d 0 else 0 := by
    funext i
    simp only [keyTarget, Setting.row0, Fin.ext_iff]
  exact (congrArg (fun f ↦ Enum.list.map f) he).trans
    (enum_head_tail _ (setting D).E.W_pos _ _)

/-- Construct the complete target queue on rQa. -/
noncomputable def targetC (D : Dims) : Code := .seq (targetHeadC D) <|
  .seq (.cp rQa 3) <|
  .seq (natC 2 rB1 (((setting D).E.W - 1) * (D.N * D.K))) (.app rQa 2)

theorem wf_targetC (D : Dims) : (targetC D).WFc :=
  ⟨wf_targetHeadC _, trivial, natC_wfc _ _ _, trivial⟩

theorem exec_targetC (D : Dims) (mpk : MPKt D) (w : St)
    (hm : w 14 = (mpkEnc D).enc mpk) (hb : w rB1 = [false])
    (hz : w rZ = encRM D.N D.K 0) :
    exec D.N D.K (targetC D) w rQa = encL D.N D.K (Enum.list.map (keyTarget mpk)) := by
  have hh := exec_targetHeadC D mpk w hm hb hz
  have hbit : exec D.N D.K (targetHeadC D) w rB1 = [false] := by
    rw [exec_writes _ _ _ (targetHeadC_frame D rB1 (by decide) (by decide) (by decide)), hb]
  rw [targetC, exec_seq, exec_seq, exec_seq,
    exec_natC _ _ (by decide) _ _ (by simpa using hbit)]
  simp only [exec_cp, exec_app, Function.update_self,
    Function.update_of_ne (by decide : rQa ≠ 2), hh,
    keyTarget_list, encL_cons, encL_zeros]

theorem publicRowsAppendC_frame (D : Dims) (r : Fin 64)
    (hr : r = 8 ∨ r = 9 ∨ r = 14 ∨ r = rB1 ∨ r = rZ) :
    ∀ is, (publicRowsAppendC D is).writes r = false
  | [] => rfl
  | i :: is => by
    have hf := publicRowC_frame D i r (by
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> tauto)
    have hn : r ≠ 15 := by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    simp [publicRowsAppendC, Code.writes, hf, publicRowsAppendC_frame D r hr is, Ne.symm hn]

theorem publicRowsC_frame (D : Dims) (r : Fin 64)
    (hr : r = 8 ∨ r = 9 ∨ r = 14 ∨ r = rB1 ∨ r = rZ) :
    (publicRowsC D).writes r = false := by
  have hn : r ≠ 15 := by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [publicRowsC, Code.writes, Bool.or_eq_false_iff]
  exact ⟨by simp [Ne.symm hn], publicRowsAppendC_frame D r hr _⟩

theorem targetC_frame (D : Dims) (r : Fin 64)
    (h0 : r ≠ 0) (h2 : r ≠ 2) (h3 : r ≠ 3) (hA : r ≠ rQa) :
    (targetC D).writes r = false := by
  simp [targetC, Code.writes, targetHeadC_frame D r h0 h2 h3,
    natC_writes _ _ _ r h2, Ne.symm hA]

/-- Evaluate the public map, form its difference from the target, and decompose all rows. -/
noncomputable def keyDigitsC (D : Dims) : Code :=
  .seq (publicRowsC D) <| .seq (targetC D) <| .seq (.cp rQb 15) <|
  .seq (natC rQc rB1 (setting D).E.W) <| .seq (natC rQk rB1 D.K) decRowsC

theorem wf_keyDigitsC (D : Dims) : (keyDigitsC D).WFc :=
  ⟨wf_publicRowsC _, wf_targetC _, trivial, natC_wfc _ _ _, natC_wfc _ _ _, wf_decRowsC⟩

theorem enum_map_ofFn {α : Type} {n : ℕ} (f : Fin n → α) :
    Enum.list.map f = List.ofFn f := by
  change (List.finRange n).map f = _
  apply List.ext_getElem <;> simp

/-- Product enumeration agrees with row-major, then digit-major gadget output. -/
theorem enum_gadget_order {α : Type} {n k : ℕ} (f : Fin n × Fin k → α) :
    Enum.list.map f = (List.ofFn (fun i : Fin n ↦
      List.ofFn (fun c : Fin k ↦ f (i, c)))).flatten := by
  change ((Enum.list (α := Fin n)).product (Enum.list (α := Fin k))).map f = _
  simp only [List.product, List.map_flatMap, List.map_map, Function.comp_def]
  simp only [enum_map_ofFn, List.flatMap_def]

/-- Actual gadget coordinates of target minus public map, computed from the encoded inputs. -/
theorem exec_keyDigitsC (D : Dims) (hK : 2 ≤ D.K) (mpk : MPKt D) (F : BP Pos)
    (p : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D) (w : St)
    (hM : w 14 = (mpkEnc D).enc mpk)
    (hA : w 8 = encL D.N D.K (matL (keyPK (helperMap D) mpk F)))
    (hP : w 9 = encL D.N D.K (Enum.list.map p))
    (h1 : w rB1 = [false]) (hZ : w rZ = encRM D.N D.K 0) :
    exec D.N D.K (keyDigitsC D) w rDq = encL D.N D.K
      (Enum.list.map (gadDec (S := setting D)
        (keyTarget mpk - pubShort (helperMap D) mpk F p))) := by
  let v := exec D.N D.K (publicRowsC D) w
  have vv : v 15 = encL D.N D.K (Enum.list.map (pubShort (helperMap D) mpk F p)) :=
    exec_publicRowsC D hK mpk F p w hM hA hP h1 hZ
  have keep : ∀ r : Fin 64, (r = 8 ∨ r = 9 ∨ r = 14 ∨ r = rB1 ∨ r = rZ) → v r = w r :=
    fun r hr ↦ exec_writes _ _ _ (publicRowsC_frame D r hr)
  have vb : v rB1 = [false] := (keep _ (by tauto)).trans h1
  have vz : v rZ = encRM D.N D.K 0 := (keep _ (by tauto)).trans hZ
  let t := exec D.N D.K (targetC D) v
  have tu : t rQa = encL D.N D.K (Enum.list.map (keyTarget mpk)) :=
    exec_targetC D mpk v ((keep _ (by tauto)).trans hM) vb vz
  have tf : ∀ r : Fin 64, r ≠ 0 → r ≠ 2 → r ≠ 3 → r ≠ rQa → t r = v r :=
    fun r h0 h2 h3 ha ↦ exec_writes _ _ _ (targetC_frame D r h0 h2 h3 ha)
  have tv : t 15 = encL D.N D.K (Enum.list.map (pubShort (helperMap D) mpk F p)) :=
    (tf _ (by decide) (by decide) (by decide) (by decide)).trans vv
  have tb : t rB1 = [false] := (tf _ (by decide) (by decide) (by decide) (by decide)).trans vb
  have tz : t rZ = encRM D.N D.K 0 :=
    (tf _ (by decide) (by decide) (by decide) (by decide)).trans vz
  let rows := List.ofFn (fun i : Fin (setting D).E.W ↦
    (keyTarget mpk i, pubShort (helperMap D) mpk F p i))
  change exec D.N D.K decRowsC (exec D.N D.K
    (.seq (.cp rQb 15) (.seq (natC rQc rB1 (setting D).E.W) (natC rQk rB1 D.K))) t) rDq = _
  simp only [exec_seq]
  rw [exec_natC rQc rB1 (by decide) _ _ (by simpa using tb)]
  rw [exec_natC rQk rB1 (by decide) _ _ (by simpa using tb)]
  have h := exec_decRowsC D.K_pos
    (Function.update (Function.update (exec D.N D.K (.cp rQb 15) t)
      rQc (List.replicate (setting D).E.W false)) rQk (List.replicate D.K false)) rows
    (by simpa only [Function.update_of_ne (by decide : rQa ≠ rQk),
      Function.update_of_ne (by decide : rQa ≠ rQc), exec_cp,
      Function.update_of_ne (by decide : rQa ≠ rQb), rows, List.map_ofFn, enum_map_ofFn, Function.comp_def] using tu)
    (by simpa only [Function.update_of_ne (by decide : rQb ≠ rQk),
      Function.update_of_ne (by decide : rQb ≠ rQc), exec_cp, Function.update_self,
      rows, List.map_ofFn, enum_map_ofFn, Function.comp_def] using tv)
    (by simp [rows]) (by simp) (by simpa using tb) (by simpa using tz)
  rw [rows_digits_gadDec] at h
  exact h.2.2.trans (congrArg (encL D.N D.K) (enum_gadget_order _).symm)

end AdvancedEncryption.ExpLUT.Prog
