import PE.Impl.ExpLUT.Prog.KeyCorrection

/-! Composition of gadget decomposition and correction into a complete key proposal. -/
namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)

theorem publicRowC_preserves_trapdoor (D : Dims) (i : Fin (setting D).E.W) :
    (publicRowC D i).writes 16 = false := by
  have hp := positiveCoeffC_frame D i 16 (by decide)
  have hn := negativeReadyC_frame D.N D.K (Enum.list (α := Jh D)).length 16 (by decide)
  have hg (js : List ℕ) := gatherC_preserves D.N D.K js 16
    (by decide) (by decide) (by decide) (by decide)
  simp only [publicRowC, saveQueueC, Code.writes, hp, hn, positiveGatherC,
    negativeGatherC, hg, rowCountsC, natC_writes rQc rB1 _ 16 (by decide),
    natC_writes 12 rB1 _ 16 (by decide), signedDotC, ipC, ipBody]
  decide

theorem publicRowsC_preserves_trapdoor (D : Dims) : (publicRowsC D).writes 16 = false := by
  have h : ∀ qs, (publicRowsAppendC D qs).writes 16 = false := by
    intro qs
    induction qs with
    | nil => rfl
    | cons i qs ih => simp [publicRowsAppendC, Code.writes, publicRowC_preserves_trapdoor, ih]
  simp only [publicRowsC, Code.writes, Bool.or_eq_false_iff]
  exact ⟨by decide, h _⟩

/-- Gadget generation keeps the sampled candidate, trapdoor and constant templates. -/
theorem keyDigitsC_frame (D : Dims) (r : Fin 64)
    (hr : r = 9 ∨ r = 16 ∨ r = rB1 ∨ r = rZ) : (keyDigitsC D).writes r = false := by
  have hp : (publicRowsC D).writes r = false := by
    rcases hr with rfl | rfl | rfl | rfl
    · exact publicRowsC_frame D 9 (by tauto)
    · exact publicRowsC_preserves_trapdoor D
    · exact publicRowsC_frame D rB1 (by tauto)
    · exact publicRowsC_frame D rZ (by tauto)
  have ht := targetC_frame D r
    (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
    (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
    (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
    (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
  have hc := natC_writes rQc rB1 (setting D).E.W r
    (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
  have hk := natC_writes rQk rB1 D.K r
    (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
  simp only [keyDigitsC, Code.writes, hp, ht, hc, hk, decRowsC, decRowBodyC,
    decRowLoadC, decomposeC, digQC, digQBody]
  rcases hr with rfl | rfl | rfl | rfl <;> decide

theorem correctionC_frame (D : Dims) (r : Fin 64)
    (hr : r = 9 ∨ r = 16 ∨ r = 17 ∨ r = rB1 ∨ r = rZ) :
    (correctionC D).writes r = false := by
  have hn : r ≠ 18 := by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  have h : ∀ qs, (correctionAppendC D qs).writes r = false := by
    intro qs
    induction qs with
    | nil => rfl
    | cons q qs ih =>
      have hc := correctionCoordC_frame D q r (by
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> tauto)
      simp [correctionAppendC, Code.writes, hc, ih, Ne.symm hn]
  simp only [correctionC, Code.writes, Bool.or_eq_false_iff]
  exact ⟨by simp [Ne.symm hn], h _⟩

/-- Gadget coordinates on17 and corrected short coordinates on18. -/
noncomputable def proposalC (D : Dims) : Code :=
  .seq (keyDigitsC D) (.seq (.cp 17 rDq) (correctionC D))

theorem wf_proposalC (D : Dims) : (proposalC D).WFc :=
  ⟨wf_keyDigitsC _, trivial, wf_correctionC _⟩

theorem exec_proposalC (D : Dims) (hK : 2 ≤ D.K) (mpk : MPKt D) (F : BP Pos)
    (T : Matrix (Wb D) (Fin D.K) (Rg D))
    (p : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D) (w : St)
    (hM : w 14 = (mpkEnc D).enc mpk)
    (hA : w 8 = encL D.N D.K (matL (keyPK (helperMap D) mpk F)))
    (hT : w 16 = (matE D (Wb D) (Fin D.K)).enc T)
    (hP : w 9 = encL D.N D.K (Enum.list.map p))
    (h1 : w rB1 = [false]) (hZ : w rZ = encRM D.N D.K 0) :
    let z := gadDec (S := setting D) (keyTarget mpk - pubShort (helperMap D) mpk F p)
    let x := p - realTrap (S := setting D) (J := Jh D) T z
    exec D.N D.K (proposalC D) w 17 = encL D.N D.K (Enum.list.map z) ∧
    exec D.N D.K (proposalC D) w 18 = encL D.N D.K (Enum.list.map x) := by
  let z := gadDec (S := setting D) (keyTarget mpk - pubShort (helperMap D) mpk F p)
  let v := exec D.N D.K (keyDigitsC D) w
  have hv : v rDq = encL D.N D.K (Enum.list.map z) :=
    exec_keyDigitsC D hK mpk F p w hM hA hP h1 hZ
  have keep : ∀ r : Fin 64, (r = 9 ∨ r = 16 ∨ r = rB1 ∨ r = rZ) → v r = w r :=
    fun r hr ↦ exec_writes _ _ _ (keyDigitsC_frame D r hr)
  let u := exec D.N D.K (.cp 17 rDq) v
  have uz : u 17 = encL D.N D.K (Enum.list.map z) := hv
  have ux := exec_correctionC D T p z u
    (by simpa [u] using (keep 16 (by tauto)).trans hT)
    (by simpa [u] using (keep 9 (by tauto)).trans hP) uz
    (by simpa [u] using (keep rB1 (by tauto)).trans h1)
    (by simpa [u] using (keep rZ (by tauto)).trans hZ)
  change exec D.N D.K (correctionC D) u 17 = _ ∧ exec D.N D.K (correctionC D) u 18 = _
  exact ⟨(exec_writes _ _ _ (correctionC_frame D 17 (by tauto))).trans uz, ux⟩

abbrev AssemblySource (D : Dims) :=
  PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W ⊕ ZIdx (setting D).τ (setting D).E.W

def assemblySource (D : Dims)
    (x : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D)
    (z : ZIdx (setting D).τ (setting D).E.W → Rg D) : AssemblySource D → Rg D
  | .inl q => x q
  | .inr q => z q

/-- Interleave short and gadget coordinates in each beta block. -/
def assemblySelection (D : Dims) :
    KCol (Wb D) (Jh D) (setting D).τ (setting D).E.W → AssemblySource D
  | .inl (i, .inl row) => .inl (.inl (i, row))
  | .inl (i, .inr c) => .inr (i, c)
  | .inr q => .inl (.inr q)

theorem assemblySource_word (D : Dims)
    (x : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D)
    (z : ZIdx (setting D).τ (setting D).E.W → Rg D) :
    encL D.N D.K (Enum.list.map (assemblySource D x z)) =
      encL D.N D.K (Enum.list.map x) ++ encL D.N D.K (Enum.list.map z) := by
  change encL D.N D.K (((Enum.list (α := PIdx (Wb D) (Jh D) (setting D).τ
    (setting D).E.W)).map Sum.inl ++
      (Enum.list (α := ZIdx (setting D).τ (setting D).E.W)).map Sum.inr).map _) = _
  simp only [List.map_append, List.map_map, Function.comp_def, assemblySource, encL_append]

theorem assemblySelection_correct (D : Dims)
    (x : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D)
    (z : ZIdx (setting D).τ (setting D).E.W → Rg D) :
    assemblySource D x z ∘ assemblySelection D = assemble (S := setting D) x z := by
  funext q
  rcases q with ⟨i, row | c⟩ | q <;> rfl

open Classical in
/-- Assemble a full key from x18 and z17, putting its wire word on19. -/
noncomputable def assembleC (D : Dims) : Code :=
  .seq (.cp 0 18) <| .seq (.app 0 17) <|
  saveQueueC (gatherC D.N D.K (Enum.list.map (Enum.index ∘ assemblySelection D))) 19

theorem wf_assembleC (D : Dims) : (assembleC D).WFc :=
  ⟨trivial, trivial, wf_gatherC _ _ _, trivial⟩

theorem keyEnc_eq_encL (D : Dims) (k : Keyt D) :
    (keyEnc D).enc k = encL D.N D.K (Enum.list.map k) := rfl

/-- The assembly program produces precisely the full key codec. -/
theorem exec_assembleC (D : Dims)
    (x : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D)
    (z : ZIdx (setting D).τ (setting D).E.W → Rg D) (w : St)
    (hx : w 18 = encL D.N D.K (Enum.list.map x))
    (hzs : w 17 = encL D.N D.K (Enum.list.map z))
    (hb : w rB1 = [false]) (hz : w rZ = encRM D.N D.K 0) :
    exec D.N D.K (assembleC D) w 19 = (keyEnc D).enc (assemble (S := setting D) x z) := by
  classical
  let v := exec D.N D.K (.app 0 17) (exec D.N D.K (.cp 0 18) w)
  have hs : v 0 = encL D.N D.K (Enum.list.map (assemblySource D x z)) := by
    simp only [v, exec_app, exec_cp, Function.update_self,
      Function.update_of_ne (by decide : (17 : Fin 64) ≠ 0), hx, hzs, assemblySource_word]
  have h := exec_gatherC_family (assemblySource D x z)
    (Enum.list.map (assemblySelection D)) v hs
    (by simpa [v] using hb) (by simpa [v] using hz)
  simp only [List.map_map, assemblySelection_correct] at h
  rw [assembleC, exec_seq, exec_seq, exec_saveQueueC]
  exact h

theorem proposalC_templates (D : Dims) (r : Fin 64) (hr : r = rB1 ∨ r = rZ) :
    (proposalC D).writes r = false := by
  have hd := keyDigitsC_frame D r (by rcases hr with rfl | rfl <;> tauto)
  have hc := correctionC_frame D r (by rcases hr with rfl | rfl <;> tauto)
  simp only [proposalC, Code.writes, hd, hc]
  rcases hr with rfl | rfl <;> decide

/-- Compute and assemble the proposal before the single-try acceptance test. -/
noncomputable def proposalKeyC (D : Dims) : Code := .seq (proposalC D) (assembleC D)

theorem wf_proposalKeyC (D : Dims) : (proposalKeyC D).WFc :=
  ⟨wf_proposalC _, wf_assembleC _⟩

theorem exec_proposalKeyC (D : Dims) (hK : 2 ≤ D.K) (mpk : MPKt D) (F : BP Pos)
    (T : Matrix (Wb D) (Fin D.K) (Rg D))
    (p : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D) (w : St)
    (hM : w 14 = (mpkEnc D).enc mpk)
    (hA : w 8 = encL D.N D.K (matL (keyPK (helperMap D) mpk F)))
    (hT : w 16 = (matE D (Wb D) (Fin D.K)).enc T)
    (hP : w 9 = encL D.N D.K (Enum.list.map p))
    (h1 : w rB1 = [false]) (hZ : w rZ = encRM D.N D.K 0) :
    let z := gadDec (S := setting D) (keyTarget mpk - pubShort (helperMap D) mpk F p)
    exec D.N D.K (proposalKeyC D) w 19 =
      (keyEnc D).enc (assemble (S := setting D)
        (p - realTrap (S := setting D) (J := Jh D) T z) z) := by
  obtain ⟨hzs, hx⟩ := exec_proposalC D hK mpk F T p w hM hA hT hP h1 hZ
  rw [proposalKeyC, exec_seq]
  exact exec_assembleC D _ _ _ hx hzs
    ((exec_writes _ _ _ (proposalC_templates D rB1 (Or.inl rfl))).trans h1)
    ((exec_writes _ _ _ (proposalC_templates D rZ (Or.inr rfl))).trans hZ)

end AdvancedEncryption.ExpLUT.Prog
