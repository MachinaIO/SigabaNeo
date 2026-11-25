import PE.Impl.ExpLUT.Prog.KeyGadget

/-! Public-map row evaluation from encoded public key, evaluator matrix, and candidate. -/
namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)

theorem positiveCoeffC_frame (D : Dims) (i : Fin (setting D).E.W) (r : Fin 64)
    (h : r ∉ ([0, 1, 2, 3, 4, 6, 49, 50, 52, 54, 55] : List (Fin 64))) :
    (positiveCoeffC D i).writes r = false := by
  simp only [List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h6, h49, h50, h52, h54, h55⟩ := h
  simp only [positiveCoeffC, mpkBHC, gatherBHC, gatherAutC, Code.writes,
    prefixC_preserves _ r h0 h2 h3, gatherC_preserves _ _ _ r h1 h2 h3 h4,
    Bool.false_or, autGatheredC, autQC, autQBody, appendAFC]
  split <;> simp [Code.writes, natC_writes _ _ _ r h52,
    natC_writes _ _ _ r h49, natC_writes _ _ _ r h6,
    prefixC_preserves _ r h0 h2 h3, Ne.symm h0, Ne.symm h4,
    Ne.symm h50, Ne.symm h52, Ne.symm h54, Ne.symm h55]

theorem negativeReadyC_frame (N K helpers : ℕ) (r : Fin 64)
    (h : r ∉ ([2, 4, 5, 6, 7] : List (Fin 64))) :
    (negativeReadyC N K helpers).writes r = false := by
  simp only [List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true] at h
  obtain ⟨h2, h4, h5, h6, h7⟩ := h
  simp [negativeReadyC, ringOneC, bitsC, negativeCoeffC, powersC, powersBody,
    repAppC, Code.writes, natC_writes _ _ _ r h2, natC_writes _ _ _ r h6,
    natC_writes _ _ _ r h7, Ne.symm h2, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7]

/-- Run a queue generator and save its result in a dedicated register. -/
def saveQueueC (c : Code) (dst : Fin 64) : Code := .seq c (.cp dst 4)

theorem exec_saveQueueC {N K : ℕ} (c : Code) (dst : Fin 64) (w : St) :
    exec N K (saveQueueC c dst) w dst = exec N K c w 4 := by simp [saveQueueC, exec_seq, exec_cp]

theorem saveQueueC_frame (c : Code) (dst r : Fin 64) (hc : c.writes r = false)
    (hr : r ≠ dst) : (saveQueueC c dst).writes r = false := by
  simp [saveQueueC, Code.writes, hc, Ne.symm hr]

noncomputable def rowCountsC (D : Dims) : Code :=
  .seq (natC rQc rB1 (Enum.list (α := PublicPos (Wb D) (Jh D) (setting D).τ)).length)
    (natC 12 rB1 (Enum.list (α := Jh D × Col (setting D).τ)).length)

/-- MPK on14, evaluator matrix on8, candidate on9; output is the public-map row on rIa. -/
noncomputable def publicRowC (D : Dims) (i : Fin (setting D).E.W) : Code :=
  .seq (.cp 0 14) <|
  .seq (saveQueueC (positiveCoeffC D i) rQa) <|
  .seq (saveQueueC (negativeReadyC D.N D.K (Enum.list (α := Jh D)).length) 10) <|
  .seq (.cp 0 9) <|
  .seq (saveQueueC (positiveGatherC D i) rQb) <|
  .seq (saveQueueC (negativeGatherC D i) 11) <|
  .seq (rowCountsC D) signedDotC

theorem wf_publicRowC (D : Dims) (i : Fin (setting D).E.W) : (publicRowC D i).WFc :=
  ⟨trivial, ⟨wf_positiveCoeffC _ _, trivial⟩, ⟨wf_negativeReadyC _ _ _, trivial⟩,
    trivial, ⟨wf_positiveGatherC _ _, trivial⟩, ⟨wf_negativeGatherC _ _, trivial⟩,
    ⟨natC_wfc _ _ _, natC_wfc _ _ _⟩, wf_signedDotC⟩

/-- The full row program computes pubShort from encoded MPK, AF and the sampled candidate. -/
theorem exec_publicRowC (D : Dims) (hK : 2 ≤ D.K) (mpk : MPKt D) (F : BP Pos)
    (p : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D)
    (i : Fin (setting D).E.W) (w : St)
    (hM : w 14 = (mpkEnc D).enc mpk)
    (hA : w 8 = encL D.N D.K (matL (keyPK (helperMap D) mpk F)))
    (hP : w 9 = encL D.N D.K (Enum.list.map p))
    (h1 : w rB1 = [false]) (hZ : w rZ = encRM D.N D.K 0) :
    exec D.N D.K (publicRowC D i) w rIa =
      encRM D.N D.K (pubShort (helperMap D) mpk F p i) := by
  let w0 := exec D.N D.K (.cp 0 14) w
  let w1 := exec D.N D.K (saveQueueC (positiveCoeffC D i) rQa) w0
  have pos : w1 rQa = encL D.N D.K
      (Enum.list.map (publicPosCoeff (helperMap D) mpk F i)) := by
    rw [show w1 rQa = _ from exec_saveQueueC _ _ w0]
    exact exec_positiveCoeffC D mpk F i w0 (by simpa [w0] using hM)
      (by simpa [w0] using hA) (by simpa [w0] using h1) (by simpa [w0] using hZ)
  have f1 : ∀ r : Fin 64, r ∉ [0, 1, 2, 3, 4, 6, 49, 50, 52, 54, 55] → w1 r = w r := by
    intro r hr
    have hn : r ≠ rQa := by simpa using (fun he ↦ hr (by simp [he]))
    rw [show w1 r = w0 r from exec_writes _ _ _
      (saveQueueC_frame _ _ _ (positiveCoeffC_frame D i r hr) hn)]
    exact Function.update_of_ne (fun he ↦ hr (by simp [he])) _ _
  let w2 := exec D.N D.K
    (saveQueueC (negativeReadyC D.N D.K (Enum.list (α := Jh D)).length) 10) w1
  have neg : w2 10 = encL D.N D.K
      (Enum.list.map (publicNegCoeff (S := setting D) (J := Jh D))) := by
    rw [show w2 10 = _ from exec_saveQueueC _ _ w1]
    exact exec_negativeReadyC_public D hK w1 ((f1 rB1 (by decide)).trans h1)
  have f2 : ∀ r : Fin 64, r ∉ [2, 4, 5, 6, 7, 10] → w2 r = w1 r := by
    intro r hr
    apply exec_writes
    apply saveQueueC_frame
    · apply negativeReadyC_frame
      intro he
      exact hr (by simpa using List.mem_append_left [10] he)
    · intro he; exact hr (by simp [he])
  let w3 := exec D.N D.K (.cp 0 9) w2
  have src : w3 0 = encL D.N D.K (Enum.list.map p) := by
    change w2 9 = _
    rw [f2 9 (by decide), f1 9 (by decide), hP]
  have f3 : ∀ r : Fin 64, r ≠ 0 → w3 r = w2 r :=
    fun r hr ↦ Function.update_of_ne hr _ _
  have bit3 : w3 rB1 = [false] := by
    rw [f3 _ (by decide), f2 _ (by decide), f1 _ (by decide), h1]
  have zero3 : w3 rZ = encRM D.N D.K 0 := by
    rw [f3 _ (by decide), f2 _ (by decide), f1 _ (by decide), hZ]
  let w4 := exec D.N D.K (saveQueueC (positiveGatherC D i) rQb) w3
  have posP : w4 rQb = encL D.N D.K (Enum.list.map (publicPosInput p i)) := by
    rw [show w4 rQb = _ from exec_saveQueueC _ _ w3]
    exact exec_positiveGatherC D i p w3 src bit3 zero3
  have f4 : ∀ r : Fin 64, r ∉ [1, 2, 3, 4, 51] → w4 r = w3 r := by
    intro r hr
    apply exec_writes
    apply saveQueueC_frame
    · apply gatherC_preserves <;> intro he <;> exact hr (by simp [he])
    · intro he; exact hr (by simp [he])
  let w5 := exec D.N D.K (saveQueueC (negativeGatherC D i) 11) w4
  have negP : w5 11 = encL D.N D.K
      (Enum.list.map (publicNegInput (helperMap D) p i)) := by
    rw [show w5 11 = _ from exec_saveQueueC _ _ w4]
    exact exec_negativeGatherC D i p w4 ((f4 0 (by decide)).trans src)
      ((f4 rB1 (by decide)).trans bit3) ((f4 rZ (by decide)).trans zero3)
  have f5 : ∀ r : Fin 64, r ∉ [1, 2, 3, 4, 11] → w5 r = w4 r := by
    intro r hr
    apply exec_writes
    apply saveQueueC_frame
    · apply gatherC_preserves <;> intro he <;> exact hr (by simp [he])
    · intro he; exact hr (by simp [he])
  have bit5 : w5 rB1 = [false] := by rw [f5 _ (by decide), f4 _ (by decide), bit3]
  have pos5 : w5 rQa = encL D.N D.K
      (Enum.list.map (publicPosCoeff (helperMap D) mpk F i)) := by
    rw [f5 _ (by decide), f4 _ (by decide), f3 _ (by decide), f2 _ (by decide), pos]
  have neg5 : w5 10 = encL D.N D.K
      (Enum.list.map (publicNegCoeff (S := setting D) (J := Jh D))) := by
    rw [f5 _ (by decide), f4 _ (by decide), f3 _ (by decide), neg]
  have posP5 : w5 rQb = encL D.N D.K (Enum.list.map (publicPosInput p i)) := by
    rw [f5 _ (by decide), posP]
  have zero5 : w5 rZ = encRM D.N D.K 0 := by
    rw [f5 _ (by decide), f4 _ (by decide), zero3]
  change exec D.N D.K signedDotC (exec D.N D.K (rowCountsC D) w5) rIa = _
  rw [rowCountsC, exec_seq, exec_natC _ _ (by decide) _ w5 bit5,
    exec_natC _ _ (by decide) _ _ (by simpa using bit5)]
  apply exec_signedDotC_public D _ mpk F p i
  · simpa using pos5
  · simpa using posP5
  · simpa using neg5
  · simpa using negP
  · simp
  · simp
  · simpa using zero5

/-- Sources, output accumulator and templates survive each public-map row. -/
theorem publicRowC_frame (D : Dims) (i : Fin (setting D).E.W) (r : Fin 64)
    (hr : r = 8 ∨ r = 9 ∨ r = 14 ∨ r = 15 ∨ r = rB1 ∨ r = rZ) :
    (publicRowC D i).writes r = false := by
  have hp := positiveCoeffC_frame D i r
    (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hn := negativeReadyC_frame D.N D.K (Enum.list (α := Jh D)).length r
    (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hg (js : List ℕ) := gatherC_preserves D.N D.K js r
    (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have h52 (n : ℕ) := natC_writes rQc rB1 n r
    (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have h12 (n : ℕ) := natC_writes 12 rB1 n r
    (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  simp only [publicRowC, saveQueueC, Code.writes, hp, hn, positiveGatherC,
    negativeGatherC, hg, rowCountsC, h52, h12, signedDotC, ipC, ipBody]
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Append public-map outputs in any prescribed row order. -/
noncomputable def publicRowsAppendC (D : Dims) : List (Fin (setting D).E.W) → Code
  | [] => .nop
  | i :: is => .seq (publicRowC D i) (.seq (.app 15 rIa) (publicRowsAppendC D is))

noncomputable def publicRowsC (D : Dims) : Code :=
  .seq (.clr 15) (publicRowsAppendC D Enum.list)

theorem wf_publicRowsAppendC (D : Dims) : ∀ is, (publicRowsAppendC D is).WFc
  | [] => trivial
  | i :: is => ⟨wf_publicRowC D i, trivial, wf_publicRowsAppendC D is⟩

theorem wf_publicRowsC (D : Dims) : (publicRowsC D).WFc :=
  ⟨trivial, wf_publicRowsAppendC D _⟩

theorem exec_publicRowsAppendC (D : Dims) (hK : 2 ≤ D.K) (mpk : MPKt D) (F : BP Pos)
    (p : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D) :
    ∀ (is : List (Fin (setting D).E.W)) (w : St) (out : List (Rg D)),
    w 14 = (mpkEnc D).enc mpk →
    w 8 = encL D.N D.K (matL (keyPK (helperMap D) mpk F)) →
    w 9 = encL D.N D.K (Enum.list.map p) →
    w rB1 = [false] → w rZ = encRM D.N D.K 0 → w 15 = encL D.N D.K out →
    exec D.N D.K (publicRowsAppendC D is) w 15 =
      encL D.N D.K (out ++ is.map (pubShort (helperMap D) mpk F p))
  | [], w, out, _, _, _, _, _, ho => by simpa [publicRowsAppendC] using ho
  | i :: is, w, out, hm, ha, hp, hb, hz, ho => by
    let v := exec D.N D.K (.app 15 rIa) (exec D.N D.K (publicRowC D i) w)
    have keep : ∀ r : Fin 64, (r = 8 ∨ r = 9 ∨ r = 14 ∨ r = rB1 ∨ r = rZ) → v r = w r := by
      intro r hr
      have hne : r ≠ 15 := by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      change Function.update _ 15 _ r = _
      rw [Function.update_of_ne hne]
      apply exec_writes
      apply publicRowC_frame
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> tauto
    have hv : v 15 = encL D.N D.K (out ++ [pubShort (helperMap D) mpk F p i]) := by
      change exec D.N D.K (publicRowC D i) w 15 ++
        exec D.N D.K (publicRowC D i) w rIa = _
      rw [exec_writes _ _ _ (publicRowC_frame D i 15 (by tauto)), ho,
        exec_publicRowC D hK mpk F p i w hm ha hp hb hz, encL_append, encL_singleton]
    have ih := exec_publicRowsAppendC D hK mpk F p is v
      (out ++ [pubShort (helperMap D) mpk F p i])
      ((keep 14 (by tauto)).trans hm) ((keep 8 (by tauto)).trans ha)
      ((keep 9 (by tauto)).trans hp) ((keep rB1 (by tauto)).trans hb)
      ((keep rZ (by tauto)).trans hz) hv
    change exec D.N D.K (publicRowsAppendC D is) v 15 = _
    simpa only [List.map_cons, List.append_assoc, List.singleton_append] using ih

/-- All public-map rows, in the encoding order expected by decomposition. -/
theorem exec_publicRowsC (D : Dims) (hK : 2 ≤ D.K) (mpk : MPKt D) (F : BP Pos)
    (p : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D) (w : St)
    (hM : w 14 = (mpkEnc D).enc mpk)
    (hA : w 8 = encL D.N D.K (matL (keyPK (helperMap D) mpk F)))
    (hP : w 9 = encL D.N D.K (Enum.list.map p))
    (h1 : w rB1 = [false]) (hZ : w rZ = encRM D.N D.K 0) :
    exec D.N D.K (publicRowsC D) w 15 =
      encL D.N D.K (Enum.list.map (pubShort (helperMap D) mpk F p)) := by
  rw [publicRowsC, exec_seq]
  simpa using exec_publicRowsAppendC D hK mpk F p Enum.list (exec D.N D.K (.clr 15) w) []
    (by simpa using hM) (by simpa using hA) (by simpa using hP)
    (by simpa using h1) (by simpa using hZ) (by simp)

end AdvancedEncryption.ExpLUT.Prog
