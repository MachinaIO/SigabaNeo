import PE.Impl.ExpLUT.Prog.KeyBHCodec

/-! Executable completion of the positive public-map coefficient stream. -/
namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)

/-- The evaluator's matrix queue begins with its row zero. -/
theorem matL_row0_prefix {N K : ℕ} (A : Fin 2 → Fin 2 × Fin K → Rq N K) :
    matL A = Enum.list.map (A 0) ++ Enum.list.map (A 1) := by
  simp [matL, enum_fin2]

/-- Complete an existing B/H queue with the first evaluator row or zeros. -/
def appendAFC (N K : ℕ) (first : Bool) : Code :=
  if first then .seq (prefixC ((2 * K) * (N * K))) (.app 4 0)
  else .seq (natC 6 rB1 ((2 * K) * (N * K))) (.app 4 6)

theorem wf_appendAFC (N K : ℕ) (first : Bool) : (appendAFC N K first).WFc := by
  cases first <;> simp only [appendAFC, Bool.false_eq_true, ↓reduceIte, Code.WFc]
  · exact ⟨natC_wfc _ _ _, trivial⟩
  · exact ⟨wf_prefixC _, trivial⟩

theorem encL_zeros {N K : ℕ} (n : ℕ) :
    encL N K (List.replicate n 0) = List.replicate (n * (N * K)) false := by
  induction n with
  | zero => simp [encL]
  | succ n ih =>
    simp only [List.replicate_succ, encL_cons, ih, encRM_zero,
      ← List.replicate_add]
    congr 1
    ring

/-- Exact queue append, starting from the actual evaluator matrix layout. -/
theorem exec_appendAFC {N K : ℕ} (first : Bool)
    (A : Fin 2 → Fin 2 × Fin K → Rq N K) (xs : List (Rq N K)) (w : St)
    (hA : w 0 = encL N K (matL A)) (hX : w 4 = encL N K xs)
    (h1 : w rB1 = [false]) :
    exec N K (appendAFC N K first) w 4 = encL N K
      (xs ++ Enum.list.map (fun c ↦ if first then A 0 c else 0)) := by
  have hl : (encL N K (Enum.list.map (A 0))).length = (2 * K) * (N * K) := by
    simp only [length_encL, List.length_map, length_enum_col]
  cases first
  · rw [appendAFC, ite_eq_right (by decide), exec_seq,
      exec_natC _ _ (by decide) _ _ h1]
    simp only [exec_app, Function.update_self,
      Function.update_of_ne (by decide : (4 : Fin 64) ≠ 6), hX,
      Bool.false_eq_true, ↓reduceIte, encL_append]
    rw [List.map_const', encL_zeros]
    congr 3
    exact length_enum_col.symm
  · have hp := exec_prefixC (N := N) (K := K) (encL N K (Enum.list.map (A 0)))
      (encL N K (Enum.list.map (A 1))) w
      (by rw [hA, matL_row0_prefix, encL_append]) h1
    rw [hl] at hp
    rw [appendAFC, ite_eq_left rfl, exec_seq, exec_app, Function.update_self, hp,
      exec_writes _ _ _ (prefixC_preserves _ 4 (by decide) (by decide) (by decide)), hX]
    simp [encL_append]

/-- B/H followed by the conditional evaluator row is the sparse positive coefficient list. -/
theorem publicPosCoeff_list (D : Dims) (mpk : MPKt D) (F : BP Pos)
    (i : Fin (setting D).E.W) :
    Enum.list.map (publicPosCoeff (helperMap D) mpk F i) =
      (Enum.list.map (fun t : BHRow D ↦ (setting D).E.σ ((setting D).idx i)
        (bhSource D mpk (bhSelection D t)))) ++
      Enum.list.map (fun c ↦ if i = (setting D).row0
        then keyPK (helperMap D) mpk F 0 c else 0) := by
  change ((Enum.list (α := Wb D)).map Sum.inl ++
    ((Enum.list (α := Jh D × Col (setting D).τ)).map Sum.inl ++
      (Enum.list (α := Col (setting D).τ)).map Sum.inr).map Sum.inr).map _ =
    (((Enum.list (α := Wb D)).map Sum.inl ++
      (Enum.list (α := Jh D × Col (setting D).τ)).map Sum.inr).map _) ++ _
  simp only [List.map_append, List.map_map, Function.comp_def,
    publicPosCoeff, bhSelection, bhSource, List.append_assoc]

/-- Append the evaluator row to the B/H output, yielding the scheme's full positive queue. -/
theorem exec_appendAFC_public (D : Dims) (mpk : MPKt D) (F : BP Pos)
    (i : Fin (setting D).E.W) (w : St)
    (hA : w 0 = encL D.N D.K (matL (keyPK (helperMap D) mpk F)))
    (hX : w 4 = encL D.N D.K (Enum.list.map (fun t : BHRow D ↦
      (setting D).E.σ ((setting D).idx i) (bhSource D mpk (bhSelection D t)))))
    (h1 : w rB1 = [false]) :
    exec D.N D.K (appendAFC D.N D.K (decide (i = (setting D).row0))) w 4 =
      encL D.N D.K (Enum.list.map (publicPosCoeff (helperMap D) mpk F i)) := by
  classical
  rw [publicPosCoeff_list]
  have h := exec_appendAFC (decide (i = (setting D).row0))
      (keyPK (helperMap D) mpk F) _ w hA hX h1
  simp only [decide_eq_true_eq] at h
  exact h

/-- The B/H generator preserves the evaluator matrix and constant templates. -/
theorem mpkBHC_preserves_inputs (D : Dims) (i : ℕ) (r : Fin 64)
    (hr : r = 8 ∨ r = rB1 ∨ r = rZ) : (mpkBHC D i).writes r = false := by
  have h0 : r ≠ 0 := by rcases hr with rfl | rfl | rfl <;> decide
  have h1 : r ≠ 1 := by rcases hr with rfl | rfl | rfl <;> decide
  have h2 : r ≠ 2 := by rcases hr with rfl | rfl | rfl <;> decide
  have h3 : r ≠ 3 := by rcases hr with rfl | rfl | rfl <;> decide
  have h4 : r ≠ 4 := by rcases hr with rfl | rfl | rfl <;> decide
  have hqc : r ≠ rQc := by rcases hr with rfl | rfl | rfl <;> decide
  have hqk : r ≠ rQk := by rcases hr with rfl | rfl | rfl <;> decide
  simp only [mpkBHC, gatherBHC, gatherAutC, Code.writes,
    prefixC_preserves _ r h0 h2 h3, gatherC_preserves _ _ _ r h1 h2 h3 h4,
    Bool.false_or, autGatheredC, natC_writes _ _ _ r hqc,
    natC_writes _ _ _ r hqk, autQC, autQBody]
  rcases hr with rfl | rfl | rfl <;> decide

/-- Public positive coefficients from the MPK word and the computed evaluator matrix on 8. -/
noncomputable def positiveCoeffC (D : Dims) (i : Fin (setting D).E.W) : Code :=
  .seq (mpkBHC D i.val) (.seq (.cp 0 8)
    (appendAFC D.N D.K (decide (i = (setting D).row0))))

theorem wf_positiveCoeffC (D : Dims) (i : Fin (setting D).E.W) :
    (positiveCoeffC D i).WFc := ⟨wf_mpkBHC _ _, trivial, wf_appendAFC _ _ _⟩

/-- The production coefficient loader consumes actual wire words. -/
theorem exec_positiveCoeffC (D : Dims) (mpk : MPKt D) (F : BP Pos)
    (i : Fin (setting D).E.W) (w : St)
    (hM : w 0 = (mpkEnc D).enc mpk)
    (hA : w 8 = encL D.N D.K (matL (keyPK (helperMap D) mpk F)))
    (h1 : w rB1 = [false]) (hZ : w rZ = encRM D.N D.K 0) :
    exec D.N D.K (positiveCoeffC D i) w 4 =
      encL D.N D.K (Enum.list.map (publicPosCoeff (helperMap D) mpk F i)) := by
  rw [positiveCoeffC, exec_seq, exec_seq]
  apply exec_appendAFC_public
  · simp only [exec_cp, Function.update_self]
    rw [exec_writes _ _ _ (mpkBHC_preserves_inputs D i 8 (Or.inl rfl)), hA]
  · simp only [exec_cp, Function.update_of_ne (by decide : (4 : Fin 64) ≠ 0)]
    exact exec_mpkBHC D i mpk w hM h1 hZ
  · simp only [exec_cp, Function.update_of_ne (by decide : rB1 ≠ 0)]
    rw [exec_writes _ _ _ (mpkBHC_preserves_inputs D i rB1 (Or.inr (Or.inl rfl))), h1]

end AdvancedEncryption.ExpLUT.Prog
