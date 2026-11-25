import PE.Impl.ExpLUT.Prog.KeyCoefficients

/-! Generation of the repeated negative gadget-row coefficient stream. -/
namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)

/-- Append the current power of two and double it. -/
def powersBody : Code := .seq (.app 4 7) (.op .add 7 7 7)

def powersC : Code := .seq (.clr 4) (.rep 2 powersBody)

theorem wf_powersC : powersC.WFc := by
  simp [powersC, powersBody, Code.WFc, Code.writes]

/-- Generate the gadget powers from the canonical word of one on register7. -/
theorem exec_powersC {N K : ℕ} (hK : 0 < K) (n : ℕ) (w : St)
    (hO : w 7 = encRM N K 1) (hC : w 2 = List.replicate n false) :
    exec N K powersC w 4 = encL N K ((List.range n).map (fun j ↦ (2 : Rq N K) ^ j)) := by
  let v := exec N K (.clr 4) w
  have hv : v 2 = List.replicate n false := by simpa [v] using hC
  have h := exec_rep_inv2 (N := N) (K := K) 2 powersBody (by decide)
    (fun m s ↦ s 4 = encL N K ((List.range m).map (fun j ↦ (2 : Rq N K) ^ j)) ∧
      s 7 = encRM N K ((2 : Rq N K) ^ m)) v
    (by simp [v, hO, encL]) ?_
  · have hn : (v 2).length = n := by simp [hv]
    rw [hn] at h
    exact h.1
  · intro m s _ hs _ _
    obtain ⟨h4, h7⟩ := hs
    unfold powersBody
    vm_simp
    constructor
    · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, h4, h7,
        List.range_succ, List.map_append, List.map_singleton, encL_append, encL_singleton]
    · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, h7, takeD_encRM, canonW_add hK]
      congr 1
      rw [pow_succ]
      ring

/-- Append the zero half of a gadget row, then repeat it for every helper. -/
def negativeCoeffC (N K helpers : ℕ) : Code :=
  .seq (natC 2 rB1 K) <| .seq powersC <|
  .seq (natC 6 rB1 (K * (N * K))) <| .seq (.app 4 6) <|
  .seq (.cp 7 4) <| .seq (.clr 4) <|
  .seq (natC 2 rB1 helpers) (repAppC 2 4 7)

theorem wf_negativeCoeffC (N K helpers : ℕ) : (negativeCoeffC N K helpers).WFc := by
  refine ⟨natC_wfc _ _ _, wf_powersC, natC_wfc _ _ _, trivial, trivial, trivial,
    natC_wfc _ _ _, ?_⟩
  simp [repAppC, Code.WFc, Code.writes]

/-- Exact generated queue, including the repeated zero half of each row. -/
theorem exec_negativeCoeffC {N K : ℕ} (hK : 0 < K) (helpers : ℕ) (w : St)
    (hO : w 7 = encRM N K 1) (h1 : w rB1 = [false]) :
    exec N K (negativeCoeffC N K helpers) w 4 =
      (List.replicate helpers (encL N K
        ((List.range K).map (fun j ↦ (2 : Rq N K) ^ j) ++ List.replicate K 0))).flatten := by
  let v := exec N K powersC (Function.update w 2 (List.replicate K false))
  have h4 : v 4 = encL N K ((List.range K).map (fun j ↦ (2 : Rq N K) ^ j)) :=
    exec_powersC hK K _ (by simpa using hO) (by simp)
  have hb : v rB1 = [false] := by
    rw [show v rB1 = (Function.update w 2 (List.replicate K false)) rB1 from
      exec_writes _ _ _ (by decide)]
    simpa using h1
  rw [negativeCoeffC, exec_seq, exec_natC _ _ (by decide) _ w h1, exec_seq]
  change exec N K _ v 4 = _
  rw [exec_seq, exec_natC _ _ (by decide) _ v hb]
  simp only [exec_seq]
  rw [exec_natC _ _ (by decide) _ _ (by simpa using hb)]
  rw [exec_repAppC _ _ _ (by decide) (by decide) (by decide)]
  simp only [exec_clr, exec_cp, exec_app, Function.update_self,
    Function.update_of_ne (by decide : (4 : Fin 64) ≠ 2),
    Function.update_of_ne (by decide : (7 : Fin 64) ≠ 2),
    Function.update_of_ne (by decide : (7 : Fin 64) ≠ 4),
    Function.update_of_ne (by decide : (4 : Fin 64) ≠ 6),
    List.length_replicate, List.nil_append, h4, encL_append, encL_zeros]

/-- The concrete gadget row has powers in its first block and zeros in its second. -/
theorem gadget_row_list (D : Dims) :
    (Enum.list (α := Col (setting D).τ)).map ((setting D).G 0) =
      (List.range D.K).map (fun j ↦ (2 : Rg D) ^ j) ++ List.replicate D.K 0 := by
  let f : Fin 2 × Fin D.K → Rg D := fun c ↦ if c.1 = 0 then 2 ^ c.2.val else 0
  have hf : (setting D).G 0 = f := by
    funext c
    rw [G_apply]
    have hg : (setting D).D.g c.2 = (2 : Rg D) ^ c.2.val := by
      change algebraMap (ZMod D.q) (Rg D) (2 ^ c.2.val) = _
      simp only [map_pow, map_ofNat]
    simp [f, eq_comm, hg]
  have he : (Enum.list (α := Col (setting D).τ)).map ((setting D).G 0) =
      (Enum.list (α := Fin 2 × Fin D.K)).map f :=
    congrArg (fun g ↦ Enum.list.map g) hf
  rw [he, rowL_eq]
  simp only [f, Fin.reduceEq, ↓reduceIte, List.map_const', List.length_finRange]
  congr 1
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp

/-- Repetition follows the helper/column enumeration of the signed-product kernel. -/
theorem negativeCoeff_word (D : Dims) :
    encL D.N D.K (Enum.list.map (publicNegCoeff (S := setting D) (J := Jh D))) =
      (List.replicate (Enum.list (α := Jh D)).length (encL D.N D.K
        ((List.range D.K).map (fun j ↦ (2 : Rg D) ^ j) ++ List.replicate D.K 0))).flatten := by
  change encL D.N D.K (((Enum.list (α := Jh D)).product
    (Enum.list (α := Col (setting D).τ))).map (fun kc ↦ (setting D).G 0 kc.2)) = _
  rw [List.product]
  simp only [List.map_flatMap, List.map_map, Function.comp_def]
  simp only [encL, List.flatMap_assoc]
  have hg := congrArg (encL D.N D.K) (gadget_row_list D)
  change ((Enum.list (α := Jh D)).flatMap (fun _ ↦
    encL D.N D.K (Enum.list.map ((setting D).G 0)))) = _
  rw [hg, List.flatMap_def, List.map_const']
  rfl

/-- Exact negative coefficient stream used by public-map evaluation. -/
theorem exec_negativeCoeffC_public (D : Dims) (w : St)
    (hO : w 7 = encRM D.N D.K 1) (h1 : w rB1 = [false]) :
    exec D.N D.K (negativeCoeffC D.N D.K (Enum.list (α := Jh D)).length) w 4 =
      encL D.N D.K (Enum.list.map (publicNegCoeff (S := setting D) (J := Jh D))) := by
  rw [negativeCoeff_word]
  exact exec_negativeCoeffC D.K_pos _ w hO h1

/-- Build the canonical ring-one word using only the false-bit template. -/
def ringOneC (N K : ℕ) : Code := .seq (.clr 5) <| .seq (bitsC 6 7 5) <|
  .seq (natC 7 rB1 (N * K - 1)) <| .seq (.app 6 7) (.cp 7 6)

theorem wf_ringOneC (N K : ℕ) : (ringOneC N K).WFc := by
  refine ⟨trivial, ?_, natC_wfc _ _ _, trivial, trivial⟩
  simp [bitsC, Code.WFc]

theorem exec_ringOneC {N K : ℕ} (hN : 0 < N) (hK : 2 ≤ K) (w : St)
    (h1 : w rB1 = [false]) : exec N K (ringOneC N K) w 7 = encRM N K 1 := by
  rw [ringOneC, exec_seq, exec_seq,
    exec_bitsC _ _ _ (by decide) (by decide) (by decide) _ (by simp), exec_seq,
    exec_natC _ _ (by decide) _ _ (by simpa using h1)]
  vm_simp
  simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]
  rw [encRM_one hN hK]
  simp only [List.nil_append, List.cons_append, ← List.replicate_add]
  congr 2
  have hn : N - 1 + 1 = N := Nat.sub_add_cancel hN
  have hk : K - 1 + 1 = K := Nat.sub_add_cancel (by omega)
  have hnk : N * K - 1 + 1 = N * K := Nat.sub_add_cancel (by nlinarith)
  nlinarith

/-- Negative coefficients with the ring-one initialization included. -/
def negativeReadyC (N K helpers : ℕ) : Code :=
  .seq (ringOneC N K) (negativeCoeffC N K helpers)

theorem wf_negativeReadyC (N K helpers : ℕ) : (negativeReadyC N K helpers).WFc :=
  ⟨wf_ringOneC _ _, wf_negativeCoeffC _ _ _⟩

theorem exec_negativeReadyC_public (D : Dims) (hK : 2 ≤ D.K) (w : St)
    (h1 : w rB1 = [false]) :
    exec D.N D.K (negativeReadyC D.N D.K (Enum.list (α := Jh D)).length) w 4 =
      encL D.N D.K (Enum.list.map (publicNegCoeff (S := setting D) (J := Jh D))) := by
  rw [negativeReadyC, exec_seq]
  apply exec_negativeCoeffC_public
  · exact exec_ringOneC D.N_pos hK w h1
  · rw [exec_writes _ _ _ ?_, h1]
    simp [ringOneC, bitsC, Code.writes, natC_writes 7 rB1 _ rB1 (by decide)]

end AdvancedEncryption.ExpLUT.Prog
