import PE.Impl.ExpLUT.Prog.KeyTimeArithmetic

/-! Invariants for all ring instructions, including direct counter-register reads. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

theorem countedFrame_counter (c : Fin 64) : countedFrame c 2 = tR c := by
  apply Fin.ext
  change (41 + c.val) % 105 = 41 + c.val
  apply Nat.mod_eq_of_lt
  have := c.isLt
  omega

theorem countedFrame_range (c : Fin 64) (j : Fin 37) :
    (countedFrame c j).val < 37 ∨ countedFrame c j = tR c := by
  by_cases hj : j.val = 2
  · have he : j = 2 := Fin.ext hj
    subst j
    exact Or.inr (countedFrame_counter c)
  · left
    change (if j.val = 0 then 32 else if j.val = 1 then 33
      else if j.val = 2 then (41 + c.val) % 105 else if j.val = 3 then 35
      else if j.val = 4 then 36 else j.val - 5) < 37
    have := j.isLt
    split_ifs <;> omega

theorem countedAfter_high (M N K count : ℕ) (c : Fin 64) (a : Fin 105 → ℕ)
    (hc : count = a (tR c)) (t : Fin 105) (ht : 39 ≤ t.val) :
    countedAfter M N K count c a t = a t := by
  rcases embedF_cases (countedFrame c) a (countedArea M N K count) t with ⟨_, h⟩ | ⟨j, hj, h⟩
  · exact h
  · by_cases h2 : j.val = 2
    · have he : j = 2 := Fin.ext h2
      subst j
      rw [countedFrame_counter] at hj
      rw [countedAfter, h]
      change count = a t
      rw [hc, hj]
    · have hv := congrArg Fin.val hj
      change (if j.val = 0 then 32 else if j.val = 1 then 33
        else if j.val = 2 then (41 + c.val) % 105 else if j.val = 3 then 35
        else if j.val = 4 then 36 else j.val - 5) = t.val at hv
      have := j.isLt
      split_ifs at hv <;> omega

theorem countedResult_high (M N K : ℕ) (d c : Fin 64) (a : Fin 105 → ℕ) (t : Fin 105)
    (ht : 39 ≤ t.val) (hd : t ≠ tR d) : countedResult M N K (a (tR c)) d c a t = a t := by
  have hne (n : Fin 105) (hn : n.val < 39) : t ≠ n := by intro h; subst t; omega
  have hcne (n : Fin 105) (hn : n.val < 39) : tR c ≠ n := by
    intro he; have hv := congrArg Fin.val he; simp only [tR_val] at hv; omega
  rw [countedResult, store_outside d _ _ t hd (hne 32 (by decide))
    (hne 33 (by decide)) (hne 34 (by decide))]
  rw [canonicalAfter, embed_outside _ _ _ t (by
    intro j hj
    have hh := (canonicalFrame_range j).1
    rw [hj] at hh
    omega)]
  rw [countedAfter_high M N K _ c _ (by simp [hcne 33 (by decide), hcne 34 (by decide)]) t ht]
  simp only [Function.update_of_ne (hne 34 (by decide)), Function.update_of_ne (hne 33 (by decide))]

theorem countedResult_templates (M N K : ℕ) (d c : Fin 64) (a : Fin 105 → ℕ) :
    countedResult M N K (a (tR c)) d c a 35 = K ∧ countedResult M N K (a (tR c)) d c a 36 = N ∧
    countedResult M N K (a (tR c)) d c a 37 = a 37 ∧ countedResult M N K (a (tR c)) d c a 38 = N * K := by
  let b := countedAfter M N K (a (tR c)) c (Function.update (Function.update a 33 (N * K)) 34 (N * K))
  have hs (t : Fin 105) (hlo : 35 ≤ t.val) (hhi : t.val ≤ 38) :
      countedResult M N K (a (tR c)) d c a t = canonicalAfter M N K b t := by
    apply store_outside
    · intro he
      have hv := congrArg Fin.val he
      simp only [tR_val] at hv
      omega
    all_goals intro he; have hv := congrArg Fin.val he; omega
  rw [hs 35 (by decide) (by decide), hs 36 (by decide) (by decide),
    hs 37 (by decide) (by decide), hs 38 (by decide) (by decide)]
  refine ⟨embedF_apply_self canonicalFrame b (ringArea M N K (N * K)) 3,
    embedF_apply_self canonicalFrame b (ringArea M N K (N * K)) 4, ?_,
    embedF_apply_self canonicalFrame b (ringArea M N K (N * K)) 2⟩
  rw [canonicalAfter, embed_outside _ _ _ 37 (by
    intro j hj
    exact (canonicalFrame_range j).2 (congrArg Fin.val hj))]
  change countedAfter M N K (a (tR c)) c _ 37 = _
  rw [countedAfter, embed_outside _ _ _ 37 (by
    intro j hj
    rcases countedFrame_range c j with hh | hh
    · rw [hj] at hh; omega
    · have hv := congrArg Fin.val (hh.symm.trans hj)
      simp only [tR_val] at hv
      omega)]
  simp

theorem countedResult_bound (M N K : ℕ) (d c : Fin 64) (a : Fin 105 → ℕ)
    (ha : ∀ t, a t ≤ M) (hNK : N * K ≤ M) (hN : N ≤ M) (hK : K ≤ M) :
    ∀ t, countedResult M N K (a (tR c)) d c a t ≤ M := by
  have h1 : ∀ t, Function.update (Function.update a (33 : Fin 105) (N * K)) 34 (N * K) t ≤ M := by
    intro t
    simp only [Function.update_apply]
    split_ifs <;> first | exact hNK | exact ha t
  have h2 := embed_bound (countedFrame c) _ _ M h1
    (countedArea_bound M N K _ hNK hN hK (ha (tR c)))
  have h3 := embed_bound canonicalFrame _ _ M h2 (ringArea_bound M N K hNK hN hK)
  apply embed_bound _ _ _ M h3
  intro j
  split_ifs <;> omega


theorem countedResult_words (M N K : ℕ) (d c : Fin 64) (a : Fin 105 → ℕ) :
    countedResult M N K (a (tR c)) d c a (tR d) = N * K ∧
    countedResult M N K (a (tR c)) d c a 32 = 0 ∧ countedResult M N K (a (tR c)) d c a 33 = 0 ∧
    countedResult M N K (a (tR c)) d c a 34 = 0 := by
  let e := mkE (fOut d) (fOut_inj d)
  let b := canonicalAfter M N K (countedAfter M N K (a (tR c)) c
    (Function.update (Function.update a 33 (N * K)) 34 (N * K)))
  let z : Fin 4 → ℕ := fun j ↦ if j = 0 then N * K else 0
  exact ⟨embedF_apply_self e b z 0, embedF_apply_self e b z 1,
    embedF_apply_self e b z 2, embedF_apply_self e b z 3⟩

theorem countedResult_ready (M N K : ℕ) (d c : Fin 64) (a : Fin 105 → ℕ)
    (h : Ready M N K a) : Ready M N K (countedResult M N K (a (tR c)) d c a) := by
  obtain ⟨hk, hn, hz, ho⟩ := countedResult_templates M N K d c a
  have h39 := countedResult_high M N K d c a 39 (by decide) (by
    intro he; have hv := congrArg Fin.val he; simp only [tR_val] at hv; omega)
  have h40 := countedResult_high M N K d c a 40 (by decide) (by
    intro he; have hv := congrArg Fin.val he; simp only [tR_val] at hv; omega)
  exact ⟨countedResult_bound M N K d c a h.top h.ring h.dimension h.width,
    h.ring, h.dimension, h.width, hk.le, hn.le, hz.trans h.zeros, ho.le,
    (countedResult_words M N K d c a).2.1, h39.trans h.scratch1, h40.trans h.scratch2⟩

/-- Every actual ring instruction preserves readiness for the next instruction. -/
theorem operationResult_ready (M N K : ℕ) (o : Op) (d c : Fin 64) (a : Fin 105 → ℕ)
    (h : Ready M N K a) : Ready M N K (operationResult M N K o d c a) := by
  unfold operationResult
  split_ifs
  · exact binaryResult_ready M N K d a h
  · exact countedResult_ready M N K d c a h

/-- A ring instruction returns both its runtime certificate and the next readiness proof. -/
theorem compile_op_ready (M N K : ℕ) (o : Op) (d s c : Fin 64) (a : Fin 105 → ℕ)
    (h : Ready M N K a) :
    Cert (MVM.compile (.op o d s c)) a (operationResult M N K o d c a)
      (operationBound M N K (a (tR c))) ∧ Ready M N K (operationResult M N K o d c a) :=
  ⟨compile_op_cert M N K o d s c a h, operationResult_ready M N K o d c a h⟩

end AdvancedEncryption.ExpLUT.Prog.KeyTime

