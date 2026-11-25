import PE.Impl.ExpLUT.Prog.KeyTimeBinary

/-! Preservation properties needed to iterate actual compiled binary operations. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

theorem embed_outside {n k : ℕ} (e : Fin n ↪ Fin k) (a : Fin k → ℕ) (b : Fin n → ℕ)
    (t : Fin k) (ht : ∀ j, e j ≠ t) : embedF e a b t = a t := by
  rcases embedF_cases e a b t with ⟨_, h⟩ | ⟨j, hj, _⟩
  · exact h
  · exact False.elim (ht j hj)

theorem binaryFrame_lt (j : Fin 37) : (binaryFrame j).val < 37 := by
  change (if j.val = 0 then 32 else if j.val = 1 then 33 else if j.val = 2 then 34
    else if j.val = 3 then 35 else if j.val = 4 then 36 else j.val - 5) < 37
  have := j.isLt
  split_ifs <;> omega

theorem canonicalFrame_range (j : Fin 28) :
    (canonicalFrame j).val ≤ 38 ∧ (canonicalFrame j).val ≠ 37 := by
  have he : (canonicalFrame j).val =
      (if j.val = 0 then 33 else if j.val = 1 then 32 else if j.val = 2 then 38
        else if j.val = 3 then 35 else if j.val = 4 then 36 else j.val - 5) := rfl
  rw [he]
  have := j.isLt
  split_ifs <;> omega

/-- Output framing changes only the destination and the three work words. -/
theorem store_outside (d : Fin 64) (a : Fin 105 → ℕ) (z : Fin 4 → ℕ) (t : Fin 105)
    (hd : t ≠ tR d) (h32 : t ≠ 32) (h33 : t ≠ 33) (h34 : t ≠ 34) :
    embedF (mkE (fOut d) (fOut_inj d)) a z t = a t := by
  apply embed_outside
  intro j hj
  fin_cases j
  · exact hd hj.symm
  · exact h32 hj.symm
  · exact h33 hj.symm
  · exact h34 hj.symm

theorem binaryResult_high (M N K : ℕ) (d : Fin 64) (a : Fin 105 → ℕ) (t : Fin 105)
    (ht : 39 ≤ t.val) (hd : t ≠ tR d) : binaryResult M N K d a t = a t := by
  have hne (n : Fin 105) (hn : n.val < 39) : t ≠ n := by intro h; subst t; omega
  rw [binaryResult, store_outside d _ _ t hd (hne 32 (by decide))
    (hne 33 (by decide)) (hne 34 (by decide))]
  rw [canonicalAfter, embed_outside _ _ _ t (by
    intro j hj
    have hh := (canonicalFrame_range j).1
    rw [hj] at hh
    omega)]
  rw [binaryAfter, embed_outside _ _ _ t (by
    intro j hj
    have hh := binaryFrame_lt j
    rw [hj] at hh
    omega)]
  simp only [Function.update_of_ne (hne 34 (by decide)), Function.update_of_ne (hne 33 (by decide))]

theorem binaryResult_other_register (M N K : ℕ) (d r : Fin 64) (a : Fin 105 → ℕ)
    (hr : r ≠ d) : binaryResult M N K d a (tR r) = a (tR r) := by
  apply binaryResult_high M N K d a (tR r) (by change 39 ≤ 41 + r.val; omega)
  intro he
  have hv := congrArg Fin.val he
  apply hr
  apply Fin.ext
  simp only [tR_val] at hv
  omega

theorem binaryResult_templates (M N K : ℕ) (d : Fin 64) (a : Fin 105 → ℕ) :
    binaryResult M N K d a 35 = K ∧ binaryResult M N K d a 36 = N ∧
    binaryResult M N K d a 37 = a 37 ∧ binaryResult M N K d a 38 = N * K := by
  let b := binaryAfter M N K (Function.update (Function.update a 33 (N * K)) 34 (N * K))
  have hs (t : Fin 105) (hlo : 35 ≤ t.val) (hhi : t.val ≤ 38) :
      binaryResult M N K d a t = canonicalAfter M N K b t := by
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
  change binaryAfter M N K _ 37 = _
  rw [binaryAfter, embed_outside _ _ _ 37 (by
    intro j hj
    have hh := binaryFrame_lt j
    rw [hj] at hh
    omega)]
  simp

theorem binaryResult_bound (M N K : ℕ) (d : Fin 64) (a : Fin 105 → ℕ)
    (ha : ∀ t, a t ≤ M) (hNK : N * K ≤ M) (hN : N ≤ M) (hK : K ≤ M) :
    ∀ t, binaryResult M N K d a t ≤ M := by
  have h1 : ∀ t, Function.update (Function.update a (33 : Fin 105) (N * K)) 34 (N * K) t ≤ M := by
    intro t
    simp only [Function.update_apply]
    split_ifs <;> first | exact hNK | exact ha t
  have h2 := embed_bound binaryFrame _ _ M h1 (ringArea_bound M N K hNK hN hK)
  have h3 := embed_bound canonicalFrame _ _ M h2 (ringArea_bound M N K hNK hN hK)
  apply embed_bound _ _ _ M h3
  intro j
  split_ifs <;> omega

/-- Conditions sufficient to run a compiled ring operation, with arbitrary bounded scratch. -/
structure Ready (M N K : ℕ) (a : Fin 105 → ℕ) : Prop where
  top : ∀ t, a t ≤ M
  ring : N * K ≤ M
  dimension : N ≤ M
  width : K ≤ M
  templateK : a 35 ≤ K
  templateN : a 36 ≤ N
  zeros : a 37 = N * K
  ones : a 38 ≤ N * K
  work : a 32 = 0
  scratch1 : a 39 = 0
  scratch2 : a 40 = 0

theorem binaryResult_ready (M N K : ℕ) (d : Fin 64) (a : Fin 105 → ℕ)
    (h : Ready M N K a) : Ready M N K (binaryResult M N K d a) := by
  obtain ⟨hk, hn, hz, ho⟩ := binaryResult_templates M N K d a
  have h39 := binaryResult_high M N K d a 39 (by decide) (by
    intro he; have hv := congrArg Fin.val he; simp only [tR_val] at hv; omega)
  have h40 := binaryResult_high M N K d a 40 (by decide) (by
    intro he; have hv := congrArg Fin.val he; simp only [tR_val] at hv; omega)
  exact ⟨binaryResult_bound M N K d a h.top h.ring h.dimension h.width,
    h.ring, h.dimension, h.width, hk.le, hn.le, hz.trans h.zeros, ho.le,
    (binaryResult_words M N K d a).2.1, h39.trans h.scratch1, h40.trans h.scratch2⟩

end AdvancedEncryption.ExpLUT.Prog.KeyTime
