import PE.Impl.ExpLUT.Prog.KeyTimeControl

/-! Explicit global bound updates for append, including its nonzero loop-counter bound. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

def appendResult (d s : Fin 64) (a : Fin 105 → ℕ) : Fin 105 → ℕ :=
  Function.update (Function.update (Function.update a 39 (a (tR s))) 40 0)
    (tR d) (a (tR d) + a (tR s))

/-- Transport an update through an embedding, retaining arbitrary prior framed values. -/
theorem embed_update {k n : ℕ} (e : Fin n ↪ Fin k) (a : Fin k → ℕ) (b : Fin n → ℕ)
    (j : Fin n) (v : ℕ) :
    embedF e a (Function.update b j v) = Function.update (embedF e a b) (e j) v := by
  funext t
  rcases embedF_cases e a b t with ⟨hn, ht⟩ | ⟨i, rfl, ht⟩
  · have hne : t ≠ e j := by
      intro he; subst t; rw [partialInv_self] at hn; contradiction
    simp only [embedF, hn, Option.elim_none, Function.update_of_ne hne]
  · rw [embedF_apply_self]
    by_cases hi : i = j
    · subst i; simp
    · simp [Function.update_of_ne hi, Function.update_of_ne (fun he ↦ hi (e.injective he)), ht]

theorem embed_original {k n : ℕ} (e : Fin n ↪ Fin k) (a : Fin k → ℕ) :
    embedF e a (a ∘ e) = a := by
  funext t
  rcases embedF_cases e a (a ∘ e) t with ⟨_, h⟩ | ⟨j, rfl, h⟩ <;> exact h

theorem compile_append (d s : Fin 64) (a : Fin 105 → ℕ) (M : ℕ)
    (hM : ∀ t, a t ≤ M) (hs : a (tR d) + a (tR s) ≤ M) :
    Cert (MVM.compile (.app d s)) a (appendResult d s a)
      ((4 * a (tR s) + 6) * (2 * M + 5)) := by
  by_cases hd : d = s
  · subst s
    let e := mkE (fAp1 d) (fAp1_inj d)
    have h := compile_app_self_cert d a M hM hs
    have he : (fun t : Fin 3 ↦ if t = 0 then (a ∘ e) 0 + (a ∘ e) 0
        else if t = 1 then (a ∘ e) 0 else if t = 2 then 0 else (a ∘ e) t) =
        Function.update (Function.update (Function.update (a ∘ e) 1 ((a ∘ e) 0)) 2 0)
          0 ((a ∘ e) 0 + (a ∘ e) 0) := by funext t; fin_cases t <;> simp
    change Cert _ _ (embedF e a _) _ at h
    rw [he, embed_update, embed_update, embed_update, embed_original] at h
    exact h
  · let e := mkE (fAp d s) (fAp_inj hd)
    have h := compile_app_cert d s hd a M hM hs
    have he : (fun t : Fin 4 ↦ if t = 0 then (a ∘ e) 0 + (a ∘ e) 1
        else if t = 2 then (a ∘ e) 1 else if t = 3 then 0 else (a ∘ e) t) =
        Function.update (Function.update (Function.update (a ∘ e) 2 ((a ∘ e) 1)) 3 0)
          0 ((a ∘ e) 0 + (a ∘ e) 1) := by funext t; fin_cases t <;> simp
    change Cert _ _ (embedF e a _) _ at h
    rw [he, embed_update, embed_update, embed_update, embed_original] at h
    exact h

end AdvancedEncryption.ExpLUT.Prog.KeyTime
