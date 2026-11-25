import PE.Impl.ExpLUT.Prog.KeyTimeCoefV

/-! Exact register-cap changes for growing queues and binary counters. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

theorem layout_update (M N K : ℕ) (b : Fin 64 → ℕ) (r : Fin 64) (n : ℕ) :
    layout M N K (Function.update b r n) = Function.update (layout M N K b) (tR r) n := by
  funext t
  by_cases ht : 41 ≤ t.val
  · let q : Fin 64 := ⟨t.val - 41, by have := t.isLt; omega⟩
    have he : tR q = t := by apply Fin.ext; simp only [tR_val, q]; omega
    rw [← he, layout_register]
    by_cases hq : q = r
    · simp only [hq, Function.update_self]
    · have hn : tR q ≠ tR r := fun he ↦ hq (tR_inj he)
      simp [Function.update_of_ne hq, Function.update_of_ne hn]
  · have hn : t ≠ tR r := by
      intro he; have hv := congrArg Fin.val he; simp only [tR_val] at hv; omega
    simp [layout, ht, Function.update_of_ne hn]

theorem layout_mono (M N K : ℕ) {b c : Fin 64 → ℕ} (h : b ≤ c) :
    layout M N K b ≤ layout M N K c := by
  intro t
  unfold layout
  split_ifs <;> first | exact h _ | exact le_rfl

theorem layout_copy_update (M N K : ℕ) (b : Fin 64 → ℕ)
    (ht : ∀ t, layout M N K b t ≤ M) (d s : Fin 64) :
    Cert (MVM.compile (.cp d s)) (layout M N K b)
      (layout M N K (Function.update b d (b s))) (2 * M + 5) := by
  rw [layout_update]
  simpa only [layout_register, show 2 * (M + 1) + 3 = 2 * M + 5 by omega] using
    compile_cp_any d s (layout M N K b) M ht

theorem layout_clear_update (M N K : ℕ) (b : Fin 64 → ℕ)
    (ht : ∀ t, layout M N K b t ≤ M) (d : Fin 64) :
    Cert (MVM.compile (.clr d)) (layout M N K b)
      (layout M N K (Function.update b d 0)) (2 * M + 5) := by
  rw [layout_update]
  exact (compile_clr_cert d _ M ht).mono le_rfl le_rfl (by omega)

/-- Append changes only the destination cap; its helper bounds fit the scratch allowance M. -/
theorem layout_append (M N K : ℕ) (b : Fin 64 → ℕ)
    (ht : ∀ t, layout M N K b t ≤ M) (d s : Fin 64) (hs : b d + b s ≤ M) :
    Cert (MVM.compile (.app d s)) (layout M N K b)
      (layout M N K (Function.update b d (b d + b s))) ((4 * b s + 6) * (2 * M + 5)) := by
  have h := compile_append d s (layout M N K b) M ht (by simpa using hs)
  simp only [layout_register] at h
  apply h.mono le_rfl _ le_rfl
  rw [layout_update]
  intro t
  by_cases hd : t = tR d
  · subst t; simp [appendResult]
  · simp only [appendResult, Function.update_of_ne hd]
    by_cases h40 : t = 40
    · subst t; simp
    · simp only [Function.update_of_ne h40]
      by_cases h39 : t = 39
      · subst t; simpa [layout] using ht (tR s)
      · simp [Function.update_of_ne h39]

theorem RingInputs.update_layout {M N K : ℕ} {b : Fin 64 → ℕ}
    (h : RingInputs M N K (layout M N K b)) (r : Fin 64) (n : ℕ) (hn : n ≤ M) :
    RingInputs M N K (layout M N K (Function.update b r n)) := by
  apply layout_inputs M N K _ _ h.ring h.dimension h.width
  intro s
  by_cases hs : s = r
  · subst s; simpa using hn
  · simpa [Function.update_of_ne hs] using h.top (tR s)

end AdvancedEncryption.ExpLUT.Prog.KeyTime
