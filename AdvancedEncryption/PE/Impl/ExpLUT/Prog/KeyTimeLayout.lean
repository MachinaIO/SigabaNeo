import PE.Impl.ExpLUT.Prog.KeyTimeEvalInputs

/-! Register-specific invariant envelopes for actual evaluator loops. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog

/-- Physical ring templates retain their exact bounds; every VM register has its own cap. -/
def layout (M N K : ℕ) (b : Fin 64 → ℕ) (t : Fin 105) : ℕ :=
  if ht : 41 ≤ t.val then b ⟨t.val - 41, by have := t.isLt; omega⟩
  else if t = 35 then K else if t = 36 then N
  else if t = 37 ∨ t = 38 then N * K else M

@[simp] theorem layout_register (M N K : ℕ) (b : Fin 64 → ℕ) (r : Fin 64) :
    layout M N K b (tR r) = b r := by simp [layout, tR]

theorem layout_top (M N K : ℕ) (b : Fin 64 → ℕ) (hb : ∀ r, b r ≤ M)
    (hNK : N * K ≤ M) (hN : N ≤ M) (hK : K ≤ M) : ∀ t, layout M N K b t ≤ M := by
  intro t
  unfold layout
  split_ifs <;> first | exact hb _ | assumption | exact le_rfl

theorem layout_inputs (M N K : ℕ) (b : Fin 64 → ℕ) (hb : ∀ r, b r ≤ M)
    (hNK : N * K ≤ M) (hN : N ≤ M) (hK : K ≤ M) : RingInputs M N K (layout M N K b) := by
  refine ⟨layout_top M N K b hb hNK hN hK, hNK, hN, hK, ?_, ?_, ?_, ?_⟩
  all_goals simp [layout]

/-- Checking the special tapes and register caps suffices to compare a complete bound vector. -/
theorem le_layout (M N K : ℕ) (b : Fin 64 → ℕ) (a : Fin 105 → ℕ)
    (ht : ∀ t, a t ≤ M) (hk : a 35 ≤ K) (hn : a 36 ≤ N)
    (hz : a 37 ≤ N * K) (ho : a 38 ≤ N * K)
    (hr : ∀ r, a (tR r) ≤ b r) : a ≤ layout M N K b := by
  intro t
  unfold layout
  split_ifs with hh h35 h36 h37
  · have he : tR ⟨t.val - 41, by have := t.isLt; omega⟩ = t := by
      apply Fin.ext; simp only [tR_val]; omega
    simpa only [he] using hr ⟨t.val - 41, by have := t.isLt; omega⟩
  · subst t; exact hk
  · subst t; exact hn
  · rcases h37 with rfl | rfl
    · exact hz
    · exact ho
  · exact ht t

/-- A ring instruction preserves a layout if its destination can hold one ring word. -/
theorem layout_op (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (o : Op) (d s c : Fin 64)
    (hd : N * K ≤ b d) :
    Cert (MVM.compile (.op o d s c)) (layout M N K b) (layout M N K b)
      (operationBound M N K M) := by
  obtain ⟨hc, hr⟩ := compile_op_scratch_ready M N K o d s c _ h
  apply hc.mono le_rfl
  · apply le_layout M N K b _ hr.top hr.templateK hr.templateN hr.zeros.le hr.ones
    intro r
    by_cases he : r = d
    · subst r; rw [operationResult_destination]; exact hd
    · rw [operationResult_other _ _ _ _ _ _ _ he, cleanWork_register, layout_register]
  · exact operationBound_mono le_rfl le_rfl le_rfl (h.top _)

theorem layout_copy (M N K : ℕ) (b : Fin 64 → ℕ)
    (ht : ∀ t, layout M N K b t ≤ M) (d s : Fin 64) (hd : b s ≤ b d) :
    Cert (MVM.compile (.cp d s)) (layout M N K b) (layout M N K b) (2 * M + 5) := by
  have h := compile_cp_any d s (layout M N K b) M ht
  apply h.mono le_rfl
  · intro t
    by_cases he : t = tR d
    · subst t; simpa using hd
    · simp [Function.update_of_ne he]
  · omega

theorem layout_tail (M N K : ℕ) (b : Fin 64 → ℕ)
    (ht : ∀ t, layout M N K b t ≤ M) (r : Fin 64) :
    Cert (MVM.compile (.tl r)) (layout M N K b) (layout M N K b) (2 * M + 5) :=
  (compile_tl_cert r _ M ht).mono le_rfl (tailB_le (tR r) _) (by omega)

/-- A fixed length envelope remains valid for every iteration of the actual compiled loop. -/
theorem rep_fixed (c : Fin 64) (body : Code) (a : Fin 105 → ℕ) (M R T : ℕ)
    (ht : ∀ t, a t ≤ M) (hc : a (tR c) ≤ R) (hb : Cert (compile body) a a T) :
    Cert (compile (.rep c body)) a a (R * (2 * M + T + 4) + 2) :=
  rep_family c body (fun _ ↦ a) R T a le_rfl hc
    (fun _ _ ↦ hb.mono (tailB_le (tR c) _) le_rfl le_rfl)
    M (fun _ _ ↦ supB_le_of ht) (fun _ _ ↦ le_rfl)

end AdvancedEncryption.ExpLUT.Prog.KeyTime
