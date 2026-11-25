import PE.Impl.ExpLUT.Prog.KeyTimeQueueArithmetic

/-! Exact fetched words and linear accumulation for statically selected key coordinates. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

theorem Cert.seq_assoc {k : ℕ} {p q r : XProg k} {a b : Fin k → ℕ} {T : ℕ}
    (h : Cert (.seq (.seq p q) r) a b T) : Cert (.seq p (.seq q r)) a b T := by
  refine ⟨h.len, ?_⟩
  simpa only [XProg.timeBoundT, XProg.lenBoundT, Nat.add_assoc] using h.time

theorem layout_nat_update (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (r u : Fin 64) (hru : r ≠ u)
    (n : ℕ) (hu : b u = 1) (hn : n ≤ M) :
    Cert (MVM.compile (natC r u n)) (layout M N K b)
      (layout M N K (Function.update b r n)) ((32 * n + 4) * (2 * M + 5)) := by
  have hp := compile_natC r u hru n M (layout M N K b) h.top (by simpa using hu) hn
  apply hp.mono le_rfl _ le_rfl
  apply le_layout M N K _ _ (natResult_top _ _ _ _ h.top hn)
  · rw [natResult_low _ _ _ _ 35 (by decide)]; exact h.templateK
  · rw [natResult_low _ _ _ _ 36 (by decide)]; exact h.templateN
  · rw [natResult_low _ _ _ _ 37 (by decide)]; exact h.zeros.le
  · rw [natResult_low _ _ _ _ 38 (by decide)]; exact h.ones
  · intro q; simp [natResult_register, Function.update_apply]

def fetchTime (M N K I : ℕ) :=
  (32 * (I * (N * K)) + 6) * (2 * M + 5) + 2 * moveAllowance M

theorem compile_fetchRingC (M N K I j : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hb : b rB1 = 1)
    (hz : b rZ ≤ N * K) (hcopy : b 0 ≤ b 1) (hoff : I * (N * K) ≤ b 2) (hj : j ≤ I) :
    Cert (MVM.compile (fetchRingC N K j)) (layout M N K b)
      (layout M N K (Function.update b 3 (N * K))) (fetchTime M N K I) := by
  have hjb : j * (N * K) ≤ b 2 := (Nat.mul_le_mul_right _ hj).trans hoff
  have hjM : j * (N * K) ≤ M := hjb.trans (by simpa using h.top (tR 2))
  have p0 := (layout_nat_update M N K b h 2 rB1 (by decide) _ hb hjM).mono le_rfl
    (layout_mono _ _ _ (cap_update_le b 2 _ hjb)) le_rfl
  have p1 := layout_copy M N K b h.top 1 0 hcopy
  have p2 := layout_drop M N K b h 1 2 (by decide)
  have p3 := layout_copy_cap M N K b h.top 3 rZ (N * K) hz
  have hi := h.update_layout 3 (N * K) h.ring
  have p4 := layout_moveR M N K (Function.update b 3 (N * K)) hi 3 1 (by decide)
  rw [fetchRingC]
  apply (p0.seq (p1.seq (p2.seq (p3.seq p4)))).mono le_rfl le_rfl
  unfold fetchTime
  have hjk := Nat.mul_le_mul_right (N * K) hj
  nlinarith

def gatherStepTime (M N K I : ℕ) := fetchTime M N K I + appendAllowance M

theorem compile_gatherStep (M N K I j : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hb : b rB1 = 1)
    (hz : b rZ ≤ N * K) (hcopy : b 0 ≤ b 1) (hoff : I * (N * K) ≤ b 2)
    (hword : N * K ≤ b 3) (hj : j ≤ I) (hs : b 4 + N * K ≤ M) :
    Cert (MVM.compile (.seq (fetchRingC N K j) (.app 4 3))) (layout M N K b)
      (layout M N K (Function.update b 4 (b 4 + N * K))) (gatherStepTime M N K I) := by
  have p0 := compile_fetchRingC M N K I j b h hb hz hcopy hoff hj
  have hi := h.update_layout 3 (N * K) h.ring
  have p1 := layout_append_uniform M N K (Function.update b 3 (N * K)) hi.top 4 3 (by simpa using hs)
  apply (p0.seq p1).mono le_rfl _ le_rfl
  apply layout_mono
  intro r
  by_cases h4 : r = 4
  · subst r; simp
  · by_cases h3 : r = 3
    · subst r; simpa using hword
    · simp [Function.update_of_ne h4, Function.update_of_ne h3]

theorem compile_gatherAppendC (M N K I : ℕ) (js : List ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hb : b rB1 = 1)
    (hz : b rZ ≤ N * K) (hcopy : b 0 ≤ b 1) (hoff : I * (N * K) ≤ b 2)
    (hword : N * K ≤ b 3) (hj : ∀ j ∈ js, j ≤ I) (hs : b 4 + js.length * (N * K) ≤ M) :
    Cert (MVM.compile (gatherAppendC N K js)) (layout M N K b)
      (layout M N K (Function.update b 4 (b 4 + js.length * (N * K))))
      (js.length * gatherStepTime M N K I + (2 * M + 5)) := by
  induction js generalizing b with
  | nil =>
    simpa [gatherAppendC] using (compile_nop (layout M N K b) M h.top).mono
      le_rfl le_rfl (show 2 * (M + 1) + 3 ≤ 2 * M + 5 by omega)
  | cons j js ih =>
    have hs0 : b 4 + N * K ≤ M := by simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hs; omega
    have p0 := compile_gatherStep M N K I j b h hb hz hcopy hoff hword (hj j (by simp)) hs0
    let c := Function.update b 4 (b 4 + N * K)
    have hi := h.update_layout 4 _ hs0
    have p1 := ih c hi (by simpa [c] using hb) (by simpa [c] using hz)
      (by simpa [c] using hcopy) (by simpa [c] using hoff) (by simpa [c] using hword)
      (fun x hx ↦ hj x (by simp [hx]))
      (by simpa [c, List.length_cons, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hs)
    have he : Function.update c 4 (c 4 + js.length * (N * K)) =
        Function.update b 4 (b 4 + (j :: js).length * (N * K)) := by
      simp [c, List.length_cons, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    rw [he] at p1
    have hf := (p0.seq p1).seq_assoc
    exact hf.mono le_rfl le_rfl (by simp [List.length_cons, Nat.add_mul]; omega)

def gatherBase (M : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update (Function.update b 1 M) 2 M) 3 M

theorem gatherBase_inputs (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) :
    RingInputs M N K (layout M N K (gatherBase M b)) :=
  ((h.update_layout 1 M le_rfl).update_layout 2 M le_rfl).update_layout 3 M le_rfl

def gatherTime (M N K I Q : ℕ) := 2 * (2 * M + 5) + Q * gatherStepTime M N K I

theorem compile_gatherC (M N K I : ℕ) (js : List ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hb : b rB1 = 1) (hz : b rZ ≤ N * K)
    (hoff : I * (N * K) ≤ M) (hj : ∀ j ∈ js, j ≤ I) (hs : js.length * (N * K) ≤ M) :
    Cert (MVM.compile (gatherC N K js)) (layout M N K b)
      (layout M N K (Function.update (gatherBase M b) 4 (js.length * (N * K))))
      (gatherTime M N K I js.length) := by
  let c := gatherBase M b
  have hi := gatherBase_inputs M N K b h
  have p0 := layout_clear_update M N K c hi.top 4
  have hi0 := hi.update_layout 4 0 (Nat.zero_le _)
  have p1 := compile_gatherAppendC M N K I js (Function.update c 4 0) hi0
    (by simpa [c, gatherBase] using hb) (by simpa [c, gatherBase] using hz)
    (by simpa [c, gatherBase] using h.top (tR 0))
    (by simpa [c, gatherBase] using hoff) (by simpa [c, gatherBase] using h.ring)
    hj (by simpa using hs)
  simp only [Function.update_self, zero_add, cap_reset] at p1
  rw [gatherC]
  apply (p0.seq p1).mono _ le_rfl (by unfold gatherTime; omega)
  apply layout_mono
  intro r
  have ht : b r ≤ M := by simpa using h.top (tR r)
  by_cases h1 : r = 1 <;> by_cases h2 : r = 2 <;> by_cases h3 : r = 3 <;>
    simp_all [c, gatherBase]

def familyResult (M N K : ℕ) (js : List ℕ) (src dst : Fin 64) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update (gatherBase M (Function.update b 0 (b src)))
    4 (js.length * (N * K))) dst (js.length * (N * K))

/-- Loading a saved family includes the source copy, exact gathering and destination copy. -/
theorem compile_loadFamilyC (M N K I : ℕ) (js : List ℕ) (src dst : Fin 64) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hb : b rB1 = 1) (hz : b rZ ≤ N * K)
    (hoff : I * (N * K) ≤ M) (hj : ∀ j ∈ js, j ≤ I) (hs : js.length * (N * K) ≤ M) :
    Cert (MVM.compile (loadFamilyC N K src dst js)) (layout M N K b)
      (layout M N K (familyResult M N K js src dst b))
      (2 * (2 * M + 5) + gatherTime M N K I js.length) := by
  let c := Function.update b 0 (b src)
  let d := Function.update (gatherBase M c) 4 (js.length * (N * K))
  have hi : RingInputs M N K (layout M N K c) :=
    h.update_layout 0 _ (by simpa using h.top (tR src))
  have hd : RingInputs M N K (layout M N K d) :=
    (gatherBase_inputs M N K c hi).update_layout 4 _ hs
  have p0 := layout_copy_update M N K b h.top 0 src
  have p1 := compile_gatherC M N K I js c hi (by simpa [c] using hb)
    (by simpa [c] using hz) hoff hj hs
  have p2 := layout_copy_update M N K d hd.top dst 4
  simp only [d, Function.update_self] at p2
  rw [loadFamilyC, saveQueueC]
  exact (p0.seq (p1.seq p2)).mono le_rfl le_rfl (by omega)

theorem familyResult_inputs (M N K : ℕ) (js : List ℕ) (src dst : Fin 64) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hs : js.length * (N * K) ≤ M) :
    RingInputs M N K (layout M N K (familyResult M N K js src dst b)) :=
  (((gatherBase_inputs M N K (Function.update b 0 (b src))
    (h.update_layout 0 _ (by simpa using h.top (tR src)))).update_layout 4 _ hs).update_layout dst _ hs)

@[simp] theorem familyResult_destination (M N K : ℕ) (js : List ℕ)
    (src dst : Fin 64) (b : Fin 64 → ℕ) :
    familyResult M N K js src dst b dst = js.length * (N * K) := by simp [familyResult]

set_option exponentiation.threshold 1000 in
theorem gatherTime_concrete :
    2 * (2 * 2 ^ 120 + 5) + gatherTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 66) (2 ^ 66)
      ≤ 2 ^ 316 := by
  norm_num [gatherTime, gatherStepTime, fetchTime, moveAllowance, appendAllowance]

/-- Concrete saved-family loading: indices and the number of selected coordinates are bounded. -/
theorem compile_loadFamilyC_concrete (js : List ℕ) (src dst : Fin 64) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hb : b rB1 = 1) (hz : b rZ ≤ 2 ^ 24 * 2 ^ 16)
    (hj : ∀ j ∈ js, j ≤ 2 ^ 66) (hl : js.length ≤ 2 ^ 66) :
    Cert (MVM.compile (loadFamilyC (2 ^ 24) (2 ^ 16) src dst js))
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) (familyResult (2 ^ 120) (2 ^ 24) (2 ^ 16) js src dst b))
      (2 ^ 316) := by
  have hs : js.length * (2 ^ 24 * 2 ^ 16) ≤ 2 ^ 120 :=
    (Nat.mul_le_mul_right _ hl).trans (by norm_num)
  have hp := compile_loadFamilyC (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 66) js src dst b h hb hz
    (by norm_num) hj hs
  apply hp.mono le_rfl le_rfl
  apply le_trans _ gatherTime_concrete
  unfold gatherTime
  gcongr

end AdvancedEncryption.ExpLUT.Prog.KeyTime
