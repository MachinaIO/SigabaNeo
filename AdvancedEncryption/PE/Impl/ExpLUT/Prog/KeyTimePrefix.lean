import PE.Impl.ExpLUT.Prog.KeyTimeNegativeReady
/-! Actual prefix extraction and the evaluator-matrix suffix of a positive coefficient row. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

def prefixResult (n : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update (Function.update b 2 n) 3 n) 0 n

def prefixTime (M n : ℕ) := (32 * n + 6) * (2 * M + 5) + moveAllowance M

theorem prefixResult_inputs (M N K n : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hn : n ≤ M) :
    RingInputs M N K (layout M N K (prefixResult n b)) :=
  ((h.update_layout 2 n hn).update_layout 3 n hn).update_layout 0 n hn

theorem compile_prefixC (M N K n : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hb : b rB1 = 1) (hn : n ≤ M) :
    Cert (MVM.compile (prefixC n)) (layout M N K b)
      (layout M N K (prefixResult n b)) (prefixTime M n) := by
  let c := Function.update b 2 n
  let d := Function.update c 3 n
  have hc := h.update_layout 2 n hn
  have hd := hc.update_layout 3 n hn
  have p0 := layout_nat_update M N K b h 2 rB1 (by decide) n hb hn
  have p1 := layout_copy_update M N K c hc.top 3 2
  have p2 := layout_move M N K d hd 3 0 2 (by decide)
  have p3 := layout_copy_update M N K d hd.top 0 3
  have he : c 2 = n := by simp [c]
  rw [he] at p1
  have he' : d 3 = n := by simp [d]
  rw [he'] at p3
  have hp := (p1.seq p2).seq p3
  rw [prefixC]
  exact (p0.seq hp).mono le_rfl le_rfl (by unfold prefixTime; ring_nf; omega)

def appendAFResult (N K : ℕ) (first : Bool) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update
    (if first then prefixResult ((2 * K) * (N * K)) b
      else Function.update b 6 ((2 * K) * (N * K)))
    4 (b 4 + (2 * K) * (N * K))

def appendAFTime (M N K : ℕ) := prefixTime M ((2 * K) * (N * K)) + appendAllowance M

theorem compile_appendAFC (M N K : ℕ) (first : Bool) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hb : b rB1 = 1)
    (hs : b 4 + (2 * K) * (N * K) ≤ M) :
    Cert (MVM.compile (appendAFC N K first)) (layout M N K b)
      (layout M N K (appendAFResult N K first b)) (appendAFTime M N K) := by
  have hn : (2 * K) * (N * K) ≤ M := by omega
  cases first with
  | false =>
    let c := Function.update b 6 ((2 * K) * (N * K))
    have hc := h.update_layout 6 _ hn
    have p0 := layout_nat_update M N K b h 6 rB1 (by decide) _ hb hn
    have p1 := layout_append_uniform M N K c hc.top 4 6 (by simpa [c] using hs)
    have ht : (32 * ((2 * K) * (N * K)) + 4) * (2 * M + 5) + appendAllowance M ≤
        appendAFTime M N K := by unfold appendAFTime prefixTime; nlinarith
    simpa only [appendAFTime, MVM.compile, appendAFC, Bool.false_eq_true, ↓reduceIte, appendAFResult,
      c, Function.update_self, Function.update_of_ne (by decide : (4 : Fin 64) ≠ 6)] using
        (p0.seq p1).mono le_rfl le_rfl ht
  | true =>
    let c := prefixResult ((2 * K) * (N * K)) b
    have hc := prefixResult_inputs M N K _ b h hn
    have p0 := compile_prefixC M N K _ b h hb hn
    have p1 := layout_append_uniform M N K c hc.top 4 0 (by simpa [c, prefixResult] using hs)
    simpa only [appendAFTime, MVM.compile, appendAFC, ↓reduceIte, appendAFResult, c, prefixResult,
      Function.update_self, Function.update_of_ne (by decide : (4 : Fin 64) ≠ 0),
      Function.update_of_ne (by decide : (4 : Fin 64) ≠ 3),
      Function.update_of_ne (by decide : (4 : Fin 64) ≠ 2)] using p0.seq p1

theorem appendAFResult_inputs (M N K : ℕ) (first : Bool) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hs : b 4 + (2 * K) * (N * K) ≤ M) :
    RingInputs M N K (layout M N K (appendAFResult N K first b)) := by
  have hn : (2 * K) * (N * K) ≤ M := by omega
  cases first
  · exact (h.update_layout 6 _ hn).update_layout 4 _ hs
  · exact (prefixResult_inputs M N K _ b h hn).update_layout 4 _ hs

theorem appendAFResult_length (N K : ℕ) (first : Bool) (b : Fin 64 → ℕ) :
    appendAFResult N K first b 4 = b 4 + (2 * K) * (N * K) := by simp [appendAFResult]

theorem appendAFResult_other (N K : ℕ) (first : Bool) (b : Fin 64 → ℕ) (r : Fin 64)
    (h0 : r ≠ 0) (h2 : r ≠ 2) (h3 : r ≠ 3) (h4 : r ≠ 4) (h6 : r ≠ 6) :
    appendAFResult N K first b r = b r := by
  cases first <;> simp [appendAFResult, prefixResult, Function.update_of_ne h0,
    Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h4,
    Function.update_of_ne h6]

set_option exponentiation.threshold 1000 in
theorem appendAFTime_concrete : appendAFTime (2 ^ 120) (2 ^ 24) (2 ^ 16) ≤ 2 ^ 246 := by
  norm_num [appendAFTime, prefixTime, moveAllowance, appendAllowance]

theorem compile_appendAFC_concrete (first : Bool) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hb : b rB1 = 1) (hs : b 4 + (2 * 2 ^ 16) * (2 ^ 24 * 2 ^ 16) ≤ 2 ^ 120) :
    Cert (MVM.compile (appendAFC (2 ^ 24) (2 ^ 16) first))
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) (appendAFResult (2 ^ 24) (2 ^ 16) first b))
      (2 ^ 246) :=
  (compile_appendAFC (2 ^ 120) (2 ^ 24) (2 ^ 16) first b h hb hs).mono
    le_rfl le_rfl appendAFTime_concrete

set_option exponentiation.threshold 1000 in
theorem prefixTime_concrete (n : ℕ) (hn : n ≤ 2 ^ 120) : prefixTime (2 ^ 120) n ≤ 2 ^ 249 := by
  unfold prefixTime
  calc
    _ ≤ (32 * 2 ^ 120 + 6) * (2 * 2 ^ 120 + 5) + moveAllowance (2 ^ 120) := by gcongr
    _ ≤ 2 ^ 249 := by norm_num [moveAllowance]

end AdvancedEncryption.ExpLUT.Prog.KeyTime
