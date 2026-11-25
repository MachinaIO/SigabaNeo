import PE.Impl.ExpLUT.Prog.KeyTimeCorrectionCoord

/-! Runtime of the complete correction traversal with linear output accumulation. -/
set_option exponentiation.threshold 1000
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib

def correctionScratch : List (Fin 64) := [0, 1, 2, 3, 4, rQa, rQb, rIa, rQc, rQk, 56]

def correctionBase (M : ℕ) (b : Fin 64 → ℕ) (r : Fin 64) : ℕ :=
  if r ∈ correctionScratch then M else b r

theorem correctionBase_inputs (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) :
    RingInputs M N K (layout M N K (correctionBase M b)) := by
  apply layout_inputs
  · intro r; unfold correctionBase; split_ifs
    · exact le_rfl
    · simpa using h.top (tR r)
  · exact h.ring
  · exact h.dimension
  · exact h.width

theorem le_correctionBase (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) : b ≤ correctionBase M b := by
  intro r; unfold correctionBase; split_ifs
  · simpa using h.top (tR r)
  · exact le_rfl

theorem correctionCoordResult_le (q : PIdxD Dc) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hs : ∀ r ∈ correctionScratch, b r = 2 ^ 120) :
    correctionCoordResult Dc (2 ^ 120) q b ≤ b := by
  have hi := correctionCoordResult_inputs Dc (2 ^ 120) q b h
    (by norm_num [Dc, Dims.N, Params.en, Params.Kc])
    (by norm_num [Dc, Dims.N, Params.en])
  intro r
  by_cases hr : r ∈ correctionScratch
  · rw [hs r hr]; simpa using hi.top (tR r)
  · exact (correctionCoordResult_other Dc (2 ^ 120) q b r hr).le

def correctionStepTime := 2 ^ 416 + appendAllowance (2 ^ 120)

theorem compile_correctionStep (q : PIdxD Dc) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K)
    (hx : Dc.N * Dc.K ≤ b rQx) (hy : Dc.N * Dc.K ≤ b rQy)
    (hw : ∀ r ∈ correctionScratch, b r = 2 ^ 120)
    (hs : b 18 + Dc.N * Dc.K ≤ 2 ^ 120) :
    Cert (MVM.compile (.seq (correctionCoordC Dc q) (.app 18 rIa)))
      (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K (Function.update b 18 (b 18 + Dc.N * Dc.K)))
      correctionStepTime := by
  let c := correctionCoordResult Dc (2 ^ 120) q b
  have hi := correctionCoordResult_inputs Dc (2 ^ 120) q b h
    (by norm_num [Dc, Dims.N, Params.en, Params.Kc])
    (by norm_num [Dc, Dims.N, Params.en])
  have ho : c 18 = b 18 := correctionCoordResult_other Dc (2 ^ 120) q b 18 (by decide)
  have ha : c rIa = Dc.N * Dc.K := correctionCoordResult_acc Dc (2 ^ 120) q b
  have p0 := compile_correctionCoordC_Dc q b h hb hz hx hy
  have p1 := layout_append_uniform (2 ^ 120) Dc.N Dc.K c hi.top 18 rIa
    (by rw [ho, ha]; exact hs)
  have hl := correctionCoordResult_le q b h hw
  apply (p0.seq p1).mono le_rfl _ le_rfl
  apply layout_mono
  intro r
  by_cases hr : r = 18
  · subst r; simp only [Function.update_self, ho, ha]; exact le_rfl
  · simp only [Function.update_of_ne hr]; exact hl r

theorem compile_correctionAppendC (qs : List (PIdxD Dc)) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K)
    (hx : Dc.N * Dc.K ≤ b rQx) (hy : Dc.N * Dc.K ≤ b rQy)
    (hw : ∀ r ∈ correctionScratch, b r = 2 ^ 120)
    (hs : b 18 + qs.length * (Dc.N * Dc.K) ≤ 2 ^ 120) :
    Cert (MVM.compile (correctionAppendC Dc qs)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K
        (Function.update b 18 (b 18 + qs.length * (Dc.N * Dc.K))))
      (qs.length * correctionStepTime + (2 * 2 ^ 120 + 5)) := by
  induction qs generalizing b with
  | nil =>
    simpa [correctionAppendC] using (compile_nop (layout (2 ^ 120) Dc.N Dc.K b)
      (2 ^ 120) h.top).mono le_rfl le_rfl (show 2 * (2 ^ 120 + 1) + 3 ≤ 2 * 2 ^ 120 + 5 by omega)
  | cons q qs ih =>
    have hs0 : b 18 + Dc.N * Dc.K ≤ 2 ^ 120 := by
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hs; omega
    have p0 := compile_correctionStep q b h hb hz hx hy hw hs0
    let c := Function.update b 18 (b 18 + Dc.N * Dc.K)
    have hc := h.update_layout 18 _ hs0
    have p1 := ih c hc (by simpa [c] using hb) (by simpa [c] using hz)
      (by simpa [c] using hx) (by simpa [c] using hy)
      (by intro r hr
          have hn : r ≠ 18 := by intro he; subst r; norm_num [correctionScratch] at hr
          simpa [c, Function.update_of_ne hn] using hw r hr)
      (by simpa [c, List.length_cons, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using hs)
    have he : Function.update c 18 (c 18 + qs.length * (Dc.N * Dc.K)) =
        Function.update b 18 (b 18 + (q :: qs).length * (Dc.N * Dc.K)) := by
      simp [c, List.length_cons, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    rw [he] at p1
    exact (p0.seq p1).seq_assoc.mono le_rfl le_rfl
      (by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega)

/-- Initial clear and the entire enumeration of corrected coordinates. -/
theorem compile_correctionClear (qs : List (PIdxD Dc)) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K)
    (hx : Dc.N * Dc.K ≤ b rQx) (hy : Dc.N * Dc.K ≤ b rQy)
    (hs : qs.length * (Dc.N * Dc.K) ≤ 2 ^ 120) :
    Cert (MVM.compile (.seq (.clr 18) (correctionAppendC Dc qs))) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K (Function.update (correctionBase (2 ^ 120) b) 18
        (qs.length * (Dc.N * Dc.K))))
      ((2 * 2 ^ 120 + 5) + (qs.length * correctionStepTime + (2 * 2 ^ 120 + 5))) := by
  let c := correctionBase (2 ^ 120) b
  have hc := correctionBase_inputs (2 ^ 120) Dc.N Dc.K b h
  have p0 := layout_clear_update (2 ^ 120) Dc.N Dc.K c hc.top 18
  have p1 := compile_correctionAppendC qs (Function.update c 18 0)
    (hc.update_layout 18 0 (by omega))
    (by simpa [c, correctionBase, correctionScratch] using hb)
    (by simpa [c, correctionBase, correctionScratch] using hz)
    (by simpa [c, correctionBase, correctionScratch] using hx)
    (by simpa [c, correctionBase, correctionScratch] using hy)
    (by intro r hr
        have hn : r ≠ 18 := by intro he; subst r; norm_num [correctionScratch] at hr
        simp [Function.update_of_ne hn, c, correctionBase, hr])
    (by simpa using hs)
  simp only [Function.update_self, zero_add, cap_reset] at p1
  exact (p0.seq p1).mono (layout_mono _ _ _ (le_correctionBase _ _ _ b h)) le_rfl le_rfl

/-- The complete actual traversal, including the initial output clear. -/
theorem compile_correctionC_Dc (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K)
    (hx : Dc.N * Dc.K ≤ b rQx) (hy : Dc.N * Dc.K ≤ b rQy) :
    Cert (MVM.compile (correctionC Dc)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K (Function.update (correctionBase (2 ^ 120) b) 18
        ((Enum.list (α := PIdxD Dc)).length * (Dc.N * Dc.K)))) (2 ^ 484) := by
  have hl := correction_counts_Dc.2.2
  have hn : Dc.N = 2 ^ 24 := by norm_num [Dc, Dims.N, Params.en]
  have hk : Dc.K = 2 ^ 16 := by norm_num [Dc, Params.Kc]
  have hs : (Enum.list (α := PIdxD Dc)).length * (Dc.N * Dc.K) ≤ 2 ^ 120 := by
    calc
      _ ≤ 2 ^ 66 * (Dc.N * Dc.K) := Nat.mul_le_mul_right _ hl
      _ ≤ 2 ^ 120 := by rw [hn, hk]; norm_num
  have ht : (2 * 2 ^ 120 + 5) +
      ((Enum.list (α := PIdxD Dc)).length * correctionStepTime + (2 * 2 ^ 120 + 5)) ≤ 2 ^ 484 := by
    calc
      _ ≤ (2 * 2 ^ 120 + 5) + (2 ^ 66 * correctionStepTime + (2 * 2 ^ 120 + 5)) := by gcongr
      _ ≤ 2 ^ 484 := by norm_num [correctionStepTime, appendAllowance]
  exact (compile_correctionClear Enum.list b h hb hz hx hy hs).mono le_rfl le_rfl ht

end AdvancedEncryption.ExpLUT.Prog.KeyTime
