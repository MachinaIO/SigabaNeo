import PE.Impl.ExpLUT.Prog.KeyTimePublicKernels

/-! Runtime composition of the actual digit and correction proposal. -/
set_option exponentiation.threshold 1000
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib

noncomputable def proposalReady (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (keyDigitsResult b) 17 (keyDigitsResult b rDq)

noncomputable def proposalResult (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (correctionBase (2 ^ 120) (proposalReady b)) 18
    ((Enum.list (α := PIdxD Dc)).length * (Dc.N * Dc.K))

theorem proposalReady_inputs (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b)) :
    RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K (proposalReady b)) := by
  have hi := keyDigitsResult_inputs b h
  exact hi.update_layout 17 _ (by simpa using hi.top (tR rDq))

/-- Actual public-map evaluation, digit save and complete correction traversal. -/
theorem compile_proposalC_Dc (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K) :
    Cert (MVM.compile (proposalC Dc)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K (proposalResult b)) (2 ^ 498) := by
  have hi := keyDigitsResult_inputs b h
  have hf := keyDigitsResult_fields b
  have p0 := compile_keyDigitsC_Dc b h hb hz
  have p1 := layout_copy_update (2 ^ 120) Dc.N Dc.K (keyDigitsResult b) hi.top 17 rDq
  have p2 := compile_correctionC_Dc (proposalReady b) (proposalReady_inputs b h)
    (by simpa [proposalReady, hf.2.1] using hb)
    (by simpa [proposalReady, hf.2.2.1] using hz)
    (by simpa [proposalReady, hf.2.2.2.1] using h.ring)
    (by simpa [proposalReady, hf.2.2.2.2.1] using h.ring)
  exact (p0.seq (p1.seq p2)).mono le_rfl le_rfl (by norm_num)

theorem proposalResult_inputs (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b)) :
    RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K (proposalResult b)) := by
  apply (correctionBase_inputs _ _ _ _ (proposalReady_inputs b h)).update_layout
  calc
    _ ≤ 2 ^ 66 * (Dc.N * Dc.K) := Nat.mul_le_mul_right _ correction_counts_Dc.2.2
    _ ≤ 2 ^ 120 := by norm_num [Dc, Dims.N, Params.en, Params.Kc]

theorem correctionSaved_fields (c : Fin 64 → ℕ) (n : ℕ) :
    let d := Function.update (correctionBase (2 ^ 120) (Function.update c 17 (c rDq))) 18 n
    d 17 = c rDq ∧ d 18 = n ∧ d rB1 = c rB1 ∧ d rZ = c rZ := by
  simp [correctionBase, correctionScratch]

theorem proposalResult_fields (b : Fin 64 → ℕ) :
    proposalResult b 17 = (setting Dc).E.W * (Dc.K * (Dc.N * Dc.K)) ∧
    proposalResult b 18 = (Enum.list (α := PIdxD Dc)).length * (Dc.N * Dc.K) ∧
    proposalResult b rB1 = b rB1 ∧ proposalResult b rZ = b rZ := by
  have hf := keyDigitsResult_fields b
  have hg := correctionSaved_fields (keyDigitsResult b)
    ((Enum.list (α := PIdxD Dc)).length * (Dc.N * Dc.K))
  exact ⟨hg.1.trans hf.1, hg.2.1, hg.2.2.1.trans hf.2.1, hg.2.2.2.trans hf.2.2.1⟩

theorem proposalResult_source_bound (b : Fin 64 → ℕ) :
    proposalResult b 18 + proposalResult b 17 ≤ 2 ^ 120 := by
  have hf := proposalResult_fields b
  have hw : (setting Dc).E.W = 2 ^ 22 := by change 2 ^ Dc.b = _; norm_num [Dc, Params.bc]
  have hn : Dc.N = 2 ^ 24 := by norm_num [Dc, Dims.N, Params.en]
  have hk : Dc.K = 2 ^ 16 := by norm_num [Dc, Params.Kc]
  calc
    _ = (Enum.list (α := PIdxD Dc)).length * (Dc.N * Dc.K) +
        (setting Dc).E.W * (Dc.K * (Dc.N * Dc.K)) := congrArg₂ (· + ·) hf.2.1 hf.1
    _ ≤ 2 ^ 66 * (Dc.N * Dc.K) + (setting Dc).E.W * (Dc.K * (Dc.N * Dc.K)) := by
      gcongr; exact correction_counts_Dc.2.2
    _ ≤ 2 ^ 120 := by rw [hw, hn, hk]; norm_num

end AdvancedEncryption.ExpLUT.Prog.KeyTime
