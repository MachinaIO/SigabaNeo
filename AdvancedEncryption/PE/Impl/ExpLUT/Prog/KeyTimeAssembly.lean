import PE.Impl.ExpLUT.Prog.KeyTimeProposal
/-! Runtime of key assembly and the complete proposal-key program. -/
set_option exponentiation.threshold 1000
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib

def assemblyReady (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update b 0 (b 18 + b 17)

def assemblyResult (js : List ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update (gatherBase (2 ^ 120) (assemblyReady b))
    4 (js.length * (Dc.N * Dc.K))) 19 (js.length * (Dc.N * Dc.K))

theorem assemblyReady_inputs (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hs : b 18 + b 17 ≤ 2 ^ 120) :
    RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K (assemblyReady b)) :=
  h.update_layout 0 _ hs

theorem assemblyResult_inputs (js : List ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hs : b 18 + b 17 ≤ 2 ^ 120) (hl : js.length * (Dc.N * Dc.K) ≤ 2 ^ 120) :
    RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K (assemblyResult js b)) :=
  (((gatherBase_inputs _ _ _ _ (assemblyReady_inputs b h hs)).update_layout 4 _ hl).update_layout 19 _ hl)

theorem compile_assembleWords (js : List ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K)
    (hs : b 18 + b 17 ≤ 2 ^ 120)
    (hj : ∀ j ∈ js, j ≤ 2 ^ 66) (hl : js.length ≤ 2 ^ 66) :
    Cert (MVM.compile (.seq (.cp 0 18) (.seq (.app 0 17)
      (saveQueueC (gatherC Dc.N Dc.K js) 19)))) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K (assemblyResult js b)) (2 ^ 318) := by
  let c := Function.update b 0 (b 18)
  have hc := h.update_layout 0 (b 18) (by simpa using h.top (tR 18))
  have p0 := layout_copy_update (2 ^ 120) Dc.N Dc.K b h.top 0 18
  have p1 := layout_append_uniform (2 ^ 120) Dc.N Dc.K c hc.top 0 17 (by simpa [c] using hs)
  have he : Function.update c 0 (c 0 + c 17) = assemblyReady b := by
    simp [c, assemblyReady]
  rw [he] at p1
  have ha := assemblyReady_inputs b h hs
  have hn : Dc.N = 2 ^ 24 := by norm_num [Dc, Dims.N, Params.en]
  have hk : Dc.K = 2 ^ 16 := by norm_num [Dc, Params.Kc]
  have hlen : js.length * (Dc.N * Dc.K) ≤ 2 ^ 120 := by
    calc
      _ ≤ 2 ^ 66 * (Dc.N * Dc.K) := Nat.mul_le_mul_right _ hl
      _ ≤ 2 ^ 120 := by rw [hn, hk]; norm_num
  have p2 := compile_gatherC (2 ^ 120) Dc.N Dc.K (2 ^ 66) js (assemblyReady b) ha
    (by change b rB1 = 1; exact hb) (by change b rZ ≤ _; exact hz)
    (by rw [hn, hk]; norm_num) hj hlen
  have hg := (gatherBase_inputs _ _ _ _ ha).update_layout 4 _ hlen
  have p3 := layout_copy_update (2 ^ 120) Dc.N Dc.K _ hg.top 19 4
  simp only [Function.update_self] at p3
  have ht : gatherTime (2 ^ 120) Dc.N Dc.K (2 ^ 66) js.length ≤ 2 ^ 316 := by
    rw [hn, hk]
    have hmax : gatherTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 66) (2 ^ 66) ≤ 2 ^ 316 := by
      have := gatherTime_concrete; omega
    apply le_trans _ hmax
    unfold gatherTime; gcongr
  have all := p0.seq (p1.seq ((p2.mono le_rfl le_rfl ht).seq p3))
  exact all.mono le_rfl le_rfl (by norm_num [appendAllowance])

open Classical in
noncomputable def assemblyIndices (D : Dims) : List ℕ :=
  Enum.list.map (Enum.index ∘ assemblySelection D)

theorem assemblyIndices_length (D : Dims) :
    (assemblyIndices D).length = (Enum.list (α := KColt D)).length := by
  simp only [assemblyIndices, List.length_map, KColt, KCol, BCol, Col, Wb, Jh,
    len_sum, Enum.length_prod, len_fin]
  simp only [setting_τ, setting_W]

theorem assemblyIndices_bound (D : Dims) (I : ℕ)
    (hi : (Enum.list (α := AssemblySource D)).length ≤ I) :
    ∀ j ∈ assemblyIndices D, j ≤ I := by
  intro j hj
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hj
  exact (Enum.index_lt (assemblySelection D x)).le.trans hi

theorem assembleC_eq (D : Dims) : assembleC D =
    .seq (.cp 0 18) (.seq (.app 0 17)
      (saveQueueC (gatherC D.N D.K (assemblyIndices D)) 19)) := by
  simp only [assembleC, assemblyIndices, Function.comp_def, index_classical]

theorem assemblyIndices_bounds :
    (∀ j ∈ assemblyIndices Dc, j ≤ 2 ^ 66) ∧ (assemblyIndices Dc).length ≤ 2 ^ 66 :=
  ⟨assemblyIndices_bound Dc _ assembly_lengths_Dc.2,
    (assemblyIndices_length Dc).le.trans assembly_lengths_Dc.1⟩

theorem compile_assembleC_Dc (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K) (hs : b 18 + b 17 ≤ 2 ^ 120) :
    Cert (MVM.compile (assembleC Dc)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K (assemblyResult (assemblyIndices Dc) b)) (2 ^ 318) := by
  rw [assembleC_eq]
  exact compile_assembleWords (assemblyIndices Dc) b h hb hz hs assemblyIndices_bounds.1 assemblyIndices_bounds.2

noncomputable def proposalKeyResult (b : Fin 64 → ℕ) := assemblyResult (assemblyIndices Dc) (proposalResult b)

theorem compile_proposalKeyC_Dc (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K) :
    Cert (MVM.compile (proposalKeyC Dc)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K (proposalKeyResult b)) (2 ^ 499) := by
  have hf := proposalResult_fields b
  have p0 := compile_proposalC_Dc b h hb hz
  have p1 := compile_assembleC_Dc (proposalResult b) (proposalResult_inputs b h)
    (hf.2.2.1.trans hb) (hf.2.2.2.le.trans hz) (proposalResult_source_bound b)
  exact (p0.seq p1).mono le_rfl le_rfl (by norm_num)

theorem assemblyResult_fields (js : List ℕ) (b : Fin 64 → ℕ) :
    assemblyResult js b 19 = js.length * (Dc.N * Dc.K) ∧
    assemblyResult js b 18 = b 18 ∧ assemblyResult js b rB1 = b rB1 ∧
    assemblyResult js b rZ = b rZ := by
  simp [assemblyResult, assemblyReady, gatherBase]

theorem proposalKeyResult_inputs (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b)) :
    RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K (proposalKeyResult b)) := by
  apply assemblyResult_inputs _ _ (proposalResult_inputs b h) (proposalResult_source_bound b)
  calc
    _ ≤ 2 ^ 66 * (Dc.N * Dc.K) := Nat.mul_le_mul_right _ assemblyIndices_bounds.2
    _ ≤ 2 ^ 120 := by norm_num [Dc, Dims.N, Params.en, Params.Kc]

theorem proposalKeyResult_fields (b : Fin 64 → ℕ) :
    proposalKeyResult b 19 = (assemblyIndices Dc).length * (Dc.N * Dc.K) ∧
    proposalKeyResult b 18 = (Enum.list (α := PIdxD Dc)).length * (Dc.N * Dc.K) ∧
    proposalKeyResult b rB1 = b rB1 ∧ proposalKeyResult b rZ = b rZ := by
  have ha := assemblyResult_fields (assemblyIndices Dc) (proposalResult b)
  have hp := proposalResult_fields b
  exact ⟨ha.1, ha.2.1.trans hp.2.1, ha.2.2.1.trans hp.2.2.1, ha.2.2.2.trans hp.2.2.2⟩

end AdvancedEncryption.ExpLUT.Prog.KeyTime
