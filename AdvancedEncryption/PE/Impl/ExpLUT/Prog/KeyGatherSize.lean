import PE.Impl.ExpLUT.Prog.KeySizeBasic
import PE.Impl.ExpLUT.Prog.SetupConf
/-! State-count bounds for the actual indexed gather and key assembly code. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib

/-- Fetch cost includes constructing the bit offset, copying, dropping, and moving one ring word. -/
theorem weight_fetchRingC (N K j : ℕ) :
    codeWeight (fetchRingC N K j) ≤ 3 * j * (N * K) + 5 := by
  have h := weight_natC 2 rB1 (j * (N * K))
  simp only [fetchRingC, codeWeight]
  nlinarith

theorem weight_gatherAppendC (N K J : ℕ) : ∀ js,
    (∀ j ∈ js, j ≤ J) →
    codeWeight (gatherAppendC N K js) ≤ js.length * (3 * J * (N * K) + 6) + 1
  | [], _ => by simp [gatherAppendC, codeWeight]
  | j :: js, h => by
    have hj := h j (by simp)
    have ih := weight_gatherAppendC N K J js (by intro i hi; exact h i (by simp [hi]))
    have hf := (weight_fetchRingC N K j).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right (N * K) (Nat.mul_le_mul_left 3 hj)) 5)
    simp only [gatherAppendC, codeWeight, List.length_cons]
    nlinarith

theorem weight_gatherC (N K J : ℕ) (js : List ℕ) (h : ∀ j ∈ js, j ≤ J) :
    codeWeight (gatherC N K js) ≤ js.length * (3 * J * (N * K) + 6) + 2 := by
  have hh := weight_gatherAppendC N K J js h
  simp only [gatherC, codeWeight]
  omega

/-- A selected finite family never indexes beyond the enumerated source family. -/
theorem weight_gatherC_family {α : Type} [Enum α] [DecidableEq α]
    (N K : ℕ) (is : List α) :
    codeWeight (gatherC N K (is.map Enum.index)) ≤
      is.length * (3 * (Enum.list (α := α)).length * (N * K) + 6) + 2 := by
  have h := weight_gatherC N K (Enum.list (α := α)).length (is.map Enum.index) (by
    intro j hj
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hj
    exact (Enum.index_lt a).le)
  simpa only [List.length_map] using h

theorem weight_loadFamilyC (N K : ℕ) (src dst : Fin 64) {α : Type} [Enum α]
    [DecidableEq α] (is : List α) :
    codeWeight (loadFamilyC N K src dst (is.map Enum.index)) ≤
      is.length * (3 * (Enum.list (α := α)).length * (N * K) + 6) + 4 := by
  have h := weight_gatherC_family N K is
  simp only [loadFamilyC, saveQueueC, codeWeight]
  omega

/-- Assembly's state count is bounded using the source and output family cardinalities. -/
theorem weight_assembleC (D : Dims) :
    codeWeight (assembleC D) ≤ (Enum.list (α := KCol (Wb D) (Jh D) (setting D).τ (setting D).E.W)).length *
      (3 * (Enum.list (α := AssemblySource D)).length * (D.N * D.K) + 6) + 5 := by
  let : DecidableEq (PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W) := Classical.decEq _
  simp only [assembleC, saveQueueC, codeWeight]
  apply le_trans (Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_right
    (weight_gatherC D.N D.K (Enum.list (α := AssemblySource D)).length _ ?_) 1) 1) 1)
  · simp only [List.length_map]
    omega
  · intro j hj
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hj
    apply Nat.le_of_lt
    exact @Enum.index_lt _ _ _ _

theorem size_assembleC (D : Dims) :
    (compile (assembleC D)).size ≤ 100000 * ((Enum.list (α := KCol (Wb D) (Jh D) (setting D).τ (setting D).E.W)).length *
      (3 * (Enum.list (α := AssemblySource D)).length * (D.N * D.K) + 6) + 5) :=
  (size_compile_weight _).trans (Nat.mul_le_mul_left _ (weight_assembleC D))

open Params

/-- Both source and output enumerations fit the same concrete cardinality budget. -/
theorem assembly_lengths_Dc :
    (Enum.list (α := KColt Dc)).length ≤ 2 ^ 66 ∧
    (Enum.list (α := AssemblySource Dc)).length ≤ 2 ^ 66 := by
  change (Enum.list (α := KCol (Wb Dc) (Jh Dc) Dc.K (2 ^ Dc.b))).length ≤ _ ∧
    (Enum.list (α := PIdx (Wb Dc) (Jh Dc) Dc.K (2 ^ Dc.b) ⊕
      ZIdx Dc.K (2 ^ Dc.b))).length ≤ _
  simp only [KCol, PIdx, ZIdx, BCol, Col, Wb, Jh, len_sum, Enum.length_prod, len_fin]
  norm_num [Dc, Kc, mbar]

theorem size_assembleC_of_bounds (D : Dims) (L S R : ℕ)
    (hL : (Enum.list (α := KColt D)).length ≤ L)
    (hS : (Enum.list (α := AssemblySource D)).length ≤ S) (hR : D.N * D.K ≤ R) :
    (compile (assembleC D)).size ≤ 100000 * (L * (3 * S * R + 6) + 5) := by
  apply (size_assembleC D).trans
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right
    (Nat.mul_le_mul hL (Nat.add_le_add_right
      (Nat.mul_le_mul (Nat.mul_le_mul_left 3 hS) hR) 6)) 5)

/-- State budget for the actual full key-assembly code. -/
theorem size_assembleC_Dc : (compile (assembleC Dc)).size ≤ 2 ^ 192 := by
  have hs := assembly_lengths_Dc
  have hNK : Dc.N * Dc.K ≤ 2 ^ 40 := by norm_num [Dc, Kc]
  exact (size_assembleC_of_bounds Dc (2 ^ 66) (2 ^ 66) (2 ^ 40) hs.1 hs.2 hNK).trans
    (by norm_num)

end AdvancedEncryption.ExpLUT.Prog
