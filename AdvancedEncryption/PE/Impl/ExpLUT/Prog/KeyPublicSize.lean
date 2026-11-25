import PE.Impl.ExpLUT.Prog.KeyCoefficientSize
/-! Uniform state-count bounds for all public-map rows of the actual KeyGen code. -/
namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Cardinality bounds for every public-row input and selected stream. -/
structure PublicSizeInputs (D : Dims) (S : ℕ) : Prop where
  source : (Enum.list (α := BHSource D)).length ≤ S
  rows : (Enum.list (α := BHRow D)).length ≤ S
  positive : (Enum.list (α := PublicPos (Wb D) (Jh D) (setting D).τ)).length ≤ S
  negative : (Enum.list (α := Jh D × Col (setting D).τ)).length ≤ S
  candidate : (Enum.list (α := PIdxD D)).length ≤ S
  helpers : (Enum.list (α := Jh D)).length ≤ S

def publicGatherBudget (D : Dims) (S : ℕ) : ℕ := S * (3 * S * (D.N * D.K) + 6) + 2

theorem weight_selectedGather {α β : Type} [Enum α] [Enum β] [DecidableEq α]
    (N K S : ℕ) (f : β → α) (hα : (Enum.list (α := α)).length ≤ S)
    (hβ : (Enum.list (α := β)).length ≤ S) :
    codeWeight (gatherC N K (Enum.list.map (Enum.index ∘ f))) ≤
      S * (3 * S * (N * K) + 6) + 2 := by
  apply (weight_gatherC N K S _ ?_).trans
  · simp only [List.length_map]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hβ) 2
  · intro j hj
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hj
    exact (Enum.index_lt (f a)).le.trans hα

theorem weight_publicGather (D : Dims) (S : ℕ) (h : PublicSizeInputs D S)
    (i : Fin (setting D).E.W) :
    codeWeight (positiveGatherC D i) ≤ publicGatherBudget D S ∧
    codeWeight (negativeGatherC D i) ≤ publicGatherBudget D S := by
  let : DecidableEq (PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W) := Classical.decEq _
  constructor
  · exact weight_selectedGather D.N D.K S (positiveSelection D i) h.candidate h.positive
  · exact weight_selectedGather D.N D.K S (negativeSelection D i) h.candidate h.negative

def publicPositiveBudget (D : Dims) (S : ℕ) : ℕ :=
  3 * S * (D.N * D.K) + S * (3 * S * (D.N * D.K) + 9) +
    6 * D.N + 6 * D.K * (D.N * D.K) + 21

theorem weight_gatherBHC (D : Dims) (S : ℕ) (h : PublicSizeInputs D S) (i : ℕ) :
    codeWeight (gatherBHC D i) ≤ S * (3 * S * (D.N * D.K) + 9) + 6 * D.N + 11 := by
  unfold gatherBHC
  apply (weight_gatherAutC D.N D.K _ S _ ?_).trans
  · simp only [List.length_map]
    have hl := Nat.mul_le_mul_right (3 * S * (D.N * D.K) + 9) h.rows
    have he := rowExponent_lt D i
    omega
  · intro j hj
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hj
    exact (Enum.index_lt (bhSelection D a)).le.trans h.source

theorem weight_positiveCoeffC (D : Dims) (S : ℕ) (h : PublicSizeInputs D S)
    (i : Fin (setting D).E.W) : codeWeight (positiveCoeffC D i) ≤ publicPositiveBudget D S := by
  have hp := weight_prefixC (bhPrefixLength D)
  have hg := weight_gatherBHC D S h i.val
  have ha := weight_appendAFC D.N D.K (decide (i = (setting D).row0))
  have hl := Nat.mul_le_mul_right (D.N * D.K) h.source
  simp only [bhPrefixLength] at hp
  simp only [positiveCoeffC, mpkBHC, codeWeight, publicPositiveBudget, bhPrefixLength]
  simp only [Nat.mul_assoc] at hp hg ha hl ⊢
  omega

def publicNegativeBudget (D : Dims) (S : ℕ) : ℕ :=
  3 * D.K + 3 * D.K * (D.N * D.K) + 3 * (D.N * D.K) + 3 * S + 20

def publicRowBudget (D : Dims) (S : ℕ) : ℕ :=
  publicPositiveBudget D S + publicNegativeBudget D S + 2 * publicGatherBudget D S + 6 * S + 108

theorem weight_publicRowC (D : Dims) (S : ℕ) (h : PublicSizeInputs D S)
    (i : Fin (setting D).E.W) : codeWeight (publicRowC D i) ≤ publicRowBudget D S := by
  have hp := weight_positiveCoeffC D S h i
  have hn := weight_negativeReadyC D.N D.K (Enum.list (α := Jh D)).length
  have hg := weight_publicGather D S h i
  have hc := weight_natC rQc rB1 (Enum.list (α := PublicPos (Wb D) (Jh D) (setting D).τ)).length
  have hd := weight_natC 12 rB1 (Enum.list (α := Jh D × Col (setting D).τ)).length
  have hs : codeWeight signedDotC ≤ 100 := by decide
  have hh := h.helpers
  have hpos := h.positive
  have hneg := h.negative
  simp only [publicRowC, saveQueueC, rowCountsC, codeWeight, publicRowBudget, publicNegativeBudget]
  omega

theorem weight_publicRowsAppendC (D : Dims) (S : ℕ) (h : PublicSizeInputs D S) : ∀ is,
    codeWeight (publicRowsAppendC D is) ≤ is.length * (publicRowBudget D S + 1) + 1
  | [] => by simp [publicRowsAppendC, codeWeight]
  | i :: is => by
    have hi := weight_publicRowC D S h i
    have ih := weight_publicRowsAppendC D S h is
    simp only [publicRowsAppendC, codeWeight, List.length_cons]
    nlinarith

theorem size_publicRowsC (D : Dims) (S : ℕ) (h : PublicSizeInputs D S) :
    (compile (publicRowsC D)).size ≤ 100000 * (2 ^ D.b * (publicRowBudget D S + 1) + 2) := by
  apply (size_compile_weight _).trans
  apply Nat.mul_le_mul_left
  have hh := weight_publicRowsAppendC D S h Enum.list
  have hl : (Enum.list (α := Fin (setting D).E.W)).length = 2 ^ D.b := len_fin _
  rw [hl] at hh
  simp only [publicRowsC, codeWeight]
  omega

open Params

/-- Symbolic cardinalities avoid evaluating the large concrete enumerations. -/
theorem public_input_lengths (D : Dims) :
    (Enum.list (α := BHSource D)).length =
      2 * (D.mb + D.K) + D.b * 2 * (2 * (2 * D.K)) ∧
    (Enum.list (α := BHRow D)).length = D.mb + D.b * 2 * (2 * D.K) ∧
    (Enum.list (α := PublicPos (Wb D) (Jh D) (setting D).τ)).length =
      D.mb + (D.b * 2 * (2 * D.K) + 2 * D.K) ∧
    (Enum.list (α := Jh D × Col (setting D).τ)).length = D.b * 2 * (2 * D.K) ∧
    (Enum.list (α := Jh D)).length = D.b * 2 := by
  simp only [BHSource, BHRow, PublicPos, Wb, Jh, Col, len_sum, Enum.length_prod, len_fin]
  exact ⟨rfl, rfl, rfl, rfl, trivial⟩

end AdvancedEncryption.ExpLUT.Prog
