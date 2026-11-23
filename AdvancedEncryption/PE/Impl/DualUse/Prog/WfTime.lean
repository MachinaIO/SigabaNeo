import PE.Impl.DualUse.Prog.WfB

/-!
# The time bound of the `W_f` block

`wfB gen W = seq (frame eGen gen) (prog (wfRest hk c W))`: the generator is bounded by a uniform
bound `∀ M, UB gen M (Tg M) (Lg M)` (a hypothesis on the generator, WS-L1), the coin-free rest by
its global bounds (`ub_prog`). **`ub_wfB`**: `∀ M, UB (wfB hk c gen W) M (wfT … M) (wfL … M)`, the
shape `time_keyPF` asks for.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates

/-- **A framed program** from a uniform bound of its body. -/
theorem ub_frameX {k m : ℕ} (e : Fin m ↪ Fin k) {p : XProg m} {M T M' : ℕ} (h : UB p M T M') :
    UB (frame e p) M T (max M M') := by
  intro ℓ hℓ
  have hc : ∀ j, (fun j => ℓ (e j)) j ≤ M := fun j => hℓ (e j)
  refine ⟨?_, fun i => ?_⟩
  · rw [timeBoundT_frame]; exact (h _ hc).1
  · show embedF e ℓ (lenBoundT p fun j => ℓ (e j)) i ≤ _
    rcases embedF_cases e ℓ (lenBoundT p fun j => ℓ (e j)) i with ⟨-, h'⟩ | ⟨j, rfl, h'⟩
    · rw [h']; exact (hℓ i).trans (le_max_left _ _)
    · rw [h']; exact ((h _ hc).2 j).trans (le_max_right _ _)

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The time of the `W_f` block from tapes below `M`. -/
noncomputable def wfT (W : ℕ) (Tg Lg : ℕ → ℕ) (M : ℕ) : ℕ :=
  Tg M + Prog.timeBound (wfRest hk c W) (max M (Lg M))

/-- The length bound after the `W_f` block, from tapes below `M`. -/
noncomputable def wfL (W : ℕ) (Lg : ℕ → ℕ) (M : ℕ) : ℕ :=
  Prog.lenBound (wfRest hk c W) (max M (Lg M))

/-- **The uniform bound of the `W_f` block**, from a uniform bound of the generator. -/
theorem ub_wfB {gen : XProg 136} {Tg Lg : ℕ → ℕ} (hU : ∀ M, UB gen M (Tg M) (Lg M)) (W M : ℕ) :
    UB (wfB hk c gen W) M (wfT hk c W Tg Lg M) (wfL hk c W Lg M) :=
  (ub_frameX eGen (hU M)).seq (ub_prog _ _)

end AdvancedEncryption.DualUse.Prog
