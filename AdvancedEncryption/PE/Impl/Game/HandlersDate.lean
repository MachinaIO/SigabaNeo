import PE.Impl.Game.HandlersMain
import PE.DateWindow

/-!
# The handlers for the date-window universe

The encodings of `dateUniverse` are onto the words of their length (10-bit dates, 1-bit
messages), so the generic decoders of the handlers (length tests) decode them (`dateCodes`).
The parameter words `paramsWord` with `λ ≥ 1` start with `true` (`head_paramsWord`), as the
instance words of the handlers must not start with `false`.
-/

namespace AdvancedEncryption.PE.Generic

open SigabaNeo AdvancedEncryption.PE.DateWindow

theorem symBits_ofBits_five (b₀ b₁ b₂ b₃ b₄ : Bool) :
    symBits ⟨ofBits [b₀, b₁, b₂, b₃, b₄], by revert b₀ b₁ b₂ b₃ b₄; decide⟩ =
      [b₀, b₁, b₂, b₃, b₄] := by
  revert b₀ b₁ b₂ b₃ b₄; decide

theorem exists_symBits {l : List Bool} (hl : l.length = 5) : ∃ s : Sym, symBits s = l := by
  match l, hl with
  | [b₀, b₁, b₂, b₃, b₄], _ => exact ⟨_, symBits_ofBits_five b₀ b₁ b₂ b₃ b₄⟩

theorem encDate_onto (w : List Bool) (hw : w.length = 10) : ∃ x, encDate x = w := by
  obtain ⟨s₁, h₁⟩ := exists_symBits (l := w.take 5) (by simp [hw])
  obtain ⟨s₂, h₂⟩ := exists_symBits (l := w.drop 5) (by simp [hw])
  refine ⟨(s₁, s₂), ?_⟩
  show symBits s₁ ++ symBits s₂ = w
  rw [h₁, h₂, List.take_append_drop]

/-- **The codes of the date-window universe**, for a fixed-length encoding of the secret. -/
def dateCodes {Sig : Type} {nS : ℕ} (sig : Encode.FixedEnc Sig nS) : Codes dateUniverse Sig where
  nA := 10
  nM := 1
  nS := nS
  sig := sig
  len_attr x := by
    show (symBits x.1 ++ symBits x.2).length = 10
    simp [length_symBits]
  len_msg μ := rfl
  full_attr := encDate_onto
  full_msg w hw := by
    match w, hw with
    | [b], _ => exact ⟨b, rfl⟩

/-- The parameter words with `λ ≥ 1` start with `true`. -/
theorem head_paramsWord (U : Universe) (p : Params) (hp : 1 ≤ p.secBits) :
    (paramsWord U p).head? = some true := by
  obtain ⟨n, hn⟩ : ∃ n, p.secBits = n + 1 := ⟨p.secBits - 1, by omega⟩
  show (([List.replicate p.secBits true, List.replicate p.corrBits true, U.desc]).flatMap
    (Turing.MultiTapeTM.frame ∘ Turing.MultiTapeTM.encBits)).head? = some true
  rw [hn]
  simp [Turing.MultiTapeTM.frame, List.replicate_succ]

end AdvancedEncryption.PE.Generic
