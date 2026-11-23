import PE.Impl.Game.HandlersMain
import PE.Impl.Gates.BPWord

/-!
# The handlers for the branching-program universe

The encodings of `bpUniverse` are onto the words of their length (128-bit attributes by
`encAttr_onto`, 1-bit messages), so the generic decoders of the handlers (length tests) decode
them (`bpCodes`). The parameter word of `bpUniverse` is that of `PUniv` (same `λ`, `κ`, empty
description): `515` bits, starting with `true` (`head_paramsWord`).
-/

namespace AdvancedEncryption.PE.Generic

open SigabaNeo AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates.BPWord

/-- **The codes of the branching-program universe**, for a fixed-length encoding of the secret. -/
def bpCodes {Sig : Type} {nS : ℕ} (sig : Encode.FixedEnc Sig nS) : Codes bpUniverse Sig where
  nA := 128
  nM := 1
  nS := nS
  sig := sig
  len_attr x := length_encAttr x
  len_msg μ := rfl
  full_attr w hw := ⟨attrOf w, encAttr_onto w hw⟩
  full_msg w hw := by
    match w, hw with
    | [b], _ => exact ⟨b, rfl⟩

theorem nA_bpCodes {Sig : Type} {nS : ℕ} (sig : Encode.FixedEnc Sig nS) : (bpCodes sig).nA = 128 :=
  rfl

theorem nM_bpCodes {Sig : Type} {nS : ℕ} (sig : Encode.FixedEnc Sig nS) : (bpCodes sig).nM = 1 :=
  rfl

/-- The parameter word of `bpUniverse`: `515` bits (as for `PUniv`). -/
theorem length_paramsWord_bp :
    (paramsWord bpUniverse AdvancedEncryption.PE.BranchingProgram.params).length = 515 := by
  rw [paramsWord, encodeTuple, Turing.MultiTapeTM.length_encList]
  simp [AdvancedEncryption.PE.BranchingProgram.params, bpUniverse, Turing.MultiTapeTM.encBits]

/-- The parameter words with `λ ≥ 1` start with `true`. -/
theorem head_paramsWord (U : Universe) (p : Params) (hp : 1 ≤ p.secBits) :
    (paramsWord U p).head? = some true := by
  obtain ⟨n, hn⟩ : ∃ n, p.secBits = n + 1 := ⟨p.secBits - 1, by omega⟩
  show (([List.replicate p.secBits true, List.replicate p.corrBits true, U.desc]).flatMap
    (Turing.MultiTapeTM.frame ∘ Turing.MultiTapeTM.encBits)).head? = some true
  rw [hn]
  simp [Turing.MultiTapeTM.frame, List.replicate_succ]

end AdvancedEncryption.PE.Generic
