import PE.Impl.RingBTVW.ImplBase
import PE.Impl.Game.HandlersBP

/-!
# The codes of the universe of the primitive

`puCodes sig : Codes PUniv Sig`: the fixed-length encodings the handlers of the reductions decode,
for the universe `PUniv = bpUniverse` behind the neutral names of `ImplBase`: `bpCodes`
(`HandlersBP`, `nA = 128` attribute bits by `encAttr_onto`, one message bit). The reductions refer
to the codes only through `puCodes`, `nA_puCodes`, `nM_puCodes` and `length_paramsWord_pu`.
-/

namespace AdvancedEncryption.RingBTVW

open SigabaNeo AdvancedEncryption.PE AdvancedEncryption.PE.Generic AdvancedEncryption.PE.BranchingProgram

/-- **The codes of the universe of the primitive.** -/
abbrev puCodes {Sig : Type} {nS : ℕ} (sig : Encode.FixedEnc Sig nS) : Codes PUniv Sig :=
  bpCodes sig

theorem nA_puCodes {Sig : Type} {nS : ℕ} (sig : Encode.FixedEnc Sig nS) : (puCodes sig).nA = nA :=
  rfl

theorem nM_puCodes {Sig : Type} {nS : ℕ} (sig : Encode.FixedEnc Sig nS) : (puCodes sig).nM = 1 :=
  rfl

theorem nS_puCodes {Sig : Type} {nS : ℕ} (sig : Encode.FixedEnc Sig nS) : (puCodes sig).nS = nS :=
  rfl

/-- The parameter word of the universe of the primitive: `515` bits. -/
theorem length_paramsWord_pu : (paramsWord PUniv params).length = 515 := by
  rw [paramsWord, encodeTuple, Turing.MultiTapeTM.length_encList]
  simp [params, bpUniverse, Turing.MultiTapeTM.encBits]

end AdvancedEncryption.RingBTVW
