import PE.Impl.ExpLUT.Prog.EncInitSpec
/-! # Phase invariants survive replacing the ciphertext output register -/
namespace AdvancedEncryption.ExpLUT.Prog.EncW
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Lattices.Algo.NegaG SigabaNeo.Tape SigabaNeo.Tape.Prog Matrix
open PE.BranchingProgram
variable {D : Dims}

theorem BPhaseOK.output {S : Store 66} (h : BPhaseOK D S) (o : List Bool) :
    BPhaseOK D (Function.update S 0 o) := by
  constructor
  · intro i hi
    have hi0 : i ≠ 0 := by intro he; subst he; simp at hi
    simp [hi0, h.scratch i hi]
  all_goals simp [h.hK, h.hN, h.hNK, h.hL, h.hK1, h.h11, h.h12, h.h13]

theorem HelperOK.output {S : Store 69} (h : HelperOK D S) (o : List Bool) :
    HelperOK D (Function.update S 0 o) := by
  constructor
  · intro i hi
    have hi0 : i ≠ 0 := by intro he; subst he; simp at hi
    simp [hi0, h.scratch i hi]
  all_goals simp [h.hK, h.hN, h.hNK, h.h11, h.h12, h.h13, h.h14, h.h15]

theorem AutBlockOK.output {S : Store 85} (h : AutBlockOK D S) (o : List Bool) :
    AutBlockOK D (Function.update S 0 o) := by
  constructor
  · intro i hi
    have hi0 : i ≠ 0 := by intro he; subst he; simp at hi
    simp [hi0, h.scratch i hi]
  all_goals simp [h.hK, h.hN, h.hNK, h.h13, h.hK1, h.h15, h.h16, h.h17, h.h18, h.h19]

theorem tailOK_output {K N : ℕ} {S : Store 104} (h : TailOK K N S) (o : List Bool) :
    TailOK K N (Function.update S 0 o) := by
  constructor
  · intro i hi
    have hi0 : i ≠ 0 := by intro he; subst he; simp at hi
    simp [hi0, h.hs i hi]
  all_goals simp [h.hK, h.hN, h.hNK, h.h28, h.hK1, h.h30, h.h31, h.h32,
    h.h33, h.h36, h.h37, h.h38, h.h1, h.h16]

theorem τT_output (S : Store 104) (o : List Bool) :
    τT (Function.update S 0 o) = τT S := by
  funext i
  have hi : i % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize he : i % 8 = j at hi
  interval_cases j <;> simp [τT, τOf, he, tCb1]

theorem TailInput.output {S : Store 104} {mpk : MPKt D} {x : Attribute w8} {μ : Bool}
    {r : EncCoins (setting D) (Wb D) (Jh D) Pos} (h : TailInput D S mpk x μ r) (o : List Bool) :
    TailInput D (Function.update S 0 o) mpk x μ r := by
  constructor
  case rotation => simpa only [τT_output] using h.rotation
  all_goals simp [h.secret, h.one, h.message, h.zero, h.entries, h.positions,
    h.xBot, h.xDig, h.aBot, h.aDig, h.aCopy, h.eBot, h.eDig, h.matrices, h.errors,
    h.initialMatrix, h.initialError, h.messageVector, h.messageError]

end AdvancedEncryption.ExpLUT.Prog.EncW
