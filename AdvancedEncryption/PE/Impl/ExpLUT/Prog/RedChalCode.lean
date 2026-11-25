import PE.Impl.ExpLUT.Prog.RedChalPhases
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMHandler
open SigabaNeo.Tape.RingVM.Handler SigabaNeo.Tape.RingVM.Hash
/-!
# The code of the reduction's challenge (package G2, `chalP`)

`chalC D : Code` computes, from the raw secret (`rawEnc`, register `ra`) and the message bit
(register `rb`), the words of the challenge `chalCT D σ μ` into the buffer `xOut`:

* `parseC`: the fields of the raw secret into their registers (the `A` part of the instance is
  dropped);
* `bC`: `b = v_B + B⁽²⁾` (canonical words), with the vectors `b̄` (`rBbar`) and `−v̄_B` (`rNV`);
* `hC`: `h_k = v_{H,k} − G⁽²⁾ + H⁽²⁾_k`, the helper samples read with a stride from the instance's
  row order;
* `autC`, `cbC`, `cinC`: the hash phases of `c^aut`, the bottom rows of `C^in`, `c^in` and `c₀`;
* `cmC`: `c_m = v_d + d₂ + ⌊q/2⌉ μ`.

`chalP D = ringIO1 … (chalC D)` is the component.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog.RedChal

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open SigabaNeo.Tape.RingVM.Hash

/-! ### Registers -/

@[simp] abbrev ra : Fin 200 := 0
@[simp] abbrev rb : Fin 200 := 1
@[simp] abbrev r1 : Fin 200 := 2
@[simp] abbrev c128 : Fin 200 := 3
@[simp] abbrev cInst : Fin 200 := 4
@[simp] abbrev cB2 : Fin 200 := 5
@[simp] abbrev cH2 : Fin 200 := 6
@[simp] abbrev cFl : Fin 200 := 7
@[simp] abbrev cZ : Fin 200 := 8
@[simp] abbrev cR0 : Fin 200 := 9
@[simp] abbrev cRin : Fin 200 := 10
@[simp] abbrev rAttr : Fin 200 := 11
@[simp] abbrev rV : Fin 200 := 12
@[simp] abbrev rB2 : Fin 200 := 13
@[simp] abbrev rH2 : Fin 200 := 14
@[simp] abbrev rd2 : Fin 200 := 15
@[simp] abbrev rZ : Fin 200 := 16
@[simp] abbrev rR0 : Fin 200 := 17
@[simp] abbrev rRin : Fin 200 := 18
@[simp] abbrev cnt : Fin 200 := 19
@[simp] abbrev cK : Fin 200 := 20
@[simp] abbrev tmpO : Fin 200 := 21
@[simp] abbrev tmpN : Fin 200 := 22
@[simp] abbrev rNV : Fin 200 := 23
@[simp] abbrev rBbar : Fin 200 := 24
@[simp] abbrev rVd : Fin 200 := 25
@[simp] abbrev c2b : Fin 200 := 26
@[simp] abbrev cHalf : Fin 200 := 27
@[simp] abbrev rS0 : Fin 200 := 28
@[simp] abbrev cntJ : Fin 200 := 29
@[simp] abbrev tmp : Fin 200 := 30
@[simp] abbrev cSkip : Fin 200 := 31
@[simp] abbrev rS1 : Fin 200 := 32
@[simp] abbrev rG : Fin 200 := 33
@[simp] abbrev cAut : Fin 200 := 34
@[simp] abbrev rP : Fin 200 := 35
@[simp] abbrev rBit : Fin 200 := 36
@[simp] abbrev cIn : Fin 200 := 45
@[simp] abbrev cCol : Fin 200 := 46
@[simp] abbrev rHalf : Fin 200 := 47

/-- The templates of `X^{w 2^{7 − j}}` (`j < 8`, MSB first). -/
def rhoR (j : ℕ) : Fin 200 := ⟨37 + j % 8, by omega⟩

/-- The templates `κ_t` of `σ_{g_t}` (`t < 32`). -/
def kR (t : ℕ) : Fin 200 := ⟨48 + t % 32, by omega⟩

/-! ### Sizes and templates -/

/-- The length of an enumeration. -/
abbrev nE (α : Type) [Enum α] : ℕ := (Enum.list (α := α)).length

variable (D : Dims)

/-- The template lengths of the registers (outside the `κ_t` block). -/
noncomputable def tmBase : ℕ → ℕ
  | 2 => D.N * D.K - 1
  | 3 => 128
  | 4 => (vecE D (Fin (circParamsD D).rows)).len
  | 5 => (vecE D (BCol (Wb D) D.K)).len
  | 6 => (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).len
  | 7 => (floodEnc D).len
  | 8 => nE (Pos × Col D.K) * nE (Wb D)
  | 9 => nE (Col D.K) * nE (Wb D)
  | 10 => nE (Pos × Dig D.K × Col D.K) * nE (Wb D)
  | 11 => 128
  | 12 => (vecE D (Fin (circParamsD D).rows)).len
  | 13 => (vecE D (BCol (Wb D) D.K)).len
  | 14 => (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).len
  | 15 => D.N * D.K
  | 16 => nE (Pos × Col D.K) * nE (Wb D)
  | 17 => nE (Col D.K) * nE (Wb D)
  | 18 => nE (Pos × Dig D.K × Col D.K) * nE (Wb D)
  | 20 => D.K
  | 23 => nE (Wb D) * (D.N * D.K)
  | 24 => nE (Wb D) * (D.N * D.K)
  | 25 => D.N * D.K
  | 26 => D.b * 2
  | 27 => D.K * (D.b * 2) * (D.N * D.K)
  | 31 => (D.b * 2 - 1) * (D.N * D.K)
  | 34 => nE (Dig D.K × Col D.K)
  | 36 => 1
  | 45 => nE (Pos × Dig D.K × Col D.K)
  | 46 => nE (Col D.K)
  | 152 => nE (Wb D)
  | 156 => D.N * D.K
  | 157 => 1
  | 158 => 1
  | 159 => D.N * D.K
  | 160 => D.N * D.K
  | 162 => (floodEnc D).len
  | 163 => D.N * D.K
  | 166 => (ctEnc D).len
  | _ => 0

/-- The weights of the attribute bits (MSB first): `w 2^{7 − j}`. -/
def wtR (j : ℕ) : ℕ := wSt * 2 ^ (7 - j)

/-- **The template lengths.** -/
noncomputable def tm (r : Fin 200) : ℕ :=
  if 48 ≤ r.val ∧ r.val < 80 then κD D (r.val - 48)
  else if 37 ≤ r.val ∧ r.val < 45 then 2 * D.N - wtR (r.val - 37) else tmBase D r.val

/-! ### The code -/

/-- **Parse** the raw secret. -/
def parseC : Code :=
  ofList [.mv rAttr ra c128, .drop ra cInst, .mv rV ra cInst, .mv rB2 ra cB2, .mv rH2 ra cH2,
    .mv rd2 ra xCNK, .mv xF ra cFl, .mv rZ ra cZ, .mv rR0 ra cR0, .mv rRin ra cRin]

/-- A round of `b` on the columns of `Ā`: also pushes `b̄_v` and `−v_{B,v}`. -/
def bBody1 : Code :=
  ofList [.mv xv rV xCNK, .mv xf rB2 xCNK, .add xS xv xf, .canon xO xS, .cp tmpO xO,
    .mv rBbar tmpO xCNK, .sub xS xZero xv, .canon tmpN xS, .mv rNV tmpN xCNK, .mv xOut xO xCNK]

/-- A round of `b` on the gadget columns. -/
def bBody2 : Code :=
  ofList [.mv xv rV xCNK, .mv xf rB2 xCNK, .add xS xv xf, .canon xO xS, .mv xOut xO xCNK]

/-- **`b`**, then `v_d` into `rVd`. -/
def bC : Code :=
  ofList [.cp cnt xCm, .rep cnt bBody1, .cp cnt cK, .rep cnt bBody2, .mv rVd rV xCNK]

/-- A helper round on the first gadget half: `v + H⁽²⁾`. -/
def hIn0 : Code :=
  ofList [.mv xv tmp xCNK, .drop tmp cSkip, .mv xf rH2 xCNK, .add xS xv xf, .canon xO xS,
    .mv xOut xO xCNK]

/-- A helper round on the second gadget half: `v + H⁽²⁾ − 2^i`. -/
def hIn1 : Code :=
  ofList [.mv xv tmp xCNK, .drop tmp cSkip, .mv xf rH2 xCNK, .add xS xv xf, .sub xS xS rG,
    .canon xO xS, .mv xOut xO xCNK, .add rG rG rG]

/-- One helper. -/
def hOuter : Code :=
  ofList [.cp tmp rS0, .cp cnt cK, .rep cnt hIn0, .drop rS0 xCNK, .cp tmp rS1, .cp rG r1,
    .cp cnt cK, .rep cnt hIn1, .drop rS1 xCNK]

/-- **The helpers.** -/
def hC : Code :=
  ofList [.cp rS1 rV, .cp rS0 rV, .drop rS0 cHalf, .cp cntJ c2b, .rep cntJ hOuter]

/-- The `c^aut` block of `t`. -/
def autStep (t : ℕ) : Code := .seq (.cp xCnt cAut) (hashPhase (autPost (kR t)))

/-- **`c^aut`.** -/
def autC : Code :=
  ofList ([.cp xV rBbar, .cp xZ ra] ++ (Enum.list (α := Fin D.b)).map fun t => autStep t.val)

/-- One attribute bit: `P := X^{w 2^{7 − j}} P` when the bit is set. -/
def rhoStep (j : ℕ) : Code := .seq (.mv rBit rAttr xC1) (.ifb rBit (.rhoJ rP rP (rhoR j)) .nop)

/-- `xH := xAcc + xP`, `xP := 2 xP`. -/
def cbPost : Code := .seq (.add xH xAcc xP) (.add xP xP xP)

/-- The bottom row of `C^in_t`. -/
def cbStep : Code :=
  ofList ([.cp rP r1] ++ (List.range 8).map rhoStep ++
    [.cp xCnt cK, hashPhase cpPost, .cp xP rP, .cp xCnt cK, hashPhase cbPost])

/-- **The bottom rows of `C^in`.** -/
def cbC : Code := ofList ([.cp xV rNV, .cp xZ rZ] ++ (Enum.list (α := Pos)).map fun _ => cbStep)

/-- **`c^in` and `c₀`.** -/
def cinC : Code :=
  ofList [.cp xV rBbar, .cp xZ rRin, .cp xCnt cIn, hashPhase cpPost, .cp xZ rR0, .cp xCnt cCol,
    hashPhase cpPost]

/-- **`c_m`.** -/
def cmC : Code :=
  ofList [.add xS rVd rd2, .rotB rHalf r1 xC1, .ifb rb (.add xS xS rHalf) .nop, .canon xO xS,
    .mv xOut xO xCNK]

/-- **The code of the challenge.** -/
def chalC : Code := ofList [parseC, bC, hC, autC D, cbC, cinC, cmC]

/-- **The challenge component.** -/
noncomputable def chalP : XProg 247 := SigabaNeo.Tape.RingVM.Handler.ringIO1 D.N D.K ra rb xOut r1 (tm D) (chalC D)

theorem loopOkB_ofList : ∀ l : List Code, loopOkB (ofList l) = l.all loopOkB
  | [] => rfl
  | c :: l => by simp [ofList, loopOkB, loopOkB_ofList l]

theorem loopOkB_hashPhase (post : Code) (hp : loopOkB post = true)
    (hw : (wr post).contains xCnt = false) : loopOkB (hashPhase post) = true := by
  simp only [hashPhase, phaseBody, loopOkB, wr, hashC, hashBody, hp, List.contains_append, hw]
  decide

theorem loopOkB_chalC : loopOkB (chalC D) = true := by
  have ha : ∀ t, loopOkB (autStep t) = true := fun t =>
    show (loopOkB (.cp xCnt cAut) && loopOkB (hashPhase (autPost (kR t)))) = true from by
      rw [loopOkB_hashPhase _ rfl (by simp [autPost, wr])]; rfl
  have hc : loopOkB cbStep = true := by
    rw [cbStep, loopOkB_ofList]
    simp only [List.all_append, List.all_cons, List.all_nil, List.all_map,
      loopOkB_hashPhase cpPost rfl (by decide), loopOkB_hashPhase cbPost rfl (by decide)]
    simp only [Bool.and_true]
    decide
  have hi : loopOkB cinC = true := by
    rw [cinC, loopOkB_ofList]
    simp only [List.all_cons, List.all_nil, loopOkB_hashPhase cpPost rfl (by decide)]
    rfl
  rw [chalC, loopOkB_ofList]
  simp only [List.all_cons, List.all_nil, hi]
  rw [autC, cbC, loopOkB_ofList, loopOkB_ofList]
  have hall : ∀ {α : Type} (l : List α), l.all (fun _ => true) = true := fun l => by
    simp
  simp only [List.all_append, List.all_cons, List.all_nil, List.all_map, Function.comp_def, ha, hc,
    hall, Bool.and_true]
  decide

end AdvancedEncryption.ExpLUT.Prog.RedChal
