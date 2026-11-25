import PE.Impl.ExpLUT.Prog.RedPubPRow
import PE.Impl.ExpLUT.Prog.RedPubPInst
import PE.Impl.ExpLUT.Prog.RedPubFront

/-!
# The code of the reduction's public key (package G2, `pubP`)

`pubC D : Code` computes, from the raw secret (`rawEnc`, register `ra`), the word of the public
key `(mpkEnc D).enc (pubK D σ)` into the shift register `rOut` (pre-sized to its length), in the
order of `pubWord_eq`:

* `parseC`: the fields of the raw secret into their registers;
* `outBC`: `B = [aB; B⁽²⁾]`;
* `outHC`: `H_k = [aH k; H⁽²⁾ k]`, the helper columns read with a stride (`exec_strided`);
* `prepC`: `Ā`, `B̄⁽²⁾`, `−v̄_B` (`= B̄⁽²⁾ − b̄`);
* `aPhC`: per position `t`, the monomial `u_t = X^{w x_t}` (`rhoStep`), the row `a_t` and the
  bottom row `cb_t` (`rowC`), kept in `rKA`, `rKC`; then `a` is pushed;
* `a0C`: the two rows of `A₀`;
* `ainC`: per `t` and digit `d = (r, c', i)`, `δ = d_i(C_{r,c'})` (`digit`) and the two rows of
  `A^in_{t,d}`;
* `autC`: per `t < b`, the matrix `C_{g_t}` (`aut`, `canon`) and the rows of `A^aut_{t,d}`;
* `outDC`: `d = [ad; d₂]`.

`pubP D = ringIO1 … (pubC D)` is the component.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog.RedPubP

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open AdvancedEncryption.ExpLUT.Prog.RedVM

/-! ### Registers -/

@[simp] abbrev ra : Fin 200 := 0
@[simp] abbrev rb : Fin 200 := 1
@[simp] abbrev r1 : Fin 200 := 2
@[simp] abbrev rOut : Fin 200 := 3
-- templates
@[simp] abbrev c128 : Fin 200 := 4
@[simp] abbrev cBC : Fin 200 := 5
@[simp] abbrev cJK : Fin 200 := 6
@[simp] abbrev cH2 : Fin 200 := 7
@[simp] abbrev cFl1 : Fin 200 := 8
@[simp] abbrev cJ : Fin 200 := 10
@[simp] abbrev cSkip : Fin 200 := 11
@[simp] abbrev cMb : Fin 200 := 12
@[simp] abbrev cColW : Fin 200 := 13
@[simp] abbrev cPos : Fin 200 := 14
@[simp] abbrev cZ : Fin 200 := 15
@[simp] abbrev rZcol : Fin 200 := 16
@[simp] abbrev cPC : Fin 200 := 17
@[simp] abbrev cFl3 : Fin 200 := 18
@[simp] abbrev cZblk : Fin 200 := 19
@[simp] abbrev cRin : Fin 200 := 20
@[simp] abbrev cCol : Fin 200 := 21
@[simp] abbrev cNK2 : Fin 200 := 22
-- data
@[simp] abbrev rAttr : Fin 200 := 30
@[simp] abbrev rAB : Fin 200 := 31
@[simp] abbrev rAd : Fin 200 := 32
@[simp] abbrev rAHp : Fin 200 := 33
@[simp] abbrev rAHk : Fin 200 := 34
@[simp] abbrev rVB : Fin 200 := 35
@[simp] abbrev rVHp : Fin 200 := 36
@[simp] abbrev rVHk : Fin 200 := 37
@[simp] abbrev rB2 : Fin 200 := 38
@[simp] abbrev rH2 : Fin 200 := 39
@[simp] abbrev rD2 : Fin 200 := 40
@[simp] abbrev rFe : Fin 200 := 41
@[simp] abbrev rZ : Fin 200 := 42
@[simp] abbrev rR0 : Fin 200 := 43
@[simp] abbrev rRin : Fin 200 := 44
@[simp] abbrev tmp : Fin 200 := 45
@[simp] abbrev rSk : Fin 200 := 46
@[simp] abbrev rSp : Fin 200 := 47
@[simp] abbrev rH2s : Fin 200 := 48
@[simp] abbrev cntJ : Fin 200 := 49
@[simp] abbrev cnt : Fin 200 := 50
@[simp] abbrev rAbar : Fin 200 := 51
@[simp] abbrev rB2bar : Fin 200 := 52
@[simp] abbrev rNV : Fin 200 := 53
@[simp] abbrev rU : Fin 200 := 54
@[simp] abbrev rKA : Fin 200 := 55
@[simp] abbrev rKC : Fin 200 := 56
@[simp] abbrev cntP : Fin 200 := 57
@[simp] abbrev rSA : Fin 200 := 58
@[simp] abbrev rSC : Fin 200 := 59
@[simp] abbrev rCt : Fin 200 := 60
@[simp] abbrev rCt2 : Fin 200 := 61
@[simp] abbrev rCw : Fin 200 := 62
@[simp] abbrev cntC : Fin 200 := 63
@[simp] abbrev cntI : Fin 200 := 64
@[simp] abbrev rRem : Fin 200 := 65
@[simp] abbrev rI : Fin 200 := 66
@[simp] abbrev rDel : Fin 200 := 67
@[simp] abbrev rG : Fin 200 := 68
@[simp] abbrev rBit : Fin 200 := 69
@[simp] abbrev rT1 : Fin 200 := 70
@[simp] abbrev rVk : Fin 200 := 71
@[simp] abbrev rVp : Fin 200 := 112

/-- The templates of `X^{w 2^{7 − j}}` (`j < 8`). -/
def rhoR (j : ℕ) : Fin 200 := ⟨72 + j % 8, by omega⟩

/-- The templates `κ_t` of `σ_{g_t}` (`t < 32`). -/
def kR (t : ℕ) : Fin 200 := ⟨80 + t % 32, by omega⟩

/-! ### Template lengths -/

/-- The length of a fixed-length encoding. -/
def pencLen {β : Type} {n : ℕ} (_ : FixedEnc β n) : ℕ := n

theorem length_pencLen {β : Type} {n : ℕ} (e : FixedEnc β n) (b : β) :
    (e.enc b).length = pencLen e := e.length b

/-- The length of an enumeration. -/
abbrev pnE (α : Type) [Enum α] : ℕ := (Enum.list (α := α)).length

variable (D : Dims)

/-- The template lengths (outside the `ρ` and `κ` blocks). -/
noncomputable def tmBase : ℕ → ℕ
  | 2 => D.N * D.K - 1
  | 3 => pencLen (mpkEnc D)
  | 4 | 30 => 128
  | 5 | 31 | 35 | 38 => pnE (BCol (Wb D) D.K) * (D.N * D.K)
  | 6 | 33 | 34 | 36 | 37 => D.K * pnE (Jh D) * (D.N * D.K)
  | 7 | 39 => pnE (Jh D) * (pnE (Col D.K) * (D.N * D.K))
  | 8 => pnE (Fin D.b) * (pnE (Dig D.K) * (pnE (Col D.K) * (D.N * D.K)))
  | 9 => D.K
  | 10 => pnE (Jh D)
  | 11 => (pnE (Jh D) - 1) * (D.N * D.K)
  | 12 | 51 | 52 | 53 => pnE (Wb D) * (D.N * D.K)
  | 13 | 16 | 60 | 61 => pnE (Col D.K) * (D.N * D.K)
  | 14 => pnE Pos
  | 15 | 42 => pnE (Pos × Col D.K) * pnE (Wb D)
  | 17 | 41 | 55 | 56 => pnE Pos * (pnE (Col D.K) * (D.N * D.K))
  | 18 => pnE Pos * (pnE (Dig D.K) * (pnE (Col D.K) * (D.N * D.K))) + pnE (Col D.K) * (D.N * D.K)
  | 19 | 43 => pnE (Col D.K) * pnE (Wb D)
  | 20 | 44 => pnE (Pos × Dig D.K × Col D.K) * pnE (Wb D)
  | 21 => pnE (Col D.K)
  | 22 => 2 * (D.N * D.K)
  | 32 | 40 | 62 => D.N * D.K
  | 69 => 1
  | 152 => pnE (Wb D)
  | 156 => D.N * D.K
  | 157 => 1
  | 158 => 1
  | 159 => D.N * D.K
  | 160 => D.N * D.K
  | 163 => D.N * D.K
  | _ => 0

/-- **The template lengths.** -/
noncomputable def tm (r : Fin 200) : ℕ :=
  if 72 ≤ r.val ∧ r.val < 80 then 2 * D.N - wSt * 2 ^ (7 - (r.val - 72))
  else if 80 ≤ r.val ∧ r.val < 112 then κD D (r.val - 80) else tmBase D r.val

/-! ### The code -/

/-- **Parse** the raw secret. -/
def parseC : Code :=
  ofList [.mv rAttr ra c128, .mv rAB ra cBC, .mv rAd ra xCNK, .mv rAHp ra cJK, .mv rAHk ra cJK,
    .mv rVB ra cBC, .drop ra xCNK, .mv rVHp ra cJK, .mv rVHk ra cJK, .mv rB2 ra cBC,
    .mv rH2 ra cH2, .mv rD2 ra xCNK, .drop ra cFl1, .mv rFe ra cPC, .drop ra cFl3, .mv rZ ra cZ,
    .mv rR0 ra cZblk, .mv rRin ra cRin]

/-- **`B`**. -/
def outBC : Code := ofList [.cp tmp rAB, .mv rOut tmp cBC, .cp tmp rB2, .mv rOut tmp cBC]

/-- A strided column read into the output. -/
def colC (src : Fin 200) : Code :=
  ofList [.cp tmp src, .cp cnt cK, .rep cnt (sBody rOut tmp xCNK cSkip), .drop src xCNK]

/-- One `H_k`: the circular column `k`, the plain column `k`, then `H⁽²⁾_k`. -/
def hBody : Code := ofList [colC rSk, colC rSp, .mv rOut rH2s cColW]

/-- **`H`**. -/
def outHC : Code := ofList [.cp rSk rAHk, .cp rSp rAHp, .cp rH2s rH2, .cp cntJ cJ, .rep cntJ hBody]

/-- A round of `−v̄_B`. -/
def nBody : Code := ofList [.mv xv tmp xCNK, .sub xS xZero xv, .mv rNV xS xCNK]

/-- **`Ā`, `B̄⁽²⁾`, `−v̄_B`.** -/
def prepC : Code :=
  ofList [.cp tmp rAB, .mv rAbar tmp cMb, .cp tmp rB2, .mv rB2bar tmp cMb, .cp tmp rVB,
    .cp cnt xCm, .rep cnt nBody]

/-- The post-map `xH := xAcc`. -/
def cpPost : Code := .cp xH xAcc

/-- The post-map `xH := σ_{g_t}(xAcc)`. -/
def autPost (t : ℕ) : Code := .aut xH xAcc (kR t)

/-- One attribute bit: `u := X^{w 2^{7 − j}} u` when the bit is set. -/
def rhoStep (j : ℕ) : Code := .seq (.mv rBit rAttr xC1) (.ifb rBit (.rhoJ rU rU (rhoR j)) .nop)

/-- The monomial `u_t = X^{w x_t}` from the next 8 attribute bits. -/
def monoC : Code := ofList (.cp rU r1 :: (List.range 8).map rhoStep)

/-- A row of hashes into the phase buffer. -/
def rowSetC (v z : Fin 200) (p : Fin 200) : Code :=
  ofList [.cp xV v, .cp xZ z, .cp xF rZcol, .cp xOut rZcol, .cp xP p]

/-- One position of `a` and `cb`. -/
def aBody : Code :=
  ofList [monoC, rowSetC rAbar rZ rU, rowC cpPost 0, .mv rKA xOut cColW,
    rowSetC rNV rZ rU, .mv xF rFe cColW, rowC cpPost 1, .mv rKC xOut cColW, .cp rZ xZ]

/-- **`a`** (and the bottom rows `cb`, kept). -/
def aPhC : Code := ofList [.cp cntP cPos, .rep cntP aBody, .cp tmp rKA, .mv rOut tmp cPC]

/-- **`A₀`**. -/
def a0C : Code :=
  ofList [rowSetC rAbar rR0 r1, rowC cpPost 0, .mv rOut xOut cColW,
    rowSetC rB2bar rR0 r1, rowC cpPost 1, .mv rOut xOut cColW]

/-- One digit: `δ = d_i(C)` (template `|rI| = i`), the two rows of hashes. -/
def dBody (m : Code) (zs : Fin 200) : Code :=
  ofList [.cp rI cK, .drop rI rRem, .tl rRem, .digit rDel rCw rI,
    rowSetC rAbar zs rDel, rowC m 0, .mv rOut xOut cColW,
    rowSetC rB2bar zs rDel, rowC m 1, .mv rOut xOut cColW, .cp zs xZ]

/-- One entry `C_{r,c'}`: its `K` digits. -/
def cBody (src : Fin 200) (m : Code) (zs : Fin 200) : Code :=
  ofList [.mv rCw src xCNK, .cp cntI cK, .cp rRem cK, .rep cntI (dBody m zs)]

/-- One row `r` of `C`: its `|Col|` entries. -/
def digRow (src : Fin 200) (m : Code) (zs : Fin 200) : Code :=
  .seq (.cp cntC cCol) (.rep cntC (cBody src m zs))

/-- One position of `A^in`. -/
def inT : Code :=
  ofList [.cp rCt rZcol, .mv rCt rSA cColW, .cp rCt2 rZcol, .mv rCt2 rSC cColW,
    digRow rCt cpPost rRin, digRow rCt2 cpPost rRin]

/-- **`A^in`**. -/
def ainC : Code := ofList [.cp rSA rKA, .cp rSC rKC, .cp cntP cPos, .rep cntP inT]

/-- An entry of the row `0` of `C_{g_t}`: `σ(aH)`. -/
def aBodyK (t : ℕ) : Code :=
  ofList [.mv xv tmp xCNK, .drop tmp cSkip, .aut xS xv (kR t), .canon xO xS, .mv rCt xO xCNK]

/-- An entry of the first half of the row `1`: `σ(0 − v_H)`. -/
def aBodyV0 (t : ℕ) : Code :=
  ofList [.mv xv tmp xCNK, .drop tmp cSkip, .sub xS xZero xv, .aut rT1 xS (kR t), .canon xO rT1,
    .mv rCt2 xO xCNK]

/-- An entry of the second half of the row `1`: `σ(2^i − v_H)`. -/
def aBodyV1 (t : ℕ) : Code :=
  ofList [.mv xv tmp xCNK, .drop tmp cSkip, .sub xS rG xv, .aut rT1 xS (kR t), .canon xO rT1,
    .mv rCt2 xO xCNK, .add rG rG rG]

/-- A strided loop of `K` rounds from `src`. -/
def strC (src : Fin 200) (body : Code) : Code :=
  ofList [.cp tmp src, .cp cnt cK, .rep cnt body]

/-- The block of `t` of `A^aut`. -/
def autT (t : ℕ) : Code :=
  ofList [.cp rCt rZcol, strC rSk (aBodyK t), strC rSp (aBodyK t),
    .cp rCt2 rZcol, strC rVk (aBodyV0 t), .cp rG r1, strC rVp (aBodyV1 t),
    .drop rSk cNK2, .drop rSp cNK2, .drop rVk cNK2, .drop rVp cNK2,
    digRow rCt (autPost t) ra, digRow rCt2 (autPost t) ra]

/-- **`A^aut`**: the streams start at the helper `(0, 1)`. -/
def autC : Code :=
  ofList ([.cp rSk rAHk, .drop rSk xCNK, .cp rSp rAHp, .drop rSp xCNK, .cp rVk rVHk,
    .drop rVk xCNK, .cp rVp rVHp, .drop rVp xCNK] ++
    (List.finRange D.b).map fun t => autT t.val)

/-- **`d`**. -/
def outDC : Code := ofList [.mv rOut rAd xCNK, .mv rOut rD2 xCNK]

/-- **The code of the public key.** -/
def pubC : Code := ofList [parseC, outBC, outHC, prepC, aPhC, a0C, ainC, autC D, outDC]

/-- **The public-key component.** -/
noncomputable def pubP : XProg 247 := RedIO.ringIO1 D.N D.K ra rb rOut r1 (tm D) (pubC D)

/-! ### Loops -/

theorem ploopOkB_ofList : ∀ l : List Code, loopOkB (ofList l) = l.all loopOkB
  | [] => rfl
  | c :: l => by simp [ofList, loopOkB, ploopOkB_ofList l]

theorem loopOkB_rowC (m : Code) (ρ : Fin 2) (hm : loopOkB m = true)
    (hw : (wr m).contains xCnt = false) :
    loopOkB (rowC m ρ) = true := by
  unfold rowC
  split_ifs <;>
  simp only [halfC, hashPhase, phaseBody, gpost, loopOkB, wr, hashC, hashBody, hm,
    List.contains_append, hw] <;> decide

theorem loopOkB_pubC : loopOkB (pubC D) = true := by
  have hA : ∀ t, loopOkB (autT t) = true := fun t => rfl
  rw [pubC, ploopOkB_ofList]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [autC, ploopOkB_ofList]
  simp only [List.all_append, List.all_map, Function.comp_def, hA]
  have hall : ∀ {α : Type} (l : List α), l.all (fun _ => true) = true := fun l => by simp
  rw [hall]
  rfl

end AdvancedEncryption.ExpLUT.Prog.RedPubP
