import PE.Impl.DualUse.Prog.WfTime
import SigabaNeo.Lib.Lattices.ProgAlgo.ValMain
import SigabaNeo.Lib.Lattices.ProgAlgo.KeySumT
import SigabaNeo.Lib.Lattices.ProgAlgo.SimTmpl

/-!
# The block-structured `W_f` block

`wfB2 hk c W : XProg 256` writes the word of `W_f = simW sd C` from `sdEnc sd` (tape `0`) and the gate
list `gsW W (parse C)` of a window predicate (tape `1`), without the gate list of `f̂`: the
simulation of `f̂` is computed block by block on the word machine (`ValVM`, step
`simStepP ginvTopP` on joint words), the predicate's Ring-GSW simulation on a second run of the
machine (step `simStepP ginvGswP`), and `simKeyP` reads the output bundle of `f̂` at the identity
positions.

The block runs in the coordinates of the machine (`wfBody`), framed by the permutation `eW` of the
256 tapes that puts `sdEnc sd` on the word `88`, the gate list on the word `GS = 101` and the output
on the scratch tape `255`:

1. `prepT`: a copy of the gate list (`89`), the gate count (`convP`, framed), the content templates
   (`simTmplP`, framed on the words `0 … 30`), the step's store, the templates (`natP`), `OB`, `ZB`;
2. the run of `f̂` (`fhatFullC`): the streams of the inputs, `one`, `fhatC`, its output bundle
   copied to the word `45`;
3. `prepG`: the step's store and the templates of the predicate's run;
4. the run of the predicate (`gswFullC`), then the unary positions (`posC`);
5. `simKeyP` on the output bundle, the positions, the predicate's output wire;
6. every tape but the word `88` and the output cleared.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.Prog Matrix AdvancedEncryption.RingBTVW AdvancedEncryption.DualUse.Algo
  Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow
open scoped SigabaNeo.Tape.Prog

set_option linter.unusedSimpArgs false

namespace WB2

open SigabaNeo.Tape.ValVM

/-! ### Tapes of the machine -/

/-- The tape of the word `x`. -/
abbrev mw (x : Fin 120) : Fin 256 := ValVM.tWd x

/-- The tape of the step's tape `j`. -/
abbrev ms (j : Fin 132) : Fin 256 := ValVM.tS j

/-- The word holding `sdEnc sd`. -/
abbrev SDW : Fin 120 := 88
/-- The copy of the gate list. -/
abbrev GSC : Fin 120 := 89
/-- The output bundle of `f̂`, kept for the key sum. -/
abbrev FOUT : Fin 120 := 45
/-- The content words of the step. -/
abbrev GADW : Fin 120 := 69
abbrev ZEROW : Fin 120 := 70
abbrev ONEW : Fin 120 := 71

/-- **The frame**: `sdEnc sd` (tape `0`) on the word `88` (tape `221`), the gate list (tape `1`) on
`GS` (tape `234`), the output (tape `2`) on the scratch tape `255`. -/
def swp : Equiv.Perm (Fin 256) :=
  (Equiv.swap 0 221).trans ((Equiv.swap 1 234).trans (Equiv.swap 2 255))

def eW : Fin 256 ↪ Fin 256 := swp.toEmbedding

/-- The tapes of `convP`: its input on `GS`, its gate count on `GCNT`, the others on the words
`1, 3 … 12`. -/
def cm13 : Fin 13 → Fin 256 := fun j =>
  if j.val = 0 then mw GS else if j.val = 2 then mw GCNT else mw ⟨j.val, by omega⟩

theorem cm13_inj : Function.Injective cm13 := by decide

/-- The tapes of `simTmplP`: the words `0 … 30`. -/
def tm31 : Fin 31 → Fin 256 := fun j => mw ⟨j.val, by omega⟩

theorem tm31_inj : Function.Injective tm31 := by decide

/-! ### The templates -/

section Tmpl

variable (N K k d W : ℕ)

/-- The number of values of a bundle. -/
abbrev nBI : ℕ := (Enum.list (α := BI N (K + 1))).length

/-- The templates of `simTmplP` (on the words `4 … 11`). -/
def tmpl31 : List (Fin 256 × ℕ) :=
  [(mw 4, K), (mw 5, N), (mw 6, N * K), (mw 7, k), (mw 8, 2 * k * (N * K)),
    (mw 9, 2 * (2 * k) * (N * K)), (mw 10, k * (N * K)), (mw 11, lenA N K k d)]

/-- The templates of the step's store (`SimPre` with `r = 1`, `GPreTop`). -/
def stepT : List (Fin 256 × ℕ) :=
  [(ms 3, K), (ms 4, N), (ms 5, N * K), (ms 6, 1), (ms 7, 2 * k), (ms 8, 2 * k), (ms 9, d * (2 * k)),
    (ms 10, 1), (ms 11, 1), (ms 12, d), (ms 13, lenA N K k 1), (ms 14, lenA N K k d),
    (ms 15, VT N K k d), (ms 16, 1 * (2 * k) * N), (ms 17, d * (2 * k) * N), (ms 86, K),
    (ms 87, 2 * k * N), (ms 88, k), (ms 89, 2 * k * (2 * k * (N * K)))]

/-- The templates of the step's store of the predicate (`SimPre` with `r = 2`, `GPreGsw`). -/
def stepG : List (Fin 256 × ℕ) :=
  [(ms 3, K), (ms 4, N), (ms 5, N * K), (ms 6, 2), (ms 7, 2 * k), (ms 8, 2 * k), (ms 9, d * (2 * k)),
    (ms 10, 1), (ms 11, 1), (ms 12, d), (ms 13, lenA N K k 2), (ms 14, lenA N K k d),
    (ms 15, VG N K k d), (ms 16, 2 * (2 * k) * N), (ms 17, d * (2 * k) * N), (ms 86, K),
    (ms 87, 2 * k * N), (ms 88, k), (ms 89, 2 * k * (2 * k * (N * K))), (ms 90, 2 * k * (N * K)),
    (ms 91, 2 * k * (N * K)), (ms 93, k * (2 * k * (N * K))), (ms 94, k * (2 * k * (N * K)))]

/-- The templates of the words of the run of `f̂` (`FInit`, the stream offsets `61 62 63`). -/
def wordsT (oB oW oP : ℕ) : List (Fin 256 × ℕ) :=
  [(ValVM.tTV, VT N K k d), (mw 10, VT N K k d), (mw 11, VT N K k d), (mw 12, K + 1), (mw 13, K + 2),
    (mw 14, (K + 1) * VT N K k d), (mw 15, (K + 2) * VT N K k d), (mw 16, (K + 3) * VT N K k d),
    (mw 20, K), (mw 27, 2), (mw 29, 1), (mw TNV, N * VT N K k d),
    (mw TNKV, N * ((K + 1) * VT N K k d)), (mw T2K, 2 * (K + 1)),
    (mw TLB, (2 * (K + 1) * N + 1) * ((K + 1) * VT N K k d)), (mw TCNT, 2 * (K + 1) * N + 1),
    (mw TH, treeHeight N (K + 1)), (mw TN, N), (mw TN1, N - 1), (mw TN1V, (N - 1) * VT N K k d),
    (mw TKV, K * VT N K k d), (mw T2kNV, 2 * (N * ((K + 1) * VT N K k d))),
    (mw T2kkNV, 2 * (K + 1) * (N * ((K + 1) * VT N K k d))), (mw TA1, lenA N K k 1),
    (mw TAd, lenA N K k d), (mw TK1, K - 1), (mw ZNK1, N * K - 1), (mw TNK, N * K),
    (mw T4k, 2 * (2 * (K + 1))), (mw T10, 10), (mw INSW, 10 * (nBI N K * VT N K k d)),
    (mw TSl, nBI N K * VT N K k d), (mw TST, (W + 1) * (nBI N K * VT N K k d)),
    (mw TD2, 2 * ((W + 1) * (nBI N K * VT N K k d))), (mw TW, W),
    (mw TPAD, (W - 10) * (nBI N K * VT N K k d)), (mw TW9, W - 9),
    (mw TINS, 10 * (nBI N K * VT N K k d)), (mw 61, oB), (mw 62, oW), (mw 63, oP)]

/-- The number of positions of the key sum. -/
abbrev nPos : ℕ := 2 * k * k * N

/-- The templates of the words of the run of the predicate (`GInit`, the stream offsets, the
templates of `posC`). -/
def wordsG (oP oR oX : ℕ) : List (Fin 256 × ℕ) :=
  [(ValVM.tTV, VG N K k d), (mw 10, VG N K k d), (mw TA1, lenA N K k 2), (mw TAd, lenA N K k d),
    (mw TK1, 0), (mw ZNK1, N * K - 1), (mw 29, 1), (mw T10, 10), (mw INSW, 10 * VG N K k d),
    (mw TSl, VG N K k d), (mw TST, (W + 1) * VG N K k d), (mw TD2, 2 * ((W + 1) * VG N K k d)),
    (mw TW, W), (mw TPAD, (W - 10) * VG N K k d), (mw TW9, W - 9), (mw TINS, 10 * VG N K k d),
    (mw 61, oP), (mw 62, oR), (mw 63, oX), (mw 73, nPos N k * nPos N k), (mw 74, nPos N k),
    (mw 75, nPos N k)]

/-- The templates of `simKeyP` on its tapes `3 … 17`, `88 … 90` (the machine's step tapes). -/
def keyT : List (Fin 256 × ℕ) :=
  [(ms 3, K), (ms 4, N), (ms 5, N * K), (ms 6, k), (ms 7, 2 * k), (ms 8, 2 * k), (ms 9, 2 * k * N),
    (ms 10, 2 * k * (N * K)), (ms 11, 2 * k * (2 * k * (N * K))), (ms 12, d),
    (ms 13, d * (2 * k) * (N * K)), (ms 14, d * (2 * k) * N), (ms 15, nPos N k),
    (ms 16, VT N K k d), (ms 17, lenA N K k 1), (ms 88, 1), (ms 89, VG N K k d),
    (ms 90, lenA N K k 2)]

end Tmpl

/-! ### The machine codes -/

open SigabaNeo.Tape.ValVM

/-- The streams of the inputs of `f̂`: the `B_j`, the `W_j`, the `ψᵢ` (offsets `61 62 63`). -/
def streamsT : Code :=
  ofList [.cp BSt SDW, .drop BSt 61, .cp WSt SDW, .drop WSt 62, .cp PSt SDW, .drop PSt 63]

/-- The streams of the inputs of the predicate: the `Ψᵢ`, the `Rᵢ`, the bits `xᵢ`. -/
def streamsG : Code :=
  ofList [.cp BSt SDW, .drop BSt 61, .cp WSt SDW, .drop WSt 62, .cp rZ SDW, .drop rZ 63]

/-- `one := gad ++ zero ++ oneW`. -/
def oneC : Code := ofList [.mv 10 GADW TA1, .mv 10 ZEROW TAd, .mv 10 ONEW TNK]

/-- **The run of `f̂`**, its output bundle kept on `FOUT`. -/
def fhatFullC : Code := ofList [streamsT, oneC, fhatC, .cp FOUT OUTW]

/-- **The run of the predicate**, then the unary positions. -/
def gswFullC : Code := ofList [.cp GS GSC, streamsG, oneC, gswC, posC]

/-! ### The phases -/

/-- The content words of the step copied to the step's tapes and to `GADW ZEROW ONEW`
(`g` the word of the gadget among the outputs of `simTmplP`). -/
def copiesP (g : Fin 120) : Prog 256 :=
  cp (ms 19) (mw g) ⨾ cp (ms 20) (mw 2) ⨾ cp (ms 21) (mw 3) ⨾ cp (mw GADW) (mw g) ⨾
    cp (mw ZEROW) (mw 2) ⨾ cp (mw ONEW) (mw 3)

/-- The words `0 … 30` and `GCNT`. -/
def lowW : List (Fin 256) := (List.finRange 31).map (fun j => mw ⟨j.val, by omega⟩) ++ [mw GCNT]

/-- A certificate of the step with no content (the program does not depend on it). -/
def nocert (P : Prog 132) : StepCert (fun _ => False) P := ⟨[], [], [], [], fun _ h => h.elim⟩

/-- The run of `f̂` on the machine. -/
noncomputable def runT : XProg 256 := (compileA (nocert (simStepP ginvTopP)) fhatFullC).toX

/-- The run of the predicate on the machine. -/
noncomputable def runG : XProg 256 := (compileA (nocert (simStepP ginvGswP)) gswFullC).toX

/-- The tapes of `simKeyP`: its output on `255`, the bundle of `f̂` on `FOUT`, the positions on
`61`, the predicate's output wire on `OUTW`, the others on the step's tapes. -/
def oK2 : Fin 94 → Fin 256 := fun j =>
  if j.val = 0 then 255 else if j.val = 1 then mw FOUT else if j.val = 2 then mw 61
  else if j.val = 86 then mw OUTW else ⟨j.val, by omega⟩

theorem oK2_inj : Function.Injective oK2 := by decide

/-- The step's tapes cleared before the key sum. -/
def keyClr : List (Fin 256) :=
  (List.finRange 19).map (fun j => ⟨j.val + 3, by omega⟩) ++
    (List.finRange 9).map (fun j => ⟨j.val + 86, by omega⟩)

/-- The preparation of the key sum. -/
def keyPrep (N K k d : ℕ) : XProg 256 :=
  .seq (.prog (clrsP keyClr)) (.seq (tmplP ValVM.tX0 (keyT N K k d)) (putW (ms 87) [false]))

/-- Every tape but `sdEnc sd` and the output. -/
def finClr : List (Fin 256) := (List.finRange 256).filter fun t => t ≠ mw SDW ∧ t ≠ 255

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- **The preparation of the run of `f̂`.** -/
def prepT (W : ℕ) : XProg 256 :=
  .seq (.prog (cp (mw GSC) (mw GS))) <|
  .seq (.prog (Prog.map cm13 (convP W))) <|
  .seq (.prog (cp (mw GS) (mw GSC))) <|
  .seq (tmplP ValVM.tX0 (tmpl31 N K k c.d)) <|
  .seq (.prog (Prog.map tm31 simTmplP ⨾ copiesP 0)) <|
  .seq (tmplP ValVM.tX0 (stepT N K k c.d ++ wordsT N K k c.d W (offB c) (offW hk c) (offPsi hk c))) <|
  .seq (putW (mw OB) [true]) (putW (mw ZB) [false])

/-- **The preparation of the run of the predicate.** -/
def prepG (W : ℕ) : XProg 256 :=
  .seq (.prog (clrsP lowW ⨾ cp (mw GS) (mw GSC))) <|
  .seq (.prog (Prog.map cm13 (convP W))) <|
  .seq (.prog (cp (mw GS) (mw GSC))) <|
  .seq (tmplP ValVM.tX0 (tmpl31 N K k c.d)) <|
  .seq (.prog (Prog.map tm31 simTmplP ⨾ copiesP 1)) <|
  (tmplP ValVM.tX0 (stepG N K k c.d ++ wordsG N K k c.d W (offPsi hk c) (offR hk c)
    (offPsi hk c + 10 * lenPsi N K k)))

/-- **The body**, in the machine's coordinates. -/
noncomputable def wfBody (W : ℕ) : XProg 256 :=
  .seq (prepT hk c W) <| .seq runT <| .seq (prepG hk c W) <| .seq runG <|
  .seq (keyPrep N K k c.d) <| .seq (.frame (ValVM.mkE oK2 oK2_inj) (.prog simKeyP))
    (.prog (clrsP finClr))

end WB2

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

open WB2 in
/-- **The block-structured `W_f` block.** -/
noncomputable def wfB2 (W : ℕ) : XProg 256 := .frame eW (wfBody hk c W)


end AdvancedEncryption.DualUse.Prog
