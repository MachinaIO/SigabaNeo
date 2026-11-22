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
set_option maxRecDepth 100000

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

/-! ### Lookups -/

theorem tmplS_mem {n : ℕ} : ∀ (l : List (Fin n × ℕ)), (l.map Prod.fst).Nodup → ∀ x ∈ l,
    ∀ s : Store n, tmplS l s x.1 = List.replicate x.2 false
  | [], _, _, hx, _ => absurd hx (by simp)
  | y :: l, hn, x, hx, s => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rw [tmplS, List.foldl_cons, ← tmplS]
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [tmplS_apply_of_not_mem l _ _ (fun z hz e => hn.1 ⟨z, hz, e⟩), Function.update_self]
    · exact tmplS_mem l hn.2 x hx _

theorem tmplS_eq {n : ℕ} : ∀ (l : List (Fin n × ℕ)), (l.map Prod.fst).Nodup → ∀ (s : Store n)
    (t : Fin n), tmplS l s t = match l.lookup t with
      | some m => List.replicate m false
      | none => s t
  | [], _, s, t => by simp [tmplS]
  | (y1, y2) :: l, hn, s, t => by
    simp only [List.map_cons, List.nodup_cons] at hn
    rw [tmplS, List.foldl_cons, ← tmplS, tmplS_eq l hn.2, List.lookup_cons]
    by_cases h : t = y1
    · subst h
      have : l.lookup t = none := by
        rw [List.lookup_eq_none_iff]; intro p hp
        simp only [bne_iff_ne, ne_eq]
        intro hpe
        exact hn.1 (by rw [List.mem_map]; exact ⟨p, hp, hpe.symm⟩)
      simp [this]
    · have : (t == y1) = false := by simpa using h
      simp only [this, Function.update_of_ne h]

theorem run_map_apply {n m : ℕ} {u : Fin n → Fin m} (hu : Function.Injective u) (p : Prog n)
    (s : Store m) (j : Fin n) : run (Prog.map u p) s (u j) = run p (s ∘ u) j := by
  rw [run_map hu, hu.extend_apply]

theorem run_map_apply_not {n m : ℕ} {u : Fin n → Fin m} (hu : Function.Injective u) (p : Prog n)
    (s : Store m) (t : Fin m) (ht : ∀ j, u j ≠ t) : run (Prog.map u p) s t = s t := by
  rw [run_map hu, Function.extend_apply' _ _ _ (fun ⟨j, hj⟩ => ht j hj)]

end WB2

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

open WB2 in
/-- **The block-structured `W_f` block.** -/
noncomputable def wfB2 (W : ℕ) : XProg 256 := .frame eW (wfBody hk c W)


namespace WB2

open SigabaNeo.Tape.ValVM

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-! ### The preparation of the run of `f̂` -/

section PrepT

variable (W : ℕ) (a : List Bool) (gs : GateList)

/-- The input, in the machine's coordinates. -/
def S0 : Store 256 := fun t => if t = mw SDW then a else if t = mw GS then gsW W gs else []

def X2 : Store 256 :=
  run (Prog.map cm13 (convP W)) (Function.update (S0 W a gs) (mw GSC) (S0 W a gs (mw GS)))

def X4 : Store 256 := tmplS (tmpl31 N K k c.d) (Function.update (X2 W a gs) (mw GS) (X2 W a gs (mw GSC)))

def X5 : Store 256 := run (Prog.map tm31 simTmplP ⨾ copiesP 0) (X4 c W a gs)

def X6 : Store 256 :=
  tmplS (stepT N K k c.d ++ wordsT N K k c.d W (offB c) (offW hk c) (offPsi hk c)) (X5 c W a gs)

/-- The store after `prepT`. -/
def S1 : Store 256 := Function.update (Function.update (X6 hk c W a gs) (mw OB)
  (X6 hk c W a gs (mw OB) ++ [true])) (mw ZB)
  (Function.update (X6 hk c W a gs) (mw OB) (X6 hk c W a gs (mw OB) ++ [true]) (mw ZB) ++ [false])

theorem coinFree_copiesP (g : Fin 120) : (copiesP g).CoinFree := rfl

theorem ne_of_keys {l : List (Fin 256 × ℕ)} {ks : List (Fin 256)} (hks : l.map Prod.fst = ks)
    {t : Fin 256} (ht : t ∉ ks) : ∀ x ∈ l, x.1 ≠ t := fun x hx e =>
  ht (hks ▸ e ▸ List.mem_map_of_mem hx)

theorem keys_tmpl31 (N K k d : ℕ) : (tmpl31 N K k d).map Prod.fst =
    [mw 4, mw 5, mw 6, mw 7, mw 8, mw 9, mw 10, mw 11] := rfl

theorem keys_T (N K k d W oB oW oP : ℕ) :
    (stepT N K k d ++ wordsT N K k d W oB oW oP).map Prod.fst =
      [ms 3, ms 4, ms 5, ms 6, ms 7, ms 8, ms 9, ms 10, ms 11, ms 12, ms 13, ms 14, ms 15, ms 16,
        ms 17, ms 86, ms 87, ms 88, ms 89, ValVM.tTV, mw 10, mw 11, mw 12, mw 13, mw 14, mw 15, mw 16,
        mw 20, mw 27, mw 29, mw TNV, mw TNKV, mw T2K, mw TLB, mw TCNT, mw TH, mw TN, mw TN1, mw TN1V,
        mw TKV, mw T2kNV, mw T2kkNV, mw TA1, mw TAd, mw TK1, mw ZNK1, mw TNK, mw T4k, mw T10,
        mw INSW, mw TSl, mw TST, mw TD2, mw TW, mw TPAD, mw TW9, mw TINS, mw 61, mw 62, mw 63] := rfl

theorem X2_tX0 : X2 W a gs tX0 = [] := by
  rw [X2, run_map_apply_not cm13_inj _ _ _ (by decide), Function.update_of_ne (by decide)]
  simp (config := {decide := true}) [S0]

theorem X4_tX0 : X4 c W a gs tX0 = [] := by
  rw [X4, tmplS_apply_of_not_mem _ _ _ (ne_of_keys (keys_tmpl31 N K k c.d) (by decide)),
    Function.update_of_ne (by decide), X2_tX0]

theorem X5_tX0 : X5 c W a gs tX0 = [] := by
  rw [X5, run_seq]
  simp only [copiesP, run_seq, run_copy]
  simp (config := {decide := true}) only [Function.update_apply, if_false]
  rw [run_map_apply_not tm31_inj _ _ _ (by decide), X4_tX0]

theorem law_prepT : (prepT hk c W).law (S0 W a gs) = PMF.pure (S1 hk c W a gs) := by
  have hc1 : (Prog.map cm13 (convP W)).CoinFree := coinFree_map _ (coinFree_convP W)
  have hc2 : (Prog.map tm31 simTmplP ⨾ copiesP 0).CoinFree := by
    have h1 := coinFree_map tm31 (coinFree_of_noGrow _ noGrow_simTmplP)
    simp only [CoinFree] at h1 ⊢
    simp [coinFreeB, h1, show (copiesP 0).coinFreeB = true from rfl]
  rw [prepT, XProg.law_seq, XProg.law_prog, law_eq_run_of_coinFree _ (by rfl), PMF.pure_bind,
    XProg.law_seq, XProg.law_prog, law_eq_run_of_coinFree _ hc1, PMF.pure_bind,
    XProg.law_seq, XProg.law_prog, law_eq_run_of_coinFree _ (by rfl), PMF.pure_bind]
  simp only [run_copy]
  rw [XProg.law_seq, law_tmplP _ _ _ (by
      rw [Function.update_of_ne (by decide)]; exact X2_tX0 W a gs)
      (ne_of_keys (keys_tmpl31 N K k c.d) (by decide)),
    PMF.pure_bind, XProg.law_seq, XProg.law_prog, law_eq_run_of_coinFree _ hc2, PMF.pure_bind,
    XProg.law_seq, law_tmplP _ _ _ (by exact X5_tX0 c W a gs)
      (ne_of_keys (keys_T N K k c.d W _ _ _) (by decide)),
    PMF.pure_bind, XProg.law_seq, law_putW, PMF.pure_bind, law_putW]
  rfl

theorem nodup_T (N K k d W oB oW oP : ℕ) :
    ((stepT N K k d ++ wordsT N K k d W oB oW oP).map Prod.fst).Nodup := by
  rw [keys_T]; decide

theorem nodup_31 (N K k d : ℕ) : ((tmpl31 N K k d).map Prod.fst).Nodup := by
  rw [keys_tmpl31]; decide

/-- The gate count and the junk of `convP`. -/
theorem X2_apply (hW : 0 < W) (hb : BndG W gs) (t : Fin 256) :
    X2 W a gs t = if t = mw GS then [] else
      if t = mw 1 then gatesW (fun i : Fin 10 => i.val) 10 W (predOf 10 gs).1 0 else
      if t = mw GCNT then List.replicate gs.length false else
      if t = mw 3 then unaryW W (gs.length + 10) else
      Function.update (S0 W a gs) (mw GSC) (gsW W gs) t := by
  have hin : (Function.update (S0 W a gs) (mw GSC) (S0 W a gs (mw GS))) ∘ cm13 =
      fun i => if i = 0 then gsW W gs else [] := by
    funext i
    fin_cases i <;> simp (config := {decide := true}) [cm13, S0, Function.update_apply]
  rw [X2]
  by_cases ht : ∃ j, cm13 j = t
  · obtain ⟨j, rfl⟩ := ht
    rw [run_map_apply cm13_inj, hin, run_convP hW gs hb _ rfl]
    fin_cases j <;> simp (config := {decide := true}) [cm13, S0, Function.update_apply]
  · push_neg at ht
    rw [run_map_apply_not cm13_inj _ _ _ ht]
    have h1 : t ≠ mw GS := fun e => ht 0 (by rw [e]; rfl)
    have h2 : t ≠ mw 1 := fun e => ht 1 (by rw [e]; rfl)
    have h3 : t ≠ mw GCNT := fun e => ht 2 (by rw [e]; rfl)
    have h4 : t ≠ mw 3 := fun e => ht 3 (by rw [e]; rfl)
    simp (config := {decide := true}) [h1, h2, h3, h4, Function.update_apply, S0]

theorem X4_word (hW : 0 < W) (hb : BndG W gs) (j : ℕ) (hj : 12 ≤ j) (hj' : j < 120) (h31 : j < 31) :
    X4 c W a gs (mw ⟨j, hj'⟩) = [] := by
  have hv : ∀ x : Fin 120, (mw ⟨j, hj'⟩ : Fin 256) = mw x → j = x.val := fun x e => by
    have := congrArg Fin.val e; simp [ValVM.tWd] at this; omega
  rw [X4, tmplS_apply_of_not_mem _ _ _ (ne_of_keys (keys_tmpl31 N K k c.d) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> have := hv _ e <;> simp at this <;>
      omega)), Function.update_of_ne (fun e => by have := hv _ e; simp at this; omega),
    X2_apply W a gs hW hb]
  have h1 : (mw ⟨j, hj'⟩ : Fin 256) ≠ mw GS := fun e => by have := hv _ e; simp at this; omega
  have h2 : (mw ⟨j, hj'⟩ : Fin 256) ≠ mw 1 := fun e => by have := hv _ e; simp at this; omega
  have h3 : (mw ⟨j, hj'⟩ : Fin 256) ≠ mw GCNT := fun e => by have := hv _ e; simp at this; omega
  have h4 : (mw ⟨j, hj'⟩ : Fin 256) ≠ mw 3 := fun e => by have := hv _ e; simp at this; omega
  have h5 : (mw ⟨j, hj'⟩ : Fin 256) ≠ mw GSC := fun e => by have := hv _ e; simp at this; omega
  have h6 : (mw ⟨j, hj'⟩ : Fin 256) ≠ mw SDW := fun e => by have := hv _ e; simp at this; omega
  simp [h1, h2, h3, h4, h5, h6, Function.update_apply, S0]

theorem X4_key {t : Fin 256} {n : ℕ} (h : (t, n) ∈ tmpl31 N K k c.d) :
    X4 c W a gs t = List.replicate n false := by
  rw [X4]; exact tmplS_mem _ (nodup_31 _ _ _ _) (t, n) h _

/-- The content words written by `simTmplP`. -/
theorem Y4_apply (hW : 0 < W) (hb : BndG W gs) (t : Fin 256) :
    run (Prog.map tm31 simTmplP) (X4 c W a gs) t =
      if t = mw 0 then gadW N K k else if t = mw 1 then gswGadW N K k else
      if t = mw 2 then zeroW (lenA N K k c.d) else if t = mw 3 then oneW N K else X4 c W a gs t := by
  have hrun := run_simTmplP (N := N) (K := K) (k := k) (Lw := lenA N K k c.d)
    (X4 c W a gs ∘ tm31) (fun t ht => by
      have := X4_word c W a gs hW hb t.val ht (by omega) t.isLt
      simpa [tm31] using this)
    (by simp [tm31, X4_key c W a gs (t := mw 4) (n := K) (by simp [tmpl31])])
    (by simp [tm31, X4_key c W a gs (t := mw 5) (n := N) (by simp [tmpl31])])
    (by simp [tm31, X4_key c W a gs (t := mw 6) (n := N * K) (by simp [tmpl31])])
    (by simp [tm31, X4_key c W a gs (t := mw 7) (n := k) (by simp [tmpl31])])
    (by simp [tm31, X4_key c W a gs (t := mw 8) (n := 2 * k * (N * K)) (by simp [tmpl31])])
    (by simp [tm31, X4_key c W a gs (t := mw 9) (n := 2 * (2 * k) * (N * K)) (by simp [tmpl31])])
    (by simp [tm31, X4_key c W a gs (t := mw 10) (n := k * (N * K)) (by simp [tmpl31])])
    (by simp [tm31, X4_key c W a gs (t := mw 11) (n := lenA N K k c.d) (by simp [tmpl31])])
  by_cases ht : ∃ j, tm31 j = t
  · obtain ⟨j, rfl⟩ := ht
    rw [run_map_apply tm31_inj, hrun]
    fin_cases j <;> simp (config := {decide := true}) [tm31, Function.update_apply]
  · push_neg at ht
    rw [run_map_apply_not tm31_inj _ _ _ ht]
    have h0 : t ≠ mw 0 := fun e => ht 0 (by rw [e]; rfl)
    have h1 : t ≠ mw 1 := fun e => ht 1 (by rw [e]; rfl)
    have h2 : t ≠ mw 2 := fun e => ht 2 (by rw [e]; rfl)
    have h3 : t ≠ mw 3 := fun e => ht 3 (by rw [e]; rfl)
    simp [h0, h1, h2, h3]

/-! #### Lookups of `S1` -/

theorem S1_key {t : Fin 256} {n : ℕ}
    (h : (t, n) ∈ stepT N K k c.d ++ wordsT N K k c.d W (offB c) (offW hk c) (offPsi hk c))
    (h1 : t ≠ mw OB) (h2 : t ≠ mw ZB) : S1 hk c W a gs t = List.replicate n false := by
  rw [S1, Function.update_of_ne h2, Function.update_of_ne h1, X6]
  exact tmplS_mem _ (nodup_T _ _ _ _ _ _ _ _) (t, n) h _

theorem S1_not {t : Fin 256} (h : t ∉ [ms 3, ms 4, ms 5, ms 6, ms 7, ms 8, ms 9, ms 10, ms 11,
    ms 12, ms 13, ms 14, ms 15, ms 16, ms 17, ms 86, ms 87, ms 88, ms 89, ValVM.tTV, mw 10, mw 11,
    mw 12, mw 13, mw 14, mw 15, mw 16, mw 20, mw 27, mw 29, mw TNV, mw TNKV, mw T2K, mw TLB, mw TCNT,
    mw TH, mw TN, mw TN1, mw TN1V, mw TKV, mw T2kNV, mw T2kkNV, mw TA1, mw TAd, mw TK1, mw ZNK1,
    mw TNK, mw T4k, mw T10, mw INSW, mw TSl, mw TST, mw TD2, mw TW, mw TPAD, mw TW9, mw TINS, mw 61,
    mw 62, mw 63]) (h1 : t ≠ mw OB) (h2 : t ≠ mw ZB) : S1 hk c W a gs t = X5 c W a gs t := by
  rw [S1, Function.update_of_ne h2, Function.update_of_ne h1, X6,
    tmplS_apply_of_not_mem _ _ _ (ne_of_keys (keys_T N K k c.d W _ _ _) h)]

theorem X5_apply (t : Fin 256) : X5 c W a gs t =
    if t = mw ONEW then run (Prog.map tm31 simTmplP) (X4 c W a gs) (mw 3) else
    if t = mw ZEROW then run (Prog.map tm31 simTmplP) (X4 c W a gs) (mw 2) else
    if t = mw GADW then run (Prog.map tm31 simTmplP) (X4 c W a gs) (mw 0) else
    if t = ms 21 then run (Prog.map tm31 simTmplP) (X4 c W a gs) (mw 3) else
    if t = ms 20 then run (Prog.map tm31 simTmplP) (X4 c W a gs) (mw 2) else
    if t = ms 19 then run (Prog.map tm31 simTmplP) (X4 c W a gs) (mw 0) else
    run (Prog.map tm31 simTmplP) (X4 c W a gs) t := by
  simp only [X5, run_seq, copiesP, run_copy]
  simp (config := {decide := true}) only [Function.update_apply, if_false]

/-- The tapes `tmplP` writes in `prepT`. -/
abbrev keysT : List (Fin 256) := [ms 3, ms 4, ms 5, ms 6, ms 7, ms 8, ms 9, ms 10, ms 11,
    ms 12, ms 13, ms 14, ms 15, ms 16, ms 17, ms 86, ms 87, ms 88, ms 89, ValVM.tTV, mw 10, mw 11,
    mw 12, mw 13, mw 14, mw 15, mw 16, mw 20, mw 27, mw 29, mw TNV, mw TNKV, mw T2K, mw TLB, mw TCNT,
    mw TH, mw TN, mw TN1, mw TN1V, mw TKV, mw T2kNV, mw T2kkNV, mw TA1, mw TAd, mw TK1, mw ZNK1,
    mw TNK, mw T4k, mw T10, mw INSW, mw TSl, mw TST, mw TD2, mw TW, mw TPAD, mw TW9, mw TINS, mw 61,
    mw 62, mw 63]

/-- **Before the bits `OB`, `ZB`, `prepT` leaves the other tapes as they were.** -/
theorem X6_eq_S0 (t : Fin 256) (h1 : t ∉ keysT)
    (h2 : t ∉ [ms 19, ms 20, ms 21, mw GADW, mw ZEROW, mw ONEW, mw GS, mw GSC])
    (h3 : ∀ j, tm31 j ≠ t) (h4 : ∀ j, cm13 j ≠ t)
    (h5 : t ∉ [mw 4, mw 5, mw 6, mw 7, mw 8, mw 9, mw 10, mw 11]) :
    X6 hk c W a gs t = S0 W a gs t := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h2
  obtain ⟨a3, a4, a5, a6, a7, a8, a9, a10⟩ := h2
  rw [X6, tmplS_apply_of_not_mem _ _ _ (ne_of_keys (keys_T N K k c.d W _ _ _) h1), X5_apply]
  simp only [if_neg a8, if_neg a7, if_neg a6, if_neg a5, if_neg a4, if_neg a3]
  rw [run_map_apply_not tm31_inj _ _ _ h3, X4, tmplS_apply_of_not_mem _ _ _
    (ne_of_keys (keys_tmpl31 N K k c.d) h5), Function.update_of_ne a9, X2,
    run_map_apply_not cm13_inj _ _ _ h4, Function.update_of_ne a10]

theorem S1_eq_S0 (t : Fin 256) (h1 : t ∉ keysT)
    (h2 : t ∉ [ms 19, ms 20, ms 21, mw GADW, mw ZEROW, mw ONEW, mw GS, mw GSC])
    (h3 : ∀ j, tm31 j ≠ t) (h4 : ∀ j, cm13 j ≠ t)
    (h5 : t ∉ [mw 4, mw 5, mw 6, mw 7, mw 8, mw 9, mw 10, mw 11]) (h6 : t ≠ mw OB)
    (h7 : t ≠ mw ZB) : S1 hk c W a gs t = S0 W a gs t := by
  rw [S1, Function.update_of_ne h7, Function.update_of_ne h6, X6_eq_S0 hk c W a gs t h1 h2 h3 h4 h5]

theorem S1_OB : S1 hk c W a gs (mw OB) = [true] := by
  rw [S1, Function.update_of_ne (by decide), Function.update_self,
    X6_eq_S0 hk c W a gs _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  rfl

theorem S1_ZB : S1 hk c W a gs (mw ZB) = [false] := by
  rw [S1, Function.update_self, Function.update_of_ne (by decide),
    X6_eq_S0 hk c W a gs _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  rfl

theorem S0_blank (t : Fin 256) (h1 : t ≠ mw SDW) (h2 : t ≠ mw GS) : S0 W a gs t = [] := by
  simp [S0, h1, h2]

/-- The step's store prepared for the run of `f̂`. -/
def s1 : Store 132 := fun j => S1 hk c W a gs (ms j)

/-- The words prepared for the run of `f̂`. -/
def w1 : ValVM.St := fun x => S1 hk c W a gs (mw x)

theorem S1_enc : S1 hk c W a gs = ValVM.enc (s1 hk c W a gs) (VT N K k c.d) (w1 hk c W a gs) := by
  refine ValVM.enc_ext (fun j => ?_) ?_ (fun x => ?_) ?_ ?_ ?_
  · simp [s1]
  · rw [ValVM.enc_tTV, S1_key hk c W a gs (n := VT N K k c.d) (by simp [stepT, wordsT])
      (by decide) (by decide)]
  · simp [w1]
  all_goals
    rw [S1_eq_S0 hk c W a gs _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), S0_blank W a gs _ (by decide) (by decide)]
    simp

/-- The step's tapes `prepT` does not write. -/
theorem s1_blank (t : Fin 132)
    (ht : ∀ j ∈ [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 86, 87, 88, 89],
      t.val ≠ j) : s1 hk c W a gs t = [] := by
  have key : ∀ t : Fin 132, (∀ j ∈ [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20,
      21, 86, 87, 88, 89], t.val ≠ j) → ms t ∉ keysT ∧
      ms t ∉ [ms 19, ms 20, ms 21, mw GADW, mw ZEROW, mw ONEW, mw GS, mw GSC] ∧
      (∀ j, tm31 j ≠ ms t) ∧ (∀ j, cm13 j ≠ ms t) ∧
      ms t ∉ [mw 4, mw 5, mw 6, mw 7, mw 8, mw 9, mw 10, mw 11] ∧ ms t ≠ mw OB ∧ ms t ≠ mw ZB ∧
      ms t ≠ mw SDW ∧ ms t ≠ mw GS := by decide +kernel
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := key t ht
  rw [s1, S1_eq_S0 hk c W a gs _ b1 b2 b3 b4 b5 b6 b7, S0_blank W a gs _ b8 b9]

theorem s1_tmpl {j : Fin 132} {n : ℕ}
    (h : (ms j, n) ∈ stepT N K k c.d ++ wordsT N K k c.d W (offB c) (offW hk c) (offPsi hk c)) :
    (s1 hk c W a gs j).length = n := by
  rw [s1, S1_key hk c W a gs h (ValVM.tS_ne_tWd _ _) (ValVM.tS_ne_tWd _ _), List.length_replicate]

theorem s1_content (hW : 0 < W) (hb : BndG W gs) :
    s1 hk c W a gs 19 = gadW N K k ∧ s1 hk c W a gs 20 = zeroW (lenA N K k c.d) ∧
      s1 hk c W a gs 21 = oneW N K := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [s1, S1_not hk c W a gs (by decide) (by decide) (by decide), X5_apply]
    simp (config := {decide := true}) only [Y4_apply c W a gs hW hb, if_true, if_false]

/-- **The step's store prepared for `f̂` meets `SimPre`.** -/
theorem s1_simPre (hW : 0 < W) (hb : BndG W gs) :
    SimPre N K k 1 c.d (gadW N K k) (GPreTop N K k) (s1 hk c W a gs) where
  blank i h h' := s1_blank hk c W a gs i (by intro j hj; simp at hj; omega)
  h3 := s1_tmpl hk c W a gs (by simp [stepT])
  h4 := s1_tmpl hk c W a gs (by simp [stepT])
  h5 := s1_tmpl hk c W a gs (by simp [stepT])
  h6 := s1_tmpl hk c W a gs (by simp [stepT])
  h7 := s1_tmpl hk c W a gs (by simp [stepT])
  h8 := s1_tmpl hk c W a gs (by simp [stepT])
  h9 := s1_tmpl hk c W a gs (by simp [stepT])
  h10 := s1_tmpl hk c W a gs (by simp [stepT])
  h11 := s1_tmpl hk c W a gs (by simp [stepT])
  h12 := s1_tmpl hk c W a gs (by simp [stepT])
  h13 := s1_tmpl hk c W a gs (by simp [stepT])
  h14 := s1_tmpl hk c W a gs (by simp [stepT])
  h15 := s1_tmpl hk c W a gs (by simp [stepT])
  h16 := s1_tmpl hk c W a gs (by simp [stepT])
  h17 := s1_tmpl hk c W a gs (by simp [stepT])
  h19 := (s1_content hk c W a gs hW hb).1
  h20 := (s1_content hk c W a gs hW hb).2.1
  h21 := (s1_content hk c W a gs hW hb).2.2
  g := by
    refine ⟨fun i h h' => ?_, ?_, ?_, ?_, ?_⟩
    · show s1 hk c W a gs (vG i) = []
      exact s1_blank hk c W a gs _ (by
        have : ∀ i : Fin 48, 6 ≤ i.val → i.val < 35 → ∀ j ∈ [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13,
          14, 15, 16, 17, 19, 20, 21, 86, 87, 88, 89], (vG i).val ≠ j := by decide +kernel
        exact this i h h')
    · rw [Function.comp_apply, show vG 2 = 86 from rfl]
      exact s1_tmpl hk c W a gs (by simp [stepT])
    · rw [Function.comp_apply, show vG 3 = 87 from rfl]
      exact s1_tmpl hk c W a gs (by simp [stepT])
    · rw [Function.comp_apply, show vG 4 = 88 from rfl]
      exact s1_tmpl hk c W a gs (by simp [stepT])
    · rw [Function.comp_apply, show vG 5 = 89 from rfl]
      exact s1_tmpl hk c W a gs (by simp [stepT])

end PrepT

/-! ### The entries of the words `ψᵢ` -/

theorem concatN_eq_flatten (n : ℕ) (f : ℕ → List Bool) :
    concatN n f = ((List.range n).map f).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => rw [concatN, ih, List.range_succ, List.map_append, List.flatten_append]; simp

/-- The entry `q = (a, (c₁, c₂))` of the word of a `2 × 2k` matrix. -/
def entQ (N K k : ℕ) (w : List Bool) (q : Fin 2 × (Fin 2 × Fin k)) : List Bool :=
  rget N K (q.1.val * (2 * k) + (q.2.1.val * k + q.2.2.val)) w

theorem getElem_product_div {α β : Type*} (l₁ : List α) (l₂ : List β) {i : ℕ}
    (hi : i < (l₁ ×ˢ l₂).length) :
    (l₁ ×ˢ l₂)[i] = (l₁[i / l₂.length]'(by
        rw [List.length_product] at hi
        exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi)),
      l₂[i % l₂.length]'(Nat.mod_lt _ (by
        rw [List.length_product] at hi; rcases Nat.eq_zero_or_pos l₂.length with h | h
        · rw [h] at hi; simp at hi
        · exact h))) := by
  have hl : 0 < l₂.length := by
    rw [List.length_product] at hi; rcases Nat.eq_zero_or_pos l₂.length with h | h
    · rw [h] at hi; simp at hi
    · exact h
  have h := ValVM.getD_product_map' l₁ l₂ (C := l₂.length) rfl id (l₁[0]'(by
      rw [List.length_product] at hi; rcases Nat.eq_zero_or_pos l₁.length with h | h
      · rw [h] at hi; simp at hi
      · exact h), l₂[0]'hl) (i := i / l₂.length) (j := i % l₂.length)
    (Nat.div_lt_of_lt_mul (by rw [List.length_product] at hi; rwa [Nat.mul_comm] at hi))
    (Nat.mod_lt _ hl)
  rw [List.map_id, Nat.div_add_mod' i l₂.length, List.getD_eq_getElem _ _ hi] at h
  exact h

theorem qsL_idx (k : ℕ) : (ValVM.qsL k).map (fun q => q.1.val * (2 * k) + (q.2.1.val * k + q.2.2.val))
    = List.range (2 * (2 * k)) := by
  apply List.ext_getElem (by simp [ValVM.length_qsL])
  intro i h1 h2
  simp only [List.length_map] at h1
  rw [List.getElem_map, List.getElem_range]
  simp only [ValVM.qsL]
  rw [getElem_product_div]
  simp only [List.getElem_finRange, Fin.val_cast, ValVM.cols]
  rw [getElem_product_div]
  simp only [List.getElem_finRange, Fin.val_cast, List.length_finRange, List.length_product]
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp [ValVM.length_qsL] at h1
    · exact h
  rw [Nat.div_add_mod' (i % (2 * k)) k, Nat.div_add_mod' i (2 * k)]

theorem qsL_entries (N K k : ℕ) (w : List Bool) (hw : w.length = 2 * (2 * k) * (N * K)) :
    ((ValVM.qsL k).map (entQ N K k w)).flatten = w := by
  have e : (ValVM.qsL k).map (entQ N K k w) =
      ((ValVM.qsL k).map (fun q => q.1.val * (2 * k) + (q.2.1.val * k + q.2.2.val))).map
        (fun p => rget N K p w) := by rw [List.map_map]; rfl
  rw [e, qsL_idx, ← concatN_eq_flatten]
  exact concatN_block hw

end WB2

end AdvancedEncryption.DualUse.Prog
