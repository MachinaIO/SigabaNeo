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
    (mw TK1, 0), (mw ZNK1, N * K - 1), (mw TNK, N * K), (mw 29, 1), (mw T10, 10), (mw INSW, 10 * VG N K k d),
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

/-! ### The streams and `one` -/

section Streams

variable {V : ℕ} {f : List Bool → List Bool → List Bool}

theorem exec_streamsT (w : St) : exec V f streamsT w =
    Function.update (Function.update (Function.update w BSt ((w SDW).drop (w 61).length)) WSt
      ((w SDW).drop (w 62).length)) PSt ((w SDW).drop (w 63).length) := by
  funext x
  simp (config := {decide := true}) only [streamsT, exec_ofList, List.foldl_cons, List.foldl_nil,
    exec_cp', exec_drop' (show BSt ≠ 61 by decide), exec_drop' (show WSt ≠ 62 by decide),
    exec_drop' (show PSt ≠ 63 by decide), Function.update_apply]
  split_ifs <;> simp_all

theorem exec_streamsG (w : St) : exec V f streamsG w =
    Function.update (Function.update (Function.update w BSt ((w SDW).drop (w 61).length)) WSt
      ((w SDW).drop (w 62).length)) rZ ((w SDW).drop (w 63).length) := by
  funext x
  simp (config := {decide := true}) only [streamsG, exec_ofList, List.foldl_cons, List.foldl_nil,
    exec_cp', exec_drop' (show BSt ≠ 61 by decide), exec_drop' (show WSt ≠ 62 by decide),
    exec_drop' (show rZ ≠ 63 by decide), Function.update_apply]
  split_ifs <;> simp_all

theorem exec_oneC (w : St) {g z o : List Bool} (h10 : w 10 = List.replicate V false)
    (hV : V = g.length + z.length + o.length) (hg : w GADW = g) (hz : w ZEROW = z)
    (ho : w ONEW = o) (h1 : (w TA1).length = g.length) (h2 : (w TAd).length = z.length)
    (h3 : (w TNK).length = o.length) :
    exec V f oneC w 10 = g ++ z ++ o ∧
      ∀ x, x ≠ 10 → x ≠ GADW → x ≠ ZEROW → x ≠ ONEW → exec V f oneC w x = w x := by
  simp only [oneC, exec_ofList, List.foldl_cons, List.foldl_nil]
  rw [exec_mv_shift (d := 10) (s := GADW) (c := TA1) (by decide) (x := g) h1.symm (L := []) (by simp [hg])]
  rw [exec_mv_shift (d := 10) (s := ZEROW) (c := TAd) (by decide) (x := z)
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), h2]) (L := [])
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hz,
      List.append_nil])]
  rw [exec_mv_shift (d := 10) (s := ONEW) (c := TNK) (by decide) (x := o)
    (by simp (config := {decide := true}) only [Function.update_apply, if_false, h3]) (L := [])
    (by simp (config := {decide := true}) only [Function.update_apply, if_false, ho,
      List.append_nil])]
  refine ⟨?_, fun x a b d e => ?_⟩
  · simp (config := {decide := true}) only [Function.update_apply, if_true, if_false, h10]
    rw [List.drop_append_of_le_length (by simp; omega), List.drop_append_of_le_length (by simp; omega),
      List.drop_append_of_le_length (by simp; omega)]
    simp [List.drop_replicate, hV]
  · simp only [Function.update_apply, if_neg a, if_neg b, if_neg d, if_neg e]

end Streams

/-! ### The words prepared for `f̂` -/

section W1

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (W : ℕ) (a : List Bool) (gs : GateList)

theorem w1_key {x : Fin 120} {n : ℕ}
    (h : (mw x, n) ∈ stepT N K k c.d ++ wordsT N K k c.d W (offB c) (offW hk c) (offPsi hk c))
    (h1 : x ≠ OB) (h2 : x ≠ ZB) : w1 hk c W a gs x = List.replicate n false :=
  S1_key hk c W a gs h (fun e => h1 (ValVM.tWd_inj e)) (fun e => h2 (ValVM.tWd_inj e))

theorem w1_SDW : w1 hk c W a gs SDW = a := by
  rw [w1, S1_eq_S0 hk c W a gs _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]
  simp [S0]

theorem w1_content (hW : 0 < W) (hb : BndG W gs) :
    w1 hk c W a gs GADW = gadW N K k ∧ w1 hk c W a gs ZEROW = zeroW (lenA N K k c.d) ∧
      w1 hk c W a gs ONEW = oneW N K := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [w1, S1_not hk c W a gs (by decide) (by decide) (by decide), X5_apply]
    simp (config := {decide := true}) only [Y4_apply c W a gs hW hb, if_true, if_false]

theorem w1_GS (hW : 0 < W) (hb : BndG W gs) :
    w1 hk c W a gs GS = gsW W gs ∧ w1 hk c W a gs GCNT = List.replicate gs.length false := by
  refine ⟨?_, ?_⟩ <;>
  · rw [w1, S1_not hk c W a gs (by decide) (by decide) (by decide), X5_apply]
    simp (config := {decide := true}) only [Y4_apply c W a gs hW hb, if_true, if_false]
    rw [X4, tmplS_apply_of_not_mem _ _ _ (ne_of_keys (keys_tmpl31 N K k c.d) (by decide))]
    simp (config := {decide := true}) only [Function.update_apply, if_true, if_false,
      X2_apply W a gs hW hb]

end W1

/-! ### The state of the run of `f̂` on the simulation data -/

theorem flatten_flatMap {α β : Type*} (l : List α) (g : α → List (List β)) :
    (l.flatMap g).flatten = l.flatMap fun i => (g i).flatten := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.flatten_append, ih]

section RunT

variable {N K : ℕ} (hk : 2 ^ K < 2 ^ (K + 1)) (c : Conf N K (K + 1)) (W : ℕ) (gs : GateList)
  (sd : SimData hk c)

/-- The step of the run of `f̂`. -/
abbrev fT (N K d : ℕ) : List Bool → List Bool → List Bool :=
  simStepJW N K (K + 1) 1 d (gadW N K (K + 1)) (ginvW N K (K + 1))

/-- The value `one` of the run of `f̂`. -/
abbrev oneT (N K d : ℕ) : List Bool :=
  gadW N K (K + 1) ++ zeroW (lenA N K (K + 1) d) ++ oneW N K

/-- The words after the streams and `one`. -/
def w2 : St := exec (VT N K (K + 1) c.d) (fT N K c.d) (ofList [streamsT, oneC])
  (w1 hk c W ((sdEnc hk c).enc sd) gs)

theorem w2_spec (hW : 0 < W) (hb : BndG W gs) :
    w2 hk c W gs sd 10 = oneT N K c.d ∧
    w2 hk c W gs sd BSt = ((sdEnc hk c).enc sd).drop (offB c) ∧
    w2 hk c W gs sd WSt = ((sdEnc hk c).enc sd).drop (offW hk c) ∧
    w2 hk c W gs sd PSt = ((sdEnc hk c).enc sd).drop (offPsi hk c) ∧
    ∀ x, x ∉ [BSt, WSt, PSt, 10, GADW, ZEROW, ONEW] → w2 hk c W gs sd x = w1 hk c W ((sdEnc hk c).enc sd) gs x := by
  obtain ⟨g1, g2, g3⟩ := w1_content hk c W ((sdEnc hk c).enc sd) gs hW hb
  have e : w2 hk c W gs sd = exec (VT N K (K + 1) c.d) (fT N K c.d) oneC
      (exec (VT N K (K + 1) c.d) (fT N K c.d) streamsT (w1 hk c W ((sdEnc hk c).enc sd) gs)) := rfl
  rw [e, exec_streamsT]
  set w := w1 hk c W ((sdEnc hk c).enc sd) gs with hw
  have l61 : (w 61).length = offB c := by
    rw [hw, w1_key hk c W _ gs (n := offB c) (by simp [wordsT]) (by decide) (by decide)]; simp
  have l62 : (w 62).length = offW hk c := by
    rw [hw, w1_key hk c W _ gs (n := offW hk c) (by simp [wordsT]) (by decide) (by decide)]; simp
  have l63 : (w 63).length = offPsi hk c := by
    rw [hw, w1_key hk c W _ gs (n := offPsi hk c) (by simp [wordsT]) (by decide) (by decide)]; simp
  have hS : w SDW = (sdEnc hk c).enc sd := w1_SDW hk c W _ gs
  obtain ⟨o1, o2⟩ := exec_oneC (V := VT N K (K + 1) c.d) (f := fT N K c.d)
    (Function.update (Function.update (Function.update w BSt ((w SDW).drop (w 61).length)) WSt
      ((w SDW).drop (w 62).length)) PSt ((w SDW).drop (w 63).length))
    (g := gadW N K (K + 1)) (z := zeroW (lenA N K (K + 1) c.d)) (o := oneW N K)
    (by simp (config := {decide := true}) only [Function.update_apply, if_false]
        rw [hw, w1_key hk c W _ gs (n := VT N K (K + 1) c.d) (by simp [wordsT]) (by decide) (by decide)])
    (by rw [length_gadW, length_zeroW, length_oneW]; simp [VT, lenA])
    (by simp (config := {decide := true}) only [Function.update_apply, if_false, g1])
    (by simp (config := {decide := true}) only [Function.update_apply, if_false, g2])
    (by simp (config := {decide := true}) only [Function.update_apply, if_false, g3])
    (by simp (config := {decide := true}) only [Function.update_apply, if_false]
        rw [hw, w1_key hk c W _ gs (n := lenA N K (K + 1) 1) (by simp [wordsT]) (by decide) (by decide),
          length_gadW]; simp)
    (by simp (config := {decide := true}) only [Function.update_apply, if_false]
        rw [hw, w1_key hk c W _ gs (n := lenA N K (K + 1) c.d) (by simp [wordsT]) (by decide) (by decide),
          length_zeroW]; simp)
    (by simp (config := {decide := true}) only [Function.update_apply, if_false]
        rw [hw, w1_key hk c W _ gs (n := N * K) (by simp [wordsT]) (by decide) (by decide),
          length_oneW]; simp)
  refine ⟨o1, ?_, ?_, ?_, fun x hx => ?_⟩
  · rw [o2 _ (by decide) (by decide) (by decide) (by decide)]
    simp (config := {decide := true}) only [Function.update_apply, if_false, if_true, hS, l61]
  · rw [o2 _ (by decide) (by decide) (by decide) (by decide)]
    simp (config := {decide := true}) only [Function.update_apply, if_false, if_true, hS, l62]
  · rw [o2 _ (by decide) (by decide) (by decide) (by decide)]
    simp (config := {decide := true}) only [Function.update_apply, if_false, if_true, hS, l63]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hx
    rw [o2 _ a4 a5 a6 a7]
    simp only [Function.update_apply, if_neg a1, if_neg a2, if_neg a3]

theorem eq_append_drop {L P R : List Bool} (h : L = P ++ R) : L = P ++ L.drop P.length := by
  rw [h, List.drop_left]

/-- The input words of `f̂` on the simulation data. -/
abbrev bWs : Fin 10 × BI N (K + 1) → List Bool := fun j => rowW N K (K + 1) (sd.mpk.Bj j)
abbrev wWs : Fin 10 × BI N (K + 1) → List Bool := fun j => colsW N K (K + 1) c.d (sd.W j)
abbrev entS : Fin 10 → Fin 2 × (Fin 2 × Fin (K + 1)) → List Bool :=
  fun i q => entQ N K (K + 1) (colsW N K (K + 1) 2 (sd.Ψ i)) q

/-- **The words before `fhatC` meet `FInit`.** -/
theorem fInit_w2 (hN : 0 < N) (hK : 0 < K) (hW : 0 < W) (hb : BndG W gs) :
    FInit (VT N K (K + 1) c.d) K N W (lenA N K (K + 1) 1) (lenA N K (K + 1) c.d) (oneT N K c.d) gs
      (bWs hk c sd) (wWs hk c sd) (entS hk c sd)
      ((w2 hk c W gs sd BSt).drop
        (((Enum.list (α := Fin 10 × BI N (K + 1))).map (bWs hk c sd)).flatten.length))
      ((w2 hk c W gs sd WSt).drop
        (((Enum.list (α := Fin 10 × BI N (K + 1))).map (wWs hk c sd)).flatten.length))
      ((w2 hk c W gs sd PSt).drop
        (((List.finRange 10).flatMap fun i => (ValVM.qsL (K + 1)).map (entS hk c sd i)).flatten.length))
      (w2 hk c W gs sd) := by
  obtain ⟨o1, oB, oW, oP, o2⟩ := w2_spec hk c W gs sd hW hb
  have L : ∀ (x : Fin 120) (n : ℕ), (mw x, n) ∈ stepT N K (K + 1) c.d ++
      wordsT N K (K + 1) c.d W (offB c) (offW hk c) (offPsi hk c) →
      x ∉ [BSt, WSt, PSt, 10, GADW, ZEROW, ONEW] → x ≠ OB → x ≠ ZB →
      (w2 hk c W gs sd x).length = n := fun x n h hx h1 h2 => by
    rw [o2 x hx, w1_key hk c W _ gs h h1 h2, List.length_replicate]
  have Z : ∀ (x : Fin 120) (n : ℕ), (mw x, n) ∈ stepT N K (K + 1) c.d ++
      wordsT N K (K + 1) c.d W (offB c) (offW hk c) (offPsi hk c) →
      x ∉ [BSt, WSt, PSt, 10, GADW, ZEROW, ONEW] → x ≠ OB → x ≠ ZB →
      w2 hk c W gs sd x = List.replicate n false := fun x n h hx h1 h2 => by
    rw [o2 x hx, w1_key hk c W _ gs h h1 h2]
  have hS1 : ∀ x : Fin 120, x ∉ [BSt, WSt, PSt, 10, GADW, ZEROW, ONEW] →
      w2 hk c W gs sd x = S1 hk c W ((sdEnc hk c).enc sd) gs (mw x) := fun x hx => by
    rw [o2 x hx]; rfl
  obtain ⟨g1, g2⟩ := w1_GS hk c W ((sdEnc hk c).enc sd) gs hW hb
  exact {
    tm := ⟨by rw [o1]; simp [VT, lenA, length_gadW, length_oneW]; ring,
      L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide),
      L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide),
      L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide),
      L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide),
      L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide),
      L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide),
      L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide),
      L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide),
      L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)⟩
    vone := o1
    ob := by rw [hS1 _ (by decide)]; exact S1_OB hk c W _ gs
    zb := by rw [hS1 _ (by decide)]; exact S1_ZB hk c W _ gs
    nv := L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    nkv := L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    t2k := L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    tlb := L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    tcnt := L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    th := L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    tn := L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    tn1 := L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    tn1v := L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    tkv := L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    t2knv := L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    t2kknv := L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    ta1 := L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    tad := L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    tk1 := L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    znk1 := Z _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    hV := rfl
    hNK := Nat.mul_pos hN hK
    hK := hK
    tnk := L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    t4k := L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    t10 := L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    bst := eq_append_drop (by rw [oB, sd_dropB]; rfl)
    wst := eq_append_drop (by rw [oW, sd_dropW]; rfl)
    pst := eq_append_drop (R := dateEnc.enc sd.x) (by
      rw [oP, sd_dropPsi, flatten_flatMap]
      refine congrArg (· ++ dateEnc.enc sd.x) (List.flatMap_congr fun i _ => ?_)
      exact (qsL_entries N K (K + 1) _ (by rw [length_colsW'])).symm)
    insw := L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    tsl := L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    tst := L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    td2 := L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    tw := L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    tpad := L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    tw9 := L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    tins := L _ _ (by simp [wordsT]) (by decide) (by decide) (by decide)
    gsw := by rw [o2 _ (by decide)]; exact g1
    gcnt := by rw [o2 _ (by decide), g2, List.length_replicate] }

theorem vstepT (N K d : ℕ) : VStep (simStepP ginvTopP) (VT N K (K + 1) d) (fT N K d)
    (SimPre N K (K + 1) 1 d (gadW N K (K + 1)) (GPreTop N K (K + 1))) :=
  let h := stepSpec_simTop N K (K + 1) d
  ⟨h.noGrow, h.pre_upd, h.run_eq, h.len⟩

/-- The words after the run of `f̂`. -/
def w3 : St := exec (VT N K (K + 1) c.d) (fT N K c.d) fhatFullC (w1 hk c W ((sdEnc hk c).enc sd) gs)

/-- **The law of the run of `f̂`.** -/
theorem law_runT (hW : 0 < W) (hb : BndG W gs) :
    runT.law (S1 hk c W ((sdEnc hk c).enc sd) gs) =
      PMF.pure (ValVM.enc (s1 hk c W ((sdEnc hk c).enc sd) gs) (VT N K (K + 1) c.d)
        (w3 hk c W gs sd)) := by
  rw [S1_enc]
  exact law_compileA (nocert _) (vstepT N K c.d) (s1_simPre hk c W _ gs hW hb)
    (s1_blank hk c W _ gs 0 (by decide)) (s1_blank hk c W _ gs 1 (by decide))
    (s1_blank hk c W _ gs 2 (by decide)) _ _

theorem w3_eq : w3 hk c W gs sd = exec (VT N K (K + 1) c.d) (fT N K c.d) (ofList [fhatC, .cp FOUT OUTW])
    (w2 hk c W gs sd) := by
  rw [w3, w2, fhatFullC, show [streamsT, oneC, fhatC, Code.cp FOUT OUTW] =
    [streamsT, oneC] ++ [fhatC, Code.cp FOUT OUTW] from rfl, exec_ofList_append]

theorem w3_frame (x : Fin 120) (hx : x ∉ wr fhatFullC) :
    w3 hk c W gs sd x = w1 hk c W ((sdEnc hk c).enc sd) gs x :=
  exec_not_mem _ _ _ hx

/-- **The output bundle of `f̂`.** -/
theorem w3_FOUT (hN : 0 < N) (hK : 0 < K) (hW : 0 < W) (hb : BndG W gs) (hgs : gs.length + 10 ≤ W)
    (hne : gs ≠ []) :
    w3 hk c W gs sd FOUT = bw (fhatV (oneT N K c.d) (fV (VT N K (K + 1) c.d) (fT N K c.d))
      (inBW (bWs hk c sd) (wWs hk c sd) (entS hk c sd)) (enumT N (K + 1)) (enumO N (K + 1))
      (gvExp (2 ^ K)) (2 ^ K) (predOf 10 gs).1 (predOf 10 gs).2) := by
  rw [w3_eq]
  simp only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp', Function.update_self]
  exact exec_fhatC (vstepT N K c.d).len hN hgs hb hne (fun j => length_rowW' _)
    (fun j => length_colsW' _ _) (fun i q => by
      simp only [entS, entQ, rget]
      exact length_block (N := 2 * (2 * (K + 1))) (by rw [length_colsW'])
        (by have := q.1.isLt; have := q.2.1.isLt; have := q.2.2.isLt; nlinarith))
    _ (fInit_w2 hk c W gs sd hN hK hW hb)

theorem w1_GSC (hW : 0 < W) (hb : BndG W gs) (a : List Bool) :
    w1 hk c W a gs GSC = gsW W gs := by
  rw [w1, S1_not hk c W a gs (by decide) (by decide) (by decide), X5_apply]
  simp (config := {decide := true}) only [Y4_apply c W a gs hW hb, if_true, if_false]
  rw [X4, tmplS_apply_of_not_mem _ _ _ (ne_of_keys (keys_tmpl31 N K (K + 1) c.d) (by decide))]
  simp (config := {decide := true}) only [Function.update_apply, if_true, if_false,
    X2_apply W a gs hW hb]

end RunT

/-! ### The preparation of the predicate's run -/

section PrepG

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (W : ℕ) (gs : GateList) (T : Store 256)

def Z1 : Store 256 := run (clrsP lowW ⨾ cp (mw GS) (mw GSC)) T

def Z2 : Store 256 := run (Prog.map cm13 (convP W)) (Z1 T)

def Z4 : Store 256 := tmplS (tmpl31 N K k c.d) (Function.update (Z2 W T) (mw GS) (Z2 W T (mw GSC)))

def Z5 : Store 256 := run (Prog.map tm31 simTmplP ⨾ copiesP 1) (Z4 c W T)

/-- The offsets of the predicate's streams. -/
abbrev oXG : ℕ := offPsi hk c + 10 * lenPsi N K k

/-- The store after `prepG`. -/
def S3 : Store 256 :=
  tmplS (stepG N K k c.d ++ wordsG N K k c.d W (offPsi hk c) (offR hk c) (oXG hk c)) (Z5 c W T)

theorem keys_G (N K k d W oP oR oX : ℕ) :
    (stepG N K k d ++ wordsG N K k d W oP oR oX).map Prod.fst =
      [ms 3, ms 4, ms 5, ms 6, ms 7, ms 8, ms 9, ms 10, ms 11, ms 12, ms 13, ms 14, ms 15, ms 16,
        ms 17, ms 86, ms 87, ms 88, ms 89, ms 90, ms 91, ms 93, ms 94, ValVM.tTV, mw 10, mw TA1,
        mw TAd, mw TK1, mw ZNK1, mw TNK, mw 29, mw T10, mw INSW, mw TSl, mw TST, mw TD2, mw TW, mw TPAD,
        mw TW9, mw TINS, mw 61, mw 62, mw 63, mw 73, mw 74, mw 75] := rfl

theorem nodup_G (N K k d W oP oR oX : ℕ) :
    ((stepG N K k d ++ wordsG N K k d W oP oR oX).map Prod.fst).Nodup := by
  rw [keys_G]; decide

theorem Z1_apply (t : Fin 256) :
    Z1 T t = if t = mw GS then T (mw GSC) else if t ∈ lowW then [] else T t := by
  rw [Z1, run_seq, run_copy, run_clrsP]
  by_cases h : t = mw GS
  · subst h; simp (config := {decide := true})
  · rw [Function.update_of_ne h, if_neg h]

theorem Z2_apply (hW : 0 < W) (hb : BndG W gs) (hT : T (mw GSC) = gsW W gs) (t : Fin 256) :
    Z2 W T t = if t = mw GS then [] else
      if t = mw 1 then gatesW (fun i : Fin 10 => i.val) 10 W (predOf 10 gs).1 0 else
      if t = mw GCNT then List.replicate gs.length false else
      if t = mw 3 then unaryW W (gs.length + 10) else Z1 T t := by
  have hin : Z1 T ∘ cm13 = fun i => if i = 0 then gsW W gs else [] := by
    funext i
    fin_cases i <;> simp (config := {decide := true}) [cm13, Z1_apply, hT, lowW]
  rw [Z2]
  by_cases ht : ∃ j, cm13 j = t
  · obtain ⟨j, rfl⟩ := ht
    rw [run_map_apply cm13_inj, hin, run_convP hW gs hb _ rfl]
    fin_cases j <;> simp (config := {decide := true}) [cm13, Z1_apply, lowW]
  · push_neg at ht
    rw [run_map_apply_not cm13_inj _ _ _ ht]
    have h1 : t ≠ mw GS := fun e => ht 0 (by rw [e]; rfl)
    have h2 : t ≠ mw 1 := fun e => ht 1 (by rw [e]; rfl)
    have h3 : t ≠ mw GCNT := fun e => ht 2 (by rw [e]; rfl)
    have h4 : t ≠ mw 3 := fun e => ht 3 (by rw [e]; rfl)
    simp [h1, h2, h3, h4]

theorem Z4_word (hW : 0 < W) (hb : BndG W gs) (hT : T (mw GSC) = gsW W gs) (j : ℕ) (hj : 12 ≤ j)
    (hj' : j < 120) (h31 : j < 31) : Z4 c W T (mw ⟨j, hj'⟩) = [] := by
  have hv : ∀ x : Fin 120, (mw ⟨j, hj'⟩ : Fin 256) = mw x → j = x.val := fun x e => by
    have := congrArg Fin.val e; simp [ValVM.tWd] at this; omega
  rw [Z4, tmplS_apply_of_not_mem _ _ _ (ne_of_keys (keys_tmpl31 N K k c.d) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> have := hv _ e <;> simp at this <;>
      omega)), Function.update_of_ne (fun e => by have := hv _ e; simp at this; omega),
    Z2_apply W gs T hW hb hT]
  have h1 : (mw ⟨j, hj'⟩ : Fin 256) ≠ mw GS := fun e => by have := hv _ e; simp at this; omega
  have h2 : (mw ⟨j, hj'⟩ : Fin 256) ≠ mw 1 := fun e => by have := hv _ e; simp at this; omega
  have h3 : (mw ⟨j, hj'⟩ : Fin 256) ≠ mw GCNT := fun e => by have := hv _ e; simp at this; omega
  have h4 : (mw ⟨j, hj'⟩ : Fin 256) ≠ mw 3 := fun e => by have := hv _ e; simp at this; omega
  have h5 : (mw ⟨j, hj'⟩ : Fin 256) ∈ lowW := by
    simp only [lowW, List.mem_append, List.mem_map, List.mem_finRange, true_and]
    exact Or.inl ⟨⟨j, h31⟩, rfl⟩
  simp [h1, h2, h3, h4, h5, Z1_apply]

theorem Z4_key {t : Fin 256} {n : ℕ} (h : (t, n) ∈ tmpl31 N K k c.d) :
    Z4 c W T t = List.replicate n false := by
  rw [Z4]; exact tmplS_mem _ (nodup_31 _ _ _ _) (t, n) h _

theorem Y4G_apply (hW : 0 < W) (hb : BndG W gs) (hT : T (mw GSC) = gsW W gs) (t : Fin 256) :
    run (Prog.map tm31 simTmplP) (Z4 c W T) t =
      if t = mw 0 then gadW N K k else if t = mw 1 then gswGadW N K k else
      if t = mw 2 then zeroW (lenA N K k c.d) else if t = mw 3 then oneW N K else Z4 c W T t := by
  have hrun := run_simTmplP (N := N) (K := K) (k := k) (Lw := lenA N K k c.d)
    (Z4 c W T ∘ tm31) (fun t ht => by
      have := Z4_word c W gs T hW hb hT t.val ht (by omega) t.isLt
      simpa [tm31] using this)
    (by simp [tm31, Z4_key c W T (t := mw 4) (n := K) (by simp [tmpl31])])
    (by simp [tm31, Z4_key c W T (t := mw 5) (n := N) (by simp [tmpl31])])
    (by simp [tm31, Z4_key c W T (t := mw 6) (n := N * K) (by simp [tmpl31])])
    (by simp [tm31, Z4_key c W T (t := mw 7) (n := k) (by simp [tmpl31])])
    (by simp [tm31, Z4_key c W T (t := mw 8) (n := 2 * k * (N * K)) (by simp [tmpl31])])
    (by simp [tm31, Z4_key c W T (t := mw 9) (n := 2 * (2 * k) * (N * K)) (by simp [tmpl31])])
    (by simp [tm31, Z4_key c W T (t := mw 10) (n := k * (N * K)) (by simp [tmpl31])])
    (by simp [tm31, Z4_key c W T (t := mw 11) (n := lenA N K k c.d) (by simp [tmpl31])])
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

theorem Z5_apply (t : Fin 256) : Z5 c W T t =
    if t = mw ONEW then run (Prog.map tm31 simTmplP) (Z4 c W T) (mw 3) else
    if t = mw ZEROW then run (Prog.map tm31 simTmplP) (Z4 c W T) (mw 2) else
    if t = mw GADW then run (Prog.map tm31 simTmplP) (Z4 c W T) (mw 1) else
    if t = ms 21 then run (Prog.map tm31 simTmplP) (Z4 c W T) (mw 3) else
    if t = ms 20 then run (Prog.map tm31 simTmplP) (Z4 c W T) (mw 2) else
    if t = ms 19 then run (Prog.map tm31 simTmplP) (Z4 c W T) (mw 1) else
    run (Prog.map tm31 simTmplP) (Z4 c W T) t := by
  simp only [Z5, run_seq, copiesP, run_copy]
  simp (config := {decide := true}) only [Function.update_apply, if_false]

theorem Z1_tX0 (hX : T tX0 = []) : Z1 T tX0 = [] := by
  rw [Z1_apply]; simp (config := {decide := true}) [lowW, hX]

theorem Z4_tX0 (hX : T tX0 = []) : Z4 c W T tX0 = [] := by
  rw [Z4, tmplS_apply_of_not_mem _ _ _ (ne_of_keys (keys_tmpl31 N K k c.d) (by decide)),
    Function.update_of_ne (by decide), Z2, run_map_apply_not cm13_inj _ _ _ (by decide),
    Z1_tX0 T hX]

theorem Z5_tX0 (hX : T tX0 = []) : Z5 c W T tX0 = [] := by
  rw [Z5_apply]
  simp (config := {decide := true}) only [if_false]
  rw [run_map_apply_not tm31_inj _ _ _ (by decide), Z4_tX0 c W T hX]

/-- **The law of `prepG`.** -/
theorem law_prepG (hX : T tX0 = []) : (prepG hk c W).law T = PMF.pure (S3 hk c W T) := by
  have hc0 : (clrsP lowW ⨾ cp (mw GS) (mw GSC)).CoinFree := by
    have : ∀ l : List (Fin 256), (clrsP l).CoinFree := by
      intro l; induction l with
      | nil => rfl
      | cons x l ih =>
        simp only [CoinFree, clrsP] at ih ⊢; simp [coinFreeB, ih]
    have h := this lowW
    simp only [CoinFree] at h ⊢
    simp [coinFreeB, h]
  have hc1 : (Prog.map cm13 (convP W)).CoinFree := coinFree_map _ (coinFree_convP W)
  have hc2 : (Prog.map tm31 simTmplP ⨾ copiesP 1).CoinFree := by
    have h1 := coinFree_map tm31 (coinFree_of_noGrow _ noGrow_simTmplP)
    simp only [CoinFree] at h1 ⊢
    simp [coinFreeB, h1, show (copiesP 1).coinFreeB = true from rfl]
  rw [prepG, XProg.law_seq, XProg.law_prog, law_eq_run_of_coinFree _ hc0, PMF.pure_bind,
    XProg.law_seq, XProg.law_prog, law_eq_run_of_coinFree _ hc1, PMF.pure_bind,
    XProg.law_seq, XProg.law_prog, law_eq_run_of_coinFree _ (by rfl), PMF.pure_bind]
  simp only [run_copy]
  rw [XProg.law_seq, law_tmplP _ _ _ (by
      rw [Function.update_of_ne (by decide), run_map_apply_not cm13_inj _ _ _ (by decide)]
      exact Z1_tX0 T hX)
      (ne_of_keys (keys_tmpl31 N K k c.d) (by decide)),
    PMF.pure_bind, XProg.law_seq, XProg.law_prog, law_eq_run_of_coinFree _ hc2, PMF.pure_bind,
    law_tmplP _ _ _ (by exact Z5_tX0 c W T hX) (ne_of_keys (keys_G N K k c.d W _ _ _) (by decide))]
  rfl

/-! #### Lookups of `S3` -/

abbrev keysG : List (Fin 256) :=
  [ms 3, ms 4, ms 5, ms 6, ms 7, ms 8, ms 9, ms 10, ms 11, ms 12, ms 13, ms 14, ms 15, ms 16,
    ms 17, ms 86, ms 87, ms 88, ms 89, ms 90, ms 91, ms 93, ms 94, ValVM.tTV, mw 10, mw TA1,
    mw TAd, mw TK1, mw ZNK1, mw TNK, mw 29, mw T10, mw INSW, mw TSl, mw TST, mw TD2, mw TW, mw TPAD,
    mw TW9, mw TINS, mw 61, mw 62, mw 63, mw 73, mw 74, mw 75]

theorem tm31_mem : ∀ j, tm31 j ∈ lowW := by decide

theorem cm13_mem : ∀ j, cm13 j ∈ lowW ∨ cm13 j = mw GS := by decide

theorem S3_key {t : Fin 256} {n : ℕ}
    (h : (t, n) ∈ stepG N K k c.d ++ wordsG N K k c.d W (offPsi hk c) (offR hk c) (oXG hk c)) :
    S3 hk c W T t = List.replicate n false :=
  tmplS_mem _ (nodup_G _ _ _ _ _ _ _ _) (t, n) h _

theorem S3_not {t : Fin 256} (h : t ∉ keysG) : S3 hk c W T t = Z5 c W T t :=
  tmplS_apply_of_not_mem _ _ _ (ne_of_keys (keys_G N K k c.d W _ _ _) h)

theorem S3_eq_T {t : Fin 256} (h1 : t ∉ keysG)
    (h2 : t ∉ [ms 19, ms 20, ms 21, mw GADW, mw ZEROW, mw ONEW, mw GS]) (h3 : t ∉ lowW) :
    S3 hk c W T t = T t := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h2
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h2
  rw [S3_not hk c W T h1, Z5_apply]
  simp only [if_neg a1, if_neg a2, if_neg a3, if_neg a4, if_neg a5, if_neg a6]
  rw [run_map_apply_not tm31_inj _ _ _ (fun j e => h3 (by rw [← e]; exact tm31_mem j)), Z4,
    tmplS_apply_of_not_mem _ _ _ (ne_of_keys (keys_tmpl31 N K k c.d) (fun hm => h3 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with e | e | e | e | e | e | e | e <;> rw [e] <;> decide))),
    Function.update_of_ne a7, Z2, run_map_apply_not cm13_inj _ _ _ (fun j e => by
      rcases cm13_mem j with m | m
      · exact h3 (by rw [← e]; exact m)
      · exact a7 (by rw [← e]; exact m)), Z1_apply, if_neg a7, if_neg h3]

theorem S3_GS (hW : 0 < W) (hb : BndG W gs) (hT : T (mw GSC) = gsW W gs) :
    S3 hk c W T (mw GS) = gsW W gs ∧ S3 hk c W T (mw GSC) = gsW W gs ∧
      S3 hk c W T (mw GCNT) = List.replicate gs.length false := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [S3_not hk c W T (by decide), Z5_apply]
    simp (config := {decide := true}) only [Y4G_apply c W gs T hW hb hT, if_true, if_false]
    rw [Z4, tmplS_apply_of_not_mem _ _ _ (ne_of_keys (keys_tmpl31 N K k c.d) (by decide))]
    simp (config := {decide := true}) only [Function.update_apply, if_true, if_false,
      Z2_apply W gs T hW hb hT, Z1_apply, hT]

theorem S3_content (hW : 0 < W) (hb : BndG W gs) (hT : T (mw GSC) = gsW W gs) :
    S3 hk c W T (ms 19) = gswGadW N K k ∧ S3 hk c W T (ms 20) = zeroW (lenA N K k c.d) ∧
      S3 hk c W T (ms 21) = oneW N K ∧ S3 hk c W T (mw GADW) = gswGadW N K k ∧
      S3 hk c W T (mw ZEROW) = zeroW (lenA N K k c.d) ∧ S3 hk c W T (mw ONEW) = oneW N K := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [S3_not hk c W T (by decide), Z5_apply]
    simp (config := {decide := true}) only [Y4G_apply c W gs T hW hb hT, if_true, if_false]

/-- The step's store prepared for the predicate. -/
def s3 : Store 132 := fun j => S3 hk c W T (ms j)

/-- The words prepared for the predicate. -/
def w4 : ValVM.St := fun x => S3 hk c W T (mw x)

theorem S3_enc (hX0 : T tX0 = []) (hX1 : T tX1 = []) (hX2 : T tX2 = []) :
    S3 hk c W T = ValVM.enc (s3 hk c W T) (VG N K k c.d) (w4 hk c W T) := by
  refine ValVM.enc_ext (fun j => ?_) ?_ (fun x => ?_) ?_ ?_ ?_
  · simp [s3]
  · rw [ValVM.enc_tTV, S3_key hk c W T (n := VG N K k c.d) (by simp [stepG, wordsG])]
  · simp [w4]
  · rw [S3_eq_T hk c W T (by decide) (by decide) (by decide), hX0]; simp
  · rw [S3_eq_T hk c W T (by decide) (by decide) (by decide), hX1]; simp
  · rw [S3_eq_T hk c W T (by decide) (by decide) (by decide), hX2]; simp

theorem s3_tmpl {j : Fin 132} {n : ℕ}
    (h : (ms j, n) ∈ stepG N K k c.d ++ wordsG N K k c.d W (offPsi hk c) (offR hk c) (oXG hk c)) :
    (s3 hk c W T j).length = n := by
  rw [s3, S3_key hk c W T h, List.length_replicate]

/-- The written step's tapes of `prepG`. -/
abbrev wrG : List ℕ :=
  [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 86, 87, 88, 89, 90, 91, 93, 94]

theorem s3_blank (hS : ∀ j : Fin 132, j.val ∉ wrG → T (ms j) = []) (j : Fin 132) (hj : j.val ∉ wrG) :
    s3 hk c W T j = [] := by
  have key : ∀ j : Fin 132, j.val ∉ wrG → ms j ∉ keysG ∧
      ms j ∉ [ms 19, ms 20, ms 21, mw GADW, mw ZEROW, mw ONEW, mw GS] ∧ ms j ∉ lowW := by
    decide +kernel
  obtain ⟨b1, b2, b3⟩ := key j hj
  rw [s3, S3_eq_T hk c W T b1 b2 b3, hS j hj]

/-- **The step's store prepared for the predicate meets `SimPre`.** -/
theorem s3_simPre (hW : 0 < W) (hb : BndG W gs) (hT : T (mw GSC) = gsW W gs)
    (hS : ∀ j : Fin 132, j.val ∉ wrG → T (ms j) = []) :
    SimPre N K k 2 c.d (gswGadW N K k) (GPreGsw N K k) (s3 hk c W T) where
  blank i h h' := s3_blank hk c W T hS i (by simp; omega)
  h3 := s3_tmpl hk c W T (by simp [stepG])
  h4 := s3_tmpl hk c W T (by simp [stepG])
  h5 := s3_tmpl hk c W T (by simp [stepG])
  h6 := s3_tmpl hk c W T (by simp [stepG])
  h7 := s3_tmpl hk c W T (by simp [stepG])
  h8 := s3_tmpl hk c W T (by simp [stepG])
  h9 := s3_tmpl hk c W T (by simp [stepG])
  h10 := s3_tmpl hk c W T (by simp [stepG])
  h11 := s3_tmpl hk c W T (by simp [stepG])
  h12 := s3_tmpl hk c W T (by simp [stepG])
  h13 := s3_tmpl hk c W T (by simp [stepG])
  h14 := s3_tmpl hk c W T (by simp [stepG])
  h15 := s3_tmpl hk c W T (by simp [stepG])
  h16 := s3_tmpl hk c W T (by simp [stepG])
  h17 := s3_tmpl hk c W T (by simp [stepG])
  h19 := (S3_content hk c W gs T hW hb hT).1
  h20 := (S3_content hk c W gs T hW hb hT).2.1
  h21 := (S3_content hk c W gs T hW hb hT).2.2.1
  g := by
    unfold GPreGsw
    refine ⟨fun i h h' => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Function.comp_apply]
      exact s3_blank hk c W T hS _ (by
        have : ∀ i : Fin 48, 12 ≤ i.val → i.val < 46 → (vG i).val ∉ wrG := by decide +kernel
        exact this i h h')
    · rw [Function.comp_apply, show vG 8 = 92 from rfl]
      exact s3_blank hk c W T hS _ (by decide)
    · rw [Function.comp_apply, show vG 2 = 86 from rfl]
      exact s3_tmpl hk c W T (by simp [stepG])
    · rw [Function.comp_apply, show vG 3 = 87 from rfl]
      exact s3_tmpl hk c W T (by simp [stepG])
    · rw [Function.comp_apply, show vG 4 = 88 from rfl]
      exact s3_tmpl hk c W T (by simp [stepG])
    · rw [Function.comp_apply, show vG 5 = 89 from rfl]
      exact s3_tmpl hk c W T (by simp [stepG])
    · rw [Function.comp_apply, show vG 6 = 90 from rfl]
      exact s3_tmpl hk c W T (by simp [stepG])
    · rw [Function.comp_apply, show vG 7 = 91 from rfl]
      exact s3_tmpl hk c W T (by simp [stepG])
    · rw [Function.comp_apply, show vG 9 = 93 from rfl]
      exact s3_tmpl hk c W T (by simp [stepG])
    · rw [Function.comp_apply, show vG 10 = 94 from rfl]
      exact s3_tmpl hk c W T (by simp [stepG])

end PrepG

/-! ### The run of the predicate -/

section RunG

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (W : ℕ) (gs : GateList) (T : Store 256)

/-- The step of the predicate's run. -/
abbrev fG (N K k d : ℕ) : List Bool → List Bool → List Bool :=
  simStepJW N K k 2 d (gswGadW N K k) (ginvGswW N K k)

/-- The value `one` of the predicate's run. -/
abbrev oneG (N K k d : ℕ) : List Bool := gswGadW N K k ++ zeroW (lenA N K k d) ++ oneW N K

theorem vstepG (N K k d : ℕ) : VStep (simStepP ginvGswP) (VG N K k d) (fG N K k d)
    (SimPre N K k 2 d (gswGadW N K k) (GPreGsw N K k)) :=
  let h := stepSpec_simGsw N K k d
  ⟨h.noGrow, h.pre_upd, h.run_eq, h.len⟩

/-- The words before `gswC`. -/
def w5 : St := exec (VG N K k c.d) (fG N K k c.d) (ofList [.cp GS GSC, streamsG, oneC]) (w4 hk c W T)

theorem w4_key {x : Fin 120} {n : ℕ}
    (h : (mw x, n) ∈ stepG N K k c.d ++ wordsG N K k c.d W (offPsi hk c) (offR hk c) (oXG hk c)) :
    w4 hk c W T x = List.replicate n false :=
  S3_key hk c W T h

theorem length_gswGadW'' : (gswGadW N K k).length = lenA N K k 2 := by
  rw [gswGadW_eq, List.length_append, List.length_append, length_gadW, length_zeroW,
    List.length_take, length_gadW, lenA]
  rw [min_eq_left (Nat.mul_le_mul_right _ (by omega))]; ring

theorem w5_spec (hW : 0 < W) (hb : BndG W gs) (hT : T (mw GSC) = gsW W gs) :
    w5 hk c W T 10 = oneG N K k c.d ∧
    w5 hk c W T BSt = (T (mw SDW)).drop (offPsi hk c) ∧
    w5 hk c W T WSt = (T (mw SDW)).drop (offR hk c) ∧
    w5 hk c W T rZ = (T (mw SDW)).drop (oXG hk c) ∧
    w5 hk c W T GS = gsW W gs ∧
    ∀ x, x ∉ [GS, BSt, WSt, rZ, 10, GADW, ZEROW, ONEW] → w5 hk c W T x = w4 hk c W T x := by
  obtain ⟨-, -, -, g1, g2, g3⟩ := S3_content hk c W gs T hW hb hT
  obtain ⟨-, gc, -⟩ := S3_GS hk c W gs T hW hb hT
  have e : w5 hk c W T = exec (VG N K k c.d) (fG N K k c.d) oneC
      (exec (VG N K k c.d) (fG N K k c.d) streamsG
        (Function.update (w4 hk c W T) GS (w4 hk c W T GSC))) := rfl
  rw [e, exec_streamsG]
  set w := Function.update (w4 hk c W T) GS (w4 hk c W T GSC) with hw
  have hw' : ∀ x, x ≠ GS → w x = w4 hk c W T x := fun x hx => by
    rw [hw, Function.update_of_ne hx]
  have l61 : (w 61).length = offPsi hk c := by
    rw [hw' _ (by decide), w4_key hk c W T (n := offPsi hk c) (by simp [wordsG])]; simp
  have l62 : (w 62).length = offR hk c := by
    rw [hw' _ (by decide), w4_key hk c W T (n := offR hk c) (by simp [wordsG])]; simp
  have l63 : (w 63).length = oXG hk c := by
    rw [hw' _ (by decide), w4_key hk c W T (n := oXG hk c) (by simp [wordsG])]; simp
  have hS : w SDW = T (mw SDW) := by
    rw [hw' _ (by decide), w4, S3_eq_T hk c W T (by decide) (by decide) (by decide)]
  obtain ⟨o1, o2⟩ := exec_oneC (V := VG N K k c.d) (f := fG N K k c.d)
    (Function.update (Function.update (Function.update w BSt ((w SDW).drop (w 61).length)) WSt
      ((w SDW).drop (w 62).length)) rZ ((w SDW).drop (w 63).length))
    (g := gswGadW N K k) (z := zeroW (lenA N K k c.d)) (o := oneW N K)
    (by simp (config := {decide := true}) only [Function.update_apply, if_false]
        rw [hw' _ (by decide), w4_key hk c W T (n := VG N K k c.d) (by simp [wordsG])])
    (by rw [length_gswGadW'', length_zeroW, length_oneW])
    (by simp (config := {decide := true}) only [Function.update_apply, if_false]; rw [hw' _ (by decide)]; exact g1)
    (by simp (config := {decide := true}) only [Function.update_apply, if_false]; rw [hw' _ (by decide)]; exact g2)
    (by simp (config := {decide := true}) only [Function.update_apply, if_false]; rw [hw' _ (by decide)]; exact g3)
    (by simp (config := {decide := true}) only [Function.update_apply, if_false]
        rw [hw' _ (by decide), w4_key hk c W T (n := lenA N K k 2) (by simp [wordsG]),
          length_gswGadW'']; simp)
    (by simp (config := {decide := true}) only [Function.update_apply, if_false]
        rw [hw' _ (by decide), w4_key hk c W T (n := lenA N K k c.d) (by simp [wordsG]),
          length_zeroW]; simp)
    (by simp (config := {decide := true}) only [Function.update_apply, if_false]
        rw [hw' _ (by decide), w4_key hk c W T (n := N * K) (by simp [wordsG]),
          length_oneW]; simp)
  refine ⟨o1, ?_, ?_, ?_, ?_, fun x hx => ?_⟩
  · rw [o2 _ (by decide) (by decide) (by decide) (by decide)]
    simp (config := {decide := true}) only [Function.update_apply, if_false, if_true, hS, l61]
  · rw [o2 _ (by decide) (by decide) (by decide) (by decide)]
    simp (config := {decide := true}) only [Function.update_apply, if_false, if_true, hS, l62]
  · rw [o2 _ (by decide) (by decide) (by decide) (by decide)]
    simp (config := {decide := true}) only [Function.update_apply, if_false, if_true, hS, l63]
  · rw [o2 _ (by decide) (by decide) (by decide) (by decide)]
    simp (config := {decide := true}) only [Function.update_apply, if_false, if_true]
    exact gc
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := hx
    rw [o2 _ a4 a5 a6 a7]
    simp only [Function.update_apply, if_neg a1, if_neg a2, if_neg a3]
    exact hw' x a0

/-- **The words before `gswC` meet `GInit`.** -/
theorem gInit_w5 (sd : SimData hk c) (hN : 0 < N) (hK : 0 < K) (hW : 0 < W) (hb : BndG W gs)
    (hT : T (mw GSC) = gsW W gs) (hA : T (mw SDW) = (sdEnc hk c).enc sd) :
    GInit (VG N K k c.d) W (lenA N K k 2) (lenA N K k c.d) (N * K) (oneG N K k c.d) gs
      (fun i => colsW N K k 2 (sd.Ψ i)) (fun i => colsW N K k c.d (sd.Rm i))
      ((T (mw SDW)).drop (oXG hk c))
      ((w5 hk c W T BSt).drop
        (((List.finRange 10).map fun i => colsW N K k 2 (sd.Ψ i)).flatten.length))
      ((w5 hk c W T WSt).drop
        (((List.finRange 10).map fun i => colsW N K k c.d (sd.Rm i)).flatten.length))
      (w5 hk c W T) := by
  obtain ⟨o1, oB, oW, oX, oG, o2⟩ := w5_spec hk c W gs T hW hb hT
  have L : ∀ (x : Fin 120) (n : ℕ), (mw x, n) ∈ stepG N K k c.d ++
      wordsG N K k c.d W (offPsi hk c) (offR hk c) (oXG hk c) →
      x ∉ [GS, BSt, WSt, rZ, 10, GADW, ZEROW, ONEW] → (w5 hk c W T x).length = n :=
    fun x n h hx => by rw [o2 x hx, w4_key hk c W T h, List.length_replicate]
  obtain ⟨-, -, g3⟩ := S3_GS hk c W gs T hW hb hT
  exact {
    it := {
      h10 := by rw [o1, oneG, List.length_append, List.length_append, length_gswGadW'',
        length_zeroW, length_oneW]
      hV := by simp [VG]
      ta1 := L _ _ (by simp [wordsG]) (by decide)
      tad := L _ _ (by simp [wordsG]) (by decide)
      tk1 := L _ _ (by simp [wordsG]) (by decide)
      znk1 := by rw [o2 _ (by decide), w4_key hk c W T (n := N * K - 1) (by simp [wordsG]),
        Nat.mul_one]
      t29 := L _ _ (by simp [wordsG]) (by decide)
      hNK := by rw [Nat.mul_one]; exact Nat.mul_pos hN hK
      hK := Nat.one_pos }
    vone := o1
    t10 := L _ _ (by simp [wordsG]) (by decide)
    bst := eq_append_drop (by rw [oB, hA, sd_dropPsi]; rfl)
    wst := eq_append_drop (by rw [oW, hA, sd_dropR]; rfl)
    zs := oX
    insw := L _ _ (by simp [wordsG]) (by decide)
    tsl := L _ _ (by simp [wordsG]) (by decide)
    tst := L _ _ (by simp [wordsG]) (by decide)
    td2 := L _ _ (by simp [wordsG]) (by decide)
    tw := L _ _ (by simp [wordsG]) (by decide)
    tpad := L _ _ (by simp [wordsG]) (by decide)
    tw9 := L _ _ (by simp [wordsG]) (by decide)
    tins := L _ _ (by simp [wordsG]) (by decide)
    gsw := oG
    gcnt := by rw [o2 _ (by decide), w4, g3, List.length_replicate] }

/-- The words after the predicate's run. -/
def w6 : St := exec (VG N K k c.d) (fG N K k c.d) gswFullC (w4 hk c W T)

/-- **The law of the predicate's run.** -/
theorem law_runG (hW : 0 < W) (hb : BndG W gs) (hT : T (mw GSC) = gsW W gs)
    (hS : ∀ j : Fin 132, j.val ∉ wrG → T (ms j) = []) (hX0 : T tX0 = []) (hX1 : T tX1 = [])
    (hX2 : T tX2 = []) :
    runG.law (S3 hk c W T) =
      PMF.pure (ValVM.enc (s3 hk c W T) (VG N K k c.d) (w6 hk c W T)) := by
  rw [S3_enc hk c W T hX0 hX1 hX2]
  exact law_compileA (nocert _) (vstepG N K k c.d) (s3_simPre hk c W gs T hW hb hT hS)
    (s3_blank hk c W T hS 0 (by decide)) (s3_blank hk c W T hS 1 (by decide))
    (s3_blank hk c W T hS 2 (by decide)) _ _

theorem w6_eq : w6 hk c W T = exec (VG N K k c.d) (fG N K k c.d) posC
    (exec (VG N K k c.d) (fG N K k c.d) gswC (w5 hk c W T)) := by
  rw [w6, w5, gswFullC, show [Code.cp GS GSC, streamsG, oneC, gswC, posC] =
    [Code.cp GS GSC, streamsG, oneC] ++ ([gswC] ++ [posC]) from rfl, exec_ofList_append,
    exec_ofList_append]
  rfl

theorem w6_frame (x : Fin 120) (hx : x ∉ wr gswFullC) : w6 hk c W T x = w4 hk c W T x :=
  exec_not_mem _ _ _ hx

/-- **The predicate's output wire and the positions.** -/
theorem w6_spec (sd : SimData hk c) (hN : 0 < N) (hK : 0 < K) (hW : 0 < W) (hb : BndG W gs)
    (hgs : gs.length + 10 ≤ W) (hne : gs ≠ [])
    (hT : T (mw GSC) = gsW W gs) (hA : T (mw SDW) = (sdEnc hk c).enc sd) (hOB : T (mw OB) = [true]) :
    w6 hk c W T OUTW = SLP.valueOf (fun i : Fin 10 =>
        ((List.finRange 10).map fun i => jw (colsW N K k 2 (sd.Ψ i)) (colsW N K k c.d (sd.Rm i))
          (((T (mw SDW)).drop (oXG hk c)).getD i.val false) (N * K) 1).getD i.val [])
      (oneG N K k c.d) (fV (VG N K k c.d) (fG N K k c.d)) (predOf 10 gs).1 (predOf 10 gs).2 ∧
    w6 hk c W T 61 = concatN (nPos N k) (unaryW (nPos N k)) := by
  have hG := exec_gswC (vstepG N K k c.d).len hgs hb hne (fun i => length_colsW' _ _)
    (fun i => length_colsW' _ _) _ (gInit_w5 hk c W gs T sd hN hK hW hb hT hA)
  have fr : ∀ x : Fin 120, x ∈ [OB, 29, 73, 74, 75] →
      exec (VG N K k c.d) (fG N K k c.d) gswC (w5 hk c W T) x = w4 hk c W T x := by
    intro x hx
    obtain ⟨-, -, -, -, -, o2⟩ := w5_spec hk c W gs T hW hb hT
    rw [exec_not_mem _ _ _ (by revert x; decide), o2 x (by revert x; decide)]
  obtain ⟨P1, P2⟩ := exec_posC (V := VG N K k c.d) (f := fG N K k c.d) (W' := nPos N k)
    (M := nPos N k) le_rfl (exec (VG N K k c.d) (fG N K k c.d) gswC (w5 hk c W T))
    (by rw [fr OB (by decide), w4, S3_eq_T hk c W T (by decide) (by decide) (by decide), hOB])
    (by rw [fr 29 (by decide), w4_key hk c W T (n := 1) (by simp [wordsG]), List.length_replicate])
    (by rw [fr 73 (by decide), w4_key hk c W T (n := nPos N k * nPos N k) (by simp [wordsG]),
      List.length_replicate])
    (by rw [fr 74 (by decide), w4_key hk c W T (n := nPos N k) (by simp [wordsG])])
    (by rw [fr 75 (by decide), w4_key hk c W T (n := nPos N k) (by simp [wordsG]),
      List.length_replicate])
  rw [w6_eq]
  exact ⟨by rw [P2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]; exact hG, P1⟩

end RunG

/-! ### The identification with the stores of the simulations -/

theorem idxOf_product {α β : Type*} [DecidableEq α] [DecidableEq β] :
    ∀ (l₁ : List α) (l₂ : List β) (a : α) (b : β), a ∈ l₁ → b ∈ l₂ →
      (l₁ ×ˢ l₂).idxOf (a, b) = l₁.idxOf a * l₂.length + l₂.idxOf b
  | [], _, _, _, ha, _ => absurd ha (by simp)
  | x :: l₁, l₂, a, b, ha, hb => by
    rw [List.product_cons]
    by_cases hx : x = a
    · subst hx
      rw [List.idxOf_append_of_mem (by simpa using hb), List.idxOf_cons_self, Nat.zero_mul,
        Nat.zero_add]
      clear ha
      induction l₂ with
      | nil => simp at hb
      | cons y l₂ ih =>
        by_cases hy : y = b
        · subst hy; simp
        · rw [List.map_cons, List.idxOf_cons_ne _ (by simp [hy]), List.idxOf_cons_ne _ hy,
            ih (by simpa [Ne.symm hy] using hb)]
    · have hm : (a, b) ∉ l₂.map (x, ·) := by
        simp only [List.mem_map, Prod.mk.injEq, not_exists, not_and]
        intro y _ e; exact absurd e hx
      have ha' : a ∈ l₁ := by
        rcases List.mem_cons.mp ha with e | e
        · exact absurd e.symm hx
        · exact e
      rw [List.idxOf_append_of_notMem hm, List.length_map,
        idxOf_product l₁ l₂ a b ha' hb, List.idxOf_cons_ne _ hx, Nat.succ_mul]
      ring

theorem idxOf_finRange {n : ℕ} (x : Fin n) : (List.finRange n).idxOf x = x.val := by
  simp

/-- The index of an output coefficient in the bundle. -/
theorem biIx_out {N k : ℕ} (c : Fin (2 * k)) (i : Fin k) (j : Fin N) :
    ValVM.biIx ((0, colE k c, i, j) : BI N k) = (c.val * k + i.val) * N + j.val := by
  unfold ValVM.biIx
  show (List.finRange 2 ×ˢ ((List.finRange 2 ×ˢ List.finRange k) ×ˢ
    (List.finRange k ×ˢ List.finRange N))).idxOf (0, colE k c, i, j) = _
  rw [idxOf_product _ _ _ _ (List.mem_finRange _)
    (List.mem_product.mpr ⟨List.mem_product.mpr ⟨by simp, by simp⟩,
      List.mem_product.mpr ⟨by simp, by simp⟩⟩), idxOf_product _ _ _ _
    (List.mem_product.mpr ⟨by simp, by simp⟩) (List.mem_product.mpr ⟨by simp, by simp⟩),
    idxOf_product _ _ _ _ (List.mem_finRange _) (List.mem_finRange _), idxOf_product _ _ _ _
    (List.mem_finRange _) (List.mem_finRange _)]
  simp only [idxOf_finRange, colE_apply, List.length_product, List.length_finRange]
  have := Nat.div_add_mod c.val k
  simp only [Fin.val_zero, Nat.zero_mul, Nat.zero_add]
  rw [show c.val / k * k + c.val % k = c.val by rw [Nat.mul_comm]; exact this]
  ring

theorem getD_block (K t i : ℕ) (E : List Bool) :
    (block K t E).getD i false = ValVM.bitE K E i t := by
  unfold block ValVM.bitE
  by_cases h : i < K
  · rw [if_pos h, getD_take_drop _ h, Nat.mul_comm t K]
  · rw [if_neg h]
    simp [List.getD_eq_getElem?_getD, List.getElem?_take, h]

/-- The values of a run on `V`-bit values have `V` bits. -/
theorem length_valueOf_fV {V : ℕ} {f : List Bool → List Bool → List Bool}
    (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) {ι : Type*}
    (inp : ι → List Bool) (one : List Bool) (hin : ∀ i, (inp i).length = V) (h1 : one.length = V)
    (p : SLP ι) (w : Wire ι) : (SLP.valueOf inp one (ValVM.fV V f) p w).length = V :=
  SLP.valueOf_invariant inp one _ (fun x => x.length = V) hin h1
    (fun a b ha hb => by
      show (f (takeD V a) (takeD V b)).length = V
      exact hf _ _ (by rw [takeD_of_length' ha]; exact ha)
        (by rw [takeD_of_length' hb]; exact hb)) p w

section IdT

variable {N K : ℕ} (hk : 2 ^ K < 2 ^ (K + 1)) (c : Conf N K (K + 1)) (sd : SimData hk c)

/-- **The inputs of the run of `f̂` are the inputs of the simulation.** -/
theorem inBW_eq (hN : 0 < N) (hK : 0 < K) (i : Fin 10) (b : BI N (K + 1)) :
    ValVM.inBW (bWs hk c sd) (wWs hk c sd) (entS hk c sd) i b =
      (insTW sd).getD (ixT N K (K + 1) hk (i, b)) [] := by
  rw [ixT, insTW]
  erw [getD_enumIx (α := JT N K (K + 1) hk)]
  obtain ⟨a, ⟨c₁, c₂⟩, i', t⟩ := b
  simp only [ValVM.inBW, ValVM.jw, jointW, Algo.psiBitsW, bitsW, constW_bitW _ hN hK, getD_block]
  rfl

theorem length_inBW (hN : 0 < N) (hK : 0 < K) (i : Fin 10) (b : BI N (K + 1)) :
    (ValVM.inBW (bWs hk c sd) (wWs hk c sd) (entS hk c sd) i b).length = VT N K (K + 1) c.d := by
  rw [inBW_eq hk c sd hN hK]
  have hl : ixT N K (K + 1) hk (i, b) < (insTW sd).length := by
    rw [length_insTW]; exact enumIx_lt (α := JT N K (K + 1) hk) _
  rw [List.getD_eq_getElem _ _ hl]
  exact length_mem_insTW sd _ (List.getElem_mem _)

/-- **The output bundle of the machine's run of `f̂` is read from the store of the simulation.** -/
theorem fhatOut_eq (C : List Bool) (hN : 0 < N) (hK : 0 < K) (b : BI N (K + 1)) :
    fhatV (oneT N K c.d) (ValVM.fV (VT N K (K + 1) c.d) (fT N K c.d))
        (ValVM.inBW (bWs hk c sd) (wWs hk c sd) (entS hk c sd)) (enumT N (K + 1))
        (enumO N (K + 1)) (gvExp (2 ^ K)) (2 ^ K) (predOf 10 (parse C)).1 (predOf 10 (parse C)).2 b =
      (storeT N K (K + 1) c.d (ordT₀ N (K + 1)) (ordO₀ N (K + 1)) (parse C) (insTW sd)
        (ixT N K (K + 1) hk)).getD (wireIx (ixT N K (K + 1) hk)
          (Enum.list (α := JT N K (K + 1) hk)).length
          (fhatProg K (ordT₀ N (K + 1)) (ordO₀ N (K + 1)) (parse C)).1.length
          ((fhatProg K (ordT₀ N (K + 1)) (ordO₀ N (K + 1)) (parse C)).2 b)) [] := by
  set inp : Fin 10 × BI N (K + 1) → List Bool := fun ib =>
    ValVM.inBW (bWs hk c sd) (wWs hk c sd) (entS hk c sd) ib.1 ib.2 with hinp
  have hin : ∀ ib, (inp ib).length = VT N K (K + 1) c.d := fun ib => length_inBW hk c sd hN hK _ _
  have h1 : (oneT N K c.d).length = VT N K (K + 1) c.d := by
    simp [oneT, length_gadW, length_oneW, VT, lenA]; ring
  have e1 := valueOf_fhatSLPL (inp := inp) (one := oneT N K c.d)
    (step := ValVM.fV (VT N K (K + 1) c.d) (fT N K c.d)) (enumT N (K + 1)) (enumO N (K + 1)) (gvExp (2 ^ K)) (2 ^ K) (predOf 10 (parse C)).1
    (predOf 10 (parse C)).2 b
  refine e1.symm.trans ?_
  rw [ValVM.valueOf_fV (vstepT N K c.d).len inp _ hin h1]
  obtain ⟨h, e⟩ := getElem_wireIx (ixT N K (K + 1) hk) (insTW sd) (length_insTW sd)
    (fun j => enumIx_lt (α := JT N K (K + 1) hk) j) (simOneW N K (K + 1) c.d (gadW N K (K + 1)))
    (SLP.values (fun j => (insTW sd).getD (ixT N K (K + 1) hk j) []) (simOneW N K (K + 1) c.d
      (gadW N K (K + 1))) (fT N K c.d) (fhatProg K (ordT₀ N (K + 1)) (ordO₀ N (K + 1)) (parse C)).1)
    ((fhatProg K (ordT₀ N (K + 1)) (ordO₀ N (K + 1)) (parse C)).2 b)
  rw [← SLP.length_values (fun j => (insTW sd).getD (ixT N K (K + 1) hk j) [])
    (simOneW N K (K + 1) c.d (gadW N K (K + 1))) (fT N K c.d)
    (fhatProg K (ordT₀ N (K + 1)) (ordO₀ N (K + 1)) (parse C)).1, storeT,
    List.getD_eq_getElem _ _ h, e]
  have hi : inp = fun j => (insTW sd).getD (ixT N K (K + 1) hk j) [] := by
    funext ib; exact inBW_eq hk c sd hN hK ib.1 ib.2
  rw [hi]
  rfl

end IdT

end WB2

end AdvancedEncryption.DualUse.Prog
