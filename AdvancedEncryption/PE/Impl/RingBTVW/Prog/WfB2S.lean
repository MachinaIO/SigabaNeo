import PE.Impl.RingBTVW.Prog.WfB2
import SigabaNeoStd.Lattices.ProgAlgo.ValMainR
import SigabaNeoStd.Machines.Prog.CapN

/-!
# The `W_f` block on register streams (stage II)

`wfB2S hk c Ic W : XProg 256` is the block of `WfB2` for a predicate given as a **register
program** `rp : RP (Fin nA) W'` (instructions `dst := NAND(a, b)`), read from tape `1` as its
instruction stream `RP.rpW W rp` (`3 W` bits per instruction: the unary slots of the destination
and of the two operands). Compared with the stage-I block `wfB2`:

* the instructions are counted in blocks of `3 W` bits (`countP (3 W)`) and the count is capped at
  `Ic` by `capN Ic`, whose template is built by `natP` (`capP` writes it literally);
* the two runs use the register loop `rloopC` (`fhatCR`, `gswCR`, `ValMainR`): each instruction
  reads its operands from the store and writes its result back to the slot of its destination;
* the output is the register written last, i.e. the value of the unfolding `RP.toSLP rp` at the
  wire of its destination.

Everything else (the templates, the inputs, `simKeyP`, the cleanup) is the code of `WfB2`, whose
lemmas are stated for any stream word `G` and count `m`.

* `w3_FOUT_R`: the output bundle of `f̂` is `bw (fhatV … (RP.toSLP rp).1 ((RP.toSLP rp).2 dst))`;
* `w6_OUTW_R`: the predicate's run ends with the value of the unfolding at that wire;
* **`law_wfB2S`** / **`wfSpecR_wfB2S`**: the block writes `colsW (simWP sd P)` with
  `P = ((RP.toSLP rp).1, (RP.toSLP rp).2 dst)` for every register program with
  `nA + W' ≤ W`, at most `Ic` instructions and a last instruction `dst := …`.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.Prog Matrix AdvancedEncryption.RingBTVW.Fresh AdvancedEncryption.RingBTVW.Algo
  Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPWord
open scoped SigabaNeo.Tape.Prog

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace WB2

open SigabaNeo.Tape.ValVM

/-! ### The codes and the program -/

/-- **The run of `f̂` on a register stream**, its output bundle kept on `FOUT`. -/
def fhatFullCR : Code := ofList [streamsT, oneC, fhatCR, .cp FOUT OUTW]

/-- **The predicate's run on a register stream**, then the unary positions. -/
def gswFullCR : Code := ofList [.cp GS GSC, streamsG, oneC, gswCR, posC]

noncomputable def runTR : XProg 256 := (compileA (nocert (simStepP ginvTopP)) fhatFullCR).toX
noncomputable def runGR : XProg 256 := (compileA (nocert (simStepP ginvGswP)) gswFullCR).toX

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The count of the instructions (`3 W` bits each), capped at `Ic`, and the clear of `12`. The
phase word `1` of the count is cleared before the cap (it is blank; the clear makes its bound `0`,
so that the cap leaves the count below `Ic`). -/
def cntS (Ic W : ℕ) (R : XProg 256) : XProg 256 :=
  .seq (.frame (ValVM.mkE cntE cntE_inj) (.prog (Prog.countP (3 * W)))) <|
  .seq (.prog (clr (mw 1))) <|
  .seq (.frame (ValVM.mkE capE capE_inj) (XProg.capN Ic)) <|
  .seq (.prog (clr (mw 12))) R

/-- **The preparation of the run of `f̂`** on a stream. -/
def prepTS (Ic W : ℕ) : XProg 256 :=
  .seq (.prog (cp (mw GSC) (mw GS))) (cntS Ic W (prepTRest hk c W))

/-- **The preparation of the predicate's run** on a stream. -/
def prepGS (Ic W : ℕ) : XProg 256 :=
  .seq (.prog (clrsP lowW ⨾ cp (mw GS) (mw GSC))) (cntS Ic W (prepGRest hk c W))

/-- **The body**, in the machine's coordinates. -/
noncomputable def wfBodyS (Ic W : ℕ) : XProg 256 :=
  .seq (prepTS hk c Ic W) <| .seq runTR <| .seq (prepGS hk c Ic W) <| .seq runGR <|
  .seq (keyPrep N K k c.d) <| .seq (.frame (ValVM.mkE oK2 oK2_inj) (.prog simKeyP))
    (.prog (clrsP finClr))

end WB2

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- **The `W_f` block on register streams**: `sdEnc sd` on tape `0`, the instruction stream on
tape `1`, `W_f` on tape `2` (the frame `eW` of `wfB2`). -/
noncomputable def wfB2S (Ic W : ℕ) : XProg 256 := .frame WB2.eW (WB2.wfBodyS hk c Ic W)

namespace WB2

open SigabaNeo.Tape.ValVM

/-! ### The count of a stream -/

/-- A framed program whose law writes one tape. -/
theorem law_frame_upd {m : ℕ} (e : Fin m ↪ Fin 256) (p : XProg m) (s : Store 256) (j0 : Fin m)
    (v : List Bool)
    (h : p.law (fun j => s (e j)) = PMF.pure (Function.update (fun j => s (e j)) j0 v)) :
    (XProg.frame e p).law s = PMF.pure (Function.update s (e j0) v) := by
  rw [XProg.law_frame, h, PMF.pure_map, embedF_upd, embedF_comp]

/-- **The count and its cap**: from a store whose stream on `GS` has `g` blocks of `3 W` bits
and whose tapes of the count are blank, `GCNT := false^(min g Ic)`. -/
theorem law_cntS (Ic W g : ℕ) (hW : 0 < W) (R : XProg 256) (Y : Store 256)
    (hG : (Y (mw GS)).length = 3 * W * g)
    (hb : ∀ t ∈ [mw 1, mw 3, mw 4, mw 5, mw 12, mw GCNT], Y t = []) :
    (cntS Ic W R).law Y = R.law (fun t => if t = mw GCNT then List.replicate (min g Ic) false
      else Y t) := by
  have b1 := hb (mw 1) (by simp)
  have b3 := hb (mw 3) (by simp)
  have b4 := hb (mw 4) (by simp)
  have b5 := hb (mw 5) (by simp)
  have b12 := hb (mw 12) (by simp)
  have bc := hb (mw GCNT) (by simp)
  -- the count
  have hin : Y ∘ cntE = ![Y (mw GS), [], [], [], []] := by
    funext i; fin_cases i <;> simp [cntE, b1, b3, b4, bc]
  have hrun := Prog.run_countP (m := 3 * W) (g := g) (by omega) (Y ∘ cntE)
    (by rw [hin]; simpa using hG) (by rw [hin]; rfl) (by rw [hin]; rfl) (by rw [hin]; rfl)
  have Y2 : run (Prog.map cntE (Prog.countP (3 * W))) Y =
      Function.update Y (mw GCNT) (List.replicate g false) := by
    funext t
    by_cases ht : ∃ j, cntE j = t
    · obtain ⟨j, rfl⟩ := ht
      rw [run_map_apply cntE_inj, hrun, hin]
      fin_cases j <;> simp (config := {decide := true}) [cntE, Function.update_apply, b1, b3, b4, bc]
    · push_neg at ht
      rw [run_map_apply_not cntE_inj _ _ _ ht,
        Function.update_of_ne (fun e => ht 1 (by rw [e]; rfl))]
  have hcE : ∀ j, (ValVM.mkE capE capE_inj) j = capE j := fun _ => rfl
  have Y2' : Function.update (Function.update Y (mw GCNT) (List.replicate g false)) (mw 1) [] =
      Function.update Y (mw GCNT) (List.replicate g false) :=
    Function.update_eq_self_iff.mpr (by rw [Function.update_of_ne (by decide), b1])
  rw [cntS, XProg.law_seq, law_frame_map cntE_inj _ (Prog.coinFree_countP (3 * W)), PMF.pure_bind,
    Y2, XProg.law_seq, show (XProg.prog (clr (mw 1)) : XProg 256) = .prog (.prim (.clear (mw 1)))
      from rfl, XProg.law_prim, PMF.pure_bind, show Prim.apply (.clear (mw 1))
        (Function.update Y (mw GCNT) (List.replicate g false)) =
        Function.update (Function.update Y (mw GCNT) (List.replicate g false)) (mw 1) [] from rfl,
    Y2', XProg.law_seq,
    law_frame_upd (ValVM.mkE capE capE_inj) (XProg.capN Ic) _ 0 (List.replicate (min g Ic) false)
      (XProg.law_capN Ic g _ (by show Function.update Y (mw GCNT) _ (capE 0) = _; rw [show capE 0 = mw GCNT from rfl, Function.update_self])
        (by show Function.update Y (mw GCNT) _ (capE 1) = []
            rw [Function.update_of_ne (by decide)]; exact b1)
        (by show Function.update Y (mw GCNT) _ (capE 2) = []
            rw [Function.update_of_ne (by decide)]; exact b5)
        (by show Function.update Y (mw GCNT) _ (capE 3) = []
            rw [Function.update_of_ne (by decide)]; exact b3)
        (by show Function.update Y (mw GCNT) _ (capE 4) = []
            rw [Function.update_of_ne (by decide)]; exact b4)), PMF.pure_bind,
    XProg.law_seq, show (XProg.prog (clr (mw 12)) : XProg 256) = .prog (.prim (.clear (mw 12)))
      from rfl, XProg.law_prim, PMF.pure_bind]
  congr 1
  funext t
  simp only [Prim.apply, Function.update_apply]
  show (if t = mw 12 then [] else if t = mw GCNT then _ else if t = mw GCNT then _ else Y t) = _
  by_cases h12 : t = mw 12
  · subst h12; simp (config := {decide := true}) [b12, hcE, capE]
  · by_cases hc : t = mw GCNT <;> simp (config := {decide := true}) [h12, hc, hcE, capE]

/-- The stream of a register program has `3 W` bits per instruction. -/
theorem length_rpW' {W' W : ℕ} (hW : nA + W' ≤ W) (rp : RP (Fin nA) W') :
    (RP.rpW W rp).length = 3 * W * rp.length := by
  rw [← spW_rpSP, length_spW (bnd_rpSP hW rp), length_rpSP]; ring

/-! ### The preparations -/

section Prep

variable (W : ℕ) (a G : List Bool) (T : Store 256)

/-- **The law of `prepTS`.** -/
theorem law_prepTS (Ic g : ℕ) (hW : 0 < W) (hG : G.length = 3 * W * g) :
    (prepTS hk c Ic W).law (S0g a G) = PMF.pure (S1 hk c W a G (min g Ic)) := by
  rw [prepTS, XProg.law_seq, XProg.law_prog, law_eq_run_of_coinFree _ (by rfl), PMF.pure_bind]
  simp only [run_copy]
  rw [law_cntS Ic W g hW _ _ (by simpa (config := {decide := true}) [Function.update_apply, S0g] using hG)
    (by intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp (config := {decide := true}) [Function.update_apply, S0g])]
  have e : (fun t => if t = mw GCNT then List.replicate (min g Ic) false
      else Function.update (S0g a G) (mw GSC) (S0g a G (mw GS)) t) = X2g a G (min g Ic) := by
    funext t; simp (config := {decide := true}) [X2g, S0g]
  rw [e]
  exact law_prepTRest hk c W a G _

/-- **The law of `prepGS`.** -/
theorem law_prepGS (Ic g : ℕ) (hW : 0 < W) (hG : (T (mw GSC)).length = 3 * W * g)
    (hX : T tX0 = []) (h92 : T (ms 92) = []) :
    (prepGS hk c Ic W).law T = PMF.pure (S3 hk c W T (min g Ic)) := by
  rw [prepGS, XProg.law_seq, XProg.law_prog, law_eq_run_of_coinFree _ coinFree_clrsP_lowW,
    PMF.pure_bind, show run (clrsP lowW ⨾ cp (mw GS) (mw GSC)) T = Z1 T from rfl]
  rw [law_cntS Ic W g hW _ _ (by rw [Z1_apply, if_pos rfl]; exact hG)
    (by intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp (config := {decide := true}) [Z1_apply, lowW])]
  exact law_prepGRest hk c W T _ hX h92

end Prep

/-! ### The runs -/

section Runs

variable {N K : ℕ} (hk : 2 ^ K < 2 ^ (K + 1)) (c : Conf N K (K + 1)) (W : ℕ) (sd : SimData hk c)

/-- **The output bundle of `f̂` on a register stream**: the word of `fhatV` at the wire of the
register written last, of the unfolding `RP.toSLP rp`. -/
theorem w3_FOUT_R {W' : ℕ} (rp : RP (Fin nA) W') (hW : nA + W' ≤ W) {ins' : Instr (Fin nA) W'}
    (hl : rp.getLast? = some ins') (hN : 0 < N) (hK : 0 < K) :
    w3 hk c W (RP.rpW W rp) rp.length sd fhatFullCR FOUT = bw (fhatV (oneT N K c.d)
      (fV (VT N K (K + 1) c.d) (fT N K c.d))
      (inBW (bWs hk c sd) (wWs hk c sd) (entS hk c sd)) (enumT N (K + 1)) (enumO N (K + 1))
      (gvExp (2 ^ K)) (2 ^ K) (RP.toSLP rp).1 ((RP.toSLP rp).2 ins'.dst)) := by
  rw [fhatFullCR, w3_eq]
  simp only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp', Function.update_self]
  exact exec_fhatCR (vstepT N K c.d).len hN rp hW hl (fun j => length_rowW' _)
    (fun j => length_colsW' _ _) (length_entS hk c sd) _ (fInit_w2 hk c W _ _ sd hN hK)

/-- **The predicate's run on a register stream**: `OUTW` ends with the value of the unfolding at
the wire of the register written last, on the joint words of the inputs; `61` holds the
positions. -/
theorem w6_OUTW_R (T : Store 256) {W' : ℕ} (rp : RP (Fin nA) W') (hW : nA + W' ≤ W)
    {ins' : Instr (Fin nA) W'} (hl : rp.getLast? = some ins') (hN : 0 < N) (hK : 0 < K)
    (hT : T (mw GSC) = RP.rpW W rp) (hA : T (mw SDW) = (sdEnc hk c).enc sd)
    (hOB : T (mw OB) = [true]) :
    w6 hk c W T rp.length gswFullCR OUTW = SLP.valueOf (fun i : Fin nA =>
        ((List.finRange nA).map fun i => jw (colsW N K (K + 1) 2 (sd.Ψ i))
          (colsW N K (K + 1) c.d (sd.Rm i))
          ((((sdEnc hk c).enc sd).drop (oXG hk c)).getD i.val false) (N * K) 1).getD i.val [])
      (oneG N K (K + 1) c.d) (fV (VG N K (K + 1) c.d) (fG N K (K + 1) c.d))
      (RP.toSLP rp).1 ((RP.toSLP rp).2 ins'.dst) ∧
    w6 hk c W T rp.length gswFullCR 61 = concatN (nPos N (K + 1)) (unaryW (nPos N (K + 1))) := by
  have hG := exec_gswCR (vstepG N K (K + 1) c.d).len rp hW hl (fun i => length_colsW' _ _)
    (fun i => length_colsW' _ _) (w5 hk c W T rp.length)
    (by rw [← hT]; exact gInit_w5 hk c W T rp.length sd hN hK hA hOB)
  obtain ⟨P1, P2⟩ := w6_pos hk c W T rp.length gswCR (by decide +kernel) hOB
  rw [show gswFullCR = ofList [.cp GS GSC, streamsG, oneC, gswCR, posC] from rfl]
  refine ⟨?_, P2⟩
  rw [P1, hG, hA]
  have hNK : 0 < N * K := Nat.mul_pos hN hK
  have hin : ∀ i : Fin nA, (jw (colsW N K (K + 1) 2 (sd.Ψ i)) (colsW N K (K + 1) c.d (sd.Rm i))
      ((((sdEnc hk c).enc sd).drop (oXG hk c)).getD i.val false) (N * K) 1).length =
      VG N K (K + 1) c.d := fun i => by
    simp only [jw, List.length_append, length_colsW', List.length_replicate, VG]
    simp; omega
  have h1 : (oneG N K (K + 1) c.d).length = VG N K (K + 1) c.d := by
    rw [oneG, List.length_append, List.length_append, length_gswGadW'', length_zeroW, length_oneW]
  have e : (fun i : Fin nA =>
      ((List.finRange nA).map fun i => jw (colsW N K (K + 1) 2 (sd.Ψ i))
        (colsW N K (K + 1) c.d (sd.Rm i))
        ((((sdEnc hk c).enc sd).drop (oXG hk c)).getD i.val false) (N * K) 1).getD i.val []) =
      fun i => jw (colsW N K (K + 1) 2 (sd.Ψ i)) (colsW N K (K + 1) c.d (sd.Rm i))
        ((((sdEnc hk c).enc sd).drop (oXG hk c)).getD i.val false) (N * K) 1 := by
    funext i; exact getD_finRange_map _ i
  rw [e, ValVM.valueOf_fV (vstepG N K (K + 1) c.d).len _ _ hin h1]

end Runs

/-! ### The law of the body -/

section Final

variable {N K : ℕ} (hk : 2 ^ K < 2 ^ (K + 1)) (c : Conf N K (K + 1)) (W : ℕ) (sd : SimData hk c)

/-- The stream codes leave the words the key sum reads. -/
theorem wr_fullR : (GSC ∉ wr fhatFullCR ∧ SDW ∉ wr fhatFullCR ∧ OB ∉ wr fhatFullCR) ∧
    FOUT ∉ wr gswFullCR ∧ SDW ∉ wr gswFullCR := by decide +kernel

/-- The predicate program of a register program: its unfolding, at the wire of the register
written last. -/
noncomputable def predR {W' : ℕ} (rp : RP (Fin nA) W') (ins' : Instr (Fin nA) W') :
    SLP (Fin nA) × Wire (Fin nA) := ((RP.toSLP rp).1, (RP.toSLP rp).2 ins'.dst)

/-- **The law of the body on a register stream.** -/
theorem law_wfBodyS (Ic : ℕ) {W' : ℕ} (rp : RP (Fin nA) W') (hW : nA + W' ≤ W) (hW0 : 0 < W)
    (hIc : rp.length ≤ Ic) {ins' : Instr (Fin nA) W'} (hl : rp.getLast? = some ins')
    (hN : 0 < N) (hK : 0 < K) :
    (wfBodyS hk c Ic W).law (S0g ((sdEnc hk c).enc sd) (RP.rpW W rp)) =
      PMF.pure (fun t => if t ∈ finClr then [] else
        S6 hk c W (RP.rpW W rp) rp.length sd fhatFullCR gswFullCR
          (colsW N K (K + 1) c.d (simWP sd (predR rp ins'))) t) := by
  have hm : min rp.length Ic = rp.length := by omega
  obtain ⟨hwr, hF, -⟩ := wr_fullR
  obtain ⟨tG, tA, tO, tS, tX0', tX1', tX2'⟩ :=
    T3_facts hk c W (RP.rpW W rp) rp.length sd fhatFullCR hwr
  obtain ⟨o86, o61⟩ := w6_OUTW_R hk c W sd _ rp hW hl hN hK tG tA tO
  have hFO := w3_FOUT_R hk c W sd rp hW hl hN hK
  rw [wfBodyS, XProg.law_seq, law_prepTS hk c W _ _ Ic rp.length hW0 (length_rpW' hW rp), hm,
    PMF.pure_bind, XProg.law_seq, show runTR = (compileA (nocert (simStepP ginvTopP)) fhatFullCR).toX
      from rfl, law_runX, PMF.pure_bind,
    show ValVM.enc (s1 hk c W ((sdEnc hk c).enc sd) (RP.rpW W rp) rp.length)
      (VT N K (K + 1) c.d) (w3 hk c W (RP.rpW W rp) rp.length sd fhatFullCR) =
      T3 hk c W (RP.rpW W rp) rp.length sd fhatFullCR from rfl,
    XProg.law_seq, law_prepGS hk c W _ Ic rp.length hW0 (by rw [tG]; exact length_rpW' hW rp) tX0'
      (tS 92 (by decide)), hm,
    PMF.pure_bind, XProg.law_seq, show runGR = (compileA (nocert (simStepP ginvGswP)) gswFullCR).toX
      from rfl, law_runGX hk c W _ _ _ tS tX0' tX1' tX2', PMF.pure_bind,
    show ValVM.enc (s3 hk c W (T3 hk c W (RP.rpW W rp) rp.length sd fhatFullCR) rp.length)
      (VG N K (K + 1) c.d)
      (w6 hk c W (T3 hk c W (RP.rpW W rp) rp.length sd fhatFullCR) rp.length gswFullCR) =
      S4 hk c W (RP.rpW W rp) rp.length sd fhatFullCR gswFullCR from rfl,
    XProg.law_seq, law_keyPrep _ _ _ _ _ (by simp [S4]), PMF.pure_bind, XProg.law_seq,
    law_keyF _ _ (key_run hk c W _ _ sd fhatFullCR gswFullCR (predR rp ins') hN hK hwr hF hFO
      o86 o61),
    PMF.pure_bind, law_clrsP]
  rfl

end Final

end WB2

open WB2 in
/-- **The law of the `W_f` block on register streams**: from `sdEnc sd` (tape `0`) and the stream
`RP.rpW W rp` (tape `1`) of a register program with `nA + W' ≤ W`, at most `Ic` instructions and
last instruction `ins'`, the word of `W_f` of the predicate program `predR rp ins'` (the unfolding
at the wire of `ins'.dst`) on tape `2`, `sdEnc sd` kept on tape `0`, every other tape blank. -/
theorem law_wfB2S {N K : ℕ} (hk : 2 ^ K < 2 ^ (K + 1)) (c : Conf N K (K + 1)) (Ic W : ℕ)
    (sd : SimData hk c) {W' : ℕ} (rp : RP (Fin nA) W') (hW : nA + W' ≤ W) (hIc : rp.length ≤ Ic)
    {ins' : Instr (Fin nA) W'} (hl : rp.getLast? = some ins') (hN : 0 < N) (hK : 0 < K) :
    (wfB2S hk c Ic W).law (io2 (R := 254) ((sdEnc hk c).enc sd) (RP.rpW W rp) []) =
      PMF.pure (Function.update (io2 (R := 254) ((sdEnc hk c).enc sd) [] []) 2
        (colsW N K (K + 1) c.d (simWP sd (predR rp ins')))) := by
  have hW0 : 0 < W := by
    have : 0 < nA := by decide
    omega
  have hin : (fun j => io2 (R := 254) ((sdEnc hk c).enc sd) (RP.rpW W rp) [] (eW j)) =
      S0g ((sdEnc hk c).enc sd) (RP.rpW W rp) := by
    funext t
    obtain ⟨e0, e1, -, -⟩ := swp_eq t
    show io2 (R := 254) ((sdEnc hk c).enc sd) (RP.rpW W rp) [] (swp t) = _
    simp only [io2, e0, e1]; rfl
  rw [wfB2S, XProg.law_frame, hin, law_wfBodyS hk c W sd Ic rp hW hW0 hIc hl hN hK,
    final_eq hk c W _ _ sd _ _ _ wr_fullR.1 wr_fullR.2.2, PMF.pure_map]
  congr 1
  funext t
  have ht : t = eW (swp t) := by simp [eW, swp_swp]
  rw [ht, embedF_apply_self]
  obtain ⟨-, -, e2, e3⟩ := swp_eq t
  show (if swp t = mw SDW then _ else if swp t = 255 then _ else []) =
    Function.update (io2 (R := 254) ((sdEnc hk c).enc sd) [] []) 2 _ (eW (swp t))
  rw [show eW (swp t) = t from swp_swp t]
  simp only [e2, e3, io2, Function.update_apply]
  by_cases h0 : t.val = 0
  · have : t ≠ 2 := fun e => by rw [e] at h0; exact absurd h0 (by decide)
    simp [h0, this]
  · by_cases h2 : t.val = 2
    · simp [h0, h2, Fin.ext_iff]
    · have : t ≠ 2 := fun e => h2 (by rw [e]; rfl)
      simp [h0, h2, this]

/-! ### Well-formedness and the specification -/

namespace WB2

open SigabaNeo.Tape.ValVM

theorem wf_wfBodyS {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (Ic W : ℕ) :
    (wfBodyS hk c Ic W).WF := by
  have hT : runTR.WF := wf_compileA _ (stepSpec_simTop N K k 1).wf fhatFullCR (by decide +kernel)
  have hG : runGR.WF := wf_compileA _ (stepSpec_simGsw N K k 1).wf gswFullCR (by decide +kernel)
  refine ⟨⟨wf_of_wfB rfl, Prog.wf_countP (3 * W), wf_of_wfB rfl, XProg.wf_capN Ic, wf_of_wfB rfl,
    wf_of_wfB rfl,
    wf_tmplP _ _ (ne_of_keys (keys_tmpl31 N K k c.d) (by decide)),
    wf_simTmplP, wf_copiesP 0,
    wf_tmplP _ _ (ne_of_keys (keys_T N K k c.d W _ _ _) (by decide)), wf_of_wfB rfl, wf_putW _ _,
    wf_putW _ _⟩,
    hT, ⟨⟨wf_clrsP _, wf_of_wfB rfl⟩, Prog.wf_countP (3 * W), wf_of_wfB rfl, XProg.wf_capN Ic,
    wf_of_wfB rfl,
    wf_of_wfB rfl, wf_tmplP _ _ (ne_of_keys (keys_tmpl31 N K k c.d) (by decide)),
    wf_simTmplP, wf_copiesP 1,
    wf_tmplP _ _ (ne_of_keys (keys_G N K k c.d W _ _ _) (by decide)), wf_of_wfB rfl,
    wf_of_wfB rfl⟩, hG,
    ⟨wf_clrsP _, wf_tmplP _ _ (ne_of_keys (keys_keyT N K k c.d) (by decide)), wf_putW _ _⟩,
    wf_simKeyP, wf_clrsP _⟩

end WB2

/-- **The specification of a `W_f` block on register streams**: from `sdEnc sd` (tape `0`) and
the stream `RP.rpW W rp` (tape `1`) of any register program `rp : RP (Fin nA) W'` with
`nA + W' ≤ W`, at most `Ic` instructions and last instruction `ins'`, the word of
`W_f = simWP sd (predR rp ins')` on tape `2`, `sdEnc sd` kept on tape `0`, every other tape blank. -/
structure WfSpecR (wfB : XProg 256) (W Ic : ℕ) : Prop where
  wf : wfB.WF
  law : ∀ (sd : SimData hk c) {W' : ℕ} (rp : RP (Fin nA) W') (ins' : Instr (Fin nA) W'),
    nA + W' ≤ W → rp.length ≤ Ic → rp.getLast? = some ins' →
    wfB.law (io2 (R := 254) ((sdEnc hk c).enc sd) (RP.rpW W rp) []) =
      PMF.pure (Function.update (io2 (R := 254) ((sdEnc hk c).enc sd) [] []) 2
        (colsW N K k c.d (simWP sd (WB2.predR rp ins'))))

/-- **The `W_f` block on register streams meets `WfSpecR`.** -/
theorem wfSpecR_wfB2S {N K : ℕ} (hk : 2 ^ K < 2 ^ (K + 1)) (c : Conf N K (K + 1)) (Ic W : ℕ)
    (hN : 0 < N) (hK : 0 < K) : WfSpecR hk c (wfB2S hk c Ic W) W Ic where
  wf := WB2.wf_wfBodyS hk c Ic W
  law sd _ rp _ hW hIc hl := law_wfB2S hk c Ic W sd rp hW hIc hl hN hK

end AdvancedEncryption.RingBTVW.Prog
