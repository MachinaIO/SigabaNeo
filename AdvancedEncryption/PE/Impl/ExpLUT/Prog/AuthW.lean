import PE.Impl.DualUse.Prog.AuthBP
import PE.Impl.ExpLUT.Prog.Words

/-!
# The authorization program for ExpLUT's predicate words (package G2)

ExpLUT's predicate words (`Prog/Words`: `predLen = 211 · 2^22` bits) store the entry `(i, u)` of the
transition table `i` at bit `14 (2^22 i + u)`, **least significant bit first**, with the index
`u = z + 2^14 a`; the output bit `u` at `210 · 2^22 + u`. The authorization program of the dual-use
predicate words (`DualUse.BpComp.authBP`: same length, index `256 z + a`, most significant bit
first) is adapted:

* `offW`: the offset of `a ‖ z` (the 8 attribute bits first, then the state, most significant
  first): `numB (a ++ z) = 2^14 a + z = u`;
* `stepW`: the 14 bits of the entry are **prepended** (`consHead`) to the new state, so that the
  state stays most significant first;
* `authW8 = lenEqP ⨾ initA ⨾ loop stepW ⨾ lastW ⨾ outA' ⨾ clrA` (the other pieces are `authBP`'s).

**`run_authW8`**: the program writes `[authAW C xs]` on tape `0`, every other tape blank
(`authAW C xs = decide (|C| = 211 · 2^22) && !lastBitW C xs`); **`authAW_encAttr`**: on attribute
bits, `authAW C (encAttribute w8 x) = decide (|C| = predLen) && !(progOf C).output x`.
-/

namespace AdvancedEncryption.ExpLUT.AuthW

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Lattices SigabaNeo.Lattices.Algo
open AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates.BPCircuit
  AdvancedEncryption.PE.Gates.BPWord AdvancedEncryption.DualUse.BpComp
open AdvancedEncryption.ExpLUT.Prog (progOf readSt uOf predLen)
open scoped Prog

/-! ### The specification -/

/-- One step: the 14 bits of entry `numB (a ++ z)` of table `i`, reversed (most significant
first). -/
def stepZW (C : List Bool) (i : ℕ) (z a : List Bool) : List Bool :=
  (((C.drop (i * tblW)).drop (14 * numB (a ++ z))).take 14).reverse

/-- The states, most significant bit first. -/
def zW (C xs : List Bool) : ℕ → List Bool
  | 0 => List.replicate 14 false
  | i + 1 => stepZW C i (zW C xs i) (symA xs i)

/-- The output bit: entry `numB (a₁₅ ++ z₁₅)` of the output table. -/
def lastBitW (C xs : List Bool) : Bool :=
  hd ((C.drop (15 * tblW)).drop (numB (symA xs 15 ++ zW C xs 15)))

/-- **The authorization bit.** -/
def authAW (C xs : List Bool) : Bool := decide (C.length = bpLenA) && !lastBitW C xs

theorem length_zW_le (C xs : List Bool) : ∀ i, (zW C xs i).length ≤ 14
  | 0 => by simp [zW]
  | i + 1 => by simp only [zW, stepZW, List.length_reverse, List.length_take]; omega

/-! ### The program -/

/-- The entry offset of `a ‖ z`: `K := 8` bits of `X`, then `z` (through `T2`), then
`U := |E| · numB K` by doubling. -/
def offW : Prog 16 :=
  clr tK ⨾ iter tK (pp tX tBit ⨾ prim (.snocHead tK tBit) ⨾ clr tBit) 8 ⨾ cp tT2 tZB ⨾
    iter tK (pp tT2 tBit ⨾ prim (.snocHead tK tBit) ⨾ clr tBit) 14 ⨾ clr tT2 ⨾ clr tU ⨾
    forN tKC tK (pp tK tBit ⨾ appT tU tU tA2 tB2 ⨾ ifBit tBit (appT tU tE tA2 tB2) (nop tU) ⨾
      clr tBit)

/-- One step: the next state from table `i` (at `CUR`), prepended bit by bit, then the next
table. -/
def stepW : Prog 16 :=
  offW ⨾ cp tT2 tCU ⨾ dropT tT2 tU tA2 ⨾ clr tZB ⨾
    iter tT2 (pp tT2 tBit ⨾ prim (.consHead tZB tBit) ⨾ clr tBit) 14 ⨾ clr tT2 ⨾
    dropT tCU tTB tA2 ⨾ clr tU

/-- The last step: the bit of the output table into `Bit`. -/
def lastW : Prog 16 :=
  clr tE ⨾ prim (.snoc tE true) ⨾ offW ⨾ cp tT2 tCU ⨾ dropT tT2 tU tA2 ⨾ pp tT2 tBit

/-- **The authorization program** for ExpLUT's predicate words. -/
def authW8 : Prog 16 :=
  Prog.map uL (lenEqP bpLenA) ⨾ initA ⨾ loop tS2 stepW ⨾ lastW ⨾ outA' ⨾ clrA

/-! ### Laws -/

/-- `n` rounds of moving the first bit of `src` to the front of `dst` (`t` scratch, blank). -/
theorem run_iter_mvRev (src dst t z : Fin 16) (hsd : src ≠ dst) (hst : src ≠ t) (hdt : dst ≠ t) :
    ∀ (n : ℕ) (s : Store 16), s t = [] →
      run (iter z (pp src t ⨾ prim (.consHead dst t) ⨾ clr t) n) s =
        Function.update (Function.update s src ((s src).drop n)) dst (((s src).take n).reverse ++ s dst)
  | 0, s, _ => by
    rw [run_iter]; simp
  | n + 1, s, ht => by
    rw [run_iter, Function.iterate_succ_apply, ← run_iter]
    have h1 : run (pp src t ⨾ prim (.consHead dst t) ⨾ clr t) s =
        Function.update (Function.update s src (s src).tail) dst ((s src).take 1 ++ s dst) := by
      simp only [run_seq, run_prim, Prim.apply]
      funext u; simp only [Function.update_apply]
      split_ifs <;> simp_all
    rw [h1, run_iter_mvRev src dst t z hsd hst hdt n _ (by
      rw [Function.update_of_ne (Ne.symm hdt), Function.update_of_ne (Ne.symm hst)]; exact ht)]
    funext u; simp only [Function.update_apply]
    split_ifs <;> simp_all
    all_goals (rcases hs : s src with _ | ⟨b, l⟩ <;> simp [hs])

/-- **The entry offset.** -/
theorem run_offW (v : AV) (e : ℕ) (he : v.e = List.replicate e true) (ht : v.t = [])
    (hkc : v.kc = []) (ha : v.a = []) (hb : v.b = []) (htt : v.tt = []) :
    run offW v.enc = AV.enc
      { v with k := [], x := v.x.drop 8, tt := [],
               u := List.replicate (e * numB (v.x.take 8 ++ v.zb.take 14)) true } := by
  simp only [offW, run_seq]
  rw [run_clear (i := tK)]; encA
  rw [run_iter_mv tX tK tBit tK (by decide) (by decide) (by decide) 8 _ (by encA; exact ht)]
  encA
  rw [run_copy]; encA
  rw [run_iter_mv tT2 tK tBit tK (by decide) (by decide) (by decide) 14 _ (by encA; exact ht)]
  encA
  rw [run_clear (i := tT2)]; encA
  rw [run_clear (i := tU)]; encA
  let G : List Bool × List Bool → Store 16 := fun p =>
    AV.enc { v with k := p.2, x := v.x.drop 8, tt := [], u := p.1 }
  have hstep : ∀ p w, run (pp tK tBit ⨾ appT tU tU tA2 tB2 ⨾ ifBit tBit (appT tU tE tA2 tB2) (nop tU) ⨾
      clr tBit) (Function.update (G p) tKC w) =
      Function.update (G (dblStep (List.replicate e true) p)) tKC w := by
    intro p w
    simp only [G]
    encA
    simp only [run_seq, run_pop]
    encA
    rw [run_appT_blank (by decide) (by decide) (by decide) _ (by encA; exact ha) (by encA; exact hb)]
    encA
    rw [run_ifBit]
    encA
    simp only [dblStep, hd_take1]
    split_ifs with h
    · rw [run_appT_blank (by decide) (by decide) (by decide) _ (by encA; exact ha)
        (by encA; exact hb), run_clear]
      encA
      simp [he, ht]
    · rw [run_nop, run_clear]
      encA
      simp [ht]
  rw [run_forN tKC tK _ G (dblStep (List.replicate e true)) hstep
    (List.replicate (e * 0) true, List.take 8 v.x ++ List.take 14 v.zb) _ (by
      simp only [G]; encA; simp)]
  encA
  simp only [List.nil_append]
  rw [iterate_dblStep]
  simp only [G]
  encA
  rw [hkc]; rfl

/-- The store before step `i`. -/
def aStW (C xs : List Bool) (fl : Bool) (i : ℕ) (w : List Bool) : AV :=
  ⟨C, xs.drop (8 * i), C.drop (i * tblW), zW C xs i, [], [], List.replicate 14 true, [], [], [], [],
    w, List.replicate tblW true, [], [], [fl]⟩

theorem aSt_zero (C xs : List Bool) (fl : Bool) (w : List Bool) :
    aSt C xs fl 0 w = aStW C xs fl 0 w := rfl

/-- **One step.** -/
theorem run_stepW (C xs : List Bool) (fl : Bool) (i : ℕ) (w : List Bool) :
    run stepW (aStW C xs fl i w).enc = (aStW C xs fl (i + 1) w).enc := by
  simp only [stepW, run_seq]
  rw [run_offW _ 14 rfl rfl rfl rfl rfl rfl]
  rw [run_copy]; encA
  rw [run_dropT_blank (t := tT2) (x := tU) (by decide) _ ?h1]; encA
  rw [run_clear (i := tZB)]; encA
  rw [run_iter_mvRev tT2 tZB tBit tT2 (by decide) (by decide) (by decide) 14 _ ?h2]; encA
  rw [run_clear (i := tT2)]; encA
  rw [run_dropT_blank (t := tCU) (x := tTB) (by decide) _ ?h3]; encA
  rw [run_clear]; encA
  · congr 1
    simp only [aStW, AV.mk.injEq]
    refine ⟨trivial, ?_, ?_, ?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      trivial, trivial, trivial, trivial, trivial⟩
    · rw [List.drop_drop, Nat.mul_succ, Nat.add_comm]
    · rw [List.length_replicate, List.drop_drop, Nat.succ_mul]
    · rw [List.length_replicate, List.append_nil, zW, stepZW,
        List.take_of_length_le (length_zW_le C xs i)]
      rfl
  case h1 => encA; rfl
  case h2 => encA; rfl
  case h3 => encA; rfl

/-- **The steps.** -/
theorem run_stepsW (C xs : List Bool) (fl : Bool) :
    run (loop tS2 stepW) (aStW C xs fl 0 (List.replicate 15 true)).enc =
      (aStW C xs fl 15 []).enc := by
  have e : ∀ i w, { aStW C xs fl i [] with sc := w } = aStW C xs fl i w := fun _ _ => rfl
  have h := run_loop_count tS2 stepW (fun i => (aStW C xs fl i []).enc) 15
    (fun i _ w => by
      simp only [AV.upd_sc]
      rw [e, e]
      exact run_stepW C xs fl i w) (List.replicate 15 true) 0 (by simp)
  simp only [AV.upd_sc, List.length_replicate, Nat.zero_add] at h
  rw [e, e] at h
  exact h

/-- The bits read by the last step. -/
def lastTW (C xs : List Bool) : List Bool :=
  (C.drop (15 * tblW)).drop (numB (symA xs 15 ++ zW C xs 15))

theorem run_lastW (C xs : List Bool) (fl : Bool) :
    run lastW (aStW C xs fl 15 []).enc =
      AV.enc ⟨C, (xs.drop (8 * 15)).drop 8, C.drop (15 * tblW), zW C xs 15, [],
        List.replicate (numB (symA xs 15 ++ zW C xs 15)) true, [true], (lastTW C xs).tail, [], [],
        [], [], List.replicate tblW true, (lastTW C xs).take 1, [], [fl]⟩ := by
  simp only [lastW, run_seq]
  rw [run_clear (i := tE)]; encA
  rw [run_prim (Prim.snoc tE true)]; simp only [Prim.apply]; encA
  rw [run_offW _ 1 rfl rfl rfl rfl rfl rfl]
  rw [run_copy (i := tT2)]; encA
  rw [run_dropT_blank (t := tT2) (x := tU) (by decide) _ (by rfl)]; encA
  rw [run_pop (i := tT2)]; encA
  simp only [aStW, List.length_replicate, Nat.one_mul, lastTW, symA,
    List.take_of_length_le (length_zW_le C xs 15)]
  rfl

/-- **The law of the authorization program** (pure semantics). -/
theorem run_authW8 (C xs : List Bool) : run authW8 (inA C xs) = outA (authAW C xs) := by
  rw [authW8]
  repeat rw [run_seq]
  rw [run_lenA, run_initA, aSt_zero, run_stepsW, run_lastW]
  simp only [outA', run_seq, run_clear]
  encA
  rw [run_ifBit]; encA
  have hlb : hd (List.take 1 (lastTW C xs)) = lastBitW C xs := by rw [hd_take1]; rfl
  simp only [hd_cons]
  unfold authAW
  cases hl : decide (C.length = bpLenA)
  · simp only [Bool.false_eq_true, ite_false, run_setB, Bool.false_and]
    encA
    simp only [clrA, run_seq, run_clear]
    encA
    rfl
  · simp only [ite_true, run_ifBit]
    encA
    rw [hlb]
    cases lastBitW C xs
    · simp only [Bool.false_eq_true, ite_false, run_setB]
      encA
      simp only [clrA, run_seq, run_clear]
      encA
      rfl
    · simp only [ite_true, run_setB]
      encA
      simp only [clrA, run_seq, run_clear]
      encA
      rfl

/-! ### Coin-freeness and well-formedness -/

theorem goodA_offW : GoodA SA offW := by
  have hb : GoodA (fun t => SA t ∧ t ≠ tKC) (pp tK tBit ⨾ appT tU tU tA2 tB2 ⨾
      ifBit tBit (appT tU tE tA2 tB2) (nop tU) ⨾ clr tBit) :=
    (GoodA.prim _ (by simp +decide)).seq <| (goodA_appT (by decide) (by decide) (by decide) (by decide)).seq <|
      GoodA.seq (⟨CoinFree.ifBit' (coinFree_appT tU tE tA2 tB2) (CoinFree.prim' (.copy tU tU)),
        ⟨wf_appT (by decide) (by decide), (trivial : (prim (Prim.copy tU tU)).WF)⟩,
        WritesIn.ifBit (writesIn_appT (by decide) (by decide) (by decide))
          (WritesIn.prim (.copy tU tU) (by simp +decide))⟩ :
        GoodA (fun t => SA t ∧ t ≠ tKC) (ifBit tBit (appT tU tE tA2 tB2) (nop tU)))
        (GoodA.prim _ (by simp +decide))
  refine (GoodA.prim _ (by simp +decide)).seq <|
    (GoodA.iter (by decide) ((GoodA.prim _ (by simp +decide)).seq <|
      (GoodA.prim _ (by simp +decide)).seq (GoodA.prim _ (by simp +decide))) 8).seq <|
    (GoodA.prim _ (by simp +decide)).seq <|
    (GoodA.iter (by decide) ((GoodA.prim _ (by simp +decide)).seq <|
      (GoodA.prim _ (by simp +decide)).seq (GoodA.prim _ (by simp +decide))) 14).seq <|
    (GoodA.prim _ (by simp +decide)).seq <| (GoodA.prim _ (by simp +decide)).seq ?_
  exact (GoodA.prim _ (by simp +decide)).seq
    ⟨hb.1.loop', ⟨hb.2.1, hb.2.2 tKC (by simp)⟩, WritesIn.loop (by decide)
      (hb.2.2.mono fun t ht => ht.1)⟩

theorem goodA_stepW : GoodA SA stepW :=
  goodA_offW.seq <| (GoodA.prim _ (by simp +decide)).seq <|
    (goodA_dropT (by decide) (by decide) (by decide)).seq <| (GoodA.prim _ (by simp +decide)).seq <|
    (GoodA.iter (by decide) ((GoodA.prim _ (by simp +decide)).seq <|
      (GoodA.prim _ (by simp +decide)).seq (GoodA.prim _ (by simp +decide))) 14).seq <|
    (GoodA.prim _ (by simp +decide)).seq <| (goodA_dropT (by decide) (by decide) (by decide)).seq
      (GoodA.prim _ (by simp +decide))

/-- **The authorization program is coin-free and well formed.** -/
theorem good_authW8 : authW8.CoinFree ∧ authW8.WF := by
  let T : Fin 16 → Prop := fun _ => True
  have hL : GoodA T (Prog.map uL (lenEqP bpLenA)) :=
    ⟨coinFree_mapP uL (coinFree_lenEqP _), WF.map uL_inj (wf_lenEqP _), fun i hi => absurd trivial hi⟩
  have hI : GoodA T initA :=
    (goodA_natU trivial trivial trivial (by decide) (by decide) _).seq <|
      (goodA_natU trivial trivial trivial (by decide) (by decide) _).seq <|
      (GoodA.prim _ (by simp [T])).seq <| (GoodA.prim _ (by simp [T])).seq <|
        GoodA.seq (⟨coinFree_snocN _ _ _, wf_snocN _ _ _,
        writesIn_snocN trivial _ _⟩ : GoodA T (snocN tZB false 14))
        (goodA_natU trivial trivial trivial (by decide) (by decide) _)
  have hS : GoodA T (loop tS2 stepW) :=
    ⟨goodA_stepW.1.loop', ⟨goodA_stepW.2.1, goodA_stepW.2.2 tS2 (by simp)⟩,
      fun i hi => absurd trivial hi⟩
  have hLa : GoodA T lastW :=
    (GoodA.prim _ (by simp [T])).seq <| (GoodA.prim _ (by simp [T])).seq <|
      GoodA.seq (⟨goodA_offW.1, goodA_offW.2.1, fun i hi => absurd trivial hi⟩ : GoodA T offW) <|
      (GoodA.prim _ (by simp [T])).seq <| (goodA_dropT trivial trivial (by decide)).seq
        (GoodA.prim _ (by simp [T]))
  have hO : GoodA T outA' :=
    (GoodA.prim _ (by simp [T])).seq ⟨CoinFree.ifBit' (CoinFree.ifBit' (coinFree_setB _ _)
      (coinFree_setB _ _)) (coinFree_setB _ _), ⟨⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩,
      ⟨trivial, trivial⟩⟩, fun i hi => absurd trivial hi⟩
  have hC : GoodA T clrA := by
    unfold clrA
    repeat (first | exact GoodA.prim _ (by simp [T]) | refine (GoodA.prim _ (by simp [T])).seq ?_)
  have h := hL.seq (hI.seq (hS.seq (hLa.seq (hO.seq hC))))
  exact ⟨h.1, h.2.1⟩

/-- **The law of the authorization program**: the point mass at the store with the bit
`authAW C xs` on tape `0`. -/
theorem law_authW8 (C xs : List Bool) :
    authW8.law (inA C xs) = PMF.pure (outA (authAW C xs)) := by
  rw [law_eq_run_of_coinFree _ good_authW8.1, run_authW8]

/-! ### The authorization bit is the program's output -/

theorem encAttribute_eq (x : Attribute w8) : encAttribute w8 x = encAttr x := rfl

/-- The program of a word, as a branching program of the gates. -/
def toBP (F : Program w8) : AdvancedEncryption.PE.BranchingProgram.BP :=
  ⟨fun i z a => F.step i z a, F.out⟩

theorem output_toBP (F : Program w8) (x : Attribute w8) :
    AdvancedEncryption.PE.BranchingProgram.output (toBP F) x = F.output x := rfl

/-- A window of 14 bits, reversed, is the state it reads, most significant first. -/
theorem reverse_window (C : List Bool) (p : ℕ) (h : p + 14 ≤ C.length) :
    ((C.drop p).take 14).reverse = bitsN (readSt C p).val 14 := by
  set w := (C.drop p).take 14 with hw
  have hl : w.length = 14 := by rw [hw]; simp; omega
  have hv : val w < 2 ^ 14 := by have := val_lt w; rwa [hl] at this
  have hr : (readSt C p).val = val w := by
    simp only [readSt, ← hw, stateBits]; exact Nat.mod_eq_of_lt hv
  rw [hr]
  have e := toBits_val w
  rw [hl, ← testBit_eq_toBits] at e
  apply List.ext_getElem (by simp [bitsN, hl])
  intro k h1 h2
  have hk : k < 14 := by simpa [hl] using h1
  simp only [List.getElem_reverse, bitsN, List.getElem_ofFn]
  have hj : w.length - 1 - k < w.length := by omega
  rw [List.getElem_of_eq e.symm hj]
  simp only [List.getElem_map, List.getElem_finRange, Fin.val_cast, hl]

/-- **The states of the authorization program** are those of the program of the word. -/
theorem zW_encAttr (C : List Bool) (hC : C.length = predLen) (x : Attr) :
    ∀ i, i ≤ 15 → zW C (encAttr x) i = bitsN (zs (toBP (progOf C)) x i).val 14
  | 0, _ => by
    simp only [zW, zs]
    apply List.ext_getElem (by simp [bitsN]); intro k h1 h2; simp [bitsN]
  | i + 1, hi => by
    rw [zW, zW_encAttr C hC x i (by omega), symA_encAttr x i (by omega)]
    simp only [zs, show i < 15 from by omega, dite_true]
    rw [stepZW, numB_append, numB_bitsN, numB_bitsN, List.drop_drop]
    have hz : (zs (toBP (progOf C)) x i).val < 2 ^ 14 := (zs (toBP (progOf C)) x i).isLt
    have ha : (x ⟨i, by omega⟩).val < 2 ^ 8 := (x ⟨i, by omega⟩).isLt
    have hl : (bitsN (zs (toBP (progOf C)) x i).val 14).length = 14 := by simp [bitsN]
    have hp : i * tblW + 14 * ((x ⟨i, by omega⟩).val % 2 ^ 8 *
        2 ^ (bitsN (zs (toBP (progOf C)) x i).val 14).length +
        (zs (toBP (progOf C)) x i).val % 2 ^ 14) = stateBits *
          (2 ^ AdvancedEncryption.ExpLUT.Prog.lutBits * i +
          (uOf (zs (toBP (progOf C)) x i) (x ⟨i, by omega⟩)).val) := by
      rw [hl, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hz]
      simp only [uOf, tblW, stateBits, AdvancedEncryption.ExpLUT.Prog.lutBits]
      ring
    rw [hp, reverse_window C _ ?_]
    · rfl
    · simp only [uOf, stateBits, AdvancedEncryption.ExpLUT.Prog.lutBits, hC, predLen]
      have : i ≤ 14 := by omega
      omega

/-- The authorization bit on attribute bits, for attributes of the gates. -/
theorem authAW_encAttr' (C : List Bool) (x : Attr) :
    authAW C (encAttr x) = (decide (C.length = predLen) && !(progOf C).output x) := by
  by_cases hC : C.length = predLen
  · have hl : lastBitW C (encAttr x) = (progOf C).output x := by
      have hrun : (progOf C).run x = zs (toBP (progOf C)) x 15 := run_eq_zs (toBP (progOf C)) x
      rw [lastBitW, zW_encAttr C hC x 15 le_rfl, symA_encAttr x 15 (by omega),
        numB_append, numB_bitsN, numB_bitsN, List.drop_drop, hd_drop]
      unfold AdvancedEncryption.PE.BranchingProgram.Program.output
      rw [hrun]
      show C.getD _ false = C.getD _ false
      congr 1
      have hz : (zs (toBP (progOf C)) x 15).val < 2 ^ 14 := (zs (toBP (progOf C)) x 15).isLt
      have ha : (x ⟨15, by omega⟩).val < 2 ^ 8 := (x ⟨15, by omega⟩).isLt
      have hl : (bitsN (zs (toBP (progOf C)) x 15).val 14).length = 14 := by simp [bitsN]
      rw [hl, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hz]
      simp only [tblW, uOf, stateBits]
      change 15 * (2 ^ 22 * 14) + ((x ⟨15, by omega⟩).val * 2 ^ 14 + _) =
        210 * 2 ^ 22 + (_ + 2 ^ 14 * (x ⟨15, by omega⟩).val)
      omega
    rw [authAW, hl, show bpLenA = predLen from rfl]
  · rw [authAW, show bpLenA = predLen from rfl]; simp [hC]

/-- **The authorization bit is the negated output of the program of the word**, within the class. -/
theorem authAW_encAttr (C : List Bool) (x : Attribute w8) :
    authAW C (encAttribute w8 x) = (decide (C.length = predLen) && !(progOf C).output x) :=
  authAW_encAttr' C x

end AdvancedEncryption.ExpLUT.AuthW
