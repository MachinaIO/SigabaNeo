import PE.Impl.DualUse.Prog.KeyPTime
import PE.Impl.DualUse.Prog.BpCompCost
import SigabaNeo.Lib.Machines.Prog.LenEq
import SigabaNeo.Lib.Machines.Prog.FrameIO
import SigabaNeo.Lib.Machines.Prog.Lookup
import SigabaNeo.Lib.Machines.Prog.Stream

/-!
# The front end for branching programs (Stage II, not wired)

`frontBP n : XProg 72` (`R = 70`), on the predicate word `C` (tape `0`):

1. the length guard `leP n` (tapes `0, 64, 65`): longer words are answered by `[]`;
2. the length test `lenEqP bpLen` (tapes `0, 64, …, 68`, flag on `64`): words of another length are
   answered by `[false]`;
3. words of `bpLen` bits: the word cut to `bpLen` bits (`cutPn`: semantically the identity, it makes
   the static bound of tape `0` equal to `bpLen`), the tapes `1 … 63` cleared (they are blank; the clearing makes their
   static bound `0`), the compiler `bpCompC` (WS7) on the first `64` tapes, then `true` consed:
   `true :: rpW 512 (bpRP (tablesOf C))`;
4. every tape but `0` cleared.

**`law_frontBP`**: the law of `frontG n (·.length = bpLen) bwBP`, from `law_bpCompC` and
`run_lenEqP`, `run_leP` (no unfolding of `bpRP`, `tablesOf` or the compiler).
**`frontSpecG_frontBP`**: `FrontSpecG (frontBP n) n (·.length = bpLen) bwBP (frontBT n) (frontBL)
(frontBS n)`; at the switch (`ValidC C := C.length = bpLen`, `blockWord W C := rpW W (bpRP
(tablesOf C))`) this is `FrontSpec (frontBP c.L) c.L 512 …`.

The compiler needs `64` tapes of its own, so the front end has `72` tapes and is framed in the shells
on `1, 83, …, 153` (`eF`): **KeyGen, Dec and the key component keep their `256` tapes**.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg SigabaNeo.Lattices
open AdvancedEncryption.PE.Gates.BPWord
open AdvancedEncryption.DualUse.BpComp (bpCompC inp law_bpCompC coinFree_bpCompC wf_bpCompC)
open scoped SigabaNeo.Tape.Prog

/-- **The block word of a branching program**: the instruction stream of its register program. -/
noncomputable def bwBP (C : List Bool) : List Bool := RP.rpW 512 (bpRP (tablesOf C))

/-! ### The program -/

/-- The tapes of the length guard. -/
def eLe : Fin 3 ↪ Fin 72 := ⟨![0, 64, 65], by decide⟩

/-- The tapes of the length test. -/
def eEq : Fin 6 ↪ Fin 72 := ⟨![0, 64, 65, 66, 67, 68], by decide⟩

/-- The tapes of the compiler: the first `64`. -/
def e64 : Fin 64 ↪ Fin 72 := Fin.castLEEmb (by norm_num)

/-- The tapes `1 … 63`. -/
def clr63 : List (Fin 72) := (List.finRange 72).filter fun t => t ≠ 0 ∧ t.val < 64

/-- Every tape but `0`. -/
def clr71 : List (Fin 72) := (List.finRange 72).filter fun t => t ≠ 0

theorem mem_clr63 (t : Fin 72) : t ∈ clr63 ↔ t ≠ 0 ∧ t.val < 64 := by simp [clr63]

theorem mem_clr71 (t : Fin 72) : t ∈ clr71 ↔ t ≠ 0 := by simp [clr71]

/-- **The cut to `bpLen` bits**: tape `0` replaced by its first `bpLen` bits (padded), through the
template on tape `69`. Its static bound on tape `0` is `bpLen` whatever the input bound. -/
def cutPn (m : ℕ) : Prog 72 :=
  SigabaNeo.Tape.Prog.putW 69 (List.replicate m false) ⨾ .prim (.carry Prog.takeOp 69 0) ⨾
    .prim (.clear 0) ⨾ .prim (.copy 0 69) ⨾ .prim (.clear 69)

/-- The branch of a word of `m` bits. -/
def validB (m : ℕ) : XProg 72 :=
  seq (prog (.prim (.clear 64))) <| seq (prog (cutPn m)) <| seq (clearL clr63) <|
    seq (frame e64 (prog bpCompC)) (prog (.prim (.cons 0 true)))

/-- The branch of a short word of another length. -/
def dumBP : XProg 72 :=
  seq (prog (.prim (.clear 64))) <| seq (prog (.prim (.clear 0))) (prog (.prim (.snoc 0 false)))

/-- The branches after the guard. -/
def shortB (m : ℕ) : XProg 72 :=
  seq (prog (.prim (.clear 64))) <| seq (frame eEq (prog (Prog.lenEqP m))) <|
    ifBit 64 (validB m) dumBP

/-- **The front end** with the guard `n` and the word length `m`. -/
def frontBPn (n m : ℕ) : XProg 72 :=
  seq (frame eLe (prog (Prog.leP n))) <| seq (ifBlank 64 (prog (.prim (.clear 0))) (shortB m))
    (clearL clr71)

/-- **The front end for branching programs.** -/
def frontBP (n : ℕ) : XProg 72 := frontBPn n bpLen

/-! ### The law -/

/-- The word `x` on tape `0`, every other tape blank. -/
def o0 (x : List Bool) : Store 72 := Function.update (fun _ => []) 0 x

theorem io2_o0 (x : List Bool) : io2 (R := 70) x [] [] = o0 x := by
  funext t
  simp only [io2, o0, Function.update_apply]
  by_cases h : t = 0
  · subst h; simp
  · have : t.val ≠ 0 := fun e => h (Fin.ext e)
    simp [h, this]

theorem law_frame_cf {m : ℕ} (e : Fin m ↪ Fin 72) (p : Prog m) (hp : p.CoinFree) (s : Store 72) :
    (frame e (prog p)).law s = PMF.pure (embedF e s (Prog.run p (fun j => s (e j)))) := by
  rw [XProg.law_frame, XProg.law_prog, Prog.law_eq_run_of_coinFree _ hp, PMF.pure_map]

theorem law_leBP (n : ℕ) (C : List Bool) :
    (frame eLe (prog (Prog.leP n))).law (o0 C) =
      PMF.pure (Function.update (o0 C) 64 (if C.length ≤ n then [true] else [])) := by
  rw [law_frame_cf _ _ (Prog.coinFree_leP n), Prog.run_leP]
  congr 1
  refine embedF_eq_of _ _ _ _ (fun j => ?_) (fun t ht => ?_)
  · fin_cases j <;> simp [eLe, o0, Function.update_apply]
  · have h64 : t ≠ 64 := fun h => ht 1 (by rw [h]; rfl)
    rw [Function.update_of_ne h64]

theorem view_eEq (C : List Bool) : (fun j => o0 C (eEq j)) = Prog.in0 C := by
  funext j
  fin_cases j <;> simp [eEq, o0, Prog.in0, Function.update_apply]

theorem law_eqBP (m : ℕ) (C : List Bool) :
    (frame eEq (prog (Prog.lenEqP m))).law (o0 C) =
      PMF.pure (Function.update (o0 C) 64 [decide (C.length = m)]) := by
  rw [law_frame_cf _ _ (Prog.coinFree_lenEqP m), view_eEq, Prog.run_lenEqP]
  congr 1
  refine embedF_eq_of _ _ _ _ (fun j => ?_) (fun t ht => ?_)
  · fin_cases j <;> simp [eEq, o0, Prog.in0, Function.update_apply]
  · have h64 : t ≠ 64 := fun h => ht 1 (by rw [h]; rfl)
    rw [Function.update_of_ne h64]

theorem update_o0_64 (C : List Bool) (w : List Bool) :
    Function.update (Function.update (o0 C) 64 w) 64 [] = o0 C := by
  funext t
  by_cases h : t = 64
  · subst h; simp [o0]
  · simp [Function.update_of_ne h]

theorem law_compBP (C : List Bool) :
    (frame e64 (prog bpCompC)).law (o0 C) = PMF.pure (o0 (bwBP C)) := by
  have hv : (fun j => o0 C (e64 j)) = inp C := by
    funext j
    simp only [o0, inp, e64, Fin.castLEEmb_apply, Function.update_apply]
    by_cases h : j = 0
    · subst h; rfl
    · have h' : Fin.castLE (by norm_num : 64 ≤ 72) j ≠ 0 := fun e =>
        h (Fin.ext (by have := congrArg Fin.val e; simpa using this))
      rw [if_neg h', if_neg (show j ≠ BpComp.tIN from h)]
  rw [XProg.law_frame, hv, XProg.law_prog, law_bpCompC, PMF.pure_map]
  congr 1
  refine embedF_eq_of _ _ _ _ (fun j => ?_) (fun t ht => ?_)
  · simp only [o0, inp, e64, Fin.castLEEmb_apply, Function.update_apply, bwBP]
    by_cases h : j = 0
    · subst h; rfl
    · have h' : Fin.castLE (by norm_num : 64 ≤ 72) j ≠ 0 := fun e =>
        h (Fin.ext (by have := congrArg Fin.val e; simpa using this))
      rw [if_neg h', if_neg (show j ≠ BpComp.tIN from h)]
  · have h0 : t ≠ 0 := fun h => ht 0 (by rw [h]; rfl)
    simp [o0, Function.update_of_ne h0]

theorem law_clr_o0 {l : List (Fin 72)} (hl : (0 : Fin 72) ∉ l) (x : List Bool) :
    (clearL l).law (o0 x) = PMF.pure (o0 x) := by
  rw [law_clearL]
  congr 1
  funext t
  split_ifs with h
  · have : t ≠ 0 := fun e => hl (e ▸ h)
    simp [o0, Function.update_of_ne this]
  · rfl

theorem coinFree_cutPn (m : ℕ) : (cutPn m).CoinFree := by
  have h := SigabaNeo.Tape.Prog.coinFree_putW (69 : Fin 72) (List.replicate m false)
  simp only [Prog.CoinFree] at h
  simp [cutPn, Prog.CoinFree, Prog.coinFreeB, h]

theorem law_cutPn {m : ℕ} {C : List Bool} (h : C.length = m) :
    (prog (cutPn m)).law (o0 C) = PMF.pure (o0 C) := by
  rw [XProg.law_prog, Prog.law_eq_run_of_coinFree _ (coinFree_cutPn m)]
  congr 1
  simp only [cutPn, Prog.run_seq, SigabaNeo.Tape.Prog.run_putW, Prog.run_prim, Prim.apply]
  have e : (carryOp Prog.takeOp (List.replicate m false) C).2 = C := by
    rw [Prog.carryOp_takeOp, List.length_replicate, ← h, takeD_of_length]
  funext t
  simp only [Function.update_apply, o0]
  by_cases h69 : t = 69
  · subst h69; simp
  · by_cases h0 : t = 0
    · subst h0; simp [e]
    · simp [h69, h0]

theorem law_validB {m : ℕ} {C : List Bool} (hC : C.length = m) :
    (validB m).law (Function.update (o0 C) 64 [true]) = PMF.pure (o0 (true :: bwBP C)) := by
  rw [validB, XProg.law_seq_pure (XProg.law_prim _ _)]
  simp only [Prim.apply]
  rw [update_o0_64, XProg.law_seq_pure (law_cutPn hC),
    XProg.law_seq_pure (law_clr_o0 (by simp [mem_clr63]) C),
    XProg.law_seq_pure (law_compBP C), XProg.law_prim]
  congr 1
  funext t
  simp only [Prim.apply, o0, Function.update_apply]
  split_ifs <;> rfl

theorem law_dumBP (C : List Bool) :
    dumBP.law (Function.update (o0 C) 64 [false]) = PMF.pure (o0 [false]) := by
  rw [dumBP, XProg.law_seq_pure (XProg.law_prim _ _), XProg.law_seq_pure (XProg.law_prim _ _),
    XProg.law_prim]
  congr 1
  funext t
  simp only [Prim.apply, o0, Function.update_apply]
  split_ifs <;> simp_all

theorem law_shortB (m : ℕ) (C : List Bool) :
    (shortB m).law (Function.update (o0 C) 64 [true]) =
      PMF.pure (o0 (if C.length = m then true :: bwBP C else [false])) := by
  rw [shortB, XProg.law_seq_pure (XProg.law_prim _ _)]
  simp only [Prim.apply]
  rw [update_o0_64, XProg.law_seq_pure (law_eqBP m C), XProg.law_ifBit]
  by_cases h : C.length = m
  · rw [if_pos (by simp [h]), if_pos h]
    simpa [h] using law_validB h
  · rw [if_neg (by simp [h]), if_neg h]
    simpa [h] using law_dumBP C

/-- **The law of the front end**, for any guard `n` and word length `m`. -/
theorem law_frontBPn (n m : ℕ) (C : List Bool) :
    (frontBPn n m).law (io2 (R := 70) C [] []) =
      PMF.pure (io2 (R := 70) (frontG n (fun C => C.length = m) bwBP C) [] []) := by
  rw [io2_o0, io2_o0, frontBPn, XProg.law_seq_pure (law_leBP n C), XProg.law_seq, XProg.law_ifBlank]
  by_cases hl : C.length ≤ n
  · rw [if_neg (by simp [hl]), if_pos hl] at *
    rw [law_shortB, PMF.pure_bind, law_clr_o0 (by simp [mem_clr71])]
    by_cases h : C.length = m
    · rw [if_pos h, frontG_valid hl h]
    · rw [if_neg h, frontG_short_not hl h]
  · rw [if_neg hl, if_pos (by simp), XProg.law_prim, PMF.pure_bind, frontG_long hl]
    have e : Prim.apply (.clear 0) (Function.update (o0 C) 64 []) = o0 [] := by
      funext t
      simp only [Prim.apply, o0, Function.update_apply]
      split_ifs <;> rfl
    rw [e, law_clr_o0 (by simp [mem_clr71])]

/-- **The law of the front end for branching programs.** -/
theorem law_frontBP (n : ℕ) (C : List Bool) :
    (frontBP n).law (io2 (R := 70) C [] []) =
      PMF.pure (io2 (R := 70) (frontG n (fun C => C.length = bpLen) bwBP C) [] []) :=
  law_frontBPn n bpLen C

theorem wf_cutPn (m : ℕ) : (cutPn m).WF :=
  ⟨SigabaNeo.Tape.Prog.wf_putW _ _, trivial, trivial, trivial, trivial⟩

theorem wf_frontBPn (n m : ℕ) : (frontBPn n m).WF :=
  ⟨Prog.wf_leP n, ⟨trivial, ⟨trivial, Prog.wf_lenEqP _,
    ⟨⟨trivial, wf_cutPn m, wf_clearL _, wf_bpCompC, trivial⟩, trivial, trivial, trivial⟩⟩⟩,
    wf_clearL _⟩

theorem wf_frontBP (n : ℕ) : (frontBP n).WF := wf_frontBPn n bpLen

theorem cf_clearL72 : ∀ l : List (Fin 72), (clearL l).coinFreeB = true
  | [] => rfl
  | _ :: l => by simp [clearL, XProg.coinFreeB, Prog.coinFreeB, cf_clearL72 l]

theorem coinFree_frontBPn (n m : ℕ) : (frontBPn n m).CoinFree := by
  have h1 := Prog.coinFree_leP n
  have h2 := Prog.coinFree_lenEqP m
  have h3 := coinFree_bpCompC
  have h4 := coinFree_cutPn m
  simp only [Prog.CoinFree] at h1 h2 h3 h4
  simp [frontBPn, shortB, validB, dumBP, XProg.CoinFree, XProg.coinFreeB, Prog.coinFreeB, h1, h2,
    h3, h4, cf_clearL72]

theorem coinFree_frontBP (n : ℕ) : (frontBP n).CoinFree := coinFree_frontBPn n bpLen

end AdvancedEncryption.DualUse.Prog
