import PE.Impl.Gates.WindowTest
import SigabaNeo.Lib.Machines.Prog.GateGen

/-!
# Window predicates written by a tape program

`genPred : Prog 40` writes, on tape `2`, the predicate `pairWord (a, b)` of a pair of dates whose
words, least significant bit first, are on the tapes `26` (`a`) and `27` (`b`)
(`run_genPred`): it is the gate generator `SigabaNeo.Tape.GateGen.genE` on `winD`, the window
expression `winExp` with the two dates read from the tapes, followed by the final negation gate.
-/

namespace AdvancedEncryption.PE.Gates.DateWindow

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Lattices.SLP SigabaNeo.Tape SigabaNeo.Tape.Prog
  SigabaNeo.Tape.GateGen AdvancedEncryption.PE.DateWindow
open scoped Prog

/-- `is = c`, static. -/
def eqD (is : List (Fin 10)) (c : Sym) : DExp := .and (.ge is (symBits c)) (.le is (symBits c))

/-- The format check, static. -/
def validD : DExp :=
  .and (.ge M (symBits 1)) <| .and (.le M (symBits 12)) <| .and (.ge D (symBits 1)) <|
    .and (.or (.not (eqD M 2)) (.le D (symBits 29)))
      (.or (.not (.or (eqD M 4) (.or (eqD M 6) (.or (eqD M 9) (eqD M 11))))) (.le D (symBits 30)))

/-- The window expression, the dates read from the tapes `26` and `27`. -/
def winD : DExp := .and (.geT A 26) (.and (.leT A 27) validD)

theorem winD_toB (env : Store 40) :
    winD.toB env = .and (.ge A (env 26).reverse) (.and (.le A (env 27).reverse) validExp) := rfl

theorem winD_depth : winD.depth ≤ 16 := by decide

/-- **The predicate of a pair of dates**: initialize, generate, negate. -/
def genPred : Prog 40 :=
  clr O ⨾ (clr G ⨾ ones' 11) ⨾ clr W ⨾ clr E ⨾ genE 0 winD ⨾ gateP (.tape W) (.tape W)
where
  /-- `G := 1^n`. -/
  ones' : ℕ → Prog 40
    | 0 => prim (.copy G G)
    | n + 1 => ones' n ⨾ prim (.snoc G true)

theorem run_ones' : ∀ (n : ℕ) (s : Store 40), run (genPred.ones' n) s = Function.update s G (s G ++ un n)
  | 0, s => by simp [genPred.ones', Prim.apply]
  | n + 1, s => by
    rw [genPred.ones', run_seq, run_ones' n s, run_prim]
    simp [Prim.apply, List.replicate_succ', List.append_assoc]

/-- The tapes `genPred` may change. -/
def predTapes (u : Fin 40) : Prop := Clob 0 winD u ∨ u = E

theorem length_encDate' (x : Date) : (encDate x).reverse.length = 10 := by simp [length_encDate]

/-- **`genPred` writes the predicate of the pair of dates.** -/
theorem run_genPred (a b : Date) (s : Store 40) (ha : s 26 = (encDate a).reverse)
    (hb : s 27 = (encDate b).reverse) :
    run genPred s O = pairWord (a, b) ∧ ∀ u, ¬ predTapes u → run genPred s u = s u := by
  set s1 := run (clr O ⨾ (clr G ⨾ genPred.ones' 11) ⨾ clr W ⨾ clr E) s with hs1
  have e1 : ∀ u, u ≠ O → u ≠ G → u ≠ W → u ≠ E → s1 u = s u := fun u h1 h2 h3 h4 => by
    simp [s1, run_ones', Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3, Function.update_of_ne h4]
  have hrep : Rep s1 [] .one := by
    refine ⟨by simp [s1, run_ones', unparse, toGates], by simp [s1, run_ones'], by simp [s1, run_ones', wireIdx],
      by simp [s1, run_ones']⟩
  have h26 : s1 26 = (encDate a).reverse := by rw [e1 26 (by decide) (by decide) (by decide) (by decide), ha]
  have h27 : s1 27 = (encDate b).reverse := by rw [e1 27 (by decide) (by decide) (by decide) (by decide), hb]
  have hok : winD.SrcOk s1 := by
    refine ⟨⟨⟨by unfold stepTapes; decide, by decide, by decide⟩, by simp [DExp.IsReg], by
      rw [h26, length_encDate']; rfl⟩, ⟨⟨⟨by unfold stepTapes; decide, by decide, by decide⟩,
      by simp [DExp.IsReg], by rw [h27, length_encDate']; rfl⟩, ?_, ?_⟩, ?_⟩
    · simp [validD, eqD, DExp.SrcOk, DExp.srcs]
    · simp [validD, eqD, DExp.srcs]
    · simp [winD, validD, eqD, DExp.srcs]
  obtain ⟨h2, f2⟩ := run_genE winD 0 s1 [] .one hrep (by simpa using winD_depth) hok
  rw [winD_toB, h26, h27, List.reverse_reverse, List.reverse_reverse] at h2
  obtain ⟨hW1, hW2⟩ := h2.okW
  obtain ⟨h3, f3⟩ := rep_gateP h2 hW1 hW1 hW2 hW2
  have erun : run genPred s = run (gateP (.tape W) (.tape W)) (run (genE 0 winD) s1) := rfl
  refine ⟨?_, fun u hu => ?_⟩
  · rw [erun, h3.1]
    simp only [addNand, pairWord, predGates, winExp]
  · have hu' : ¬ Clob 0 winD u := fun hc => hu (Or.inl hc)
    have hst : ¬ stepTapes u := fun h => hu' (Or.inl h)
    rw [erun, f3 u (fun hg => hst (stepTapes_of_gate hg)), f2 u hu']
    exact e1 u (fun e => hst (by simp [stepTapes, e])) (fun e => hst (by simp [stepTapes, e]))
      (fun e => hst (by simp [stepTapes, e])) (fun e => hu (Or.inr e))

end AdvancedEncryption.PE.Gates.DateWindow
