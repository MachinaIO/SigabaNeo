import PE.Impl.DualUse.ReductionMachine
import SigabaNeo.Lib.Machines.Prog.Pass

/-!
# The post-processing machine of the reduction

`Post n E nA nM` reads `pairOut o u = o ++ false :: true :: dbl u`, the output `o` of the
adversary (`|o| ≤ n`) paired with the encoded final state `u` of the handlers (`|u| ≤ E`), and
writes `[false]` when the flag of the state is up, and `true :: encodeTuple [encOpt attr,
encOpt msg, o]` otherwise (`postG`).

Every primitive of the tape language sweeps whole tapes, so the long word `o` is never read bit by
bit by a program. The machine is one closed machine of four phases (`SigabaNeo.Tape.Pass`), each
linear in the input length, with no clock between them (so its number of states does not depend on
`n`):

1. `revInPhase`: tape `0` := the reversal of the input, `dbl (rev u) ++ true :: false :: rev o`;
2. `trPhase sepT`: tape `1` := the separator transducer `sepT` on tape `0`: it reads pairs, emits
   `[true, b]` for a pair `b b` (a bit of `rev u`) and `[false, false]` for the first unequal pair
   `true false` (the separator), then `[c, true]` for every bit `c` of `rev o`, so that tape `1` is
   `frame (rev u) ++ rev (frame o)` (`sepT_run`);
3. the tape program `postProg E nA nM`: `E` rounds move the bits of `u` (at most `E`) to tape `3`;
   tape `1` is then `rev (frame o)`, and the program appends the reversal of the head
   `true :: frame (encOpt attr) ++ frame (encOpt msg)` read off `u` (or writes `[false]` when the
   flag is up). It has no loop, so it takes `pcount · (2 L + …)` steps for words of length `L`;
4. `revOutPhase`: emit the reversal of tape `1`.

## Main results

* `Generic.run_post`: `(Post n E cd.nA cd.nM).run (pairOut o (cd.encState st)) =
  PMF.pure (postG (obs (o, st.2)))` for `|o| ≤ n` and a state `st` as the handlers keep it
  (`PostOK`: the instance word does not start with `false`, the experiment state is initial or
  selected, the encoded state has at most `E` bits).
* `Generic.time_post`: `(Post n E nA nM).time = postA E nA nM * n + postB E nA nM`;
  `Generic.descLen_post`: the description length does not depend on `n`.
-/

namespace AdvancedEncryption.PE.Generic

open SigabaNeo SigabaNeo.Tape SigabaNeo.Inline Cslib Turing MultiTapePTM

/-! ### The separator transducer -/

/-- The step of `sepT`: `some none` before the first bit of a pair, `some (some b)` after a first
bit `b`, `none` after the separator. -/
def sepStep : Option (Option Bool) → Bool → Option (Option Bool) × List Bool
  | some none, a => (some (some a), [])
  | some (some b), a => if a = b then (some none, [true, b]) else (none, [false, false])
  | none, c => (none, [c, true])

theorem length_sepStep (q : Option (Option Bool)) (a : Bool) : (sepStep q a).2.length ≤ 2 := by
  rcases q with _ | _ | b
  · simp [sepStep]
  · simp [sepStep]
  · simp only [sepStep]; split_ifs <;> simp

/-- **The separator transducer.** -/
def sepT : MultiTapeTM.Transducer Bool (Option (Option Bool)) where
  q₀ := some none
  step := sepStep
  final _ := []
  length_step_le := length_sepStep
  length_final_le _ := by simp

@[simp] theorem sepT_step : sepT.step = sepStep := rfl
@[simp] theorem sepT_final (q : Option (Option Bool)) : sepT.final q = [] := rfl
@[simp] theorem sepT_q₀ : sepT.q₀ = some none := rfl

theorem sepT_run_none : ∀ r : List Bool, sepT.run none r = r.flatMap (fun c => [c, true])
  | [] => rfl
  | c :: r => by
    rw [MultiTapeTM.Transducer.run_cons]
    simp [sepStep, sepT_run_none r]

theorem sepT_run (r : List Bool) : ∀ v : List Bool,
    sepT.run (some none) (dbl v ++ true :: false :: r) =
      v.flatMap (fun b => [true, b]) ++ false :: false :: r.flatMap (fun c => [c, true])
  | [] => by
    simp [MultiTapeTM.Transducer.run_cons, sepStep, sepT_run_none]
  | b :: v => by
    simp [MultiTapeTM.Transducer.run_cons, sepStep, sepT_run r v]

theorem reverse_pairOut (o u : List Bool) :
    (pairOut o u).reverse = dbl u.reverse ++ true :: false :: o.reverse := by
  simp [pairOut, reverse_dbl]

/-- **The word of tape `1` after the transducer.** -/
theorem sepT_run_pairOut (o u : List Bool) :
    sepT.run sepT.q₀ (pairOut o u).reverse =
      u.reverse.flatMap (fun b => [true, b]) ++ false :: false ::
        o.reverse.flatMap (fun c => [c, true]) := by
  rw [reverse_pairOut, sepT_q₀]; exact sepT_run _ _

/-! ### The program

Tapes: `0` the reversed input, `1` the word being built, `2` a flag tape of the phases, `3` the
state word `u`, `4` a blank scratch tape, `5` the reversed attribute, `6` the reversed message,
`7` the message flag. -/

/-- One round: if tape `1` starts with `true b`, drop it and put `b` in front of tape `3`. -/
def rnd : Prog 8 :=
  .ifBit 1 (.seq (.prim (.tail 1)) (.seq (.prim (.pop 1 4)) (.seq (.prim (.consHead 3 4))
    (.prim (.clear 4))))) (.prim (.copy 1 1))

/-- Append `false`, then `b true` for each of the `c` first bits `b` of tape `j`, then
`true true`. -/
def appendFR (j : Fin 8) (c : ℕ) : Prog 8 :=
  .seq (.prim (.snoc 1 false)) (.seq (Prog.iter 1 (.seq (.prim (.snocHead 1 j))
    (.seq (.prim (.snoc 1 true)) (.prim (.tail j)))) c) (.seq (.prim (.snoc 1 true))
      (.prim (.snoc 1 true))))

/-- Before the selection: append `false false true`. -/
def caseA : Prog 8 := .seq (.prim (.snoc 1 false)) (.seq (.prim (.snoc 1 false)) (.prim (.snoc 1 true)))

/-- The flag is up: write `[false]`. -/
def badB : Prog 8 := .seq (.prim (.clear 1)) (.prim (.cons 1 false))

/-- The flag is down: parse `m :: msg ++ attr ++ σ` and append the reversed head. -/
def goodB (nA nM : ℕ) : Prog 8 :=
  .seq (.prim (.tail 3)) (.seq (.prim (.pop 3 7)) (.seq (Prog.moveRev nM 3 6 4)
    (.seq (Prog.moveRev nA 3 5 4) (.seq (.ifBit 7 (appendFR 6 nM) (.prim (.snoc 1 false)))
      (.seq (appendFR 5 nA) (.prim (.snoc 1 true)))))))

/-- After the selection: `false :: bad :: …`. -/
def caseB (nA nM : ℕ) : Prog 8 := .seq (.prim (.tail 3)) (.ifBit 3 badB (goodB nA nM))

/-- **The program of the post-processing.** -/
def postProg (E nA nM : ℕ) : Prog 8 :=
  .seq (Prog.iter 1 rnd E) (.seq (.prim (.tail 1))
    (.ifBlank 3 caseA (.ifBit 3 caseA (caseB nA nM))))

/-! ### Its semantics -/

section Sem

open Prog

theorem run_rnd_true (s : Store 8) {b : Bool} {R : List Bool} (h1 : s 1 = true :: b :: R)
    (h4 : s 4 = []) : run rnd s = Function.update (Function.update s 1 R) 3 (b :: s 3) := by
  funext j
  fin_cases j <;> simp [rnd, run_ifBit, run_prim, Prim.apply, Function.update_apply, h1, h4]

theorem run_rnd_false (s : Store 8) {R : List Bool} (h1 : s 1 = false :: R) : run rnd s = s := by
  funext j
  fin_cases j <;> simp [rnd, run_ifBit, run_prim, Prim.apply, Function.update_apply, h1]

theorem run_rnds (R : List Bool) : ∀ (v : List Bool) (s : Store 8) (E : ℕ),
    s 1 = v.flatMap (fun b => [true, b]) ++ false :: R → s 4 = [] → v.length ≤ E →
    (run rnd)^[E] s = Function.update (Function.update s 1 (false :: R)) 3 (v.reverse ++ s 3)
  | [], s, E, h1, _, _ => by
    have hfix : ∀ m, (run rnd)^[m] s = s := fun m =>
      Function.iterate_fixed (run_rnd_false s (by simpa using h1)) m
    rw [hfix]
    funext j
    simp only [List.flatMap_nil, List.nil_append] at h1
    simp [Function.update_apply]
    split_ifs <;> simp_all
  | b :: v, s, E, h1, h4, hE => by
    obtain ⟨E, rfl⟩ : ∃ E', E = E' + 1 := ⟨E - 1, by simp at hE; omega⟩
    rw [Function.iterate_succ_apply, run_rnd_true s (by simpa using h1) h4]
    rw [run_rnds R v _ E (by simp) (by simp [Function.update_apply, h4]) (by simp at hE; omega)]
    funext j
    simp [Function.update_apply]
    split_ifs <;> simp_all

/-- The round of `appendFR`. -/
def frBody (j : Fin 8) : Prog 8 :=
  .seq (.prim (.snocHead 1 j)) (.seq (.prim (.snoc 1 true)) (.prim (.tail j)))

theorem run_frBody_iter (j : Fin 8) (hj : j ≠ 1) : ∀ (l : List Bool) (s : Store 8), s j = l →
    (run (frBody j))^[l.length] s =
      Function.update (Function.update s 1 (s 1 ++ l.flatMap (fun b => [b, true]))) j []
  | [], s, h => by
    funext i
    simp only [List.length_nil, Function.iterate_zero, id_eq, List.flatMap_nil, List.append_nil,
      Function.update_apply]
    split_ifs <;> simp_all
  | b :: l, s, h => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : run (frBody j) s =
        Function.update (Function.update s 1 (s 1 ++ [b, true])) j l := by
      funext i
      simp only [frBody, run_seq, run_prim, Prim.apply, Function.update_apply, h]
      split_ifs <;> simp_all
    rw [hstep, run_frBody_iter j hj l _ (by simp)]
    funext i
    simp only [Function.update_apply]
    split_ifs <;> simp_all

theorem run_appendFR (j : Fin 8) (hj : j ≠ 1) (s : Store 8) :
    run (appendFR j (s j).length) s =
      Function.update (Function.update s 1
        (s 1 ++ false :: (s j).flatMap (fun b => [b, true]) ++ [true, true])) j [] := by
  have e : appendFR j (s j).length = .seq (.prim (.snoc 1 false))
      (.seq (Prog.iter 1 (frBody j) (s j).length) (.seq (.prim (.snoc 1 true))
        (.prim (.snoc 1 true)))) := rfl
  rw [e, run_seq, run_seq, run_iter, run_prim]
  have hj' : (Prim.snoc 1 false).apply s j = s j := by
    simp [Prim.apply, Function.update_apply, hj]
  rw [← hj', run_frBody_iter j hj _ _ rfl]
  funext i
  simp only [run_seq, run_prim, Prim.apply, Function.update_apply]
  split_ifs <;> simp_all

theorem coinFree_moveRev (n : ℕ) (src dst tmp : Fin 8) : (Prog.moveRev n src dst tmp).CoinFree :=
  coinFree_iter src (Prog.stepR src dst tmp) rfl n

theorem pmf_pure_inj {α : Type} {a b : α} (h : PMF.pure a = PMF.pure b) : a = b := by
  have : a ∈ (PMF.pure b).support := h ▸ (PMF.mem_support_pure_iff a a).mpr rfl
  simpa using this

theorem run_moveRev (n : ℕ) {src dst tmp : Fin 8} (h1 : src ≠ dst) (h2 : src ≠ tmp)
    (h3 : dst ≠ tmp) (s : Store 8) (hs : s tmp = []) :
    run (Prog.moveRev n src dst tmp) s =
      Function.update (Function.update s src ((s src).drop n)) dst
        (((s src).take n).reverse ++ s dst) := by
  have h := law_moveRev n h1 h2 h3 s hs
  rw [law_eq_run_of_coinFree _ (coinFree_moveRev n src dst tmp)] at h
  exact pmf_pure_inj h

/-- The reversed frame of a word: `rev (frame (true :: l))`. -/
def rfr (l : List Bool) : List Bool := false :: l.reverse.flatMap (fun b => [b, true]) ++ [true, true]

theorem run_caseA (t : Store 8) : run caseA t 1 = t 1 ++ [false, false, true] := by
  simp [caseA, run_seq, run_prim, Prim.apply]

theorem run_caseB_bad (nA nM : ℕ) (t : Store 8) {rest : List Bool}
    (h3 : t 3 = false :: true :: rest) : run (caseB nA nM) t 1 = [false] := by
  simp [caseB, badB, run_seq, run_ifBit, run_prim, Prim.apply, h3]

theorem run_caseB_good (nA nM : ℕ) (t : Store 8) {m : Bool} {μ a σ : List Bool}
    (hμ : μ.length = nM) (ha : a.length = nA)
    (h3 : t 3 = false :: false :: m :: (μ ++ (a ++ σ))) (h4 : t 4 = []) (h5 : t 5 = [])
    (h6 : t 6 = []) :
    run (caseB nA nM) t 1 = t 1 ++ (if m then rfr μ else [false]) ++ rfr a ++ [true] := by
  -- the store after dropping `false`, the flag and the message flag
  set t1 : Store 8 := Function.update (Function.update t 3 (μ ++ (a ++ σ))) 7 [m] with ht1
  have e1 : (Prim.pop 3 7).apply ((Prim.tail 3).apply ((Prim.tail 3).apply t)) = t1 := by
    funext i
    simp only [Prim.apply, Function.update_apply, ht1, h3]
    split_ifs <;> simp_all
  have hb : hd (((Prim.tail 3).apply t) 3) = false := by simp [Prim.apply, h3]
  set t2 := Function.update (Function.update t1 3 (a ++ σ)) 6 μ.reverse with ht2
  have e2 : run (Prog.moveRev nM 3 6 4) t1 = t2 := by
    rw [run_moveRev nM (by decide) (by decide) (by decide) t1 (by simp [ht1, h4])]
    simp [ht1, ht2, ← hμ, h6, List.drop_left', List.take_left']
  set t3 := Function.update (Function.update t2 3 σ) 5 a.reverse with ht3
  have e3 : run (Prog.moveRev nA 3 5 4) t2 = t3 := by
    rw [run_moveRev nA (by decide) (by decide) (by decide) t2 (by simp [ht2, ht1, h4])]
    simp [ht2, ht3, ht1, ← ha, h5, List.drop_left', List.take_left']
  set t4 := run (.ifBit 7 (appendFR 6 nM) (.prim (.snoc 1 false))) t3 with ht4
  have h7 : t3 7 = [m] := by simp [ht3, ht2, ht1]
  have h6' : t3 6 = μ.reverse := by simp [ht3, ht2]
  have e4 : t4 1 = t 1 ++ (if m then rfr μ else [false]) ∧ t4 5 = a.reverse := by
    rw [ht4, run_ifBit, h7]
    cases m
    · simp [run_prim, Prim.apply, ht3, ht2, ht1]
    · simp only [hd_cons, ite_true]
      rw [show nM = (t3 6).length by simp [h6', hμ], run_appendFR 6 (by decide)]
      simp [rfr, ht3, ht2, ht1]
  rw [caseB, run_seq, run_prim, run_ifBit, hb]
  simp only [Bool.false_eq_true, ite_false]
  rw [goodB, run_seq, run_prim,
    run_seq, run_prim, e1, run_seq, e2, run_seq, e3, run_seq, ← ht4, run_seq, run_prim,
    show nA = (t4 5).length by simp [e4.2, ha], run_appendFR 5 (by decide)]
  simp [Prim.apply, e4.1, e4.2, rfr]

end Sem

end AdvancedEncryption.PE.Generic
