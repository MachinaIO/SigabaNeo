import PE.Impl.DualUse.ReductionMachine
import PE.Impl.Game.HandlersBP
import SigabaNeo.Lib.Machines.Prog.Pass

/-!
# The post-processing machine of the reduction

`Post n E nA nM` reads `pairOut o u = o ++ false :: true :: dbl u`, the output `o` of the
adversary (`|o| ≤ n`) paired with the encoded final state `u` of the handlers (`|u| ≤ E`), and
writes `[false]` when the flag of the state is up, and `true :: encodeTuple [encOpt attr,
encOpt msg, o]` otherwise (`postG`).

Every primitive of the tape language sweeps whole tapes, so the long word `o` is never read bit by
bit by a program. The machine is one closed machine of four phases (`SigabaNeo.Tape.Pass`), each
linear in the input length, with no clock between them (so its number of states depends neither on
`n` nor on `E`):

1. `revInPhase`: tape `0` := the reversal of the input, `dbl (rev u) ++ true :: false :: rev o`;
2. `trPhase sepT`: tape `1` := the separator transducer `sepT` on tape `0`: it reads pairs, emits
   `[true, b]` for a pair `b b` (a bit of `rev u`) and `[false, false]` for the first unequal pair
   `true false` (the separator), then `[c, true]` for every bit `c` of `rev o`, so that tape `1` is
   `frame (rev u) ++ rev (frame o)` (`sepT_run`);
3. `trPhase cntT`: tape `7` := the counter transducer `cntT` on tape `0`: one bit per pair of
   `dbl (rev u)`, so tape `7` is `rev u`, of length `|u| ≤ E` (`cntT_run`);
4. the tape program `postProg nA nM`: a loop on the counter tape `7` (`|u|` rounds) moves the bits
   of `u` to tape `3`; tape `1` is then `rev (frame o)`, and the program appends the reversal of
   the head `true :: frame (encOpt attr) ++ frame (encOpt msg)` read off `u` (or writes `[false]`
   when the flag is up). Its states do not depend on `E`; under per-tape bounds
   (`compile_runsWordsT`) the loop costs `|u| ≤ E` rounds of `O(n + E)` steps;
5. `revOutPhase`: emit the reversal of tape `1`.

## Main results

* `Generic.run_post`: `(Post n E cd.nA cd.nM).run (pairOut o (cd.encState st)) =
  PMF.pure (postG (obs (o, st.2)))` for `|o| ≤ n` and a state `st` as the handlers keep it
  (`PostOK`: the instance word does not start with `false`, the experiment state is initial or
  selected, the encoded state has at most `E` bits).
* `Generic.time_post`: `(Post n E nA nM).time = postA E nA nM * n + postB E nA nM`, with
  `postA = 19 + 28 E + 4 postPc` and `postB = O(E ^ 2)`;
  `Generic.descLen_post`, `Generic.states_post`, `Generic.tapes_post`: the description length, the
  states and the tapes depend neither on `n` nor on `E`.
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

/-! ### The counter transducer -/

/-- The step of `cntT`: as `sepStep`, but it emits the bit `b` of a pair `b b`, and nothing at and
after the separator. -/
def cntStep : Option (Option Bool) → Bool → Option (Option Bool) × List Bool
  | some none, a => (some (some a), [])
  | some (some b), a => if a = b then (some none, [b]) else (none, [])
  | none, _ => (none, [])

theorem length_cntStep (q : Option (Option Bool)) (a : Bool) : (cntStep q a).2.length ≤ 2 := by
  rcases q with _ | _ | b
  · simp [cntStep]
  · simp [cntStep]
  · simp only [cntStep]; split_ifs <;> simp

/-- **The counter transducer**: on `dbl v ++ true :: false :: r` it writes `v`. -/
def cntT : MultiTapeTM.Transducer Bool (Option (Option Bool)) where
  q₀ := some none
  step := cntStep
  final _ := []
  length_step_le := length_cntStep
  length_final_le _ := by simp

@[simp] theorem cntT_step : cntT.step = cntStep := rfl
@[simp] theorem cntT_final (q : Option (Option Bool)) : cntT.final q = [] := rfl
@[simp] theorem cntT_q₀ : cntT.q₀ = some none := rfl

theorem cntT_run_none : ∀ r : List Bool, cntT.run none r = []
  | [] => rfl
  | c :: r => by
    rw [MultiTapeTM.Transducer.run_cons]
    simp [cntStep, cntT_run_none r]

theorem cntT_run (r : List Bool) : ∀ v : List Bool,
    cntT.run (some none) (dbl v ++ true :: false :: r) = v
  | [] => by
    simp [MultiTapeTM.Transducer.run_cons, cntStep, cntT_run_none]
  | b :: v => by
    simp [MultiTapeTM.Transducer.run_cons, cntStep, cntT_run r v]

/-- **The word of tape `7` after the counter transducer.** -/
theorem cntT_run_pairOut (o u : List Bool) :
    cntT.run cntT.q₀ (pairOut o u).reverse = u.reverse := by
  rw [reverse_pairOut, cntT_q₀]; exact cntT_run _ _

/-! ### The program

Tapes: `0` the reversed input, `1` the word being built, `2` a flag tape of the phases, `3` the
state word `u`, `4` a blank scratch tape, `5` the reversed attribute, `6` the reversed message,
`7` the counter of the rounds, then the message flag. -/

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

/-- The program after the rounds. -/
def postRest (nA nM : ℕ) : Prog 8 :=
  .seq (.prim (.tail 1)) (.ifBlank 3 caseA (.ifBit 3 caseA (caseB nA nM)))

/-- **The program of the post-processing**: one round per bit of the counter tape `7`, then the
rest. -/
def postProg (nA nM : ℕ) : Prog 8 := .seq (.loop 7 rnd) (postRest nA nM)

/-! ### Its semantics -/

section Sem

open Prog

theorem run_rnd_true (s : Store 8) {b : Bool} {R : List Bool} (h1 : s 1 = true :: b :: R)
    (h4 : s 4 = []) : run rnd s = Function.update (Function.update s 1 R) 3 (b :: s 3) := by
  funext j
  fin_cases j <;> simp [rnd, run_ifBit, run_prim, Prim.apply, h1, h4]

theorem run_rnd_false (s : Store 8) {R : List Bool} (h1 : s 1 = false :: R) : run rnd s = s := by
  funext j
  fin_cases j <;> simp [rnd, run_ifBit, run_prim, Prim.apply, h1]

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
    rw [run_rnds R v _ E (by simp) (by simp [h4]) (by simp at hE; omega)]
    funext j
    simp [Function.update_apply]
    split_ifs <;> simp_all

/-- **The rounds as a loop on the counter tape `7`**: each round drops a bit of the counter. -/
theorem iterate_rnd (R : List Bool) : ∀ (v : List Bool) (s : Store 8),
    s 1 = v.flatMap (fun b => [true, b]) ++ false :: R → s 4 = [] →
    (fun t => run rnd (tailAt 7 t))^[v.length] s =
      Function.update (Function.update (Function.update s 1 (false :: R)) 3 (v.reverse ++ s 3)) 7
        ((s 7).drop v.length)
  | [], s, h1, _ => by
    funext j
    simp only [List.flatMap_nil, List.nil_append] at h1
    simp only [List.length_nil, Function.iterate_zero, id_eq, List.reverse_nil, List.nil_append,
      List.drop_zero, Function.update_apply]
    split_ifs <;> simp_all
  | b :: v, s, h1, h4 => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have ht1 : tailAt 7 s 1 = true :: b :: (v.flatMap (fun b => [true, b]) ++ false :: R) := by
      simp [tailAt, h1]
    have ht4 : tailAt 7 s 4 = [] := by simp [tailAt, h4]
    rw [run_rnd_true _ ht1 ht4]
    rw [iterate_rnd R v _ (by simp) (by simp [tailAt, h4])]
    have hd : ((s 7).tail).drop v.length = (s 7).drop (v.length + 1) := by
      rcases s 7 with _ | ⟨a, l⟩ <;> simp
    funext j
    fin_cases j <;> simp [tailAt, hd]

theorem run_loop_rnd (R : List Bool) (v : List Bool) (s : Store 8)
    (h1 : s 1 = v.flatMap (fun b => [true, b]) ++ false :: R) (h4 : s 4 = [])
    (h7 : (s 7).length = v.length) :
    run (.loop 7 rnd) s =
      Function.update (Function.update (Function.update s 1 (false :: R)) 3 (v.reverse ++ s 3)) 7
        [] := by
  rw [run_loop, h7, iterate_rnd R v s h1 h4, ← h7, List.drop_length]

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
    simp [Prim.apply, hj]
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

/-- **The program, up to its branch**: the rounds (one per bit of the counter tape `7`, which holds
`|u|` bits) move the bits of `u` to tape `3`. -/
theorem run_postProg (nA nM : ℕ) (s : Store 8) (u R : List Bool)
    (h1 : s 1 = u.reverse.flatMap (fun b => [true, b]) ++ false :: R) (h3 : s 3 = [])
    (h4 : s 4 = []) (h7 : (s 7).length = u.length) :
    run (postProg nA nM) s 1 = run (.ifBlank 3 caseA (.ifBit 3 caseA (caseB nA nM)))
      (Function.update (Function.update (Function.update s 1 R) 3 u) 7 []) 1 := by
  rw [postProg, run_seq, run_loop_rnd R u.reverse s h1 h4 (by simpa using h7), postRest, run_seq,
    run_prim]
  congr 2
  funext i
  simp only [Prim.apply, Function.update_apply, List.reverse_reverse, h3, List.append_nil]
  split_ifs <;> simp_all

end Sem

/-! ### Structural properties -/

section Struct

open Prog

theorem loopFree_frBody (j : Fin 8) : (frBody j).LoopFree := by simp [frBody, LoopFree]

theorem loopFree_appendFR (j : Fin 8) (c : ℕ) : (appendFR j c).LoopFree := by
  have h := loopFree_iter 1 (frBody j) (loopFree_frBody j) c
  simp only [frBody] at h
  simp [appendFR, LoopFree, h]

theorem loopFree_rnd : rnd.LoopFree := by simp [rnd, LoopFree]

theorem loopFree_postRest (nA nM : ℕ) : (postRest nA nM).LoopFree := by
  simp [postRest, caseA, caseB, badB, goodB, LoopFree, loopFree_moveRev, loopFree_appendFR]

theorem wf_of_loopFree : ∀ p : Prog 8, p.LoopFree → p.WF
  | .prim _, _ | .coin _, _ => trivial
  | .seq p q, h => ⟨wf_of_loopFree p h.1, wf_of_loopFree q h.2⟩
  | .ifBlank _ p q, h => ⟨wf_of_loopFree p h.1, wf_of_loopFree q h.2⟩
  | .ifBit _ p q, h => ⟨wf_of_loopFree p h.1, wf_of_loopFree q h.2⟩
  | .loop _ _, h => h.elim

theorem coinFree_appendFR (j : Fin 8) (c : ℕ) : (appendFR j c).CoinFree := by
  have h := coinFree_iter 1 (frBody j) rfl c
  simp only [CoinFree, frBody] at h ⊢
  simp [appendFR, coinFreeB, h]

theorem coinFree_postProg (nA nM : ℕ) : (postProg nA nM).CoinFree := by
  have h1 : rnd.CoinFree := rfl
  have h2 := coinFree_moveRev nM 3 6 4
  have h3 := coinFree_moveRev nA 3 5 4
  have h4 := coinFree_appendFR 6 nM
  have h5 := coinFree_appendFR 5 nA
  simp only [CoinFree] at *
  simp [postProg, postRest, caseA, caseB, badB, goodB, coinFreeB, h1, h2, h3, h4, h5]

theorem wf_postProg (nA nM : ℕ) : (postProg nA nM).WF :=
  ⟨⟨wf_of_loopFree rnd loopFree_rnd, by simp [rnd, Preserves, Prim.writes]⟩,
    wf_of_loopFree _ (loopFree_postRest nA nM)⟩

theorem preserves_appendFR (j : Fin 8) (hj : j ≠ 2) (c : ℕ) : (appendFR j c).Preserves 2 := by
  have h := preserves_iter 1 (frBody j) (i := 2) (by decide)
    (by simp [frBody, Preserves, Prim.writes, Ne.symm hj]) c
  simp only [frBody] at h
  simp [appendFR, Preserves, Prim.writes, h]

theorem preserves_moveRev2 (n : ℕ) (dst : Fin 8) (hd : dst ≠ 2) :
    (Prog.moveRev n 3 dst 4).Preserves 2 :=
  preserves_iter _ _ (by decide) (by simp [Prog.stepR, Preserves, Prim.writes, Ne.symm hd]) n

theorem preserves_postProg (nA nM : ℕ) : (postProg nA nM).Preserves 2 := by
  have h1 : rnd.Preserves 2 := by simp [rnd, Preserves, Prim.writes]
  simp [postProg, postRest, caseA, caseB, badB, goodB, Preserves, Prim.writes, h1,
    preserves_moveRev2 _ 6 (by decide), preserves_moveRev2 _ 5 (by decide),
    preserves_appendFR 6 (by decide), preserves_appendFR 5 (by decide)]

end Struct

/-! ### The machine -/

/-- Tape `0` of the first phase. -/
def eIn : Fin 1 ↪ Fin 8 := ⟨fun _ => 0, fun a b _ => Subsingleton.elim a b⟩
/-- Output, input and flag tapes of the transducer. -/
def eTr : Fin 3 ↪ Fin 8 := ⟨![1, 0, 2], by decide⟩
/-- Input and flag tapes of the last phase. -/
def eOut : Fin 2 ↪ Fin 8 := ⟨![1, 2], by decide⟩

@[simp] theorem eIn_apply (i : Fin 1) : eIn i = 0 := rfl
@[simp] theorem eTr_zero : eTr 0 = 1 := rfl
@[simp] theorem eTr_one : eTr 1 = 0 := rfl
@[simp] theorem eTr_two : eTr 2 = 2 := rfl
@[simp] theorem eOut_zero : eOut 0 = 1 := rfl
@[simp] theorem eOut_one : eOut 1 = 2 := rfl

/-- Output, input and flag tapes of the counter transducer. -/
def eCnt : Fin 3 ↪ Fin 8 := ⟨![7, 0, 2], by decide⟩

@[simp] theorem eCnt_zero : eCnt 0 = 7 := rfl
@[simp] theorem eCnt_one : eCnt 1 = 0 := rfl
@[simp] theorem eCnt_two : eCnt 2 = 2 := rfl

/-- The five phases. -/
noncomputable def postPTM (nA nM : ℕ) :=
  (revInPhase eIn).seq ((trPhase sepT eTr).seq ((trPhase cntT eCnt).seq
    ((Prog.compile (postProg nA nM)).seq (revOutPhase eOut))))

/-- The number of primitives of the program after the rounds. -/
def postPc (nA nM : ℕ) : ℕ := Prog.pcount (postRest nA nM)

theorem pcount_rnd : Prog.pcount rnd = 6 := rfl

/-- The bound on every tape but the counter after the rounds: `L + E` with `L = 2 N + 2`,
`N = n + 2 + 2 E`. -/
def postM (n E : ℕ) : ℕ := 2 * (n + 2 + 2 * E) + 2 + E

/-- The time bound of the program under per-tape bounds: `E` rounds, then the rest. -/
def postProgTime (n E nA nM : ℕ) : ℕ :=
  E * (2 * postM n E + 3 + 6 * (2 * (postM n E + 6) + 5) + 1) + 2 +
    postPc nA nM * (2 * (postM n E + postPc nA nM) + 5)

/-- The clock, for outputs of `A` of at most `n` bits and encoded states of at most `E` bits. -/
def postClock (n E nA nM : ℕ) : ℕ :=
  3 * (n + 2 + 2 * E) + 4 + (6 * (n + 2 + 2 * E) + 16) + (6 * (n + 2 + 2 * E) + 16) +
    postProgTime n E nA nM + (2 * (postM n E + postPc nA nM) + 6)

/-- **The post-processing machine.** -/
noncomputable def Post (n E nA nM : ℕ) : Machine :=
  Machine.ofPTM (postPTM nA nM) (postClock n E nA nM)

/-- The store before the program. -/
def postS (x : List Bool) : Store 8 :=
  Function.update (Function.update (Function.update (fun _ => []) 0 x.reverse) 1
    (sepT.run sepT.q₀ x.reverse)) 7 (cntT.run cntT.q₀ x.reverse)

/-! ### The time of the program under per-tape bounds -/

section TimeT

open Prog

theorem compile_runsWordsTU (p : Prog 8) (hp : p.WF) (hc : p.CoinFree) (x : List Bool)
    (ℓ : Fin 8 → ℕ) (s : Store 8) (out₀ : List Bool) (hs : Fits s ℓ) :
    (compile p).RunsWords x s out₀ (timeBoundT p ℓ) (pure ()) (fun _ => run p s) (fun _ => []) := by
  have h := compile_runsWordsT p hp x ℓ s out₀ hs
  rw [denote_eq_run_of_coinFree p hc s, ProbOracleComp.sample_pure] at h
  exact RunsWords.toUnit h

theorem lenBound_rnd (c : ℕ) : lenBound rnd c ≤ c + 1 := by
  simp [rnd, lenBound, Prim.grow]

theorem loopStepT_rnd_le {ℓ : Fin 8 → ℕ} {c : ℕ} (h : ∀ t, ℓ t ≤ c) (t : Fin 8) :
    loopStepT 7 rnd ℓ t ≤ c + 1 := by
  have h1 : loopStepT 7 rnd ℓ ≤ lenBoundT rnd (fun _ => c) :=
    lenBoundT_mono rnd ((tailB_le 7 ℓ).trans fun t => h t)
  exact (h1 t).trans ((lenBoundT_const_le rnd c t).trans (lenBound_rnd c))

theorem iterate_loopStepT_rnd_le {ℓ : Fin 8 → ℕ} {c : ℕ} (h : ∀ t, ℓ t ≤ c) :
    ∀ j t, ((loopStepT 7 rnd)^[j] ℓ) t ≤ c + j
  | 0, t => h t
  | j + 1, t => by
    rw [Function.iterate_succ_apply']
    exact loopStepT_rnd_le (iterate_loopStepT_rnd_le h j) t

/-- **The time of the program** from per-tape bounds `ℓ`, all at most `L`, with at most `E` bits on
the counter tape. -/
theorem timeBoundT_postProg (nA nM L E : ℕ) (ℓ : Fin 8 → ℕ) (hℓ : ∀ t, ℓ t ≤ L) (h7 : ℓ 7 ≤ E) :
    timeBoundT (postProg nA nM) ℓ ≤
      E * (2 * (L + E) + 3 + 6 * (2 * (L + E + 6) + 5) + 1) + 2 +
        postPc nA nM * (2 * (L + E + postPc nA nM) + 5) ∧
    lenBoundT (postProg nA nM) ℓ 1 ≤ L + E + postPc nA nM := by
  have hit := iterate_loopStepT_rnd_le hℓ
  have hloop : timeBoundT (loop 7 rnd) ℓ ≤
      ℓ 7 * (2 * (L + E) + 3 + 6 * (2 * (L + E + 6) + 5) + 1) + 2 := by
    refine timeBoundT_loop_le 7 rnd ℓ fun j hj => ?_
    have hj' : ∀ t, ((loopStepT 7 rnd)^[j] ℓ) t ≤ L + E := fun t => (hit j t).trans (by omega)
    have h1 := roundTimeT_le rnd 7 ((loopStepT 7 rnd)^[j] ℓ)
    have h2 : supB ((loopStepT 7 rnd)^[j] ℓ) ≤ L + E := Finset.sup_le fun t _ => hj' t
    have h3 := timeBoundT_le_pcount rnd loopFree_rnd _ hj'
    rw [pcount_rnd] at h3
    omega
  have hlenL : ∀ t, lenBoundT (loop 7 rnd) ℓ t ≤ L + E := by
    intro t
    rw [lenBoundT_loop]
    exact Finset.sup_le fun j hj => (hit j t).trans (by simp at hj; omega)
  have hrest := timeBoundT_le_pcount (postRest nA nM) (loopFree_postRest nA nM) _ hlenL
  refine ⟨?_, ?_⟩
  · have e : timeBoundT (postProg nA nM) ℓ =
        timeBoundT (loop 7 rnd) ℓ + timeBoundT (postRest nA nM) (lenBoundT (loop 7 rnd) ℓ) := rfl
    have hm : ℓ 7 * (2 * (L + E) + 3 + 6 * (2 * (L + E + 6) + 5) + 1) ≤
        E * (2 * (L + E) + 3 + 6 * (2 * (L + E + 6) + 5) + 1) := Nat.mul_le_mul_right _ h7
    rw [e]; unfold postPc; omega
  · have e : lenBoundT (postProg nA nM) ℓ 1 =
        lenBoundT (postRest nA nM) (lenBoundT (loop 7 rnd) ℓ) 1 := rfl
    rw [e]
    have h1 : lenBoundT (postRest nA nM) (lenBoundT (loop 7 rnd) ℓ) 1 ≤
        lenBoundT (postRest nA nM) (fun _ => L + E) 1 :=
      lenBoundT_mono (postRest nA nM) (show lenBoundT (loop 7 rnd) ℓ ≤ fun _ => L + E
        from hlenL) 1
    have h2 : lenBoundT (postRest nA nM) (fun _ => L + E) 1 ≤ lenBound (postRest nA nM) (L + E) :=
      lenBoundT_const_le (postRest nA nM) (L + E) 1
    have h3 := lenBound_le_pcount (postRest nA nM) (loopFree_postRest nA nM) (L + E)
    unfold postPc; omega

end TimeT

/-- **The output of the machine on a word** whose counter (`cntT` on its reversal) has at most `E`
bits: the reversal of tape `1` after the program. -/
theorem run_Post_word (n E nA nM : ℕ) (x : List Bool) (hx : x.length ≤ n + 2 + 2 * E)
    (hc : (cntT.run cntT.q₀ x.reverse).length ≤ E) :
    (Post n E nA nM).run x =
      PMF.pure (Prog.run (postProg nA nM) (postS x) 1).reverse := by
  set p := postProg nA nM
  set L := 2 * (n + 2 + 2 * E) + 2
  set s₁ := Function.update (fun _ => ([] : List Bool)) (eIn 0) x.reverse with hs₁
  set s₂ := Function.update s₁ (eTr 0) (sepT.run sepT.q₀ (s₁ (eTr 1))) with hs₂
  have h1 := revInPhase_runs eIn x (fun _ => []) rfl []
  have h2 := trPhase_runs sepT eTr x s₁ (by simp [hs₁]) (by simp [hs₁]) ([] ++ [])
  have h2' := trPhase_runs cntT eCnt x s₂ (by simp [hs₂, hs₁]) (by simp [hs₂, hs₁])
    ([] ++ [] ++ [])
  have hs₃ : Function.update s₂ (eCnt 0) (cntT.run cntT.q₀ (s₂ (eCnt 1))) = postS x := by
    simp [hs₂, hs₁, postS]
  rw [hs₃] at h2'
  set ℓ : Fin 8 → ℕ := Function.update (fun _ => L) 7 E with hℓ
  have hfits : Fits (postS x) ℓ := by
    intro i
    have h0 := Transducer.length_run_le sepT sepT.q₀ x.reverse
    simp only [List.length_reverse, sepT_q₀] at h0
    have hc' := hc
    simp only [cntT_q₀] at hc'
    fin_cases i <;> simp [postS, hℓ] <;> omega
  have hℓL : ∀ t, ℓ t ≤ L := by
    intro t; simp only [hℓ, Function.update_apply]; split_ifs <;> omega
  have hT := timeBoundT_postProg nA nM L E ℓ hℓL (by simp [hℓ])
  have h3 := compile_runsWordsTU p (wf_postProg nA nM) (coinFree_postProg nA nM) x ℓ (postS x)
    ([] ++ [] ++ [] ++ []) hfits
  have h4 := revOutPhase_runs eOut x (Prog.run p (postS x))
    (by rw [eOut_one,
      Prog.run_eq_of_preserves p (coinFree_postProg nA nM) (preserves_postProg nA nM)]; rfl)
    ([] ++ [] ++ [] ++ [] ++ [])
  have h := RunsWords.seqU h1 (RunsWords.seqU h2 (RunsWords.seqU h2' (RunsWords.seqU h3 h4)))
  have hlen : (Prog.run p (postS x) 1).length ≤ L + E + postPc nA nM := by
    have hs := Prog.lenBoundT_spec p ℓ (postS x) hfits (Prog.run p (postS x))
      (by rw [Prog.law_eq_run_of_coinFree p (coinFree_postProg nA nM)]; simp)
    exact (hs 1).trans hT.2
  have hin : (s₂ (eCnt 1)).length = x.length := by simp [hs₂, hs₁]
  have hin' : (s₁ (eTr 1)).length = x.length := by simp [hs₁]
  have hclock : 3 * x.length + 4 + (6 * (s₁ (eTr 1)).length + 16 + (6 * (s₂ (eCnt 1)).length + 16 +
      (Prog.timeBoundT p ℓ + (2 * (Prog.run p (postS x) (eOut 0)).length + 6)))) ≤
      postClock n E nA nM := by
    rw [hin, hin', eOut_zero]
    have hT1 := hT.1
    simp only [postClock, postProgTime, postM]
    simp only [L] at hT1 hlen
    generalize postPc nA nM = c at *
    generalize Prog.timeBoundT p ℓ = tb at *
    generalize (Prog.run p (postS x) 1).length = lo at *
    generalize E * (2 * (2 * (n + 2 + 2 * E) + 2 + E) + 3 +
      6 * (2 * (2 * (n + 2 + 2 * E) + 2 + E + 6) + 5) + 1) = T₁ at *
    generalize c * (2 * (2 * (n + 2 + 2 * E) + 2 + E + c) + 5) = T₂ at *
    omega
  rw [Post, Machine.run_ofPTM]
  exact eval_runClosed_of_runsWordsU (h.mono hclock)

/-! ### Frames -/

/-- The frame of a word (`Turing.MultiTapeTM.frame`). -/
def fr (l : List Bool) : List Bool := l.flatMap (fun b => [true, b]) ++ [false]

theorem frame_eq_fr (l : List Bool) : MultiTapeTM.frame l = fr l := rfl

theorem encodeTuple_three (a b c : List Bool) : encodeTuple [a, b, c] = fr a ++ fr b ++ fr c := by
  simp [encodeTuple, frame_eq_fr]

theorem reverse_flatMap_ct : ∀ l : List Bool,
    (l.flatMap (fun c => [c, true])).reverse = l.reverse.flatMap (fun c => [true, c])
  | [] => rfl
  | c :: l => by simp [reverse_flatMap_ct l]

theorem reverse_rfr (l : List Bool) : (rfr l).reverse = fr (true :: l) := by
  simp [rfr, fr, reverse_flatMap_ct]

theorem reverse_body (o : List Bool) :
    (false :: o.reverse.flatMap (fun c => [c, true])).reverse = fr o := by
  simp [fr, reverse_flatMap_ct]

theorem length_dbl : ∀ u : List Bool, (dbl u).length = 2 * u.length
  | [] => rfl
  | b :: u => by simp [length_dbl u]; ring

/-! ### The post-processing of a run -/

variable {U : Universe} {Sig : Type}

/-- **The word of the post-processing**: `[false]` when the flag is up, otherwise `true` and the
view `encodeTuple [encOpt attr, encOpt msg, o]`. -/
def postG (ob : List Bool × Option U.Attr × Option U.Msg × Bool) : List Bool :=
  if ob.2.2.2 then [false] else
    true :: encodeTuple [encOpt U.encAttr ob.2.1, encOpt U.encMsg ob.2.2.1, ob.1]

/-- The states the post-processing reads: the instance word does not start with `false`, the
experiment state is the initial or a selected one, and the encoded state has at most `E` bits.
The invariant `InvS` of the handlers gives the first two (`postOK_of_invS`). -/
def PostOK (cd : Codes U Sig) (E : ℕ) (st : List Bool × GState U Sig) : Prop :=
  st.1.head? ≠ some false ∧ (st.2 = {} ∨ ∃ x σ, st.2.attr = some x ∧ st.2.sec = some σ) ∧
    (cd.encState st).length ≤ E

theorem postOK_of_invS (cd : Codes U Sig) {IW : List Bool → Prop} {W : ℕ} {Ok : Sig → Prop}
    {E : ℕ} {st : List Bool × GState U Sig} (h : InvS IW W Ok st)
    (hE : (cd.encState st).length ≤ E) : PostOK cd E st := by
  refine ⟨h.2.2.1, ?_, hE⟩
  rcases h.2.2.2 with h | ⟨x, σ, hx, hσ, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨x, σ, hx, hσ⟩

/-- **The post-processing machine computes `postG`** on `A`'s output (at most `n` bits) paired with
the encoded state. -/
theorem run_post (cd : Codes U Sig) (n E : ℕ) (o : List Bool) (st : List Bool × GState U Sig)
    (ho : o.length ≤ n) (hst : PostOK cd E st) :
    (Post n E cd.nA cd.nM).run (pairOut o (cd.encState st)) = PMF.pure (postG (obs (o, st.2))) := by
  obtain ⟨hw, hsh, hE⟩ := hst
  set u := cd.encState st with hu
  have hx : (pairOut o u).length ≤ n + 2 + 2 * E := by
    simp only [pairOut, List.length_append, List.length_cons, length_dbl]; omega
  have hc : (cntT.run cntT.q₀ (pairOut o u).reverse).length ≤ E := by
    rw [cntT_run_pairOut, List.length_reverse]; exact hE
  rw [run_Post_word _ _ _ _ _ hx hc]
  congr 1
  set R := false :: o.reverse.flatMap (fun c => [c, true])
  have h1 : postS (pairOut o u) 1 = u.reverse.flatMap (fun b => [true, b]) ++ false :: R := by
    simp only [postS, Function.update_self, Function.update_of_ne (show (1 : Fin 8) ≠ 7 by decide)]
    exact sepT_run_pairOut o u
  have h7 : (postS (pairOut o u) 7).length = u.length := by
    simp only [postS, Function.update_self]; rw [cntT_run_pairOut, List.length_reverse]
  rw [run_postProg cd.nA cd.nM _ u R h1 (by simp [postS]) (by simp [postS]) h7]
  set t := Function.update (Function.update (Function.update (postS (pairOut o u)) 1 R) 3 u) 7 []
  have t1 : t 1 = R := by simp [t]
  have t3 : t 3 = u := by simp [t]
  have t4 : t 4 = [] := by simp [t, postS]
  have t5 : t 5 = [] := by simp [t, postS]
  have t6 : t 6 = [] := by simp [t, postS]
  obtain ⟨w, g⟩ := st
  rcases hsh with hg | ⟨x, σ, hx, hσ⟩
  · -- before the selection
    simp only at hg
    subst hg
    have hu' : u = w := rfl
    have hA : Prog.run (.ifBlank 3 caseA (.ifBit 3 caseA (caseB cd.nA cd.nM))) t 1 =
        R ++ [false, false, true] := by
      by_cases hw0 : w = []
      · simp only [Prog.run_ifBlank, t3, hu', hw0, ite_true]; rw [run_caseA, t1]
      · obtain ⟨b, w', rfl⟩ := List.exists_cons_of_ne_nil hw0
        cases b
        · exact absurd rfl hw
        · simp only [Prog.run_ifBlank, Prog.run_ifBit, t3, hu', reduceCtorEq, ite_false, hd_cons,
            ite_true]
          rw [run_caseA, t1]
    rw [hA]
    simp [postG, obs, encOpt, encodeTuple_three, R, fr, reverse_flatMap_ct]
  · -- after the selection
    simp only at hx hσ
    have hu' : u = cd.selWord g.bad g.msg x σ := by
      simp [hu, Codes.encState, hx, hσ]
    have hB : Prog.run (.ifBlank 3 caseA (.ifBit 3 caseA (caseB cd.nA cd.nM))) t 1 =
        Prog.run (caseB cd.nA cd.nM) t 1 := by
      rw [Prog.run_ifBlank, t3, hu']
      simp [Codes.selWord, Prog.run_ifBit, t3, hu']
    rw [hB]
    cases hb : g.bad
    · -- the flag is down
      rcases hm : g.msg with _ | μ
      · have h3 : t 3 = false :: false :: false ::
            (List.replicate cd.nM false ++ (U.encAttr x ++ cd.sig.enc σ)) := by
          rw [t3, hu']; simp [Codes.selWord, Codes.msgWord, hb, hm]
        rw [run_caseB_good cd.nA cd.nM t (by simp) (cd.len_attr x) h3 t4 t5 t6, t1]
        simp [postG, obs, encOpt, encodeTuple_three, R, reverse_rfr, hb, hm, hx, fr,
          reverse_flatMap_ct]
      · have h3 : t 3 = false :: false :: true :: (U.encMsg μ ++ (U.encAttr x ++ cd.sig.enc σ)) := by
          rw [t3, hu']; simp [Codes.selWord, Codes.msgWord, hb, hm]
        rw [run_caseB_good cd.nA cd.nM t (cd.len_msg μ) (cd.len_attr x) h3 t4 t5 t6, t1]
        simp [postG, obs, encOpt, encodeTuple_three, R, reverse_rfr, hb, hm, hx, fr,
          reverse_flatMap_ct]
    · -- the flag is up
      have h3 : t 3 = false :: true :: (cd.msgWord g.msg ++ (U.encAttr x ++ cd.sig.enc σ)) := by
        rw [t3, hu']; simp [Codes.selWord, hb]
      rw [run_caseB_bad cd.nA cd.nM t h3]
      simp [postG, obs, hb]

/-! ### Cost -/

/-- The slope of the clock in `n`. -/
def postA (E nA nM : ℕ) : ℕ := 19 + 28 * E + 4 * postPc nA nM

/-- The clock for `n = 0`. -/
def postB (E nA nM : ℕ) : ℕ := postClock 0 E nA nM

/-- **The time of the post-processing** is affine in the bound `n` on `A`'s output. -/
theorem time_post (n E nA nM : ℕ) : (Post n E nA nM).time = postA E nA nM * n + postB E nA nM := by
  show postClock n E nA nM = _
  simp only [postClock, postProgTime, postM, postA, postB]
  ring

theorem time_post_le (n E nA nM c : ℕ) (hn : n ≤ c) (hc : 1 ≤ c) :
    (Post n E nA nM).time ≤ (postA E nA nM + postB E nA nM) * c := by
  rw [time_post]
  have h1 : postA E nA nM * n ≤ postA E nA nM * c := Nat.mul_le_mul_left _ hn
  have h2 : postB E nA nM ≤ postB E nA nM * c := Nat.le_mul_of_pos_right _ hc
  nlinarith

theorem states_ofPTM_clock {k : ℕ} {S : Type} [Finite S] (m : MultiTapePTM k Bool S) (t t' : ℕ) :
    (Machine.ofPTM m t).states = (Machine.ofPTM m t').states := rfl

theorem tapes_ofPTM_clock {k : ℕ} {S : Type} [Finite S] (m : MultiTapePTM k Bool S) (t t' : ℕ) :
    (Machine.ofPTM m t).tapes = (Machine.ofPTM m t').tapes := rfl

/-- **The description length depends neither on `n` nor on `E`.** -/
theorem descLen_post (n n' E E' nA nM : ℕ) :
    (Post n E nA nM).descLen = (Post n' E' nA nM).descLen :=
  descLen_ofPTM _ _ _

/-- **The states depend neither on `n` nor on `E`.** -/
theorem states_post (n n' E E' nA nM : ℕ) : (Post n E nA nM).states = (Post n' E' nA nM).states :=
  states_ofPTM_clock _ _ _

/-- **The tapes depend neither on `n` nor on `E`.** -/
theorem tapes_post (n n' E E' nA nM : ℕ) : (Post n E nA nM).tapes = (Post n' E' nA nM).tapes :=
  tapes_ofPTM_clock _ _ _

end AdvancedEncryption.PE.Generic

/-! ### The post-processing of the reduction -/

namespace AdvancedEncryption.DualUse

open SigabaNeo SigabaNeo.Inline AdvancedEncryption.PE AdvancedEncryption.PE.Generic

theorem postW_eq_postG (ob : Ob) : postW ob = postG ob := rfl

/-- **The hypothesis `hPost` of `acceptProb_reduction`** for the handlers of the branching-program
universe (state encoding `(bpCodes sig).encState`, invariant `InvS IW W Ok`, encoded states of at
most `E` bits), with `Post A.time E 128 1`. -/
theorem hPost_post {Sig : Type} {nS : ℕ} (sig : Encode.FixedEnc Sig nS) (IW : List Bool → Prop)
    (W : ℕ) (Ok : Sig → Prop) (n E : ℕ)
    (hE : ∀ st, InvS IW W Ok st → ((bpCodes sig).encState st).length ≤ E) :
    ∀ (o : List Bool) (st : List Bool × GState AdvancedEncryption.PE.BranchingProgram.bpUniverse Sig), o.length ≤ n →
      InvS IW W Ok st →
      (Post n E 128 1).run (pairOut o ((bpCodes sig).encState st)) =
        PMF.pure (postW (Generic.obs (o, st.2))) :=
  fun o st ho hst => run_post (bpCodes sig) n E o st ho (postOK_of_invS _ hst (hE st hst))

/-- **The time of the post-processing against the cost of `A`.** -/
theorem time_post_le_cost {ops : ℕ} (A : Machine ops) (E nA nM : ℕ) :
    (Post A.time E nA nM).time ≤ (postA E nA nM + postB E nA nM) * A.cost :=
  time_post_le _ _ _ _ _ (by unfold Machine.cost; omega) A.one_le_cost

variable {m : ℕ}

/-- **Cost of the reduction with this post-processing**: the factor does not depend on `A`
(`Post 0 …` has the description length of `Post A.time …`). -/
theorem cost_reduction_post (P : Machine) (A : Machine 3) (H : Fin 3 → Routine (m + 3))
    (E Q L : ℕ) (D : Machine) :
    (reduction P (Post A.time E 10 1) A H E Q L D).cost ≤
      redFactor P (Post 0 E 10 1) H E Q L (postA E 10 1 + postB E 10 1) * A.cost * D.cost := by
  have h := cost_reduction_le P (Post A.time E 10 1) A H E Q L _ D (time_post_le_cost A E 10 1)
  have e : redFactor P (Post A.time E 10 1) H E Q L (postA E 10 1 + postB E 10 1) =
      redFactor P (Post 0 E 10 1) H E Q L (postA E 10 1 + postB E 10 1) := by
    unfold redFactor; rw [descLen_post A.time 0 E E]
  rw [← e]; exact h

end AdvancedEncryption.DualUse
