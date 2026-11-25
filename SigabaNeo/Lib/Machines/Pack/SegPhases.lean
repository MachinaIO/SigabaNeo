import SigabaNeo.Lib.Machines.Pack.Seg
import SigabaNeo.Lib.Machines.Pack.OutWord
import SigabaNeo.Lib.Machines.Pack.ZProg

/-!
# The segment phases: native machines reading and replacing a segment in linear time

* `getPh j t st fl`: `t := S j` on the packed store of tape `st` — the transducer `getT j` run from
  tape `st` onto the blank tape `t` (`SigabaNeo.Tape.trPhase`), `6 |pkW S| + 16` steps.
* `putPh j t st fl B`: `S j := t`, `t := []` — the transducers `preT j` (on `st`), `frT` (on `t`),
  `sufT j` (on `st`) emit their outputs one after the other, redirected to the blank tape `B`
  (`RunsWords.outputToWord_of_le`), then `st := B`, `B := []`, `t := []` (column primitives).
  Linear in `|pkW S| + |S' j|`.

Both are `Phase`s (`SigabaNeo.Lib.Machines.Pack.ZProg`) whose store functions are the segment
operations on any word (`getF`, `putF`); on packed stores they read and replace a segment
(`getF_pkW`, `putF_pkW`). When the tapes are not distinct the phase is a dummy with an unsatisfiable
precondition (the store function is the same).
-/

namespace SigabaNeo.Tape.Pack

open Cslib Turing MultiTapeMachine MultiTapePTM Function

variable {k : ℕ}

/-! ### Emitting a transducer's output on a tape word -/

/-- Emit the output of `τ` on the word of tape `e 0` (`e 1` a blank flag tape). -/
noncomputable def emitTr {Q : Type} [Finite Q] (τ : MultiTapeTM.Transducer Bool Q)
    (e : Fin 2 ↪ Fin k) :=
  ((ofDeterministic (τ.toTM.seq (MultiTapeTM.rewindInput Bool)) :
    MultiTapePTM 0 Bool _ Empty).inputFromWord true).extendTapes e

theorem emitTr_runs {Q : Type} [Finite Q] (τ : MultiTapeTM.Transducer Bool Q)
    (e : Fin 2 ↪ Fin k) (x : List Bool) (ws₀ : Store k) (h1 : ws₀ (e 1) = []) (out₀ : List Bool) :
    (emitTr τ e).RunsWords x ws₀ out₀ (4 * (ws₀ (e 0)).length + 12) (pure ())
      (fun _ => ws₀) (fun _ => τ.run τ.q₀ (ws₀ (e 0))) := by
  set w := ws₀ (e 0)
  have hdet := ComputesTidily.of_deterministic (Operation := Empty) (τ.computesTidily w)
  have hw := (hdet out₀).inputFromWord (x := x) true
  have hb : (fun j => ws₀ (e j)) = Fin.append (fun _ : Fin 0 => ([] : List Bool)) ![w, []] := by
    funext j; fin_cases j
    · rfl
    · show ws₀ (e 1) = _; rw [h1]; rfl
  rw [← hb] at hw
  have h := RunsWords.toUnit (RunsWords.extendTapes (ws₀ := ws₀) e hw)
  change (emitTr τ e).RunsWords x ws₀ out₀ _ (pure ()) (fun _ => embedF e ws₀ (fun j => ws₀ (e j)))
    (fun _ => τ.run τ.q₀ w) at h
  rw [embedF_self] at h
  exact h

/-- From a unit phase with a fixed final store to a store phase. -/
theorem RunsWords.toSample {S : Type} {M : MultiTapePTM k Bool S Empty} {x : List Bool}
    {s s' : Store k} {out₀ : List Bool} {t : ℕ}
    (h : M.RunsWords x s out₀ t (pure ()) (fun _ => s') (fun _ => [])) :
    M.RunsWords x s out₀ t (ProbOracleComp.sample (pure s')) id (fun _ => []) := by
  have h' := RunsWords.of_map (fun _ : Unit => s') id (fun _ => []) h
  simpa using h'

/-! ### Reading a segment -/

/-- The store function of reading the segment `j` of tape `st` onto tape `t`. -/
def getF (j : ℕ) (t st : Fin k) (P : Store k) : Store k :=
  update P t ((getT j).run (getT j).q₀ (P st))

theorem getF_pkW {K : ℕ} (j : Fin K) (t st : Fin k) (P : Store k) (S : Store K)
    (hS : P st = pkW S) : getF j t st P = update P t (S j) := by
  rw [getF, hS, run_getT_pkW]

/-- The three tapes of a read: the target, the store, the flag. -/
def emb3 (a b c : Fin k) (h : a ≠ b ∧ a ≠ c ∧ b ≠ c) : Fin 3 ↪ Fin k :=
  ⟨![a, b, c], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩

/-- **The read phase** `t := S j` (`fl` a blank flag tape). -/
noncomputable def getPh (j : ℕ) (t st fl : Fin k) : Phase k :=
  if h : t ≠ st ∧ t ≠ fl ∧ st ≠ fl then
    { State := _
      fintype := Fintype.ofFinite _
      machine := trPhase (getT j) (emb3 t st fl h)
      f := getF j t st
      pre := fun P => P t = [] ∧ P fl = []
      time := fun P => 6 * (P st).length + 16
      runs := fun x P out₀ hP => by
        apply RunsWords.toSample
        exact trPhase_runs (getT j) (emb3 t st fl h) x P hP.1 hP.2 out₀ }
  else
    { State := Unit
      fintype := inferInstance
      machine := ofDeterministic (haltTM k)
      f := getF j t st
      pre := fun _ => False
      time := fun _ => 0
      runs := fun _ _ _ hP => hP.elim }

theorem getPh_f (j : ℕ) (t st fl : Fin k) : (getPh j t st fl).f = getF j t st := by
  unfold getPh; split_ifs <;> rfl

theorem getPh_pre {j : ℕ} {t st fl : Fin k} (h : t ≠ st ∧ t ≠ fl ∧ st ≠ fl) (P : Store k)
    (h1 : P t = []) (h2 : P fl = []) : (getPh j t st fl).pre P := by
  unfold getPh; rw [dif_pos h]; exact ⟨h1, h2⟩

theorem getPh_time {j : ℕ} {t st fl : Fin k} (h : t ≠ st ∧ t ≠ fl ∧ st ≠ fl) (P : Store k) :
    (getPh j t st fl).time P = 6 * (P st).length + 16 := by
  unfold getPh; rw [dif_pos h]

/-! ### Replacing a segment -/

/-- The emitter of the new packed store, on the tapes `0` (store), `1` (new segment), `2` (flag). -/
noncomputable def catM (j : ℕ) :=
  (emitTr (preT j) (emb2 0 2 (by decide))).seq
    ((emitTr frT (emb2 1 2 (by decide))).seq (emitTr (sufT j) (emb2 0 2 (by decide))))
where
  /-- Two distinct tapes. -/
  emb2 (a b : Fin 3) (h : a ≠ b) : Fin 2 ↪ Fin 3 :=
    ⟨![a, b], by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩

/-- The emitted word: `putW j (ws 1) (ws 0)`. -/
theorem catM_runs (j : ℕ) (x : List Bool) (ws : Store 3) (h2 : ws 2 = []) (out₀ : List Bool) :
    (catM j).RunsWords x ws out₀
      ((4 * (ws 0).length + 12) + ((4 * (ws 1).length + 12) + (4 * (ws 0).length + 12)))
      (pure ()) (fun _ => ws) (fun _ => putW j (ws 1) (ws 0)) := by
  have h₁ := emitTr_runs (preT j) (catM.emb2 0 2 (by decide)) x ws h2 out₀
  have h₂ := emitTr_runs frT (catM.emb2 1 2 (by decide)) x ws h2
    (out₀ ++ (preT j).run (preT j).q₀ (ws 0))
  have h₃ := emitTr_runs (sufT j) (catM.emb2 0 2 (by decide)) x ws h2
    (out₀ ++ (preT j).run (preT j).q₀ (ws 0) ++ frT.run frT.q₀ (ws 1))
  have h₂₃ := RunsWords.seqU h₂ h₃
  have h := RunsWords.seqU h₁ h₂₃
  have heq : putW j (ws 1) (ws 0) = (preT j).run (preT j).q₀ (ws 0) ++
      (frT.run frT.q₀ (ws 1) ++ (sufT j).run (sufT j).q₀ (ws 0)) := by
    rw [putW, run_frT, List.append_assoc]
  rw [heq]
  exact h

/-- The words of four tapes as three words and a blank last tape. -/
theorem snocW_four (ws : Store 4) (h3 : ws 3 = []) :
    snocW (fun i : Fin 3 => ws i.castSucc) [] = ws := by
  funext i
  induction i using Fin.lastCases with
  | last => rw [snocW_last]; exact h3.symm
  | cast i => simp

/-- The cleanup: `0 := 3`, `3 := []`, `1 := []`. -/
def putTail : Prog 4 := .seq (.prim (.copy 0 3)) (.seq (.prim (.clear 3)) (.prim (.clear 1)))

theorem coinFree_putTail : putTail.CoinFree := rfl

theorem wf_putTail : putTail.WF := ⟨trivial, trivial, trivial⟩

theorem timeBound_putTail (L : ℕ) : putTail.timeBound L = 3 * (2 * L + 3) := by
  simp [putTail, Prog.timeBound, Prog.lenBound, Prim.pad, Prim.grow]
  ring

theorem run_putTail (ws : Store 4) :
    putTail.run ws = update (update (update ws 0 (ws 3)) 3 []) 1 [] := by
  simp [putTail, Prog.run, Prim.apply]

/-- The local machine of a replacement, on the tapes `0` (store), `1` (segment), `2` (flag),
`3` (new store). -/
noncomputable def putLocal (j : ℕ) := (catM j).outputToWord.seq (Prog.compile putTail)

/-- The time of a replacement, from the lengths of the store `E` and of the segment `U`. -/
def putTime (E U : ℕ) : ℕ :=
  ((4 * E + 12) + ((4 * U + 12) + (4 * E + 12))) + ((2 * E + 2 * U + 1) + 2) +
    3 * (2 * (2 * E + 2 * U + 1) + 3)

theorem length_putW_le (j : ℕ) (u E : List Bool) :
    (putW j u E).length ≤ 2 * E.length + 2 * u.length + 1 := by
  have h1 := length_run_segT_le j (fun n _ _ => decide (n < j)) E (preT j).q₀
  have h2 := length_run_segT_le j (fun n _ _ => decide (j < n)) E (sufT j).q₀
  have h3 := length_frame' u
  simp only [putW, List.length_append]
  simp only [preT, sufT] at h1 h2 ⊢
  omega

theorem putLocal_runs (j : ℕ) (x : List Bool) (ws : Store 4) (h2 : ws 2 = []) (h3 : ws 3 = [])
    (out₀ : List Bool) :
    (putLocal j).RunsWords x ws out₀ (putTime (ws 0).length (ws 1).length)
      (ProbOracleComp.sample (pure (update (update ws 0 (putW j (ws 1) (ws 0))) 1 [])))
      id (fun _ => []) := by
  set ws3 : Store 3 := fun i => ws i.castSucc
  have hc := catM_runs j x ws3 h2 []
  have ho := RunsWords.outputToWord_of_le (l := 2 * (ws 0).length + 2 * (ws 1).length + 1) hc
    (fun _ _ _ _ _ _ => length_putW_le j _ _) out₀
  rw [snocW_four ws h3] at ho
  have ho' := RunsWords.toSample ho
  set w4 := snocW ws3 (putW j (ws3 1) (ws3 0))
  have hL : maxLen w4 ≤ 2 * (ws 0).length + 2 * (ws 1).length + 1 := by
    rw [maxLen_le_iff]
    intro i
    induction i using Fin.lastCases with
    | last => simp only [w4, snocW_last]; exact length_putW_le j _ _
    | cast i =>
      simp only [w4, snocW_castSucc, ws3]
      fin_cases i <;> simp [h2] <;> omega
  have ht := Prog.compile_runsWords putTail wf_putTail x _ w4 out₀ hL
  have h := RunsWords.seqStore ho' (fun a ha => by
    simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at ha
    subst ha
    exact ht)
  rw [pure_bind, Prog.denote_eq_run_of_coinFree _ coinFree_putTail, run_putTail] at h
  have hfin : update (update (update w4 0 (w4 3)) 3 []) 1 [] =
      update (update ws 0 (putW j (ws 1) (ws 0))) 1 [] := by
    funext i
    fin_cases i <;> simp [w4, ws3, snocW, Fin.lastCases, Fin.reverseInduction, h3] <;> rfl
  rw [hfin, timeBound_putTail] at h
  refine h.mono ?_
  have e0 : (ws3 0).length = (ws 0).length := rfl
  have e1 : (ws3 1).length = (ws 1).length := rfl
  simp only [putTime, e0, e1]
  omega

/-- The four tapes of a replacement. -/
def emb4 (a b c d : Fin k) (h : [a, b, c, d].Nodup) : Fin 4 ↪ Fin k :=
  ⟨![a, b, c, d], by
    intro i j hij
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at h
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩

/-- The store function of replacing the segment `j` of tape `st` by the word of tape `t`. -/
def putF (j : ℕ) (t st : Fin k) (P : Store k) : Store k :=
  update (update P st (putW j (P t) (P st))) t []

theorem putF_pkW {K : ℕ} (j : Fin K) (t st : Fin k) (P : Store k) (S : Store K)
    (hS : P st = pkW S) : putF j t st P = update (update P st (pkW (update S j (P t)))) t [] := by
  rw [putF, hS, putW_pkW]

theorem ne_of_partialInv_none {m : ℕ} {e : Fin m ↪ Fin k} {l : Fin k}
    (hl : MultiTapeTM.partialInv e l = none) (i : Fin m) : e i ≠ l := by
  intro hi
  rw [← hi, partialInv_self] at hl
  simp at hl

theorem embedF_putF (j : ℕ) {t st fl B : Fin k} (h : [st, t, fl, B].Nodup) (P : Store k)
    (hfl : P fl = []) (hB : P B = []) :
    embedF (emb4 st t fl B h) P
      (update (update (fun i => P (emb4 st t fl B h i)) 0
        (putW j (P (emb4 st t fl B h 1)) (P (emb4 st t fl B h 0)))) 1 []) = putF j t st P := by
  have hd := h
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at hd
  obtain ⟨⟨h1, h2, h3, -⟩, ⟨h4, h5, -⟩, ⟨h6, -⟩, -⟩ := hd
  funext l
  rcases embedF_cases (emb4 st t fl B h) P _ l with ⟨hl, e⟩ | ⟨i, rfl, e⟩
  · have n0 : st ≠ l := ne_of_partialInv_none hl 0
    have n1 : t ≠ l := ne_of_partialInv_none hl 1
    rw [e, putF, update_of_ne (Ne.symm n1), update_of_ne (Ne.symm n0)]
  · rw [e]
    fin_cases i
    · show (update (update (fun i : Fin 4 => P (emb4 st t fl B h i)) (0 : Fin 4) _) (1 : Fin 4) [] : Store 4) 0 = putF j t st P st
      rw [update_of_ne (by decide), update_self, putF, update_of_ne h1, update_self]
      rfl
    · show (update (update (fun i : Fin 4 => P (emb4 st t fl B h i)) (0 : Fin 4) _) (1 : Fin 4) [] : Store 4) 1 = putF j t st P t
      rw [update_self, putF, update_self]
    · show (update (update (fun i : Fin 4 => P (emb4 st t fl B h i)) (0 : Fin 4) _) (1 : Fin 4) [] : Store 4) 2 = putF j t st P fl
      rw [update_of_ne (by decide), update_of_ne (by decide), putF, update_of_ne (Ne.symm h4),
        update_of_ne (Ne.symm h2)]
      rfl
    · show (update (update (fun i : Fin 4 => P (emb4 st t fl B h i)) (0 : Fin 4) _) (1 : Fin 4) [] : Store 4) 3 = putF j t st P B
      rw [update_of_ne (by decide), update_of_ne (by decide), putF, update_of_ne (Ne.symm h5),
        update_of_ne (Ne.symm h3)]
      rfl

/-- **The replacement phase** `S j := t`, `t := []` (`fl` a blank flag tape, `B` a blank tape). -/
noncomputable def putPh (j : ℕ) (t st fl B : Fin k) : Phase k :=
  if h : [st, t, fl, B].Nodup then
    { State := _
      fintype := Fintype.ofFinite _
      machine := (putLocal j).extendTapes (emb4 st t fl B h)
      f := putF j t st
      pre := fun P => P fl = [] ∧ P B = []
      time := fun P => putTime (P st).length (P t).length
      runs := fun x P out₀ hP => by
        have hl := putLocal_runs j x (fun i => P (emb4 st t fl B h i)) hP.1 hP.2 out₀
        have he := RunsWords.of_map _ id (fun _ => [])
          (RunsWords.extendTapes (ws₀ := P) (emb4 st t fl B h) hl)
        rw [ProbOracleComp.sample_pure, map_pure] at he
        convert he using 3
        all_goals first
          | rfl
          | (rw [ProbOracleComp.sample_pure]; congr 1; exact (embedF_putF j h P hP.1 hP.2).symm) }
  else
    { State := Unit
      fintype := inferInstance
      machine := ofDeterministic (haltTM k)
      f := putF j t st
      pre := fun _ => False
      time := fun _ => 0
      runs := fun _ _ _ hP => hP.elim }

end SigabaNeo.Tape.Pack

namespace SigabaNeo.Tape.Pack

open Function

variable {k : ℕ}

theorem putPh_f (j : ℕ) (t st fl B : Fin k) : (putPh j t st fl B).f = putF j t st := by
  unfold putPh; split_ifs <;> rfl

theorem putPh_pre {j : ℕ} {t st fl B : Fin k} (h : [st, t, fl, B].Nodup) (P : Store k)
    (h1 : P fl = []) (h2 : P B = []) : (putPh j t st fl B).pre P := by
  unfold putPh; rw [dif_pos h]; exact ⟨h1, h2⟩

theorem putPh_time {j : ℕ} {t st fl B : Fin k} (h : [st, t, fl, B].Nodup) (P : Store k) :
    (putPh j t st fl B).time P = putTime (P st).length (P t).length := by
  unfold putPh; rw [dif_pos h]

end SigabaNeo.Tape.Pack
