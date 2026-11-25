import SigabaNeoStd.Machines.Prog.Macros
import SigabaNeoStd.Machines.Prog.Frame
import SigabaNeoStd.Machines.Prog.Det
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Reverse
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Transducer

/-!
# Single-pass phases and deterministic tape programs

Every primitive of the tape language sweeps whole tapes, so a program reading a word of length `n`
bit by bit takes time quadratic in `n`. The phases here read or write a long word in **one pass**,
in time linear in its length, and compose with compiled programs through `RunsWords` (no clock is
needed between phases, so the number of states does not depend on the input length):

* `revInPhase e`: write the reversal of the input on tape `e 0` (cslib's `reverseInput`, its output
  redirected to a work tape), `3 |x| + 4` steps (`revInPhase_runs`);
* `trPhase τ e`: run the finite-state transducer `τ` on the word of tape `e 1`, writing its output
  on the blank tape `e 0` (`e 2` is a blank flag tape), `6 |w| + 16` steps (`trPhase_runs`);
* `revOutPhase e`: emit the reversal of the word of tape `e 0` (`e 1` is a blank flag tape),
  `2 |w| + 6` steps (`revOutPhase_runs`);
* `compile p` for a coin-free program `p` (`Prog.CoinFree`), whose law is the point mass at its pure
  semantics `Prog.run p` (`Prog.law_eq_run_of_coinFree`): `compile_runsWordsU`.

All phases are stated for the trivial program `pure ()` with explicit final stores, and chain with
`RunsWords.seqU`; `eval_runClosed_of_runsWordsU` reads the output law of the whole machine.
-/

namespace SigabaNeo.Tape

open Cslib Turing MultiTapeMachine MultiTapePTM

variable {k : ℕ}

/-! ### Deterministic phases -/

/-- A phase computing a fixed value, stated for the trivial program. -/
theorem RunsWords.toUnit {S : Type} {M : MultiTapePTM k Bool S Empty} {x : List Bool}
    {ws₀ : Store k} {out₀ : List Bool} {t : ℕ} {α : Type} {a : α} {ws₁ : α → Store k}
    {emit : α → List Bool} (h : M.RunsWords x ws₀ out₀ t (pure a) ws₁ emit) :
    M.RunsWords x ws₀ out₀ t (pure ()) (fun _ => ws₁ a) (fun _ => emit a) := by
  intro OracleState oracle s cfg htapes hbuf
  obtain ⟨hlaw, hclean⟩ := h OracleState oracle s cfg htapes hbuf
  refine ⟨?_, hclean⟩
  rw [hlaw]
  simp

/-- **Sequencing deterministic phases.** -/
theorem RunsWords.seqU {S₁ S₂ : Type} {M₁ : MultiTapePTM k Bool S₁ Empty}
    {M₂ : MultiTapePTM k Bool S₂ Empty} {x : List Bool} {ws₀ ws₁ ws₂ : Store k}
    {out₀ e₁ e₂ : List Bool} {t₁ t₂ : ℕ}
    (h₁ : M₁.RunsWords x ws₀ out₀ t₁ (pure ()) (fun _ => ws₁) (fun _ => e₁))
    (h₂ : M₂.RunsWords x ws₁ (out₀ ++ e₁) t₂ (pure ()) (fun _ => ws₂) (fun _ => e₂)) :
    (M₁.seq M₂).RunsWords x ws₀ out₀ (t₁ + t₂) (pure ()) (fun _ => ws₂) (fun _ => e₁ ++ e₂) :=
  RunsWords.seq_pure_left h₁ h₂

/-- **The output law of a deterministic machine** realizing a phase from blank tapes. -/
theorem eval_runClosed_of_runsWordsU {S : Type} {M : MultiTapePTM k Bool S Empty} {x : List Bool}
    {t : ℕ} {ws : Store k} {e : List Bool}
    (h : M.RunsWords x (fun _ => []) [] t (pure ()) (fun _ => ws) (fun _ => e)) :
    ProbComp.eval (M.runClosed t x) = PMF.pure e := by
  have h' : M.RunsWords x (fun _ => []) [] t (ProbOracleComp.sample (pure ws)) id
      (fun _ => e) := by
    have := RunsWords.of_map (fun _ : Unit => ws) id (fun _ => e) h
    simpa using this
  rw [Prog.eval_runClosed_of_runsWords h']
  simp

/-- The description length of a machine does not depend on its clock. -/
theorem descLen_ofPTM {S : Type} [Finite S] (m : MultiTapePTM k Bool S) (t t' : ℕ) :
    (Machine.ofPTM m t).descLen = (Machine.ofPTM m t').descLen := rfl

/-! ### Embedded stores -/

/-- An embedded phase that changes only its tape `j`. -/
theorem embedF_eq_update {m : ℕ} {α : Type} (e : Fin m ↪ Fin k) (f : Fin k → α) (g : Fin m → α)
    (j : Fin m) (hg : ∀ i, i ≠ j → g i = f (e i)) :
    embedF e f g = Function.update f (e j) (g j) := by
  funext l
  rcases embedF_cases e f g l with ⟨hl, h⟩ | ⟨i, rfl, h⟩
  · rw [h, Function.update_of_ne]
    rintro rfl
    rw [partialInv_self] at hl
    simp at hl
  · rw [h]
    by_cases hij : i = j
    · subst hij; simp
    · rw [Function.update_of_ne (fun h => hij (e.injective h)), hg i hij]

/-- An embedded phase that changes nothing. -/
theorem embedF_self {m : ℕ} {α : Type} (e : Fin m ↪ Fin k) (f : Fin k → α) :
    embedF e f (fun i => f (e i)) = f := by
  funext l
  rcases embedF_cases e f (fun i => f (e i)) l with ⟨-, h⟩ | ⟨i, rfl, h⟩ <;> exact h

/-! ### Reversing the input onto a tape -/

/-- Write the reversal of the input on tape `e 0`. -/
noncomputable def revInPhase (e : Fin 1 ↪ Fin k) :=
  ((ofDeterministic (MultiTapeTM.reverseInput Bool) : MultiTapePTM 0 Bool Bool Empty).outputToWord).extendTapes e

theorem revInPhase_runs (e : Fin 1 ↪ Fin k) (x : List Bool) (ws₀ : Store k)
    (h0 : ws₀ (e 0) = []) (out₀ : List Bool) :
    (revInPhase e).RunsWords x ws₀ out₀ (3 * x.length + 4) (pure ())
      (fun _ => Function.update ws₀ (e 0) x.reverse) (fun _ => []) := by
  have hdet := ComputesTidily.of_deterministic (Operation := Empty)
    (MultiTapeTM.ReverseInput.computesTidily (Symbol := Bool) x)
  have hw := hdet.outputToWord_of_le (l := x.length) (fun _ oracle s w s' hw => by
    simp only [ProbOracleComp.runWith_pure, PMF.support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hw
    rw [hw.1, List.length_reverse]) out₀
  have hb : (fun j => ws₀ (e j)) = fun _ => ([] : List Bool) := by
    funext j; fin_cases j; exact h0
  rw [← hb] at hw
  have h := (RunsWords.toUnit (RunsWords.extendTapes (ws₀ := ws₀) e hw)).mono
    (show 2 * x.length + 2 + (x.length + 2) ≤ 3 * x.length + 4 by omega)
  have hws : embedF e ws₀ (Function.update (fun j => ws₀ (e j)) (Fin.last 0) x.reverse) =
      Function.update ws₀ (e 0) x.reverse := by
    rw [embedF_eq_update e ws₀ _ 0 (fun i hi => absurd (Subsingleton.elim i 0) hi)]
    simp
  rw [← hws]
  exact h

/-! ### A transducer between tapes -/

theorem Transducer.length_run_le {Q : Type} (τ : MultiTapeTM.Transducer Bool Q) :
    ∀ (q : Q) (w : List Bool), (τ.run q w).length ≤ 2 * w.length + 2
  | q, [] => τ.length_final_le q
  | q, a :: w => by
    rw [MultiTapeTM.Transducer.run_cons, List.length_append]
    have h1 := τ.length_step_le q a
    have h2 := Transducer.length_run_le τ (τ.step q a).1 w
    simp only [List.length_cons]
    omega

/-- Run the transducer `τ` on the word of tape `e 1`, writing its output on the blank tape `e 0`;
`e 2` is a blank flag tape. -/
noncomputable def trPhase {Q : Type} [Finite Q] (τ : MultiTapeTM.Transducer Bool Q)
    (e : Fin 3 ↪ Fin k) :=
  ((ofDeterministic (τ.toTM.seq (MultiTapeTM.rewindInput Bool)) :
    MultiTapePTM 0 Bool _ Empty).onWords true).extendTapes e

theorem trPhase_runs {Q : Type} [Finite Q] (τ : MultiTapeTM.Transducer Bool Q)
    (e : Fin 3 ↪ Fin k) (x : List Bool) (ws₀ : Store k) (h0 : ws₀ (e 0) = [])
    (h2 : ws₀ (e 2) = []) (out₀ : List Bool) :
    (trPhase τ e).RunsWords x ws₀ out₀ (6 * (ws₀ (e 1)).length + 16) (pure ())
      (fun _ => Function.update ws₀ (e 0) (τ.run τ.q₀ (ws₀ (e 1)))) (fun _ => []) := by
  set w := ws₀ (e 1)
  have hdet := ComputesTidily.of_deterministic (Operation := Empty) (τ.computesTidily w)
  have hw := hdet.onWords_of_le (x := x) (l := 2 * w.length + 2) true (fun _ oracle s w' s' hw => by
    simp only [ProbOracleComp.runWith_pure, PMF.support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hw
    rw [hw.1]; exact Transducer.length_run_le τ _ _) out₀
  have hb : (fun j => ws₀ (e j)) =
      Function.update (fun _ => ([] : List Bool)) (Fin.natAdd (0 + 1) (0 : Fin 2) : Fin (0 + 1 + 2)) w := by
    funext j; fin_cases j
    · simpa using h0
    · rfl
    · simpa using h2
  rw [← hb] at hw
  have h := (RunsWords.toUnit (RunsWords.extendTapes (ws₀ := ws₀) e hw)).mono
    (show 4 * w.length + 8 + (2 * w.length + 2) + 6 ≤ 6 * w.length + 16 by omega)
  have hws : embedF e ws₀ (Function.update (fun j => ws₀ (e j))
      ((Fin.last 0).castAdd 2 : Fin (0 + 1 + 2)) (τ.run τ.q₀ w)) =
      Function.update ws₀ (e 0) (τ.run τ.q₀ w) := by
    rw [embedF_eq_update e ws₀ _ 0 (fun i hi => by
      rw [Function.update_of_ne (by simpa using hi)])]
    simp
  rw [← hws]
  exact h

/-! ### Emitting the reversal of a tape -/

/-- Emit the reversal of the word of tape `e 0`; `e 1` is a blank flag tape. -/
noncomputable def revOutPhase (e : Fin 2 ↪ Fin k) :=
  ((ofDeterministic (MultiTapeTM.reverseInput Bool) : MultiTapePTM 0 Bool Bool Empty).inputFromWord
    true).extendTapes e

theorem revOutPhase_runs (e : Fin 2 ↪ Fin k) (x : List Bool) (ws₀ : Store k)
    (h1 : ws₀ (e 1) = []) (out₀ : List Bool) :
    (revOutPhase e).RunsWords x ws₀ out₀ (2 * (ws₀ (e 0)).length + 6) (pure ())
      (fun _ => ws₀) (fun _ => (ws₀ (e 0)).reverse) := by
  set w := ws₀ (e 0)
  have hdet := ComputesTidily.of_deterministic (Operation := Empty)
    (MultiTapeTM.ReverseInput.computesTidily (Symbol := Bool) w)
  have hw := (hdet out₀).inputFromWord (x := x) true
  have hb : (fun j => ws₀ (e j)) = Fin.append (fun _ : Fin 0 => ([] : List Bool)) ![w, []] := by
    funext j; fin_cases j
    · rfl
    · show ws₀ (e 1) = _; rw [h1]; rfl
  rw [← hb] at hw
  have h := RunsWords.toUnit (RunsWords.extendTapes (ws₀ := ws₀) e hw)
  change (revOutPhase e).RunsWords x ws₀ out₀ _ (pure ()) (fun _ => embedF e ws₀ (fun j => ws₀ (e j)))
    (fun _ => w.reverse) at h
  rw [embedF_self] at h
  exact h

/-! ### Coin-free programs -/

namespace Prog

/-- No coin. -/
def coinFreeB : Prog k → Bool
  | prim _ => true
  | coin _ => false
  | seq p q => p.coinFreeB && q.coinFreeB
  | ifBlank _ p q => p.coinFreeB && q.coinFreeB
  | ifBit _ p q => p.coinFreeB && q.coinFreeB
  | loop _ body => body.coinFreeB

/-- `p` uses no coin. -/
def CoinFree (p : Prog k) : Prop := p.coinFreeB = true

/-- A coin-free program denotes its pure semantics. -/
theorem denote_eq_run_of_coinFree : ∀ (p : Prog k), p.CoinFree → ∀ s, p.denote s = pure (p.run s)
  | prim p, _, s => rfl
  | coin i, h, s => absurd h (by simp [CoinFree, coinFreeB])
  | seq p q, h, s => by
    simp only [CoinFree, coinFreeB, Bool.and_eq_true] at h
    rw [denote, denote_eq_run_of_coinFree p h.1, pure_bind, denote_eq_run_of_coinFree q h.2]; rfl
  | ifBlank i p q, h, s => by
    simp only [CoinFree, coinFreeB, Bool.and_eq_true] at h
    rw [denote, run, denote_eq_run_of_coinFree p h.1, denote_eq_run_of_coinFree q h.2]
    split_ifs <;> rfl
  | ifBit i p q, h, s => by
    simp only [CoinFree, coinFreeB, Bool.and_eq_true] at h
    rw [denote, run, denote_eq_run_of_coinFree p h.1, denote_eq_run_of_coinFree q h.2]
    simp only [head?_eq_some_true]
    split_ifs <;> rfl
  | loop i body, h, s => by
    have hb : body.CoinFree := h
    rw [denote, run]
    have : (fun t => denote body (tailAt i t)) = fun t => pure (run body (tailAt i t)) :=
      funext fun t => denote_eq_run_of_coinFree body hb _
    rw [this]
    exact iterate_pure (fun t => run body (tailAt i t)) _ s

/-- **The law of a coin-free program** is the point mass at its pure semantics. -/
theorem law_eq_run_of_coinFree (p : Prog k) (hp : p.CoinFree) (s : Store k) :
    p.law s = PMF.pure (p.run s) := by
  rw [law, denote_eq_run_of_coinFree p hp s, ProbComp.eval_pure]

theorem coinFree_iter (z : Fin k) (p : Prog k) (hp : p.CoinFree) : ∀ n, (iter z p n).CoinFree
  | 0 => rfl
  | n + 1 => by
    simp only [CoinFree, iter, coinFreeB, Bool.and_eq_true]
    exact ⟨hp, coinFree_iter z p hp n⟩

theorem run_iter (z : Fin k) (p : Prog k) : ∀ n s, run (iter z p n) s = (run p)^[n] s
  | 0, s => by simp [iter, run_prim, apply_copy_self]
  | n + 1, s => by
    rw [iter, run_seq, run_iter z p n, Function.iterate_succ_apply]

theorem preserves_iter (z : Fin k) (p : Prog k) {i : Fin k} (hz : z ≠ i) (hp : p.Preserves i) :
    ∀ n, (iter z p n).Preserves i
  | 0 => by simp [iter, Preserves, Prim.writes, Ne.symm hz]
  | n + 1 => ⟨hp, preserves_iter z p hz hp n⟩

/-- A coin-free program leaves the tapes it never writes alone. -/
theorem run_eq_of_preserves (p : Prog k) (hc : p.CoinFree) {i : Fin k} (hp : p.Preserves i)
    (s : Store k) : run p s i = s i :=
  preserves_spec i p hp s _ (by rw [law_eq_run_of_coinFree p hc s]; simp)

/-- **The compiled machine of a coin-free program**, as a deterministic phase. -/
theorem compile_runsWordsU (p : Prog k) (hp : p.WF) (hc : p.CoinFree) (x : List Bool) (L : ℕ)
    (s : Store k) (out₀ : List Bool) (hs : maxLen s ≤ L) :
    (compile p).RunsWords x s out₀ (timeBound p L) (pure ()) (fun _ => run p s) (fun _ => []) := by
  have h := compile_runsWords p hp x L s out₀ hs
  rw [denote_eq_run_of_coinFree p hc s, ProbOracleComp.sample_pure] at h
  exact RunsWords.toUnit h

end Prog

end SigabaNeo.Tape
