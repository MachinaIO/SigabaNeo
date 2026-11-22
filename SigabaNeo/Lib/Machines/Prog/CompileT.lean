import SigabaNeo.Lib.Machines.Prog.BoundsT
import SigabaNeo.Lib.Machines.Prog.Machine

/-!
# The compiled machine under per-tape bounds

The same compiled machine `compile p` as in `SigabaNeo.Lib.Machines.Prog.Compile`, analysed from
per-tape bounds `ℓ` (`Fits s ℓ`) instead of one bound on the longest word.

## Main results

* `compile_runsWordsT`: from any store fitting `ℓ`, the compiled machine of a well-formed program
  realizes `denote p s` within `timeBoundT p ℓ` steps on every coin sequence.
* `toMachineT`, `run_toMachineT`, `cost_toMachineT`: the explicit machine of a program (the same
  `toPTM`, with the clock `totalTimeT`) and its output law and cost.
-/

namespace SigabaNeo.Tape

open Cslib Turing MultiTapeMachine MultiTapePTM

variable {k : ℕ}

namespace Prog

theorem roundTimeT_le_sup (body : Prog k) (i : Fin k) (ℓ : Fin k → ℕ) {j : ℕ} (hj : j < ℓ i) :
    roundTimeT (timeBoundT body) i ((loopStepT i body)^[j] ℓ) ≤
      (Finset.range (ℓ i)).sup
        (fun j => roundTimeT (timeBoundT body) i ((loopStepT i body)^[j] ℓ)) :=
  Finset.le_sup (f := fun j => roundTimeT (timeBoundT body) i ((loopStepT i body)^[j] ℓ))
    (Finset.mem_range.mpr hj)

/-- **Correctness and time of the compiled machine, from per-tape bounds.** From any store `s`
with `|s i| ≤ ℓ i` for every tape `i`, the compiled machine of a well-formed program realizes the
law of `denote p s` on its work tapes, emits nothing, and halts within `timeBoundT p ℓ` steps on
every coin sequence. -/
theorem compile_runsWordsT (p : Prog k) (hp : p.WF) (x : List Bool) :
    ∀ (ℓ : Fin k → ℕ) (s : Store k) (out₀ : List Bool), Fits s ℓ →
      (compile p).RunsWords x s out₀ (timeBoundT p ℓ) (ProbOracleComp.sample (denote p s)) id
        (fun _ => []) := by
  induction p with
  | prim p =>
    intro ℓ s out₀ hs
    have := hs.maxLen_le
    exact colTM_runsWords p.spec x s (p.apply s) out₀
      (by rw [p.spec_e]; simp only [timeBoundT]; omega) (p.result s)
  | coin i =>
    intro ℓ s out₀ hs
    have hL := hs.maxLen_le
    have h := RunsWords.seqStore (A := pure (Function.update s i []))
      (B := fun a => (fun b => Function.update a i [b]) <$> ProbComp.uniform Bool)
      (colTM_runsWords (clearSpec i) x s (Function.update s i []) out₀
        (t := 2 * supB ℓ + 3) (by simp only [clearSpec, bwdSpec]; omega) (clear_result i s))
      (fun a ha => by
        simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at ha
        subst ha
        exact coinPTM_runsWords i x _ (by simp) out₀)
    have heq : (pure (Function.update s i []) >>= fun a =>
        (fun b => Function.update a i [b]) <$> ProbComp.uniform Bool) = denote (coin i) s := by
      simp [denote, Function.update_idem]
    rw [heq] at h
    exact h.mono (by simp only [timeBoundT]; omega)
  | seq p q ihp ihq =>
    intro ℓ s out₀ hs
    exact RunsWords.seqStore (ihp hp.1 ℓ s out₀ hs)
      (fun a ha => ihq hp.2 _ a out₀ (lenBoundT_spec p ℓ s hs a ha))
  | ifBlank i p q ihp ihq =>
    intro ℓ s out₀ hs
    by_cases hi : s i = []
    · have h := RunsWords.branch_nil i (compile q) hi (ihp hp.1 ℓ s out₀ hs)
      simp only [denote, hi, ↓reduceIte]
      exact h.mono (by simp only [timeBoundT]; omega)
    · have h := RunsWords.branch_ne_nil i (compile p) hi (ihq hp.2 ℓ s out₀ hs)
      simp only [denote, hi, ↓reduceIte]
      exact h.mono (by simp only [timeBoundT]; omega)
  | ifBit i p q ihp ihq =>
    intro ℓ s out₀ hs
    by_cases hi : (s i).head? = some true
    · have h := RunsWords.branchBit_true i (compile q) hi (ihp hp.1 ℓ s out₀ hs)
      simp only [denote, hi, ↓reduceIte]
      exact h.mono (by simp only [timeBoundT]; omega)
    · have h := RunsWords.branchBit_false i (compile p) hi (ihq hp.2 ℓ s out₀ hs)
      simp only [denote, hi, ↓reduceIte]
      exact h.mono (by simp only [timeBoundT]; omega)
  | loop i body ih =>
    intro ℓ s out₀ hs
    set g := loopStepT i body with hg
    set T := (Finset.range (ℓ i)).sup
      (fun j => roundTimeT (timeBoundT body) i (g^[j] ℓ)) with hT
    -- one round, from a store fitting `ℓ'`
    have hround : ∀ (ℓ' : Fin k → ℕ) (t : Store k), Fits t ℓ' →
        (loopRound i (compile body)).RunsWords x t out₀ (roundTimeT (timeBoundT body) i ℓ')
          (ProbOracleComp.sample (denote body (tailAt i t))) id (fun _ => []) := by
      intro ℓ' t ht
      have hL := ht.maxLen_le
      have h := RunsWords.seqStore (A := pure (tailAt i t)) (B := denote body)
        (colTM_runsWords (tailSpec i) x t (tailAt i t) out₀ (t := 2 * supB ℓ' + 3)
          (by simp only [tailSpec, bwdSpec]; omega) (tail_result i t))
        (fun a ha => by
          simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at ha
          subst ha
          exact ih hp.1 _ _ out₀ (fits_tailAt ht i))
      rw [pure_bind] at h
      exact h
    have hn : (s i).length ≤ ℓ i := hs i
    by_cases h0 : s i = []
    · have hhalt : (ofDeterministic (haltTM k) : MultiTapePTM k Bool Unit Empty).RunsWords x s out₀ 1
          (pure s) id (fun _ => []) := runsWords_of_runFrom (haltTM_runFrom x s out₀)
      have h := RunsWords.branch_nil i (repeatUntilBlank i (loopRound i (compile body))) h0 hhalt
      simp only [denote, h0, List.length_nil, OracleComp.iterate_zero]
      exact h.mono (by simp only [timeBoundT]; omega)
    · set n := (s i).length with hn'
      have hpos : 0 < n := List.length_pos_iff.mpr h0
      have hloop := RunsWords.repeatUntilBlank i (body := loopRound i (compile body))
        (x := x) (out₀ := out₀) (t := T) (rounds := n - 1) (s₀ := s) (ws := id) Function.injective_id
        (step := fun t => ProbOracleComp.sample (denote body (tailAt i t)))
        (last := fun t => ProbOracleComp.sample (denote body (tailAt i t)))
        (fun m t => (t i).length = n - m ∧ Fits t (g^[m] ℓ)) ⟨by simp [hn'], hs⟩
        (fun m hm t ht => (hround _ t ht.2).mono (roundTimeT_le_sup body i ℓ (by omega)))
        (fun t ht => (hround _ t ht.2).mono (roundTimeT_le_sup body i ℓ (by omega)))
        (fun m hm t ht OS oracle st st' t' ht' => by
          have ht'' := mem_support_of_runWith_sample ht'
          have hi := preserves_spec i body hp.2 _ t' ht''
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · rw [hi]; simp [tailAt, ht.1]; omega
          · rw [Function.iterate_succ_apply']
            exact lenBoundT_spec body _ _ (fits_tailAt ht.2 i) t' ht''
          · show t' i ≠ []
            rw [hi]
            simp only [tailAt, Function.update_self, ne_eq]
            rw [← List.length_eq_zero_iff, List.length_tail, ht.1]
            omega)
        (fun t ht OS oracle st st' t' ht' => by
          have hi := preserves_spec i body hp.2 _ t' (mem_support_of_runWith_sample ht')
          show t' i = []
          rw [hi]
          simp only [tailAt, Function.update_self]
          rw [← List.length_eq_zero_iff, List.length_tail, ht.1]
          omega)
      have h := RunsWords.branch_ne_nil i (ofDeterministic (haltTM k)) h0 hloop
      have hprog : (OracleComp.iterate (n - 1)
          (fun t => ProbOracleComp.sample (denote body (tailAt i t))) s >>=
            fun t => ProbOracleComp.sample (denote body (tailAt i t)) :
            ProbOracleComp (fun _ : Empty × List Bool => List Bool) (Store k)) =
          ProbOracleComp.sample (denote (loop i body) s) := by
        rw [← OracleComp.iterate_succ, Nat.sub_add_cancel hpos, denote, sample_iterate]
      rw [hprog] at h
      refine h.mono ?_
      show (n - 1 + 1) * (T + 1) + 1 ≤ ℓ i * (T + 1) + 2
      have : (n - 1 + 1) * (T + 1) ≤ ℓ i * (T + 1) := Nat.mul_le_mul_right _ (by omega)
      omega

/-! ### The explicit machine -/

/-- The per-tape bounds of the input store: `n` on tape `i₀`, `0` elsewhere. -/
def inputBound (i₀ : Fin k) (n : ℕ) : Fin k → ℕ := Function.update (fun _ => 0) i₀ n

theorem fits_inputStore (i₀ : Fin k) {x : List Bool} {n : ℕ} (hx : x.length ≤ n) :
    Fits (inputStore i₀ x) (inputBound i₀ n) :=
  (show Fits (fun _ => []) (fun _ => 0) from fun _ => le_rfl).update i₀ hx

/-- The clock of the machine of a program from per-tape bounds, for inputs at most `n` long: load,
run the program from `inputBound i₀ n`, emit tape `o` (whose own bound is all that counts). -/
def totalTimeT (p : Prog k) (i₀ o : Fin k) (n : ℕ) : ℕ :=
  (2 * n + 2) + timeBoundT p (inputBound i₀ n) + (2 * lenBoundT p (inputBound i₀ n) o + 2)

/-- **The machine of a program as a phase, per-tape clock.** -/
theorem toPTM_runsWordsT (p : Prog k) (hp : p.WF) (i₀ o : Fin k) (n : ℕ) (x : List Bool)
    (hx : x.length ≤ n) :
    (p.toPTM i₀ o).RunsWords x (fun _ => []) [] (totalTimeT p i₀ o n)
      (ProbOracleComp.sample (denote p (inputStore i₀ x))) id (fun s => s o) := by
  have hload : (ofDeterministic (loadTM i₀) : MultiTapePTM k Bool Bool Empty).RunsWords x
      (fun _ => []) [] (2 * n + 2) (ProbOracleComp.sample (pure (inputStore i₀ x))) id
      (fun _ => []) :=
    (runsWords_of_runFrom (loadTM_runFrom i₀ x _ rfl [])).mono (by omega)
  have h₁ := RunsWords.seqStore hload (fun a ha => by
    simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at ha
    subst ha
    exact compile_runsWordsT p hp x _ _ [] (fits_inputStore i₀ hx))
  rw [pure_bind] at h₁
  have h₂ := h₁.seq_bind (t₂ := 2 * lenBoundT p (inputBound i₀ n) o + 2)
    (prog₂ := fun a => pure a) (ws₂ := fun _ => id)
    (emit₂ := fun _ b => b o) (fun a b hab => by simpa using hab)
    (fun a _ _ _ _ ha => by
      have hlen := lenBoundT_spec p _ _ (fits_inputStore i₀ hx) a
        (mem_support_of_runWith_sample ha) o
      refine (runsWords_of_runFrom_emit (e := fun b => b o)
        (emitTM_runFrom o x a ([] ++ []))).mono ?_
      omega)
  have h₃ := h₂.of_map Prod.snd id (fun s => s o)
  have heq : (Prod.snd <$> (ProbOracleComp.sample (denote p (inputStore i₀ x)) >>= fun a =>
      (fun b => (a, b)) <$> (pure a : ProbOracleComp (fun _ : Empty × List Bool => List Bool) _))) =
      ProbOracleComp.sample (denote p (inputStore i₀ x)) := by
    simp
  rw [heq] at h₃
  exact h₃

/-- The explicit machine of a program with the per-tape clock `totalTimeT p i₀ o n`: the same
`toPTM` as `toMachine`, only the clock differs. -/
noncomputable def toMachineT (p : Prog k) (i₀ o : Fin k) (n : ℕ) : Machine :=
  Machine.ofPTM (p.toPTM i₀ o) (totalTimeT p i₀ o n)

/-- **The output law of the machine of a program, per-tape clock.** -/
theorem run_toMachineT (p : Prog k) (hp : p.WF) (i₀ o : Fin k) (n : ℕ) (x : List Bool)
    (hx : x.length ≤ n) :
    (p.toMachineT i₀ o n).run x = (p.law (inputStore i₀ x)).map (fun s => s o) := by
  rw [toMachineT, Machine.run_ofPTM]
  exact eval_runClosed_of_runsWords (toPTM_runsWordsT p hp i₀ o n x hx)

theorem states_toMachineT (p : Prog k) (i₀ o : Fin k) (n : ℕ) :
    (p.toMachineT i₀ o n).states = p.size + 4 := by
  show Nat.card ((Bool ⊕ p.State) ⊕ Bool) = _
  rw [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_bool,
    show Fintype.card p.State = p.size from p.card_state]
  ring

/-- **The cost of the machine of a program, per-tape clock.** -/
theorem cost_toMachineT (p : Prog k) (i₀ o : Fin k) (n : ℕ) :
    (p.toMachineT i₀ o n).cost =
      totalTimeT p i₀ o n + 6 * (p.size + 4) * 3 ^ k * 3 ^ 0 * Machine.entryBits k (p.size + 4) 0 := by
  rw [Machine.cost, Machine.descLen, states_toMachineT]
  rfl

end Prog

end SigabaNeo.Tape
