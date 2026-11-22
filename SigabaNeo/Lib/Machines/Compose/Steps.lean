import SigabaNeo.Lib.Machines.Compose.Law
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ExtendTapes
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.OutputToTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.InputFromTape

/-!
# Deterministic runs, and the laws of the redirection combinators

* `Runs M c t c'`: from `c` the machine runs exactly `t` steps, deterministically, to `c'`;
  `runs_cons`, `runs_halt` build it one step at a time with `law_one_det`.
* `law_extendTapes`, `law_outputToTape`, `law_inputFromTape`: cslib-frontier's program-level
  simulations, through `law`.
* `embed_eq`: a configuration is the embedding of any configuration that agrees with it on the
  embedded tapes.
-/

namespace SigabaNeo.Compose

open Cslib Turing MultiTapeMachine

variable {k k' : ℕ} {S : Type} {x : List Bool}

/-- From `c` the machine runs exactly `t` steps, deterministically, to `c'`. -/
def Runs (M : MultiTapePTM k Bool S (Fin 0)) (c : Config k Bool S (Fin 0) x) (t : ℕ)
    (c' : Config k Bool S (Fin 0) x) : Prop :=
  Exact M c t ∧ law M t c = PMF.pure c'

theorem runs_cons {M : MultiTapePTM k Bool S (Fin 0)} {c c₁ c' : Config k Bool S (Fin 0) x}
    {t : ℕ} (hc : c.tapes.state ≠ none) (h1 : law M 1 c = PMF.pure c₁) (h : Runs M c₁ t c') :
    Runs M c (t + 1) c' := by
  have hl : ∀ i, law M (i + 1) c = law M i c₁ := fun i => by
    rw [Nat.add_comm, law_add, h1, PMF.pure_bind]
  refine ⟨⟨fun i hi r hr => ?_, fun r hr => ?_⟩, ?_⟩
  · cases i with
    | zero => rw [law_zero, PMF.mem_support_pure_iff] at hr; exact hr ▸ hc
    | succ i => rw [hl] at hr; exact h.1.1 i (by omega) r hr
  · rw [hl] at hr; exact h.1.2 r hr
  · rw [hl]; exact h.2

theorem runs_halt {M : MultiTapePTM k Bool S (Fin 0)} {c c' : Config k Bool S (Fin 0) x}
    (hc : c.tapes.state ≠ none) (h1 : law M 1 c = PMF.pure c') (h' : c'.tapes.state = none) :
    Runs M c 1 c' := by
  refine ⟨⟨fun i hi r hr => ?_, fun r hr => ?_⟩, h1⟩
  · obtain rfl : i = 0 := by omega
    rw [law_zero, PMF.mem_support_pure_iff] at hr; exact hr ▸ hc
  · rw [h1, PMF.mem_support_pure_iff] at hr; exact hr ▸ h'

theorem runs_trans {M : MultiTapePTM k Bool S (Fin 0)} {c c₁ c' : Config k Bool S (Fin 0) x}
    {a b : ℕ} (ha : Runs M c a c₁) (hb : Runs M c₁ b c') :
    Runs M c (a + b) c' := by
  have hl : ∀ i, law M (a + i) c = law M i c₁ := fun i => by
    rw [law_add, ha.2, PMF.pure_bind]
  refine ⟨⟨fun i hi r hr => ?_, fun r hr => ?_⟩, ?_⟩
  · by_cases hia : i < a
    · exact ha.1.1 i hia r hr
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hia)
      rw [hl] at hr
      exact hb.1.1 j (by omega) r hr
  · rw [hl] at hr; exact hb.1.2 r hr
  · rw [hl]; exact hb.2

/-- One deterministic step. -/
theorem law_one_det (M : MultiTapePTM k Bool S (Fin 0)) (c : Config k Bool S (Fin 0) x) {q : S}
    (hq : c.tapes.state = some q) (act : Turing.Action k Bool S) (sym : Fin 0 → Option Bool)
    (mv : Fin 0 → SignType)
    (h : ∀ b, M.tr q c.tapes.inputSymbol c.tapes.workTapeSymbols c.answerSymbols b =
      .step act sym mv) :
    law M 1 c = PMF.pure (c.step act sym mv) := by
  have hf : M.tr q c.tapes.inputSymbol c.tapes.workTapeSymbols c.answerSymbols =
      fun _ => .step act sym mv := funext h
  unfold law MultiTapePTM.runConfigFrom
  simp only [MultiTapeMachine.runConfigFrom, hq, hf]
  simp only [ProbComp.eval_bind, ProbComp.eval_map, PMF.bind_map]
  exact PMF.bind_const _ _

/-! ### Combinators through `law` -/

theorem law_extendTapes (M : MultiTapePTM k Bool S (Fin 0)) (e : Fin k ↪ Fin k') (n : ℕ)
    (c : Config k Bool S (Fin 0) x) (X : Fin k' → ℤ → Option Bool) (P : Fin k' → ℤ) :
    law (M.extendTapes e) n (c.embed e X P) = (law M n c).map (fun f => f.embed e X P) := by
  unfold law
  rw [MultiTapePTM.runConfigFrom_embed, ProbComp.eval_map]

theorem law_outputToTape (M : MultiTapePTM k Bool S (Fin 0)) (n : ℕ)
    (c : Config k Bool S (Fin 0) x) :
    law M.outputToTape n (OutputToTape.config c) = (law M n c).map OutputToTape.config := by
  unfold law
  rw [MultiTapePTM.runConfigFrom_outputToTape, ProbComp.eval_map]

theorem law_inputFromTape {y : List Bool} (M : MultiTapePTM k Bool S (Fin 0)) (n : ℕ)
    (c : Config k Bool S (Fin 0) y) (pos : Fin (x.length + 2)) :
    law M.inputFromTape n (InputFromTape.config true c x pos) =
      (law M n c).map (fun f => InputFromTape.config true f x pos) := by
  unfold law
  rw [MultiTapePTM.runConfigFrom_inputFromTape, ProbComp.eval_map]

theorem exact_extendTapes (M : MultiTapePTM k Bool S (Fin 0)) (e : Fin k ↪ Fin k')
    (c : Config k Bool S (Fin 0) x) (X : Fin k' → ℤ → Option Bool) (P : Fin k' → ℤ) (t : ℕ)
    (h : Exact M c t) : Exact (M.extendTapes e) (c.embed e X P) t := by
  refine ⟨fun i hi r hr => ?_, fun r hr => ?_⟩
  · rw [law_extendTapes, PMF.mem_support_map_iff] at hr
    obtain ⟨f, hf, rfl⟩ := hr
    exact h.1 i hi f hf
  · rw [law_extendTapes, PMF.mem_support_map_iff] at hr
    obtain ⟨f, hf, rfl⟩ := hr
    exact h.2 f hf

theorem runs_extendTapes {M : MultiTapePTM k Bool S (Fin 0)} (e : Fin k ↪ Fin k')
    {c c' : Config k Bool S (Fin 0) x} (X : Fin k' → ℤ → Option Bool) (P : Fin k' → ℤ) {t : ℕ}
    (h : Runs M c t c') : Runs (M.extendTapes e) (c.embed e X P) t (c'.embed e X P) :=
  ⟨exact_extendTapes M e c X P t h.1, by rw [law_extendTapes, h.2, PMF.pure_map]⟩

/-! ### Embedded configurations -/

theorem embed_workTapes_of (c : Config k Bool S (Fin 0) x) (e : Fin k ↪ Fin k')
    (X : Fin k' → ℤ → Option Bool) (P : Fin k' → ℤ) {j : Fin k} {l : Fin k'} (h : e j = l) :
    (c.embed e X P).tapes.workTapes l = c.tapes.workTapes j := by
  subst h
  simp [Config.embed, MultiTapeTM.embed]

theorem embed_workTapePos_of (c : Config k Bool S (Fin 0) x) (e : Fin k ↪ Fin k')
    (X : Fin k' → ℤ → Option Bool) (P : Fin k' → ℤ) {j : Fin k} {l : Fin k'} (h : e j = l) :
    (c.embed e X P).tapes.workTapePos l = c.tapes.workTapePos j := by
  subst h
  simp [Config.embed, MultiTapeTM.embed]

theorem partialInv_eq_none (e : Fin k ↪ Fin k') {l : Fin k'} (h : ∀ j, e j ≠ l) :
    MultiTapeTM.partialInv e l = none := by
  cases hp : MultiTapeTM.partialInv e l with
  | none => rfl
  | some j => exact absurd ((MultiTapeTM.partialInv_isPartialInv e j l).mp hp) (h j)

theorem embed_workTapes_of_not (c : Config k Bool S (Fin 0) x) (e : Fin k ↪ Fin k')
    (X : Fin k' → ℤ → Option Bool) (P : Fin k' → ℤ) {l : Fin k'} (h : ∀ j, e j ≠ l) :
    (c.embed e X P).tapes.workTapes l = X l := by
  simp [Config.embed, MultiTapeTM.embed, partialInv_eq_none e h]

theorem embed_workTapePos_of_not (c : Config k Bool S (Fin 0) x) (e : Fin k ↪ Fin k')
    (X : Fin k' → ℤ → Option Bool) (P : Fin k' → ℤ) {l : Fin k'} (h : ∀ j, e j ≠ l) :
    (c.embed e X P).tapes.workTapePos l = P l := by
  simp [Config.embed, MultiTapeTM.embed, partialInv_eq_none e h]

/-- A configuration is the embedding of one that agrees with it on the embedded tapes. -/
theorem embed_eq (c : Config k' Bool S (Fin 0) x) (d : Config k Bool S (Fin 0) x)
    (e : Fin k ↪ Fin k') (hs : c.tapes.state = d.tapes.state)
    (hi : c.tapes.inputPos = d.tapes.inputPos) (ho : c.tapes.output = d.tapes.output)
    (ht : ∀ j, c.tapes.workTapes (e j) = d.tapes.workTapes j)
    (hp : ∀ j, c.tapes.workTapePos (e j) = d.tapes.workTapePos j) :
    c = d.embed e c.tapes.workTapes c.tapes.workTapePos := by
  refine Config.ext ?_ (funext fun o => o.elim0)
  rcases c with ⟨⟨cs, ci, cw, cp, co⟩, cch⟩
  refine Cfg.ext hs hi (funext fun l => ?_) (funext fun l => ?_) ho <;>
    simp only [Config.embed, MultiTapeTM.embed] <;>
    cases h : MultiTapeTM.partialInv e l with
    | none => rfl
    | some j =>
      have := (MultiTapeTM.partialInv_isPartialInv e j l).mp h
      subst this
      first | exact ht j | exact hp j

end SigabaNeo.Compose
