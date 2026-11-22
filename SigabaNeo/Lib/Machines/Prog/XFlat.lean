import SigabaNeo.Lib.Machines.Prog.Frame
import SigabaNeo.Lib.Machines.Prog.Det

/-!
# Framed programs as plain programs

A frame only restricts *which tapes a program's cost sees*; its semantics is that of the relabelled
program (`Prog.map`). `XProg.flat` replaces every frame by the relabelling of its body:

* **`denote_eq_run_flat`**: if `flat p` is deterministic and never lengthens a word (`NoGrow`), the
  framed program denotes the point mass at `run (flat p)`; so its law is computed with the
  `run_*` lemmas of plain programs (`law_eq_run_flat`), while its bounds keep the frames
  (`timeBoundT`, `lenBoundT` of `XProg`).
-/

namespace SigabaNeo.Tape

namespace XProg

open Prog

variable {k : ℕ}

/-- Every frame replaced by the relabelling of its body. -/
def flat : {k : ℕ} → XProg k → Prog k
  | _, prog p => p
  | _, frame e p => Prog.map e (flat p)
  | _, seq p q => .seq (flat p) (flat q)
  | _, ifBlank i p q => .ifBlank i (flat p) (flat q)
  | _, ifBit i p q => .ifBit i (flat p) (flat q)
  | _, loop i b => .loop i (flat b)

theorem embedF_eq_extend {m : ℕ} {α : Type} (e : Fin m ↪ Fin k) (f : Fin k → α) (g : Fin m → α) :
    embedF e f g = Function.extend e g f := by
  funext t
  rcases embedF_cases e f g t with ⟨hn, h⟩ | ⟨j, rfl, h⟩
  · rw [h, Function.extend_apply']
    rintro ⟨j, rfl⟩
    rw [partialInv_self] at hn
    exact Option.some_ne_none _ hn
  · rw [h, e.injective.extend_apply]

/-- **A deterministic framed program denotes its flattening.** -/
theorem denote_eq_run_flat : ∀ {k : ℕ} (p : XProg k), (flat p).NoGrow →
    ∀ s, p.denote s = pure (Prog.run (flat p) s)
  | _, prog p, h, s => Prog.denote_eq_run p h s
  | _, frame e p, h, s => by
    have hp : (flat p).NoGrow := by
      have := h; simp only [flat, NoGrow] at this; rwa [noGrowB_map] at this
    rw [denote, denote_eq_run_flat p hp, map_pure, flat, run_map e.injective,
      embedF_eq_extend]
    rfl
  | _, seq p q, h, s => by
    simp only [flat, NoGrow, noGrowB, Bool.and_eq_true] at h
    rw [denote, denote_eq_run_flat p h.1, pure_bind, denote_eq_run_flat q h.2]; rfl
  | _, ifBlank i p q, h, s => by
    simp only [flat, NoGrow, noGrowB, Bool.and_eq_true] at h
    rw [denote, flat, run_ifBlank, denote_eq_run_flat p h.1, denote_eq_run_flat q h.2]
    split_ifs <;> rfl
  | _, ifBit i p q, h, s => by
    simp only [flat, NoGrow, noGrowB, Bool.and_eq_true] at h
    rw [denote, flat, run_ifBit, denote_eq_run_flat p h.1, denote_eq_run_flat q h.2]
    simp only [head?_eq_some_true]
    split_ifs <;> rfl
  | _, loop i b, h, s => by
    have hb : (flat b).NoGrow := h
    rw [denote, flat, run_loop]
    have : (fun t => denote b (tailAt i t)) = fun t => pure (Prog.run (flat b) (tailAt i t)) :=
      funext fun t => denote_eq_run_flat b hb _
    rw [this]
    exact iterate_pure (fun t => Prog.run (flat b) (tailAt i t)) _ s

/-- **The law of a deterministic framed program** is the point mass at its flattening's run. -/
theorem law_eq_run_flat (p : XProg k) (hp : (flat p).NoGrow) (s : Store k) :
    p.law s = PMF.pure (Prog.run (flat p) s) := by
  rw [law, denote_eq_run_flat p hp s, Cslib.ProbComp.eval_pure]

end XProg

end SigabaNeo.Tape
