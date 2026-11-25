import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Bool
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod

/-!
# A guard on the input length

`lenGuard L` is a deterministic machine with no work tapes that decides whether its input has
length at most `L`: it moves right over at most `L + 1` cells, comes back and emits the answer.
It halts within `2L + 2` steps on every input, however long, and leaves its tapes as it found them
(`lenGuard_computes`). Algorithms branch on it so that inputs longer than `L` cost a bounded number
of steps.
-/

namespace SigabaNeo

open Turing Turing.MultiTapeTM

/-- The states: moving right after `i` cells, or moving back `j` cells before emitting `b`. -/
abbrev GuardState (L : ℕ) := Fin (L + 1) ⊕ (Fin (L + 1) × Bool)

instance (L : ℕ) : Finite (GuardState L) :=
  inferInstanceAs (Finite (Fin (L + 1) ⊕ (Fin (L + 1) × Bool)))

/-- The transitions of the guard. -/
def guardTr (L : ℕ) : GuardState L → Option Bool → (Fin 0 → Option Bool) →
    Action 0 Bool (GuardState L)
  | .inl i, none, _ => ⟨0, Fin.elim0, none, some (.inr (i, true))⟩
  | .inl i, some _, _ =>
    if h : i.val < L then ⟨1, Fin.elim0, none, some (.inl ⟨i.val + 1, by omega⟩)⟩
    else ⟨0, Fin.elim0, none, some (.inr (i, false))⟩
  | .inr (j, b), _, _ =>
    if h : j.val = 0 then ⟨0, Fin.elim0, some b, none⟩
    else ⟨-1, Fin.elim0, none, some (.inr (⟨j.val - 1, by omega⟩, b))⟩

/-- The guard. -/
def lenGuard (L : ℕ) : MultiTapeTM 0 Bool (GuardState L) := ofTr (.inl 0) (guardTr L)

/-- A configuration of the guard. -/
def guardCfg {L : ℕ} (w : List Bool) (q : Option (GuardState L)) (p : ℕ) (hp : p < w.length + 2)
    (out : List Bool) : Cfg 0 Bool (GuardState L) w :=
  ⟨q, ⟨p, hp⟩, Fin.elim0, Fin.elim0, out⟩

theorem guard_step {L : ℕ} (w : List Bool) (q : GuardState L) (p : ℕ) (hp : p < w.length + 2)
    (out : List Bool) :
    (lenGuard L).step (guardCfg w (some q) p hp out) =
      (guardTr L q (guardCfg w (some q) p hp out).inputSymbol Fin.elim0).apply
        (guardCfg w (some q) p hp out) := by
  rw [MultiTapeTM.step_of_state rfl, lenGuard, tr_ofTr]
  congr 2
  funext i; exact i.elim0

theorem guard_runFrom_succ {L : ℕ} (w : List Bool) (c : Cfg 0 Bool (GuardState L) w) (t : ℕ) :
    (lenGuard L).runFrom c (t + 1) = (lenGuard L).runFrom ((lenGuard L).step c) t := by
  show (lenGuard L).step^[t + 1] c = (lenGuard L).step^[t] ((lenGuard L).step c)
  rw [Function.iterate_succ_apply]

/-- Moving right: after `i ≤ min |w| L` steps, at cell `1 + i`. -/
theorem guard_fwd {L : ℕ} (w : List Bool) :
    ∀ i (hi : i ≤ L) (hw : i ≤ w.length),
      (lenGuard L).runFrom (guardCfg w (some (.inl 0)) 1 (by omega) []) i =
        guardCfg w (some (.inl ⟨i, by omega⟩)) (1 + i) (by omega) []
  | 0, _, _ => rfl
  | i + 1, hi, hw => by
    have ih := guard_fwd w i (by omega : i ≤ L) (by omega : i ≤ w.length)
    show (lenGuard L).step^[i + 1] _ = _
    rw [Function.iterate_succ_apply']
    rw [show (lenGuard L).step^[i] (guardCfg w (some (.inl 0)) 1 (by omega) []) = _ from ih,
      guard_step]
    have hsym : (guardCfg (L := L) w (some (.inl ⟨i, by omega⟩)) (1 + i) (by omega) []).inputSymbol
        = some w[i] := inputSymbolInner i rfl (by omega)
    rw [hsym]
    simp only [guardTr, show i < L by omega, ↓reduceDIte]
    apply Cfg.ext_zero_tapes
    · rfl
    · simp only [Action.apply_inputPos, guardCfg]
      apply Fin.ext
      have h := val_moveInputPos_eq (⟨1 + i, by omega⟩ : Fin (w.length + 2)) 1
      simp only [SignType.coe_one] at h
      simp only
      omega
    · rfl

/-- Moving back from cell `1 + j`, then emitting `b`. -/
theorem guard_bwd {L : ℕ} (w : List Bool) (b : Bool) :
    ∀ j (hj : j ≤ L) (hp : 1 + j < w.length + 2),
      (lenGuard L).runFrom (guardCfg w (some (.inr (⟨j, by omega⟩, b))) (1 + j) hp []) (j + 1) =
        guardCfg w none 1 (by omega) [b]
  | 0, _, _ => by
    rw [guard_runFrom_succ, guard_step]
    simp only [guardTr, ↓reduceDIte]
    show Action.apply _ _ = _
    apply Cfg.ext_zero_tapes <;> simp [guardCfg]
  | j + 1, hj, hp => by
    rw [guard_runFrom_succ, guard_step]
    simp only [guardTr, show j + 1 ≠ 0 by omega, ↓reduceDIte]
    have h := guard_bwd w b j (by omega : j ≤ L) (by omega : 1 + j < w.length + 2)
    refine Eq.trans (congrArg (fun c => (lenGuard L).runFrom c (j + 1)) ?_) h
    apply Cfg.ext_zero_tapes
    · rfl
    · simp only [Action.apply_inputPos, guardCfg]
      apply Fin.ext
      have h' := val_moveInputPos_eq (⟨1 + (j + 1), hp⟩ : Fin (w.length + 2)) (-1)
      simp only [SignType.coe_neg, SignType.coe_one] at h'
      simp only
      omega
    · rfl

theorem guard_runFrom_add {L : ℕ} (w : List Bool) (c : Cfg 0 Bool (GuardState L) w) (a b : ℕ) :
    (lenGuard L).runFrom c (a + b) = (lenGuard L).runFrom ((lenGuard L).runFrom c a) b := by
  show (lenGuard L).step^[a + b] c = (lenGuard L).step^[b] ((lenGuard L).step^[a] c)
  rw [Nat.add_comm, Function.iterate_add_apply]

theorem wordsCfg_eq_guardCfg {L : ℕ} (w : List Bool) :
    (wordsCfg w (some (.inl 0)) (fun _ => []) [] : Cfg 0 Bool (GuardState L) w) =
      guardCfg w (some (.inl 0)) 1 (by omega) [] :=
  Cfg.ext_zero_tapes rfl rfl rfl

/-- **The run of the guard**: after `2L + 2` steps it has halted with output `[|w| ≤ L]`, its
input head back at the start. -/
theorem lenGuard_runFrom (L : ℕ) (w : List Bool) :
    (lenGuard L).runFrom (wordsCfg w (some (lenGuard L).q₀) (fun _ => []) []) (2 * L + 2) =
      wordsCfg w none (fun _ => []) [decide (w.length ≤ L)] := by
  have hq : (lenGuard L).q₀ = .inl 0 := rfl
  rw [hq, wordsCfg_eq_guardCfg]
  have hend : guardCfg (L := L) w none 1 (by omega) [decide (w.length ≤ L)] =
      wordsCfg w none (fun _ => []) [decide (w.length ≤ L)] := Cfg.ext_zero_tapes rfl rfl rfl
  rw [← hend]
  by_cases hw : w.length ≤ L
  · -- The end of the input is reached after `|w|` steps.
    set n := w.length with hn
    have h1 := guard_fwd (L := L) w n hw le_rfl
    have hstep : (lenGuard L).step (guardCfg w (some (.inl ⟨n, by omega⟩)) (1 + n) (by omega) []) =
        guardCfg w (some (.inr (⟨n, by omega⟩, true))) (1 + n) (by omega) [] := by
      rw [guard_step]
      have hsym : (guardCfg (L := L) w (some (.inl ⟨n, by omega⟩)) (1 + n) (by omega) []).inputSymbol
          = none := inputSymbol_eq_none_of_boundary (Or.inr (by simp [guardCfg]; omega))
      rw [hsym]
      apply Cfg.ext_zero_tapes <;> simp [guardTr, guardCfg]
    have h2 := guard_bwd (L := L) w true n hw (by omega)
    have hhalt : (lenGuard L).runFrom (guardCfg w (some (.inl 0)) 1 (by omega) []) (n + 1 + (n + 1))
        = guardCfg w none 1 (by omega) [true] := by
      rw [show n + 1 + (n + 1) = n + (1 + (n + 1)) by omega, guard_runFrom_add w _ n, h1,
        guard_runFrom_add w _ 1, show (lenGuard L).runFrom _ 1 = (lenGuard L).step _ from rfl,
        hstep, h2]
    rw [runFrom_eq_of_halt _ _ (by omega : n + 1 + (n + 1) ≤ 2 * L + 2) (by rw [hhalt]; rfl),
      hhalt, decide_eq_true hw]
  · -- The cell `L + 1` holds a symbol.
    have h1 := guard_fwd (L := L) w L le_rfl (by omega)
    have hstep : (lenGuard L).step (guardCfg w (some (.inl ⟨L, by omega⟩)) (1 + L) (by omega) []) =
        guardCfg w (some (.inr (⟨L, by omega⟩, false))) (1 + L) (by omega) [] := by
      rw [guard_step]
      have hsym : (guardCfg (L := L) w (some (.inl ⟨L, by omega⟩)) (1 + L) (by omega) []).inputSymbol
          = some w[L] := inputSymbolInner L rfl (by omega)
      rw [hsym]
      apply Cfg.ext_zero_tapes <;> simp [guardTr, guardCfg]
    have h2 := guard_bwd (L := L) w false L le_rfl (by omega)
    rw [show 2 * L + 2 = L + (1 + (L + 1)) by omega, guard_runFrom_add w _ L, h1,
      guard_runFrom_add w _ 1, show (lenGuard L).runFrom _ 1 = (lenGuard L).step _ from rfl,
      hstep, h2, decide_eq_false hw]

/-- **The guard computes `|w| ≤ L` tidily** within `2L + 2` steps and no work-tape cell. -/
theorem lenGuard_computes (L : ℕ) (w : List Bool) :
    (lenGuard L).ComputesTidilyInTimeAndSpace w [decide (w.length ≤ L)] (2 * L + 2) 0 := by
  rw [computesTidily_iff_runFrom]
  refine ⟨lenGuard_runFrom L w, ?_⟩
  simp [MultiTapeNTM.RunPath.space]

/-- **The guard on encoded inputs**: deciding whether the encoding is at most `L` long is tidily
computable within `2L + 2` steps on every input. -/
theorem computable_lenGuard {α : Type*} (encIn : α ↪ List Bool) (L : ℕ) :
    ComputableTidilyInTimeAndSpace (fun a => decide ((encIn a).length ≤ L)) encIn encBool
      (fun _ => 2 * L + 2) (fun _ => 0) :=
  ⟨0, GuardState L, inferInstance, lenGuard L, fun a => by
    simpa [encBool_apply] using lenGuard_computes L (encIn a)⟩

end SigabaNeo
