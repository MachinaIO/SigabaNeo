import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VM
import SigabaNeoStd.Machines.Prog.Lookup
import SigabaNeoStd.Machines.Prog.FrameSize
import SigabaNeoStd.Machines.Prog.Sample
import SigabaNeoStd.Machines.Inline.Regions

/-!
# Two-word input/output for the Mersenne VM

`frontIO` moves the two handler inputs to registers 0 and 1, installs the fixed templates,
runs compiled VM code, and returns register 0 with every other tape cleared. Constants are
written by `putW`; their lengths must therefore be charged in the eventual description bound.
-/

namespace SigabaNeo.Tape.MVM

open Prog XProg

namespace IO

/-- Write the selected tapes, leaving all other tapes unchanged. -/
def setList (f : Store 105) : List (Fin 105) → Prog 105
  | [] => .prim (.copy 0 0)
  | t :: l => .seq (putW t (f t)) (setList f l)

theorem run_setList (f : Store 105) (l : List (Fin 105)) (s : Store 105) :
    (setList f l).run s = fun t ↦ if t ∈ l then f t else s t := by
  induction l generalizing s with
  | nil => funext t; simp [setList, run_prim, Prim.apply]
  | cons r l ih =>
    rw [setList, run_seq, run_putW, ih]
    funext t
    by_cases ht : t ∈ l <;> by_cases hr : t = r <;> simp [ht, hr]

theorem coinFree_setList (f : Store 105) (l : List (Fin 105)) : (setList f l).CoinFree := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    simp only [setList, Prog.CoinFree, Prog.coinFreeB, Bool.and_eq_true]
    exact ⟨coinFree_putW r (f r), ih⟩

theorem wf_setList (f : Store 105) (l : List (Fin 105)) : (setList f l).WF := by
  induction l with
  | nil => trivial
  | cons r l ih => exact ⟨wf_putW r (f r), ih⟩

/-- Initial registers: handler inputs followed by fixed zero templates. -/
def init (a b : List Bool) (tm : Fin 64 → ℕ) : St := fun r ↦
  if r = 0 then a else if r = 1 then b else List.replicate (tm r) false

/-- All tapes except the two input registers. -/
def preTapes : List (Fin 105) := (List.finRange 105).filter fun t ↦ t ≠ 41 ∧ t ≠ 42

/-- Input copies and fixed VM templates. -/
def pre (N K : ℕ) (tm : Fin 64 → ℕ) : Prog 105 :=
  cp 41 0 ⨾ cp 42 1 ⨾ setList (enc N K (fun r ↦ List.replicate (tm r) false)) preTapes

/-- All tapes except the handler output tape. -/
def postTapes : List (Fin 105) := (List.finRange 105).filter fun t ↦ t ≠ 0

/-- Output copy and complete workspace cleanup. -/
def post : Prog 105 := cp 0 41 ⨾ setList (fun _ ↦ []) postTapes

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem run_pre (N K : ℕ) (tm : Fin 64 → ℕ) (a b : List Bool) :
    (pre N K tm).run (io2 (R := 103) a b []) = enc N K (init a b tm) := by
  simp only [pre, run_seq, run_copy, run_setList]
  funext t
  fin_cases t <;> simp [preTapes, enc, encX, init, io2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem run_post (N K : ℕ) (w : St) :
    post.run (enc N K w) = io2 (R := 103) (w 0) [] [] := by
  simp only [post, run_seq, run_copy, run_setList]
  funext t
  fin_cases t <;> simp [postTapes, enc, encX, io2]

theorem coinFree_pre (N K : ℕ) (tm : Fin 64 → ℕ) : (pre N K tm).CoinFree :=
  by
    simpa only [pre, Prog.CoinFree, Prog.coinFreeB, Bool.and_eq_true, true_and] using
      coinFree_setList (enc N K (fun r ↦ List.replicate (tm r) false)) preTapes

theorem coinFree_post : post.CoinFree := by
  simpa only [post, Prog.CoinFree, Prog.coinFreeB, Bool.and_eq_true, true_and] using
    coinFree_setList (fun _ ↦ []) postTapes

/-- State count of a literal word writer, including its initial clear. -/
theorem size_putW (t : Fin 105) (w : List Bool) : (putW t w).size = 36 + 60 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [putW, Prog.size, Prim.pad, ih]; omega

/-- Explicit cost of installing literal templates. -/
theorem size_setList_le (f : Store 105) (l : List (Fin 105)) (B : ℕ)
    (h : ∀ t ∈ l, (f t).length ≤ B) :
    (setList f l).size ≤ 36 + l.length * (36 + 60 * B) := by
  induction l with
  | nil => simp [setList, Prog.size, Prim.pad]
  | cons t l ih =>
    have ht := h t (by simp)
    have hh := ih (fun t ht ↦ h t (by simp [ht]))
    simp only [setList, Prog.size, size_putW, List.length_cons]
    nlinarith

end IO

/-- Execute VM code as a two-input, one-output handler on 105 tapes. -/
def frontIO (N K : ℕ) (tm : Fin 64 → ℕ) (c : Code) : XProg 105 :=
  .seq (.prog (IO.pre N K tm)) (.seq (compile c) (.prog IO.post))

theorem law_frontIO {N K : ℕ} (hN : 0 < N) (hK : 0 < K) (tm : Fin 64 → ℕ)
    (c : Code) (a b : List Bool) :
    (frontIO N K tm c).law (io2 (R := 103) a b []) =
      PMF.pure (io2 (R := 103) (exec N K c (IO.init a b tm) 0) [] []) := by
  rw [frontIO, XProg.law_seq, XProg.law_prog, Prog.law_eq_run_of_coinFree _ (IO.coinFree_pre N K tm), IO.run_pre,
    PMF.pure_bind, XProg.law_seq, law_compile hN hK, PMF.pure_bind,
    XProg.law_prog, Prog.law_eq_run_of_coinFree _ IO.coinFree_post, IO.run_post]

/-- The handler is well formed whenever the VM loops preserve their counters. -/
theorem wf_frontIO (N K : ℕ) (tm : Fin 64 → ℕ) (c : Code) (hc : c.WFc) :
    (frontIO N K tm c).WF :=
  ⟨⟨trivial, ⟨trivial, IO.wf_setList _ _⟩⟩, ⟨wf_compile c hc,
    ⟨trivial, IO.wf_setList _ _⟩⟩⟩

/-- Template installation is charged explicitly; this bound does not hide the literal words. -/
theorem size_frontIO_le (N K : ℕ) (tm : Fin 64 → ℕ) (c : Code) (B : ℕ)
    (hB : ∀ t, (enc N K (fun r ↦ List.replicate (tm r) false) t).length ≤ B) :
    (frontIO N K tm c).size ≤ (compile c).size + 8000 + 6300 * B := by
  have hp := IO.size_setList_le (enc N K (fun r ↦ List.replicate (tm r) false))
    IO.preTapes B (fun t _ ↦ hB t)
  have hq := IO.size_setList_le (fun _ ↦ []) IO.postTapes 0 (by simp)
  have lp : IO.preTapes.length ≤ 105 := by
    exact (List.length_filter_le _ _).trans_eq List.length_finRange
  have lq : IO.postTapes.length ≤ 105 := by
    exact (List.length_filter_le _ _).trans_eq List.length_finRange
  have hp' := Nat.mul_le_mul_right (36 + 60 * B) lp
  have hq' := Nat.mul_le_mul_right 36 lq
  simp only [frontIO, XProg.size, IO.pre, IO.post, Prog.size, Prim.pad]
  omega

end SigabaNeo.Tape.MVM
