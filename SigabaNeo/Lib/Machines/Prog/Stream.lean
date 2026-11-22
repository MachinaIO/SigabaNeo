import SigabaNeo.Lib.Machines.Prog.Serial

/-!
# Streams and registers

A *stream* is a tape read from its first bit, popping as it goes; a *register* is a tape of fixed
width into which bits are shifted at the end (`Prog.push`). The counter idiom `for i < |s t|`
copies a template `t` to a counter tape and loops on it (`run_forN`).

* `takeD n w`: the first `n` bits of `w`, padded with `false`.
* `mvP : Prog 5` (tapes `0` stream, `1` register, `2` `3` scratch, `4` template): move `|s 4|` bits
  from the stream into the register (`run_mvP`).
* `dropP : Prog 3` (`0` stream, `1` scratch, `2` template): drop `|s 2|` bits (`run_dropP`).
* `fillP b : Prog 3` (`0` register, `1` scratch, `2` template): shift in `|s 2|` copies of `b`.
-/

namespace SigabaNeo.Tape

variable {k n : ℕ}

/-- The first `n` bits of `w`, padded with `false`. -/
def takeD : ℕ → List Bool → List Bool
  | 0, _ => []
  | n + 1, w => hd w :: takeD n w.tail

@[simp] theorem length_takeD (n : ℕ) (w : List Bool) : (takeD n w).length = n := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih => simp [takeD, ih]

theorem takeD_eq_take : ∀ {n : ℕ} {w : List Bool}, n ≤ w.length → takeD n w = w.take n
  | 0, _, _ => rfl
  | n + 1, [], h => by simp at h
  | n + 1, b :: w, h => by
    simp only [takeD, hd_cons, List.tail_cons, List.take_succ_cons]
    rw [takeD_eq_take (by simpa using h)]

theorem takeD_of_length (w : List Bool) : takeD w.length w = w := by
  rw [takeD_eq_take le_rfl, List.take_length]

theorem takeD_of_length' {n : ℕ} {w : List Bool} (h : w.length = n) : takeD n w = w := by
  subst h; exact takeD_of_length w

theorem takeD_add : ∀ (a b : ℕ) (w : List Bool), takeD (a + b) w = takeD a w ++ takeD b (w.drop a)
  | 0, b, w => by simp [takeD]
  | a + 1, b, w => by
    rw [Nat.add_right_comm, takeD, takeD_add a b w.tail, takeD]
    cases w <;> simp

theorem takeD_nil (n : ℕ) : takeD n [] = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [takeD, ih, List.replicate_succ]

/-- Shifting `m` bits into a register `r`, then `m'` more. -/
theorem drop_append_drop (r a b : List Bool) :
    ((r ++ a).drop a.length ++ b).drop b.length = (r ++ (a ++ b)).drop (a.length + b.length) := by
  rw [← List.drop_append_of_le_length (by simp : a.length ≤ (r ++ a).length), List.drop_drop,
    List.append_assoc, Nat.add_comm]

namespace Prog

open scoped Prog

/-- `for i < |s t|: body`, with the counter on tape `c`. -/
def forN (c t : Fin k) (body : Prog k) : Prog k := cp c t ⨾ loop c body

/-- **The counter idiom**: `forN c t body` runs the abstract step `|s t|` times. -/
theorem run_forN {σ : Type} (c t : Fin k) (body : Prog k) (G : σ → Store k) (step : σ → σ)
    (hstep : ∀ a w, run body (Function.update (G a) c w) = Function.update (G (step a)) c w)
    (a : σ) (s : Store k) (hs : Function.update s c (s t) = Function.update (G a) c (s t)) :
    run (forN c t body) s = Function.update (G (step^[(s t).length] a)) c [] := by
  rw [forN, run_seq, run_copy, hs]
  exact run_loop_iter c body G step (fun _ => True) (fun a w _ => hstep a w) (fun _ _ => trivial)
    (s t) a trivial

/-! ### Moving bits -/

/-- Move `|s 4|` bits from the stream `0` into the register `1`. -/
def mvP : Prog 5 := forN 3 4 (pp 0 2 ⨾ push 1 2 ⨾ clr 2)

def mvStep : List Bool × List Bool → List Bool × List Bool
  | (sv, rv) => (sv.tail, (rv ++ [hd sv]).tail)

theorem mvStep_iter : ∀ (m : ℕ) (sv rv : List Bool),
    (mvStep)^[m] (sv, rv) = (sv.drop m, (rv ++ takeD m sv).drop m)
  | 0, sv, rv => by simp [takeD]
  | m + 1, sv, rv => by
    rw [Function.iterate_succ_apply, mvStep, mvStep_iter m, takeD, tail_append_drop,
      List.drop_tail]

theorem run_mvP (s : Store 5) (h2 : s 2 = []) (h3 : s 3 = []) :
    run mvP s = Function.update (Function.update s 0 ((s 0).drop (s 4).length)) 1
      ((s 1 ++ takeD (s 4).length (s 0)).drop (s 4).length) := by
  let G : List Bool × List Bool → Store 5 := fun a =>
    Function.update (Function.update s 0 a.1) 1 a.2
  have h := run_forN 3 4 (pp 0 2 ⨾ push 1 2 ⨾ clr 2) G mvStep (fun a w => by
      obtain ⟨sv, rv⟩ := a
      funext t
      simp only [G, mvStep, run_seq, run_pop, run_push, run_clear]
      fin_cases t <;> simp [h2]) (s 0, s 1) s (by
      funext t; simp only [G]; fin_cases t <;> simp )
  rw [mvP, h, mvStep_iter]
  funext t
  simp only [G]
  fin_cases t <;> simp [h3]

theorem run_mvP_map {u : Fin 5 → Fin k} (hu : Function.Injective u) (s : Store k)
    (h2 : s (u 2) = []) (h3 : s (u 3) = []) :
    run (map u mvP) s = Function.update (Function.update s (u 0) ((s (u 0)).drop (s (u 4)).length))
      (u 1) ((s (u 1) ++ takeD (s (u 4)).length (s (u 0))).drop (s (u 4)).length) := by
  rw [run_map hu, run_mvP _ h2 h3, extend_update hu, extend_update hu, extend_comp_self]; rfl

/-- Drop `|s 2|` bits of the stream `0`. -/
def dropP : Prog 3 := forN 1 2 (tl 0)

theorem run_dropP (s : Store 3) (h1 : s 1 = []) :
    run dropP s = Function.update s 0 ((s 0).drop (s 2).length) := by
  have h := run_forN 1 2 (tl 0) (fun w => Function.update s 0 w) List.tail (fun a w => by
      funext t
      simp only [run_tail]
      fin_cases t <;> simp ) (s 0) s (by
      funext t; fin_cases t <;> simp )
  have : ∀ m (w : List Bool), List.tail^[m] w = w.drop m := by
    intro m; induction m with
    | zero => intro w; rfl
    | succ m ih => intro w; rw [Function.iterate_succ_apply, ih, List.drop_tail]
  rw [dropP, h, this]
  funext t
  fin_cases t <;> simp [h1]

theorem run_dropP_map {u : Fin 3 → Fin k} (hu : Function.Injective u) (s : Store k)
    (h1 : s (u 1) = []) :
    run (map u dropP) s = Function.update s (u 0) ((s (u 0)).drop (s (u 2)).length) :=
  run_map_eq_update hu _ s 0 _ (run_dropP _ h1)

/-- Shift `|s 2|` copies of `b` into the register `0`. -/
def fillP (b : Bool) : Prog 3 := forN 1 2 (sin b 0)

theorem run_fillP (b : Bool) (s : Store 3) (h1 : s 1 = []) :
    run (fillP b) s = Function.update s 0
      ((s 0 ++ List.replicate (s 2).length b).drop (s 2).length) := by
  have h := run_forN 1 2 (sin b 0) (fun w => Function.update s 0 w) (fun r => (r ++ [b]).tail)
    (fun a w => by
      funext t
      simp only [run_sin]
      fin_cases t <;> simp ) (s 0) s (by
      funext t; fin_cases t <;> simp )
  have : ∀ m (r : List Bool), (fun r => (r ++ [b]).tail)^[m] r = (r ++ List.replicate m b).drop m := by
    intro m; induction m with
    | zero => intro r; simp
    | succ m ih =>
      intro r
      rw [Function.iterate_succ_apply, ih, List.replicate_succ, tail_append_drop]
  rw [fillP, h, this]
  funext t
  fin_cases t <;> simp [h1]

theorem run_fillP_map {u : Fin 3 → Fin k} (hu : Function.Injective u) (b : Bool) (s : Store k)
    (h1 : s (u 1) = []) :
    run (map u (fillP b)) s =
      Function.update s (u 0) ((s (u 0) ++ List.replicate (s (u 2)).length b).drop (s (u 2)).length) :=
  run_map_eq_update hu _ s 0 _ (run_fillP b _ h1)

theorem noGrow_mvP : mvP.NoGrow := rfl
theorem noGrow_dropP : dropP.NoGrow := rfl
theorem noGrow_fillP (b : Bool) : (fillP b).NoGrow := rfl
theorem wf_mvP : mvP.WF := wf_of_wfB (by decide)
theorem wf_dropP : dropP.WF := wf_of_wfB (by decide)
theorem wf_fillP (b : Bool) : (fillP b).WF := wf_of_wfB (by cases b <;> decide)

end Prog

end SigabaNeo.Tape
