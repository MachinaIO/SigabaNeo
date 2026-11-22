import SigabaNeo.Lib.Machines.Inline.LinMain
import SigabaNeo.Lib.Machines.Inline.InitFix

/-!
# Inlining an oracle handler for a reduction: the machine

`Machine.inlineOracleInit A H w₀ E Q L` runs the oracle machine `A` on the **fixed** word `w₀`,
its queries answered by the handlers `H`, the handler state starting as the **input** `x` of the
machine, and outputs `A`'s output paired with the final handler state (`pairOut`).

It is the sequence (`MultiTapePTM.seq`) of four phases on the tapes of `Inline.machine`:

1. `machineLin H haltM (T + 1)`: the short preparation of `Inline.machineLin` writes a clock of
   `T + 1` cells (`T = A.time`) on blank tapes; the simulated machine `haltM` then halts at once,
   consuming one cell;
2. `copyM`: erases the extra clock cell, copies the input `x` onto the `st` tape, and rewinds the
   `st` and input heads (`2 |x| + 4` steps);
3. `simM H (fixInput A.machine w₀) T []`: the simulation of `A` on `w₀` (`Inline.fixInput`), as in
   `Inline.machine`, with the handler state `x`;
4. `outM`: appends `[false, true]` and the `st` word with every bit doubled to the output
   (`2 |u| + 3` steps for a state word `u`).

`E` bounds the length of the encoded states (and so of the input `x`, the initial state), which
bounds the phases 2 and 4 for the clock of the machine.

The laws are in `Inline.InitMain` (`Machine.law_inlineOracleInit`, `Machine.run_inlineOracleInit`),
the bounds in `Inline.InitCost` (`Machine.time_inlineOracleInit_le`,
`Machine.cost_inlineOracleInit_le`).
-/

namespace SigabaNeo.Inline

open Cslib Turing MultiTapeMachine

variable {kA ops m : ℕ}

/-! ### The pairing of the output with the state word -/

/-- Every bit doubled. -/
def dbl (u : List Bool) : List Bool := u.flatMap fun b => [b, b]

@[simp] theorem dbl_nil : dbl [] = [] := rfl
@[simp] theorem dbl_cons (b : Bool) (u : List Bool) : dbl (b :: u) = b :: b :: dbl u := rfl

/-- **The output of the machine**: the output `o` of `A`, the separator `[false, true]`, then the
state word `u` with every bit doubled. -/
def pairOut (o u : List Bool) : List Bool := o ++ false :: true :: dbl u

theorem dbl_append (u v : List Bool) : dbl (u ++ v) = dbl u ++ dbl v := by
  simp [dbl, List.flatMap_append]

theorem reverse_dbl (u : List Bool) : (dbl u).reverse = dbl u.reverse := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [ih, dbl_append]

theorem dbl_sep_inj : ∀ (v v' p p' : List Bool),
    dbl v ++ true :: false :: p = dbl v' ++ true :: false :: p' → v = v' ∧ p = p'
  | [], [], p, p', h => by simpa using h
  | [], b :: v', p, p', h => by cases b <;> simp at h
  | b :: v, [], p, p', h => by cases b <;> simp at h
  | b :: v, b' :: v', p, p', h => by
    simp only [dbl_cons, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, -, h⟩ := h
    obtain ⟨rfl, rfl⟩ := dbl_sep_inj v v' p p' h
    exact ⟨rfl, rfl⟩

/-- **The pairing is injective.** -/
theorem pairOut_injective {o o' u u' : List Bool} (h : pairOut o u = pairOut o' u') :
    o = o' ∧ u = u' := by
  have h' := congrArg List.reverse h
  simp only [pairOut, List.reverse_append, List.reverse_cons, reverse_dbl, List.append_assoc,
    List.nil_append, List.cons_append] at h'
  obtain ⟨h1, h2⟩ := dbl_sep_inj _ _ _ _ h'
  exact ⟨List.reverse_injective h2, List.reverse_injective h1⟩

/-! ### The phases -/

/-- The machine that halts at once. -/
def haltM : MultiTapePTM kA Bool Unit (Fin ops) where
  initial := ()
  tr _ _ _ _ := fun _ => .step ⟨0, fun _ => (none, 0), none, none⟩ (fun _ => none) (fun _ => 0)

/-- The states of the copy phase. -/
inductive CStep where
  | clkR | clkE | copy | rew
  deriving DecidableEq

instance : Fintype CStep :=
  ⟨⟨(([.clkR, .clkE, .copy, .rew] : List CStep) : Multiset CStep), by decide⟩,
    fun x => by cases x <;> decide⟩

@[simp] theorem CStep.card : Fintype.card CStep = 4 := rfl

/-- A step of the copy phase: step onto the extra clock cell and erase it; copy the input onto
`st`; rewind `st` and the input head. -/
def cpAct (q : CStep) (inp : Option Bool) (work : Fin (nTapes kA ops m) → Option Bool) :
    Turing.Action (nTapes kA ops m) Bool CStep :=
  match q with
  | .clkR => mkAct 0 (mv1 .clock none 1) none (some .clkE)
  | .clkE => mkAct 0 (mv1 .clock (some none) (-1)) none (some .copy)
  | .copy => match inp with
    | some b => mkAct 1 (mv1 .st (some (some b)) 1) none (some .copy)
    | none => mkAct (-1) (mv1 .st none (-1)) none (some .rew)
  | .rew => match work (Tape.st (kA := kA) (ops := ops) (m := m)).idx with
    | some _ => mkAct (-1) (mv1 .st none (-1)) none (some .rew)
    | none => mkAct 1 (mv1 .st none 1) none none

/-- **The copy phase.** -/
def copyM : MultiTapePTM (nTapes kA ops m) Bool CStep (Fin 0) where
  initial := .clkR
  tr q inp work _ := fun _ => stepR (cpAct q inp work)

/-- The states of the output phase. -/
inductive OStep where
  | s0 | s1 | loop | dup (b : Bool)
  deriving DecidableEq

instance : Fintype OStep :=
  ⟨⟨(([.s0, .s1, .loop, .dup false, .dup true] : List OStep) : Multiset OStep), by decide⟩,
    fun x => by rcases x with _ | _ | _ | _ | _ <;> decide⟩

@[simp] theorem OStep.card : Fintype.card OStep = 5 := rfl

/-- A step of the output phase: the separator, then each bit of the `st` word twice. -/
def outAct (q : OStep) (work : Fin (nTapes kA ops m) → Option Bool) :
    Turing.Action (nTapes kA ops m) Bool OStep :=
  match q with
  | .s0 => mkAct 0 noop (some false) (some .s1)
  | .s1 => mkAct 0 noop (some true) (some .loop)
  | .loop => match work (Tape.st (kA := kA) (ops := ops) (m := m)).idx with
    | some b => mkAct 0 noop (some b) (some (.dup b))
    | none => mkAct 0 noop none none
  | .dup b => mkAct 0 (mv1 .st none 1) (some b) (some .loop)

/-- **The output phase.** -/
def outM : MultiTapePTM (nTapes kA ops m) Bool OStep (Fin 0) where
  initial := .s0
  tr q _ work _ := fun _ => stepR (outAct q work)

/-- The control states of the inlined machine for reductions. -/
abbrev IState (SA : Type) (H : Fin ops → Routine (m + 3)) (h : ℕ) : Type :=
  LState Unit H h ⊕ (CStep ⊕ (Ctl SA H ⊕ OStep))

/-- **The inlined machine for reductions**, simulating `M` (on its fixed input) for the clock
`T`. -/
def initM {SA : Type} (H : Fin ops → Routine (m + 3)) (M : MultiTapePTM kA Bool SA (Fin ops))
    (T : ℕ) :
    MultiTapePTM (nTapes kA ops m) Bool (IState SA H (clockDigits kA (T + 1)).length) (Fin 0) :=
  (machineLin H (haltM (kA := kA) (ops := ops)) (T + 1)).seq
    ((copyM (kA := kA) (ops := ops) (m := m)).seq ((simM H M T []).seq outM))

end SigabaNeo.Inline

namespace SigabaNeo

open Cslib Turing MultiTapeMachine Inline

variable {ops m : ℕ}

/-- The clock of the inlined machine for reductions: the preparation of the clock, the copy, the
simulation and the output. -/
def inlineTimeInit (T h Q L ops E : ℕ) : ℕ :=
  (4 * (T + 1) + 4 * h + 5) + ((2 * E + 4) + ((T * (Q + 2 * L + 4 * ops + 9) + 1) + (2 * E + 3)))

/-- **The inlined machine for reductions**: on the input `x`, `A` runs on the fixed word `w₀` with
its queries answered by the handlers `H`, the handler state starting as `x`; the output is `A`'s
output paired (`pairOut`) with the final handler state word. `E` bounds the lengths of the encoded
states. -/
noncomputable def Machine.inlineOracleInit (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (w₀ : List Bool) (E Q L : ℕ) : Machine :=
  Machine.ofPTMOps (initM H (Inline.fixInput A.machine w₀) A.time)
    (inlineTimeInit A.time (clockDigits A.tapes (A.time + 1)).length Q L ops E)

end SigabaNeo
