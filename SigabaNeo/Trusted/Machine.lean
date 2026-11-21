import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Oracle
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Explicit machines

The machine model of Sigaba Neo, shared by the algorithms of primitives
(`SigabaNeo.Trusted.Primitive`) and by attackers (`SigabaNeo.Trusted.Assumption`).

`Machine ops` is a fair-coin multi-tape Turing machine over `Bool` (cslib-frontier's
`Turing.MultiTapePTM`) with `states` control states, `tapes` work tapes and `ops` oracle channels,
run with the clock `time`: it is stopped after `time` steps if it has not halted. `Machine` is
`Machine 0`, a machine without oracles.

* `Machine.run`: the output law of a machine without oracles on a word.
* `Machine.runWith`: the joint law of the output and the final state of a stateful oracle handler.
* `Machine.Deterministic`: the transitions ignore the coin. A machine's worst-case number of steps
  on every input and every coin sequence is at most its clock `time`.
* `Machine.cost`: `time + descLen`, where `descLen` is the length of the canonical fixed-width
  encoding of the transition table. Counting the description excludes the attackers with a
  hard-wired table that exist non-constructively at fixed parameters (Bernstein–Lange,
  De–Trevisan–Tulsiani).
* `Machine.acceptProb`, `Machine.solveProb`: success probabilities on a decision and a search
  problem.
-/

namespace SigabaNeo

open Cslib Turing

/-- An explicit machine: a fair-coin multi-tape Turing machine over `Bool` with `states` control
states, `tapes` work tapes and `ops` oracle channels, run with the clock `time`. -/
structure Machine (ops : ℕ := 0) where
  /-- Number of work tapes. -/
  tapes : ℕ
  /-- Number of control states. -/
  states : ℕ
  /-- The machine, with one query channel per oracle. -/
  machine : MultiTapePTM tapes Bool (Fin states) (Fin ops)
  /-- The clock: the number of steps it is run for. -/
  time : ℕ

namespace Machine

variable {ops : ℕ}

/-- Bits of one entry of the canonical transition table: the input head move (2 bits), for each
work tape an optional write of an optional symbol and a move (4 bits), an optional output symbol
(2 bits), for each channel an optional query symbol and an answer head move (4 bits), the channel
submitted, if any (`Nat.size ops` bits encode `0, …, ops`), and the successor state or halt
(`Nat.size s` bits). -/
def entryBits (k s ops : ℕ) : ℕ := 4 + 4 * k + 4 * ops + Nat.size ops + Nat.size s

/-- Length of the canonical fixed-width encoding of the transition table: one entry for each state,
symbol under the input head (3 values), symbols under the `k` work heads (`3^k`), symbols under the
answer heads (`3^ops`) and coin value (2). -/
def descLen (A : Machine ops) : ℕ :=
  6 * A.states * 3 ^ A.tapes * 3 ^ ops * entryBits A.tapes A.states ops

/-- Cost: steps plus description length. -/
def cost (A : Machine ops) : ℕ := A.time + A.descLen

theorem one_le_cost (A : Machine ops) : 1 ≤ A.cost := by
  have hs : 0 < A.states := Fin.pos A.machine.initial
  have h : 0 < A.descLen := by unfold descLen entryBits; positivity
  unfold cost
  omega

/-- The transitions ignore the coin, so every run is a function of the input and the replies. -/
def Deterministic (A : Machine ops) : Prop :=
  ∀ q a w o, A.machine.tr q a w o true = A.machine.tr q a w o false

/-- The joint law of the output and the final oracle state, on input `x`, against the stateful
oracle `oracle` started at `s`. Each query is the channel and the word written on it. -/
noncomputable def runWith {σ : Type} (A : Machine ops)
    (oracle : Fin ops × List Bool → StateT σ PMF (List Bool)) (x : List Bool) (s : σ) :
    PMF (List Bool × σ) :=
  ProbOracleComp.runWith oracle (A.machine.runOracle A.time x) s

/-- The output law of a machine without oracles on input `x`: the output tape after at most `time`
steps, over fresh fair coins at each step. -/
noncomputable def run (A : Machine) (x : List Bool) : PMF (List Bool) :=
  ProbComp.eval (A.machine.run (ProbComp.uniform Bool) (fun o => o.elim0) A.time x)

/-- Probability that the machine outputs `[true]` on an instance drawn from `D`. -/
noncomputable def acceptProb (A : Machine) (D : PMF (List Bool)) : ℝ :=
  ((D.bind A.run) [true]).toReal

/-- Probability that the machine outputs a solution of an instance drawn from `D`. -/
noncomputable def solveProb (A : Machine) (D : PMF (List Bool × Set (List Bool))) : ℝ :=
  (∑' z, D z * (A.run z.1).toOuterMeasure z.2).toReal

theorem acceptProb_nonneg (A : Machine) (D : PMF (List Bool)) : 0 ≤ A.acceptProb D :=
  ENNReal.toReal_nonneg

theorem acceptProb_le_one (A : Machine) (D : PMF (List Bool)) : A.acceptProb D ≤ 1 := by
  unfold acceptProb
  have h := (D.bind A.run).coe_le_one [true]
  have hne : (D.bind A.run) [true] ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top h
  exact (ENNReal.toReal_le_toReal hne ENNReal.one_ne_top).mpr h |>.trans_eq ENNReal.toReal_one

private theorem outer_le_one {α : Type} (p : PMF α) (s : Set α) : p.toOuterMeasure s ≤ 1 :=
  (p.toOuterMeasure_mono (t := Set.univ) (Set.subset_univ _)).trans
    (le_of_eq (p.toOuterMeasure_apply_eq_one_iff Set.univ |>.mpr (Set.subset_univ _)))

theorem solveProb_nonneg (A : Machine) (D : PMF (List Bool × Set (List Bool))) :
    0 ≤ A.solveProb D :=
  ENNReal.toReal_nonneg

theorem solveProb_le_one (A : Machine) (D : PMF (List Bool × Set (List Bool))) :
    A.solveProb D ≤ 1 := by
  unfold solveProb
  have h : ∑' z, D z * (A.run z.1).toOuterMeasure z.2 ≤ 1 := by
    calc ∑' z, D z * (A.run z.1).toOuterMeasure z.2 ≤ ∑' z, D z :=
          tsum_le_tsum fun z => mul_le_of_le_one_right' (outer_le_one _ _)
      _ = 1 := D.tsum_coe
  have hne : ∑' z, D z * (A.run z.1).toOuterMeasure z.2 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top h
  exact (ENNReal.toReal_le_toReal hne ENNReal.one_ne_top).mpr h |>.trans_eq ENNReal.toReal_one

end Machine

end SigabaNeo
