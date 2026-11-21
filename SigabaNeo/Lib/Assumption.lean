import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Hardness assumptions with a security function

The form of assumptions of the Sigaba Neo concept (Section 3.3), described in
`docs/ASSUMPTIONS.md`:

* `Attacker`: an explicit attacker, a fair-coin multi-tape Turing machine over `Bool`
  (cslib-frontier's `Turing.MultiTapePTM`) with `states` control states and `tapes` work tapes,
  run for `time` steps. Its cost is `time + descLen`, where `descLen` is the length of the
  canonical fixed-width encoding of its transition table. Counting the description excludes the
  attackers with a hard-wired table that exist non-constructively at fixed parameters
  (Bernstein–Lange, De–Trevisan–Tulsiani).
* `Problem`: what the attacker is given. A decision problem is a pair of laws on encoded
  instances; the attacker outputs `[true]` to say "real". A search problem is a law on pairs of an
  encoded instance and its set of encoded solutions.
* `Problem.HardAt P k`: every attacker has `cost / gain ≥ 2^k`, where the gain is the success
  probability for a search problem and the squared advantage for a decision problem
  (Micciancio–Walter). It is monotone in `k` (`Problem.HardAt.mono`) and holds at `k = 0`
  (`Problem.hardAt_zero`).
* `Assumption`: a parameter type, the problem at each parameter, and the security function `H`
  (the bits the assumption claims). `Assumption.Holds a` is the claim `∀ p, HardAt a p (H p)`.
  A submission's premise `(a, p₀, k)` with `k ≤ H p₀` follows from it (`Assumption.Holds.hardAt`).
* `Assumption.Attack a p c`: an explicit attacker with `cost ≤ 2^c · gain` and a positive gain.
  It refutes `HardAt a p k` for every `k > c` (`Assumption.Attack.not_hardAt`), which is what
  justifies lowering `H p` to `c`.
-/

namespace SigabaNeo

open Cslib

/-- An explicit attacker: a fair-coin multi-tape Turing machine over `Bool` with `states` control
states and `tapes` work tapes, run for `time` steps on the encoded instance. -/
structure Attacker where
  /-- Number of work tapes. -/
  tapes : ℕ
  /-- Number of control states. -/
  states : ℕ
  /-- The machine; it has no oracle channels. -/
  machine : Turing.MultiTapePTM tapes Bool (Fin states)
  /-- Number of steps it is run for. -/
  time : ℕ

namespace Attacker

/-- Bits of one entry of the canonical transition table: the input head move (2 bits), for each
work tape an optional write of an optional symbol and a move (4 bits), an optional output symbol
(2 bits), and the successor state or halt (`Nat.size s` bits). -/
def entryBits (k s : ℕ) : ℕ := 4 + 4 * k + Nat.size s

/-- Length of the canonical fixed-width encoding of the transition table: one entry for each state,
symbol under the input head (3 values), symbols under the `k` work heads (`3^k`) and coin value
(2). -/
def descLen (A : Attacker) : ℕ := 6 * A.states * 3 ^ A.tapes * entryBits A.tapes A.states

/-- Attack cost: steps plus description length. -/
def cost (A : Attacker) : ℕ := A.time + A.descLen

/-- The output law of the attacker on input `x`. -/
noncomputable def run (A : Attacker) (x : List Bool) : PMF (List Bool) :=
  ProbComp.eval (A.machine.runClosed A.time x)

/-- Probability that the attacker outputs `[true]` on an instance drawn from `D`. -/
noncomputable def acceptProb (A : Attacker) (D : PMF (List Bool)) : ℝ :=
  ((D.bind A.run) [true]).toReal

/-- Probability that the attacker outputs a solution of an instance drawn from `D`. -/
noncomputable def solveProb (A : Attacker) (D : PMF (List Bool × Set (List Bool))) : ℝ :=
  (∑' z, D z * (A.run z.1).toOuterMeasure z.2).toReal

theorem one_le_cost (A : Attacker) : 1 ≤ A.cost := by
  have hs : 0 < A.states := Fin.pos A.machine.initial
  have : 1 ≤ A.descLen := by
    unfold descLen entryBits
    have h3 : 0 < 3 ^ A.tapes := by positivity
    have : 1 ≤ 6 * A.states * 3 ^ A.tapes := by
      have := Nat.mul_pos (Nat.mul_pos (by norm_num : 0 < 6) hs) h3
      omega
    calc 1 ≤ 6 * A.states * 3 ^ A.tapes := this
      _ ≤ 6 * A.states * 3 ^ A.tapes * (4 + 4 * A.tapes + Nat.size A.states) :=
        Nat.le_mul_of_pos_right _ (by omega)
  unfold cost
  omega

theorem acceptProb_nonneg (A : Attacker) (D : PMF (List Bool)) : 0 ≤ A.acceptProb D :=
  ENNReal.toReal_nonneg

theorem acceptProb_le_one (A : Attacker) (D : PMF (List Bool)) : A.acceptProb D ≤ 1 := by
  unfold acceptProb
  have h := (D.bind A.run).coe_le_one [true]
  have hne : (D.bind A.run) [true] ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top h
  exact (ENNReal.toReal_le_toReal hne ENNReal.one_ne_top).mpr h |>.trans_eq ENNReal.toReal_one

private theorem outer_le_one {α : Type} (p : PMF α) (s : Set α) : p.toOuterMeasure s ≤ 1 :=
  (p.toOuterMeasure_mono (t := Set.univ) (Set.subset_univ _)).trans
    (le_of_eq (p.toOuterMeasure_apply_eq_one_iff Set.univ |>.mpr (Set.subset_univ _)))

theorem solveProb_nonneg (A : Attacker) (D : PMF (List Bool × Set (List Bool))) :
    0 ≤ A.solveProb D :=
  ENNReal.toReal_nonneg

theorem solveProb_le_one (A : Attacker) (D : PMF (List Bool × Set (List Bool))) :
    A.solveProb D ≤ 1 := by
  unfold solveProb
  have h : ∑' z, D z * (A.run z.1).toOuterMeasure z.2 ≤ 1 := by
    calc ∑' z, D z * (A.run z.1).toOuterMeasure z.2 ≤ ∑' z, D z :=
          tsum_le_tsum fun z => mul_le_of_le_one_right' (outer_le_one _ _)
      _ = 1 := D.tsum_coe
  have hne : ∑' z, D z * (A.run z.1).toOuterMeasure z.2 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top h
  exact (ENNReal.toReal_le_toReal hne ENNReal.one_ne_top).mpr h |>.trans_eq ENNReal.toReal_one

end Attacker

/-- What an attacker is given: a decision problem (two laws on encoded instances) or a search
problem (a law on encoded instances with their sets of encoded solutions). -/
inductive Problem where
  /-- Distinguish `real` from `ideal`; the attacker outputs `[true]` for "real". -/
  | decision (real ideal : PMF (List Bool))
  /-- Output a solution of the instance. -/
  | search (instances : PMF (List Bool × Set (List Bool)))

namespace Problem

/-- The attacker's gain: the squared advantage, or the success probability. -/
noncomputable def gain : Problem → Attacker → ℝ
  | .decision real ideal, A => (A.acceptProb real - A.acceptProb ideal) ^ 2
  | .search instances, A => A.solveProb instances

theorem gain_nonneg (P : Problem) (A : Attacker) : 0 ≤ P.gain A := by
  cases P with
  | decision real ideal => exact sq_nonneg _
  | search instances => exact A.solveProb_nonneg instances

theorem gain_le_one (P : Problem) (A : Attacker) : P.gain A ≤ 1 := by
  cases P with
  | decision real ideal =>
    have h1 := A.acceptProb_nonneg real
    have h2 := A.acceptProb_le_one real
    have h3 := A.acceptProb_nonneg ideal
    have h4 := A.acceptProb_le_one ideal
    show (A.acceptProb real - A.acceptProb ideal) ^ 2 ≤ 1
    nlinarith
  | search instances => exact A.solveProb_le_one instances

/-- `k` bits of strength: every attacker has `cost / gain ≥ 2^k`. -/
def HardAt (P : Problem) (k : ℕ) : Prop :=
  ∀ A : Attacker, (2 : ℝ) ^ k * P.gain A ≤ A.cost

/-- Fewer bits follow from more. -/
theorem HardAt.mono {P : Problem} {k k' : ℕ} (h : P.HardAt k) (hk : k' ≤ k) : P.HardAt k' :=
  fun A => (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk)
    (P.gain_nonneg A)).trans (h A)

/-- Zero bits are always there: gains are at most `1` and costs at least `1`. -/
theorem hardAt_zero (P : Problem) : P.HardAt 0 := fun A => by
  simp only [pow_zero, one_mul]
  exact (P.gain_le_one A).trans (by exact_mod_cast A.one_le_cost)

end Problem

/-- A hardness assumption: parameters, the problem at each parameter, and the security function
`H`, the number of bits claimed at each parameter. -/
structure Assumption where
  /-- The parameter set. -/
  Params : Type
  /-- The problem given to the attacker at each parameter. -/
  problem : Params → Problem
  /-- The security function: bits claimed at each parameter. -/
  H : Params → ℕ

namespace Assumption

/-- `HardAt a p k`: at parameters `p`, every attacker has `cost / gain ≥ 2^k`. -/
def HardAt (a : Assumption) (p : a.Params) (k : ℕ) : Prop := (a.problem p).HardAt k

/-- The claim of the assumption: `H p` bits at every parameter `p`. -/
def Holds (a : Assumption) : Prop := ∀ p, a.HardAt p (a.H p)

/-- A premise `(a, p, k)` with `k ≤ H p` follows from the assumption. -/
theorem Holds.hardAt {a : Assumption} (h : a.Holds) {p : a.Params} {k : ℕ} (hk : k ≤ a.H p) :
    a.HardAt p k :=
  Problem.HardAt.mono (h p) hk

/-- An explicit attack at `p` with `cost / gain ≤ 2^c`. -/
def Attack (a : Assumption) (p : a.Params) (c : ℕ) : Prop :=
  ∃ A : Attacker, 0 < (a.problem p).gain A ∧ (A.cost : ℝ) ≤ 2 ^ c * (a.problem p).gain A

/-- An attack with `cost / gain ≤ 2^c` refutes every strength above `c`. -/
theorem Attack.not_hardAt {a : Assumption} {p : a.Params} {c k : ℕ} (h : a.Attack p c)
    (hk : c < k) : ¬ a.HardAt p k := by
  intro hh
  obtain ⟨A, hpos, hA⟩ := h
  have h1 := hh A
  have h2 : (2 : ℝ) ^ k * (a.problem p).gain A ≤ 2 ^ c * (a.problem p).gain A := h1.trans hA
  have h3 : (2 : ℝ) ^ k ≤ 2 ^ c := le_of_mul_le_mul_right h2 hpos
  have h4 : (2 : ℝ) ^ c < 2 ^ k := pow_lt_pow_right₀ (by norm_num) hk
  linarith

/-- An attack bounds the strength that can hold: `HardAt a p k` and an attack at `c` give
`k ≤ c`. -/
theorem Attack.le {a : Assumption} {p : a.Params} {c k : ℕ} (h : a.Attack p c)
    (hh : a.HardAt p k) : k ≤ c := by
  by_contra hk
  exact h.not_hardAt (Nat.lt_of_not_le hk) hh

end Assumption

end SigabaNeo
