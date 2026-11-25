import SigabaNeo.Trusted.Machine

/-!
# Hardness assumptions with a security function

The form of assumptions of the Sigaba Neo concept (Section 3.3), described in
`docs/ASSUMPTIONS.md`:

* Attackers are explicit machines without oracles (`Machine`, `SigabaNeo.Trusted.Machine`). An
  attacker's cost is `Machine.cost`: steps plus the description length of its transition table.
* `Problem`: what the attacker is given. A decision problem is a pair of laws on encoded
  instances; the attacker outputs `[true]` to say "real". A search problem is a law on pairs of an
  encoded instance and its set of encoded solutions.
* `Problem.HardAt P k`: every attacker has `cost / gain ≥ 2^k`, where the gain is the success
  probability for a search problem and the squared advantage for a decision problem
  (Micciancio–Walter). It is monotone in `k` (`Problem.HardAt.mono`) and holds at `k = 0`
  (`Problem.hardAt_zero`).
* `Assumption`: a parameter type, the problem at each parameter, and the security function `H`
  (the bits the assumption claims). `Assumption.Holds a` is the claim `∀ p, HardAt a p (H p)`.
  A premise `(a, p₀, k)` with `k ≤ H p₀` follows from it (`Assumption.Holds.hardAt`).
* `Assumption.Attack a p c`: an explicit attacker with `cost ≤ 2^c · gain` and a positive gain.
  It refutes `HardAt a p k` for every `k > c` (`Assumption.Attack.not_hardAt`), which is what
  justifies lowering `H p` to `c`.
* `Assumption.Lowering a H H'`: `H'` lowers the security function `H` (`H' ≤ H` everywhere, and an
  attack at `H' p` wherever it is strictly lower). This is the form of every update of a strength
  in the DAG (`docs/ASSUMPTIONS.md`, "Lowerings"): an attack on a region of parameters is a
  new security function with that region lowered. Lowerings compose (`Lowering.trans`), and one
  refutes every claim above the new value (`Lowering.not_hardAt`).
* `Registry`: the assumptions the harness admits, by name: the parameter set and the problem of
  each, which never change. Their current strengths are kept apart (`Registry.Strength`), because
  the harness lowers them when attacks are proven. `Registry.of` registers `Assumption`s, with
  their `H` as the initial strengths (`Registry.initial`). `Registry.univ` names every assumption
  by itself; which ones are registered, and at which strength, is the harness's (the DAG's), so a
  submission over it may use any assumption registered at any time. `Registry.Holds R H n`:
  assumption `n` has the strength `H n p` at every `p`; lowering `H` keeps it
  (`Registry.Holds.mono`).
* `Premise R`: a triple `(n, p₀, k)`, "the registered assumption `n` has `k` bits at `p₀`", as a
  submission lists them. `Premise.Valid H`: `k ≤ H n p₀` for the harness's current strengths `H`,
  the numerical check; with `R.Holds H n` it gives `HardAt` (`Premise.hardAt`).
-/

namespace SigabaNeo

universe u

open Cslib

/-- What an attacker is given: a decision problem (two laws on encoded instances) or a search
problem (a law on encoded instances with their sets of encoded solutions). -/
inductive Problem where
  /-- Distinguish `real` from `ideal`; the attacker outputs `[true]` for "real". -/
  | decision (real ideal : PMF (List Bool))
  /-- Output a solution of the instance. -/
  | search (instances : PMF (List Bool × Set (List Bool)))

namespace Problem

/-- The attacker's gain: the squared advantage, or the success probability. -/
noncomputable def gain : Problem → Machine → ℝ
  | .decision real ideal, A => (A.acceptProb real - A.acceptProb ideal) ^ 2
  | .search instances, A => A.solveProb instances

theorem gain_nonneg (P : Problem) (A : Machine) : 0 ≤ P.gain A := by
  cases P with
  | decision real ideal => exact sq_nonneg _
  | search instances => exact A.solveProb_nonneg instances

theorem gain_le_one (P : Problem) (A : Machine) : P.gain A ≤ 1 := by
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
  ∀ A : Machine, (2 : ℝ) ^ k * P.gain A ≤ A.cost

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
  ∃ A : Machine, 0 < (a.problem p).gain A ∧ (A.cost : ℝ) ≤ 2 ^ c * (a.problem p).gain A

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

/-- `H'` lowers the security function `H`: it is nowhere higher, and wherever it is strictly lower
an explicit attack reaches it. -/
def Lowering (a : Assumption) (H H' : a.Params → ℕ) : Prop :=
  ∀ p, H' p ≤ H p ∧ (H' p < H p → a.Attack p (H' p))

/-- Every security function lowers itself (no parameter is strictly lower). -/
theorem Lowering.refl (a : Assumption) (H : a.Params → ℕ) : a.Lowering H H :=
  fun _ => ⟨le_rfl, fun h => absurd h (lt_irrefl _)⟩

/-- Lowerings compose. -/
theorem Lowering.trans {a : Assumption} {H H' H'' : a.Params → ℕ} (h₁ : a.Lowering H H')
    (h₂ : a.Lowering H' H'') : a.Lowering H H'' := fun p => by
  obtain ⟨le₁, at₁⟩ := h₁ p
  obtain ⟨le₂, at₂⟩ := h₂ p
  refine ⟨le₂.trans le₁, fun hlt => ?_⟩
  rcases lt_or_eq_of_le le₂ with h | h
  · exact at₂ h
  · rw [h] at hlt ⊢
    exact at₁ hlt

/-- A lowering refutes every claim above the new value where it is strictly lower. -/
theorem Lowering.not_hardAt {a : Assumption} {H H' : a.Params → ℕ} (h : a.Lowering H H')
    {p : a.Params} (hlt : H' p < H p) {k : ℕ} (hk : H' p < k) : ¬ a.HardAt p k :=
  ((h p).2 hlt).not_hardAt hk

/-- A lowering keeps every true claim: if `H p` bits hold, so do `H' p` bits. -/
theorem Lowering.hardAt {a : Assumption} {H H' : a.Params → ℕ} (h : a.Lowering H H')
    {p : a.Params} (hh : a.HardAt p (H p)) : a.HardAt p (H' p) :=
  Problem.HardAt.mono hh (h p).1

end Assumption

/-! ### The registry of assumptions and premises -/

/-- The assumptions the harness admits, by name: the parameter set and the problem given to the
attacker of each. These never change; the strengths are kept apart (`Registry.Strength`). -/
structure Registry where
  /-- The names of the registered assumptions. -/
  Name : Type u
  /-- The parameter set of each assumption. -/
  Params : Name → Type
  /-- The problem given to the attacker at each parameter. -/
  problem : (n : Name) → Params n → Problem

namespace Registry

/-- `HardAt n p k`: at parameters `p`, every attacker on assumption `n` has `cost / gain ≥ 2^k`. -/
def HardAt (R : Registry.{u}) (n : R.Name) (p : R.Params n) (k : ℕ) : Prop :=
  (R.problem n p).HardAt k

/-- The strengths the harness currently assigns: bits claimed for each assumption at each
parameter. The harness only lowers them, by proven attacks (`Assumption.Attack`). -/
def Strength (R : Registry.{u}) : Type u := (n : R.Name) → R.Params n → ℕ

/-- Assumption `n` has the strength `H n p` at every parameter `p`. -/
def Holds (R : Registry.{u}) (H : R.Strength) (n : R.Name) : Prop := ∀ p, R.HardAt n p (H n p)

/-- Lowering a strength keeps every true claim. -/
theorem Holds.mono {R : Registry.{u}} {H H' : R.Strength} {n : R.Name} (h : R.Holds H n)
    (hle : ∀ p, H' n p ≤ H n p) : R.Holds H' n :=
  fun p => Problem.HardAt.mono (h p) (hle p)

/-- The registry of the assumptions `as`. -/
def of {Name : Type} (as : Name → Assumption) : Registry where
  Name := Name
  Params n := (as n).Params
  problem n := (as n).problem

/-- The initial strengths of registered assumptions: their own security functions. -/
def initial {Name : Type} (as : Name → Assumption) : (of as).Strength := fun n => (as n).H

/-- A registered assumption whose claim holds holds at its initial strength. -/
theorem holds_initial {Name : Type} {as : Name → Assumption} {n : Name} (h : (as n).Holds) :
    (of as).Holds (initial as) n :=
  h

/-- Every assumption, named by itself. Which assumptions are registered and their current
strengths are the harness's: a premise naming an unregistered one has strength `0`, so it can only
ask for `0` bits, which always hold (`Problem.hardAt_zero`). -/
def univ : Registry.{1} where
  Name := Assumption
  Params a := a.Params
  problem a := a.problem

end Registry

/-- A premise: the registered assumption `n` has `k` bits of strength at its parameters `p`. -/
structure Premise (R : Registry.{u}) where
  /-- The name of the assumption. -/
  n : R.Name
  /-- Its parameters. -/
  p : R.Params n
  /-- The bits of strength needed. -/
  k : ℕ

namespace Premise

variable {R : Registry.{u}}

/-- The premise as a proposition: `HardAt n p k`. -/
def Holds (d : Premise R) : Prop := R.HardAt d.n d.p d.k

/-- The premise asks for at most the current strength of its assumption: `k ≤ H n p`. -/
def Valid (H : R.Strength) (d : Premise R) : Prop := d.k ≤ H d.n d.p

/-- A valid premise follows from its assumption at the current strengths. -/
theorem hardAt {H : R.Strength} {d : Premise R} (hv : d.Valid H) (h : R.Holds H d.n) : d.Holds :=
  Problem.HardAt.mono (h d.p) hv

end Premise

end SigabaNeo
