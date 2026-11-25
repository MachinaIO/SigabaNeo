import SigabaNeoStd.Machines.Inline.Prep
import Mathlib.Data.Nat.Size

/-!
# Inlining an oracle handler into a machine

`Machine.inlineOracle A H w Q L` runs the oracle machine `A : Machine ops` together with handler
routines `H o` (one per channel, `m + 3` tapes each: query, answer, state, `m` scratch) as one
closed `Machine`. The handler state is kept encoded on a tape, initially `w`.

Hypotheses (`Handles`): for every query `b` of length at most `A.time` and every state `s` with
`InvS s`, `H o` turns the words `(b, [], enc s, [], …)` into `(b, a, enc s', [], …)` with
`(a, s')` drawn from `oracle (o, b) s` (`Routine.Runs`), within its clock `(H o).time ≤ Q`; the
oracle keeps `InvS` and its answers have length at most `L`.

## Main results

* `Machine.law_inlineOracle`: the joint law of the output and of the state tape of the inlined
  machine is that of the output and of the encoded final state of `A.runWith oracle x s₀`;
* `Machine.run_inlineOracle`: its output law is that of `A.runWith oracle x s₀`;
* `Machine.tapes_inlineOracle`, `Machine.states_inlineOracle`, `Machine.time_inlineOracle`: the
  exact number of tapes `A.tapes + 2 ops + 2 + m`, of states
  `(2 |w| + A.time + 1) + A.states * 3 ^ ops * (1 + ∑ o, (9 + (H o).states))`, and the clock
  `2 |w| + A.time + 2 + A.time * (Q + 2 L + 4 ops + 9)`;
* `Machine.descLen_inlineOracle_le`, `Machine.cost_inlineOracle_le`: with
  `Y = A.cost + 2 |w| + 1`, `descLen ≤ C_H * Y ^ 2 * Nat.size Y` and
  `cost ≤ C_H * Y ^ 2 * Nat.size Y + (Q + 2 L + 4 ops + 10) * Y`, where `C_H` depends only on
  `ops`, `m` and the numbers of states of the handlers.
-/

namespace SigabaNeo

open Cslib Turing MultiTapeMachine Inline

variable {ops m : ℕ}

/-- The clock of the inlined machine. -/
def inlineTime (T wl Q L ops : ℕ) : ℕ := 2 * wl + T + 1 + (T * (Q + 2 * L + 4 * ops + 9) + 1)

/-- **The inlined machine**: `A` with its queries answered by the handlers `H`, the handler state
initially encoded as `w`. -/
noncomputable def Machine.inlineOracle (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (w : List Bool) (Q L : ℕ) : Machine :=
  Machine.ofPTMOps (Inline.machine H A.machine A.time w) (inlineTime A.time w.length Q L ops)

/-- The handlers realize the oracle on the encoded states satisfying `InvS`, within `Q` steps,
with answers of length at most `L`. -/
structure Handles {σ : Type} (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (oracle : Fin ops × List Bool → StateT σ PMF (List Bool)) (enc : σ → List Bool)
    (InvS : σ → Prop) (Q L : ℕ) : Prop where
  time_le : ∀ o, (H o).time ≤ Q
  runs : ∀ o b s, b.length ≤ A.time → InvS s →
    (H o).Runs (layout b [] (enc s)) ((oracle (o, b) s).map (fun r => layout b r.1 (enc r.2)))
  inv : ∀ o b s, b.length ≤ A.time → InvS s → ∀ r ∈ (oracle (o, b) s).support,
    InvS r.2 ∧ r.1.length ≤ L

/-- **The law of the inlined machine**: the output and the state tape of its final configuration
are distributed as the output and the encoded final state of `A` against the oracle. -/
theorem Machine.law_inlineOracle {σ : Type} (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (oracle : Fin ops × List Bool → StateT σ PMF (List Bool)) (enc : σ → List Bool)
    (InvS : σ → Prop) (Q L : ℕ) (hH : Handles A H oracle enc InvS Q L) (s₀ : σ) (hs₀ : InvS s₀)
    (x : List Bool) :
    (lawR H A.machine A.time (enc s₀) (inlineTime A.time (enc s₀).length Q L ops)
        ((Inline.machine H A.machine A.time (enc s₀)).initialConfig x)).map projR =
      (A.runWith oracle x s₀).map (fun r => (r.1, tapeOfList (enc r.2))) := by
  unfold inlineTime
  rw [lawR_prep]
  have hgood : Good A.time L InvS A.time (A.machine.initialConfig x) s₀ (fun _ => .empty) :=
    ⟨le_rfl, fun o => by simp [MultiTapeMachine.initialConfig],
      fun o => by simp [MultiTapeMachine.initialConfig],
      fun o => by simp [MultiTapeMachine.initialConfig], hs₀⟩
  have hpot : pot (A.machine.initialConfig x) = 0 := by
    simp [pot, MultiTapeMachine.initialConfig]
  rw [(lawR_embA H A.machine A.time (enc s₀) oracle enc InvS L Q hH.time_le hH.runs hH.inv
    A.time _ s₀ _ hgood _ (by rw [hpot])).2]
  unfold Machine.runWith lawA
  rw [MultiTapePTM.runOracle_eq_map, ProbOracleComp.runWith_map, PMF.map_comp]
  rfl

/-- **The output law of the inlined machine** is that of `A` against the oracle. -/
theorem Machine.run_inlineOracle {σ : Type} (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (oracle : Fin ops × List Bool → StateT σ PMF (List Bool)) (enc : σ → List Bool)
    (InvS : σ → Prop) (Q L : ℕ) (hH : Handles A H oracle enc InvS Q L) (s₀ : σ) (hs₀ : InvS s₀)
    (x : List Bool) :
    (A.inlineOracle H (enc s₀) Q L).run x = (A.runWith oracle x s₀).map Prod.fst := by
  have h := congrArg (PMF.map Prod.fst) (A.law_inlineOracle H oracle enc InvS Q L hH s₀ hs₀ x)
  rw [PMF.map_comp, PMF.map_comp] at h
  rw [Machine.run_eq_runWith _ (fun e : Fin 0 × List Bool => e.1.elim0) x (),
    Machine.inlineOracle, Machine.runWith_ofPTMOps, MultiTapePTM.runOracle_eq_map,
    ProbOracleComp.runWith_map, PMF.map_comp]
  exact h

/-! ### Explicit bounds -/

@[simp] theorem Machine.tapes_inlineOracle (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (w : List Bool) (Q L : ℕ) : (A.inlineOracle H w Q L).tapes = A.tapes + 2 * ops + 2 + m := rfl

@[simp] theorem Machine.time_inlineOracle (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (w : List Bool) (Q L : ℕ) :
    (A.inlineOracle H w Q L).time = inlineTime A.time w.length Q L ops := rfl

/-- The number of states of the inlined machine. -/
def inlineStates (A : Machine ops) (H : Fin ops → Routine (m + 3)) (wl : ℕ) : ℕ :=
  (2 * wl + A.time + 1) + A.states * 3 ^ ops * (1 + ∑ o, (9 + (H o).states))

theorem Machine.states_inlineOracle (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (w : List Bool) (Q L : ℕ) :
    (A.inlineOracle H w Q L).states = inlineStates A H w.length := by
  simp only [Machine.inlineOracle, Machine.states_ofPTMOps, RState, Ctl, inlineStates,
    Fintype.card_sum, Fintype.card_fin, Fintype.card_prod, Fintype.card_option,
    Fintype.card_sigma, Fintype.card_pi, AFlag.card, QStep.card, Finset.prod_const,
    Finset.card_univ, Routine.states]
  ring

theorem Machine.time_inlineOracle_le (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (w : List Bool) (Q L : ℕ) :
    (A.inlineOracle H w Q L).time ≤ A.time * (Q + 2 * L + 4 * ops + 10) + 2 * w.length + 2 := by
  simp only [Machine.time_inlineOracle, inlineTime]
  nlinarith

theorem size_mul_le' (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)

/-- The factor of the description length bound: it depends only on `ops`, `m` and the numbers of
states of the handlers. -/
def inlineFactor (H : Fin ops → Routine (m + 3)) : ℕ :=
  let Z := 1 + ∑ o, (9 + (H o).states)
  3 ^ (2 * ops + 2 + m) * (1 + Z) * (13 + 8 * ops + 4 * m + Nat.size (1 + Z))

/-- **Description length of the inlined machine.** With `Y = A.cost + 2 |w| + 1`,
`descLen ≤ C_H * Y ^ 2 * Nat.size Y`. -/
theorem Machine.descLen_inlineOracle_le (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (w : List Bool) (Q L : ℕ) :
    (A.inlineOracle H w Q L).descLen ≤
      inlineFactor H * (A.cost + 2 * w.length + 1) ^ 2 *
        Nat.size (A.cost + 2 * w.length + 1) := by
  set Y := A.cost + 2 * w.length + 1 with hY
  set Z := 1 + ∑ o, (9 + (H o).states) with hZ
  set D := A.descLen with hD
  set SR := inlineStates A H w.length with hSR
  set P := 2 * w.length + A.time + 1 with hP
  have hDY : D ≤ Y := by simp only [hY, hD, Machine.cost]; omega
  have hPY : P ≤ Y := by simp only [hY, hP, Machine.cost]; omega
  have hY1 : 1 ≤ Y := by omega
  have hsY : 1 ≤ Nat.size Y := Nat.lt_size.mpr (by simpa using hY1)
  -- the parts of the description length of `A`
  have h3D : 6 * 3 ^ A.tapes ≤ D := by
    have hs : 0 < A.states := Fin.pos A.machine.initial
    have he : 1 ≤ Machine.entryBits A.tapes A.states ops := by unfold Machine.entryBits; omega
    simp only [hD, Machine.descLen]
    calc 6 * 3 ^ A.tapes = 6 * 1 * 3 ^ A.tapes * 1 * 1 := by ring
      _ ≤ 6 * A.states * 3 ^ A.tapes * 3 ^ ops * Machine.entryBits A.tapes A.states ops := by
        gcongr <;> first | omega | exact Nat.one_le_pow _ _ (by norm_num)
  have hSD : 6 * A.states * 3 ^ A.tapes * 3 ^ ops ≤ D := by
    have he : 1 ≤ Machine.entryBits A.tapes A.states ops := by unfold Machine.entryBits; omega
    simp only [hD, Machine.descLen]
    exact Nat.le_mul_of_pos_right _ he
  have hkA : A.tapes < Nat.size Y := by
    rw [Nat.lt_size]
    calc 2 ^ A.tapes ≤ 3 ^ A.tapes := Nat.pow_le_pow_left (by norm_num) _
      _ ≤ D := by omega
      _ ≤ Y := hDY
  -- states
  have hSRY : SR ≤ (1 + Z) * Y := by
    have : A.states * 3 ^ ops * Z ≤ Z * Y := by
      have : A.states * 3 ^ ops ≤ Y := by
        have : A.states * 3 ^ ops ≤ 6 * A.states * 3 ^ A.tapes * 3 ^ ops := by
          have := Nat.one_le_pow A.tapes 3 (by norm_num)
          nlinarith [Nat.zero_le (A.states * 3 ^ ops)]
        omega
      nlinarith
    simp only [hSR, inlineStates, ← hZ, ← hP]
    nlinarith
  -- the number of states times the table rows per state
  have hrows : 6 * SR * 3 ^ (A.tapes + 2 * ops + 2 + m) ≤
      3 ^ (2 * ops + 2 + m) * ((1 + Z) * Y * Y) := by
    have hrow : 6 * SR * 3 ^ A.tapes ≤ (1 + Z) * Y * Y := by
      simp only [hSR, inlineStates, ← hZ, ← hP]
      have h1 : 6 * P * 3 ^ A.tapes ≤ Y * Y := by
        calc 6 * P * 3 ^ A.tapes = P * (6 * 3 ^ A.tapes) := by ring
          _ ≤ Y * Y := Nat.mul_le_mul hPY (h3D.trans hDY)
      have h2 : 6 * (A.states * 3 ^ ops * Z) * 3 ^ A.tapes ≤ Z * Y * Y := by
        calc 6 * (A.states * 3 ^ ops * Z) * 3 ^ A.tapes
            = Z * (6 * A.states * 3 ^ A.tapes * 3 ^ ops) := by ring
          _ ≤ Z * Y * 1 := by rw [Nat.mul_one]; exact Nat.mul_le_mul_left _ (hSD.trans hDY)
          _ ≤ Z * Y * Y := Nat.mul_le_mul_left _ hY1
      nlinarith
    calc 6 * SR * 3 ^ (A.tapes + 2 * ops + 2 + m)
        = 3 ^ (2 * ops + 2 + m) * (6 * SR * 3 ^ A.tapes) := by
          rw [show A.tapes + 2 * ops + 2 + m = A.tapes + (2 * ops + 2 + m) by omega, pow_add]
          ring
      _ ≤ _ := Nat.mul_le_mul_left _ hrow
  -- the entry width
  have hentry : Machine.entryBits (A.tapes + 2 * ops + 2 + m) SR 0 ≤
      (13 + 8 * ops + 4 * m + Nat.size (1 + Z)) * Nat.size Y := by
    have hsSR : Nat.size SR ≤ Nat.size (1 + Z) + Nat.size Y :=
      (Nat.size_le_size hSRY).trans (size_mul_le' _ _)
    simp only [Machine.entryBits, Nat.size_zero]
    have h1 := Nat.mul_le_mul_left (8 * ops + 4 * m + Nat.size (1 + Z)) hsY
    have h2 : 4 * A.tapes + 4 ≤ 4 * Nat.size Y := by omega
    nlinarith
  have hdesc : (A.inlineOracle H w Q L).descLen =
      6 * SR * 3 ^ (A.tapes + 2 * ops + 2 + m) * 3 ^ 0 *
        Machine.entryBits (A.tapes + 2 * ops + 2 + m) SR 0 := by
    rw [Machine.descLen, Machine.states_inlineOracle, Machine.tapes_inlineOracle]
  rw [hdesc, pow_zero, Nat.mul_one]
  calc 6 * SR * 3 ^ (A.tapes + 2 * ops + 2 + m) * Machine.entryBits (A.tapes + 2 * ops + 2 + m) SR 0
      ≤ (3 ^ (2 * ops + 2 + m) * ((1 + Z) * Y * Y)) *
          ((13 + 8 * ops + 4 * m + Nat.size (1 + Z)) * Nat.size Y) :=
        Nat.mul_le_mul hrows hentry
    _ = inlineFactor H * Y ^ 2 * Nat.size Y := by
        simp only [inlineFactor, ← hZ]; ring

/-- **Cost of the inlined machine.** With `Y = A.cost + 2 |w| + 1`,
`cost ≤ C_H * Y ^ 2 * Nat.size Y + (Q + 2 L + 4 ops + 10) * Y`. -/
theorem Machine.cost_inlineOracle_le (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (w : List Bool) (Q L : ℕ) :
    (A.inlineOracle H w Q L).cost ≤
      inlineFactor H * (A.cost + 2 * w.length + 1) ^ 2 * Nat.size (A.cost + 2 * w.length + 1) +
        (Q + 2 * L + 4 * ops + 10) * (A.cost + 2 * w.length + 1) := by
  have ht := A.time_inlineOracle_le H w Q L
  have hd := A.descLen_inlineOracle_le H w Q L
  have hT : A.time ≤ A.cost := by unfold Machine.cost; omega
  have h1 := Nat.mul_le_mul_left (Q + 2 * L + 4 * ops + 10) hT
  have h2 : (Q + 2 * L + 4 * ops + 10) * (A.cost + 2 * w.length + 1) =
      (Q + 2 * L + 4 * ops + 10) * A.cost + (Q + 2 * L + 4 * ops + 10) * (2 * w.length) +
        (Q + 2 * L + 4 * ops + 10) := by ring
  have h3 : 2 * w.length ≤ (Q + 2 * L + 4 * ops + 10) * (2 * w.length) :=
    Nat.le_mul_of_pos_left _ (by omega)
  rw [Machine.cost]
  nlinarith

end SigabaNeo
