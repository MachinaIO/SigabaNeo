import SigabaNeoStd.Machines.Inline.InitMain
import SigabaNeoStd.Machines.Inline.LinCost

/-!
# Inlining an oracle handler for a reduction: explicit bounds

* `Machine.tapes_inlineOracleInit`, `Machine.states_inlineOracleInit`, `Machine.time_inlineOracleInit`:
  `A.tapes + 2 ops + 2 + m` tapes; `(h + 4) + 3 ^ ops Z + 9 + A.states (|w₀| + 2) 3 ^ ops Z`
  states, with `Z = 1 + ∑ o, (9 + (H o).states)` and `h` the number of digits of `A.time + 1`;
  the clock `inlineTimeInit`;
* `Machine.time_inlineOracleInit_le`: `time ≤ A.time * (Q + 2 L + 4 ops + 17) + 4 E + 21`;
* `Machine.descLen_inlineOracleInit_le`: the description length is at most `10` times that of
  `(A.fixInput w₀).inlineOracleLin H Q L`, so at most
  `10 * linDescFactor H * fixFactor |w₀| * A.cost`;
* `Machine.cost_inlineOracleInit_le`: `cost ≤ initFactor H Q L |w₀| E * A.cost`, where
  `initFactor` depends only on `ops`, `m`, the numbers of states of the handlers, `Q`, `L`, `|w₀|`
  and `E`.
-/

namespace SigabaNeo

open Cslib Turing MultiTapeMachine Inline

variable {ops m : ℕ}

/-- One more unit adds at most one digit. -/
theorem digits_length_succ_le (b n : ℕ) (hb : 2 ≤ b) :
    (Nat.digits b (n + 1)).length ≤ (Nat.digits b n).length + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.digits_def' (by omega) (by omega)]
    simp [Nat.div_eq_of_lt (show 1 < b by omega)]
  · rw [Nat.length_digits b (n + 1) (by omega) (by omega), Nat.length_digits b n (by omega) (by omega)]
    have h1 : n + 1 ≤ n * b := by nlinarith
    have h2 := Nat.log_mono_right (b := b) h1
    rw [Nat.log_mul_base (by omega) (by omega)] at h2
    omega

theorem clockDigits_succ_le (kA T : ℕ) :
    (clockDigits kA (T + 1)).length ≤ (clockDigits kA T).length + 1 :=
  digits_length_succ_le _ _ (baseB_two_le (kA := kA))

@[simp] theorem Machine.tapes_inlineOracleInit (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (w₀ : List Bool) (E Q L : ℕ) :
    (A.inlineOracleInit H w₀ E Q L).tapes = A.tapes + 2 * ops + 2 + m := rfl

@[simp] theorem Machine.time_inlineOracleInit (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (w₀ : List Bool) (E Q L : ℕ) :
    (A.inlineOracleInit H w₀ E Q L).time =
      inlineTimeInit A.time (clockDigits A.tapes (A.time + 1)).length Q L ops E := rfl

/-- The number of states of the inlined machine for reductions. -/
def inlineStatesInit (A : Machine ops) (H : Fin ops → Routine (m + 3)) (wl : ℕ) : ℕ :=
  ((clockDigits A.tapes (A.time + 1)).length + 4) + 3 ^ ops * (1 + ∑ o, (9 + (H o).states)) + 9 +
    A.states * (wl + 2) * 3 ^ ops * (1 + ∑ o, (9 + (H o).states))

theorem Machine.states_inlineOracleInit (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (w₀ : List Bool) (E Q L : ℕ) :
    (A.inlineOracleInit H w₀ E Q L).states = inlineStatesInit A H w₀.length := by
  simp only [Machine.inlineOracleInit, Machine.states_ofPTMOps, IState, LState, Ctl,
    inlineStatesInit, Fintype.card_sum, Fintype.card_fin, Fintype.card_prod, Fintype.card_option,
    Fintype.card_sigma, Fintype.card_pi, AFlag.card, QStep.card, LStep.card, CStep.card,
    OStep.card, Finset.prod_const, Finset.card_univ, Routine.states, Fintype.card_unit]
  ring

/-- **The clock**: `time ≤ A.time * (Q + 2 L + 4 ops + 17) + 4 E + 21`. -/
theorem Machine.time_inlineOracleInit_le (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (w₀ : List Bool) (E Q L : ℕ) :
    (A.inlineOracleInit H w₀ E Q L).time ≤ A.time * (Q + 2 * L + 4 * ops + 17) + 4 * E + 21 := by
  have h1 := clockDigits_length_le_size A.tapes (A.time + 1)
  have h2 := size_le_self' (A.time + 1)
  simp only [Machine.time_inlineOracleInit, inlineTimeInit]
  nlinarith

/-- The number of states is at most five times that of `(A.fixInput w₀).inlineOracleLin H Q L`. -/
theorem inlineStatesInit_le (A : Machine ops) (H : Fin ops → Routine (m + 3)) (w₀ : List Bool) :
    inlineStatesInit A H w₀.length ≤ 5 * inlineStatesLin (A.fixInput w₀) H := by
  have hd := clockDigits_succ_le A.tapes A.time
  have hs : 0 < A.states := Fin.pos A.machine.initial
  have hG : 3 ^ ops * (1 + ∑ o, (9 + (H o).states)) ≤
      A.states * (w₀.length + 2) * 3 ^ ops * (1 + ∑ o, (9 + (H o).states)) := by
    rw [Nat.mul_assoc (A.states * (w₀.length + 2))]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  simp only [inlineStatesInit, inlineStatesLin, Machine.states_fixInput, Machine.tapes_fixInput,
    Machine.time_fixInput]
  omega

/-- **Description length of the inlined machine for reductions**: at most ten times that of the
inlined machine with a short preparation for `A` on the fixed input. -/
theorem Machine.descLen_inlineOracleInit_le (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (w₀ : List Bool) (E Q L : ℕ) :
    (A.inlineOracleInit H w₀ E Q L).descLen ≤
      10 * ((A.fixInput w₀).inlineOracleLin H Q L).descLen := by
  set S := inlineStatesInit A H w₀.length with hSd
  set S' := inlineStatesLin (A.fixInput w₀) H with hS'd
  set K := A.tapes + 2 * ops + 2 + m with hK
  have hS := inlineStatesInit_le A H w₀
  rw [← hSd, ← hS'd] at hS
  have hS'4 : 4 ≤ S' := by rw [hS'd, inlineStatesLin]; omega
  have h1 : (A.inlineOracleInit H w₀ E Q L).descLen = 6 * S * 3 ^ K * 3 ^ 0 * (4 + 4 * K + 4 * 0 +
      Nat.size 0 + Nat.size S) := by
    rw [Machine.descLen, Machine.states_inlineOracleInit, Machine.tapes_inlineOracleInit]; rfl
  have h2 : ((A.fixInput w₀).inlineOracleLin H Q L).descLen = 6 * S' * 3 ^ K * 3 ^ 0 *
      (4 + 4 * K + 4 * 0 + Nat.size 0 + Nat.size S') := by
    rw [Machine.descLen, Machine.states_inlineOracleLin, Machine.tapes_inlineOracleLin]; rfl
  have hsz : Nat.size S ≤ Nat.size S' + 3 :=
    (Nat.size_le_size hS).trans ((size_mul_le' 5 S').trans (by
      have : Nat.size 5 = 3 := by decide
      omega))
  rw [h1, h2]
  simp only [pow_zero, Nat.mul_one, Nat.size_zero, Nat.mul_zero, Nat.add_zero]
  have hE : 4 + 4 * K + Nat.size S ≤ 2 * (4 + 4 * K + Nat.size S') := by omega
  calc 6 * S * 3 ^ K * (4 + 4 * K + Nat.size S)
      ≤ 6 * (5 * S') * 3 ^ K * (2 * (4 + 4 * K + Nat.size S')) := by gcongr
    _ = 10 * (6 * S' * 3 ^ K * (4 + 4 * K + Nat.size S')) := by ring

/-- The factor of the cost bound: it depends only on `ops`, `m`, the numbers of states of the
handlers, `Q`, `L`, the length of the fixed word and the bound `E` on the encoded states. -/
def initFactor (H : Fin ops → Routine (m + 3)) (Q L wl E : ℕ) : ℕ :=
  10 * linDescFactor H * fixFactor wl + (Q + 2 * L + 4 * ops + 17) + 4 * E + 21

/-- **Cost of the inlined machine for reductions**: `cost ≤ initFactor H Q L |w₀| E * A.cost`. -/
theorem Machine.cost_inlineOracleInit_le (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (w₀ : List Bool) (E Q L : ℕ) :
    (A.inlineOracleInit H w₀ E Q L).cost ≤ initFactor H Q L w₀.length E * A.cost := by
  have ht := A.time_inlineOracleInit_le H w₀ E Q L
  have hd := A.descLen_inlineOracleInit_le H w₀ E Q L
  have hl := (A.fixInput w₀).descLen_inlineOracleLin_le H Q L
  have hf := A.cost_fixInput_le w₀
  have h1 := A.one_le_cost
  have hT : A.time ≤ A.cost := by unfold Machine.cost; omega
  have h2 := Nat.mul_le_mul_left (Q + 2 * L + 4 * ops + 17) hT
  have h3 : linDescFactor H * (A.fixInput w₀).cost ≤
      linDescFactor H * (fixFactor w₀.length * A.cost) := Nat.mul_le_mul_left _ hf
  have h4 : 4 * E + 21 ≤ (4 * E + 21) * A.cost := Nat.le_mul_of_pos_right _ h1
  rw [Machine.cost, initFactor]
  nlinarith

end SigabaNeo
