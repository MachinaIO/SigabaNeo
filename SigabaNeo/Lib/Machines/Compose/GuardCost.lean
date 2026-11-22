import SigabaNeo.Lib.Machines.Compose.AndThenGuard
import SigabaNeo.Lib.Machines.Compose.LinCost

/-!
# Explicit bounds for `Machine.andThenGuard`

* `tapes_andThenGuard`, `states_andThenGuard`, `time_andThenGuard`: `k₁ + k₂ + 3` tapes,
  `h + 2 s₁ + s₂ + 15` states, the clock `dprepTime + 3 T + 7 + M₂.time ≤ 11 T + 13 + M₂.time`;
* `descLen_andThenGuard_le`: `descLen ≤ 641520 * M₁.cost * M₂.descLen`;
* `cost_andThenGuard_le_mul`: `cost ≤ 650000 * M₁.cost * M₂.cost`;
* three stages with a fixed first stage `P`: `run_andThenLin_andThenGuard`,
  `acceptProb_andThenLin_andThenGuard`, `cost_andThenLin_andThenGuard_le_mul`
  (`cost ≤ P.andThenLinFactor * (650000 * M.cost * D.cost)`).
-/

namespace SigabaNeo

open Cslib Turing MultiTapeMachine Compose Inline DigitPrep

variable (M₁ M₂ : Machine)

@[simp] theorem Machine.tapes_andThenGuard :
    (M₁.andThenGuard M₂).tapes = M₁.tapes + M₂.tapes + 3 := rfl

theorem Machine.states_andThenGuard :
    (M₁.andThenGuard M₂).states =
      (clockDigits M₁.tapes M₁.time).length + 2 * M₁.states + M₂.states + 15 := by
  simp only [Machine.andThenGuard, Machine.states_ofPTMOps, Machine.AndThenGuardState,
    Clock.Control, Fintype.card_sum, Fintype.card_prod, Fintype.card_option, Fintype.card_bool,
    Fintype.card_fin, Inline.LStep.card]
  ring

theorem Machine.time_andThenGuard :
    (M₁.andThenGuard M₂).time = dprepTime M₁.tapes M₁.time + 3 * M₁.time + 7 + M₂.time := by
  simp only [Machine.andThenGuard, Machine.time_ofPTMOps, Machine.andThenGuardTime]
  ring

theorem Machine.time_andThenGuard_le :
    (M₁.andThenGuard M₂).time ≤ 11 * M₁.time + 13 + M₂.time := by
  have h1 := dprepTime_le M₁.tapes M₁.time
  have h2 := clockDigits_length_le_size M₁.tapes M₁.time
  have h3 := size_le_self' M₁.time
  rw [Machine.time_andThenGuard]
  omega

/-- **Description length of the guarded composition.** -/
theorem Machine.descLen_andThenGuard_le :
    (M₁.andThenGuard M₂).descLen ≤ 641520 * M₁.cost * M₂.descLen := by
  have hcore := M₁.digit_core
  have hs₁ := M₁.one_le_states
  have hs₂ := M₂.one_le_states
  rw [Machine.descLen_eq, Machine.states_andThenGuard, Machine.tapes_andThenGuard,
    Machine.descLen_eq M₂]
  generalize (clockDigits M₁.tapes M₁.time).length = h at *
  generalize M₁.cost = X at *
  generalize M₁.states = s₁ at *
  generalize M₂.states = s₂ at *
  generalize M₁.tapes = k₁ at *
  generalize M₂.tapes = k₂ at *
  set V := s₁ + h with hV
  set u := k₁ + 1 + Nat.size s₁ + h with hu
  set e₂ := 4 + 4 * k₂ + Nat.size s₂ with he₂
  have hV1 : 1 ≤ V := by omega
  have hu1 : 1 ≤ u := by omega
  have he1 : 1 ≤ e₂ := by omega
  have hVs : 1 ≤ V * s₂ := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hS : h + 2 * s₁ + s₂ + 15 ≤ 18 * (V * s₂) := by
    have e1 : V ≤ V * s₂ := Nat.le_mul_of_pos_right _ (by omega)
    have e2 : s₂ ≤ V * s₂ := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hsizeS : Nat.size (h + 2 * s₁ + s₂ + 15) ≤ 5 + Nat.size V + Nat.size s₂ := by
    have e1 := Nat.size_le_size hS
    have e2 : 18 * (V * s₂) = (18 * V) * s₂ := by ring
    rw [e2] at e1
    have e3 := Compose.size_mul_le (18 * V) s₂
    have e4 := Compose.size_mul_le 18 V
    have h18 : Nat.size 18 = 5 := by decide
    omega
  have hsizeV : Nat.size V ≤ Nat.size s₁ + h + 1 := by
    have e1 := size_add_le' s₁ h
    rw [← hV] at e1
    have := size_le_self' h
    omega
  have hE : 4 + 4 * (k₁ + k₂ + 3) + Nat.size (h + 2 * s₁ + s₂ + 15) ≤ 22 * (u * e₂) := by
    have e1 : u ≤ u * e₂ := Nat.le_mul_of_pos_right _ he1
    have e2 : e₂ ≤ u * e₂ := Nat.le_mul_of_pos_left _ hu1
    omega
  calc 6 * (h + 2 * s₁ + s₂ + 15) * 3 ^ (k₁ + k₂ + 3) *
        (4 + 4 * (k₁ + k₂ + 3) + Nat.size (h + 2 * s₁ + s₂ + 15))
      ≤ 6 * (18 * (V * s₂)) * 3 ^ (k₁ + k₂ + 3) * (22 * (u * e₂)) := by gcongr
    _ = 10692 * (3 ^ k₁ * V * u) * (6 * s₂ * 3 ^ k₂ * e₂) := by rw [pow_add, pow_add]; ring
    _ ≤ 10692 * (60 * X) * (6 * s₂ * 3 ^ k₂ * e₂) := by gcongr
    _ = 641520 * X * (6 * s₂ * 3 ^ k₂ * e₂) := by ring

/-- **The cost of the guarded composition**: at most a constant times the product of the
costs. -/
theorem Machine.cost_andThenGuard_le_mul :
    (M₁.andThenGuard M₂).cost ≤ 650000 * M₁.cost * M₂.cost := by
  have ht := M₁.time_andThenGuard_le M₂
  have hd := M₁.descLen_andThenGuard_le M₂
  have h1 := M₁.one_le_cost
  have h2 := M₂.one_le_cost
  have hT₁ := M₁.time_le_cost
  have hT₂ := M₂.time_le_cost
  have hD₂ := M₂.descLen_le_cost
  rw [Machine.cost]
  generalize M₁.cost = a at *
  generalize M₂.cost = b at *
  have e1 : a ≤ a * b := Nat.le_mul_of_pos_right _ (by omega)
  have e2 : b ≤ a * b := Nat.le_mul_of_pos_left _ (by omega)
  have e3 : 641520 * a * M₂.descLen ≤ 641520 * a * b := Nat.mul_le_mul_left _ hD₂
  have e4 : 650000 * a * b = 650000 * (a * b) := by ring
  have e5 : 641520 * a * b = 641520 * (a * b) := by ring
  omega

/-- **The cost of the guarded composition**, quadratically in the two costs. -/
theorem Machine.cost_andThenGuard_le :
    (M₁.andThenGuard M₂).cost ≤ 162500 * (M₁.cost + M₂.cost) ^ 2 := by
  have h := M₁.cost_andThenGuard_le_mul M₂
  have := four_mul_le_sq M₁.cost M₂.cost
  calc (M₁.andThenGuard M₂).cost ≤ 650000 * M₁.cost * M₂.cost := h
    _ = 162500 * (4 * M₁.cost * M₂.cost) := by ring
    _ ≤ 162500 * (M₁.cost + M₂.cost) ^ 2 := Nat.mul_le_mul_left _ this

/-! ### Three stages -/

section Three

variable (P M D : Machine)

/-- The output law of three stages, the last one guarded. -/
theorem Machine.run_andThenLin_andThenGuard (x : List Bool) :
    (P.andThenLin (M.andThenGuard D)).run x = ((P.run x).bind M.run).bind D.guardK := by
  rw [Machine.run_andThenLin, PMF.bind_bind]
  congr 1; funext y; rw [Machine.run_andThenGuard]

/-- **Acceptance of three stages**, the last one guarded. -/
theorem Machine.acceptProb_andThenLin_andThenGuard (μ : PMF (List Bool)) :
    (P.andThenLin (M.andThenGuard D)).acceptProb μ =
      ((((μ.bind P.run).bind M.run).bind D.guardK) [true]).toReal := by
  rw [Machine.acceptProb_andThenLin, Machine.acceptProb_andThenGuard]

/-- **Cost of three stages** with a fixed first stage `P`, the last one guarded. -/
theorem Machine.cost_andThenLin_andThenGuard_le_mul :
    (P.andThenLin (M.andThenGuard D)).cost ≤
      P.andThenLinFactor * (650000 * M.cost * D.cost) :=
  (Machine.cost_andThenLin_le_first P _).trans
    (Nat.mul_le_mul_left _ (Machine.cost_andThenGuard_le_mul M D))

/-- **Cost of three stages** with a fixed first stage `P`, the last one guarded, in the form
`P.andThenLinFactor * c * M.cost * D.cost`. -/
theorem Machine.cost_andThenLin_andThenGuard_le :
    (P.andThenLin (M.andThenGuard D)).cost ≤
      P.andThenLinFactor * 650000 * M.cost * D.cost := by
  have := Machine.cost_andThenLin_andThenGuard_le_mul P M D
  calc _ ≤ _ := this
    _ = P.andThenLinFactor * 650000 * M.cost * D.cost := by ring

end Three

end SigabaNeo
