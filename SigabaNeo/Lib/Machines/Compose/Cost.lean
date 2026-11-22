import SigabaNeo.Lib.Machines.Compose.AndThen
import Mathlib.Data.Nat.Size

/-!
# Explicit bounds for `Machine.andThen`

* `tapes_andThen`, `states_andThen`, `time_andThen`, `descLen_andThen`: exact values. With
  `T = M₁.time`: `k₁ + k₂ + 3` tapes, `T + 2 s₁ + s₂ + 10` states, clock `4 T + 9 + M₂.time`.
* `cost_andThen_le_first`: for a fixed first machine the cost is **linear** in the second:
  `cost ≤ andThenFactor M₁ * M₂.cost`.
* `cost_andThen_le`: `cost ≤ 392 * M₁.cost ^ 2 * M₂.cost * (Nat.size M₁.cost + 2)`.

The first machine's clock is written in unary by `T + 5` states of the composed machine, and each
state has a row for every symbol combination of all `k₁ + k₂ + 3` tapes, hence the term
`T * 3 ^ k₁ * 3 ^ k₂` of the description length: the cost is not `O((M₁.cost + M₂.cost) ^ 2)` in
general, but it is linear in `M₂.cost` for a fixed `M₁`.
-/

namespace SigabaNeo

open Cslib Turing MultiTapeMachine Compose AndThen

variable (M₁ M₂ : Machine)

@[simp] theorem Machine.tapes_andThen : (M₁.andThen M₂).tapes = M₁.tapes + M₂.tapes + 3 := rfl

theorem Machine.states_andThen :
    (M₁.andThen M₂).states = M₁.time + 2 * M₁.states + M₂.states + 10 := by
  simp only [Machine.andThen, Machine.states_ofPTMOps, Machine.AndThenState, Clock.Control,
    Fintype.card_sum, Fintype.card_prod, Fintype.card_option, Fintype.card_bool, Fintype.card_fin]
  ring

theorem Machine.time_andThen : (M₁.andThen M₂).time = 4 * M₁.time + 9 + M₂.time := by
  simp only [Machine.andThen, Machine.time_ofPTMOps, Machine.andThenTime]
  ring

theorem Machine.descLen_eq (A : Machine) :
    A.descLen = 6 * A.states * 3 ^ A.tapes * (4 + 4 * A.tapes + Nat.size A.states) := by
  simp [Machine.descLen, Machine.entryBits]

theorem Machine.descLen_andThen :
    (M₁.andThen M₂).descLen =
      6 * (M₁.time + 2 * M₁.states + M₂.states + 10) * 3 ^ (M₁.tapes + M₂.tapes + 3) *
        (4 + 4 * (M₁.tapes + M₂.tapes + 3) + Nat.size (M₁.time + 2 * M₁.states + M₂.states + 10)) := by
  rw [Machine.descLen_eq, Machine.states_andThen, Machine.tapes_andThen]

theorem Compose.size_mul_le (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)

theorem Machine.one_le_states (A : Machine) : 1 ≤ A.states := Fin.pos A.machine.initial

theorem Machine.time_le_cost (A : Machine) : A.time ≤ A.cost := by unfold Machine.cost; omega

theorem Machine.descLen_le_cost (A : Machine) : A.descLen ≤ A.cost := by
  unfold Machine.cost; omega

/-- The factor of the cost bound for a fixed first machine. -/
def Machine.andThenFactor (M₁ : Machine) : ℕ :=
  let C := M₁.time + 2 * M₁.states + 11
  27 * C * 3 ^ M₁.tapes * (16 + 4 * M₁.tapes + Nat.size C) + 4 * M₁.time + 10

/-- **Linear cost in the second machine.** -/
theorem Machine.cost_andThen_le_first : (M₁.andThen M₂).cost ≤ M₁.andThenFactor * M₂.cost := by
  set C := M₁.time + 2 * M₁.states + 11 with hC
  set s₂ := M₂.states
  have hs₂ := M₂.one_le_states
  have hS : M₁.time + 2 * M₁.states + s₂ + 10 ≤ C * s₂ := by nlinarith
  have hsize : Nat.size (M₁.time + 2 * M₁.states + s₂ + 10) ≤ Nat.size C + Nat.size s₂ :=
    (Nat.size_le_size hS).trans (Compose.size_mul_le _ _)
  have hE : 4 + 4 * (M₁.tapes + M₂.tapes + 3) + Nat.size (M₁.time + 2 * M₁.states + s₂ + 10) ≤
      (16 + 4 * M₁.tapes + Nat.size C) * (4 + 4 * M₂.tapes + Nat.size s₂) := by nlinarith
  have hD : (M₁.andThen M₂).descLen ≤
      (27 * C * 3 ^ M₁.tapes * (16 + 4 * M₁.tapes + Nat.size C)) * M₂.descLen := by
    rw [Machine.descLen_andThen, Machine.descLen_eq M₂]
    calc 6 * (M₁.time + 2 * M₁.states + s₂ + 10) * 3 ^ (M₁.tapes + M₂.tapes + 3) *
          (4 + 4 * (M₁.tapes + M₂.tapes + 3) + Nat.size (M₁.time + 2 * M₁.states + s₂ + 10))
        ≤ 6 * (C * s₂) * 3 ^ (M₁.tapes + M₂.tapes + 3) *
          ((16 + 4 * M₁.tapes + Nat.size C) * (4 + 4 * M₂.tapes + Nat.size s₂)) := by
          gcongr
      _ = _ := by rw [pow_add, pow_add]; ring
  have hT₂ := M₂.time_le_cost
  have hD₂ := M₂.descLen_le_cost
  have h1 := M₂.one_le_cost
  rw [Machine.cost, Machine.time_andThen, Machine.andThenFactor]
  generalize 27 * C * 3 ^ M₁.tapes * (16 + 4 * M₁.tapes + Nat.size C) = F at hD ⊢
  have e1 := Nat.mul_le_mul_left F hD₂
  have e2 := Nat.mul_le_mul_left (4 * M₁.time + 9) h1
  calc 4 * M₁.time + 9 + M₂.time + (M₁.andThen M₂).descLen
      ≤ (4 * M₁.time + 9) * M₂.cost + M₂.cost + F * M₂.cost := by linarith
    _ = (F + 4 * M₁.time + 10) * M₂.cost := by ring


/-- **The cost of the composition**, polynomially in the two costs. -/
theorem Machine.cost_andThen_le :
    (M₁.andThen M₂).cost ≤ 392 * M₁.cost ^ 2 * M₂.cost * (Nat.size M₁.cost + 2) := by
  set a₁ := M₁.cost
  set a₂ := M₂.cost
  have h1 := M₁.one_le_cost
  have h2 := M₂.one_le_cost
  have hs₁ := M₁.one_le_states
  have hs₂ := M₂.one_le_states
  have hT := M₁.time_le_cost
  have hT₂ := M₂.time_le_cost
  have hd₁ := M₁.descLen_le_cost
  have hd₂ := M₂.descLen_le_cost
  rw [Machine.descLen_eq] at hd₁ hd₂
  -- the first machine's row factor and its states
  have hpos : 1 ≤ 3 ^ M₁.tapes * (4 + 4 * M₁.tapes + Nat.size M₁.states) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hr₁ : 3 ^ M₁.tapes * (4 + 4 * M₁.tapes) ≤ a₁ := by
    calc 3 ^ M₁.tapes * (4 + 4 * M₁.tapes)
        ≤ 3 ^ M₁.tapes * (4 + 4 * M₁.tapes + Nat.size M₁.states) :=
          Nat.mul_le_mul_left _ (by omega)
      _ ≤ 6 * M₁.states * (3 ^ M₁.tapes * (4 + 4 * M₁.tapes + Nat.size M₁.states)) :=
          Nat.le_mul_of_pos_left _ (by omega)
      _ = 6 * M₁.states * 3 ^ M₁.tapes * (4 + 4 * M₁.tapes + Nat.size M₁.states) := by ring
      _ ≤ a₁ := hd₁
  have hst₁ : M₁.states ≤ a₁ := by
    calc M₁.states ≤ 6 * M₁.states * (3 ^ M₁.tapes * (4 + 4 * M₁.tapes + Nat.size M₁.states)) := by
          nlinarith
      _ = 6 * M₁.states * 3 ^ M₁.tapes * (4 + 4 * M₁.tapes + Nat.size M₁.states) := by ring
      _ ≤ a₁ := hd₁
  set S := M₁.time + 2 * M₁.states + M₂.states + 10
  have hS : S ≤ 14 * M₂.states * a₁ := by
    have e1 : a₁ ≤ M₂.states * a₁ := Nat.le_mul_of_pos_left _ (by omega)
    have e2 : M₂.states ≤ M₂.states * a₁ := Nat.le_mul_of_pos_right _ (by omega)
    have : 14 * M₂.states * a₁ = 14 * (M₂.states * a₁) := by ring
    rw [this]; simp only [S]; linarith
  have hsize : Nat.size S ≤ 4 + Nat.size M₂.states + Nat.size a₁ := by
    refine (Nat.size_le_size hS).trans ((Compose.size_mul_le _ _).trans ?_)
    have := Compose.size_mul_le 14 M₂.states
    have h14 : Nat.size 14 = 4 := by decide
    omega
  have key : ∀ u v w : ℕ, 4 ≤ u → 4 ≤ v → 2 ≤ w → u + v + w + 10 ≤ u * v * w := by
    intro u v w hu hv hw
    have huv : u + v + 8 ≤ u * v := by nlinarith
    have h16 : 16 ≤ u * v := by nlinarith
    nlinarith
  have hE : 4 + 4 * (M₁.tapes + M₂.tapes + 3) + Nat.size S ≤
      (4 + 4 * M₁.tapes) * (4 + 4 * M₂.tapes + Nat.size M₂.states) * (2 + Nat.size a₁) := by
    have := key (4 + 4 * M₁.tapes) (4 + 4 * M₂.tapes + Nat.size M₂.states) (2 + Nat.size a₁)
      (by omega) (by omega) (by omega)
    omega
  have hD : (M₁.andThen M₂).descLen ≤ 378 * (a₁ ^ 2 * a₂ * (Nat.size a₁ + 2)) := by
    rw [Machine.descLen_andThen]
    calc 6 * S * 3 ^ (M₁.tapes + M₂.tapes + 3) * (4 + 4 * (M₁.tapes + M₂.tapes + 3) + Nat.size S)
        ≤ 6 * (14 * M₂.states * a₁) * 3 ^ (M₁.tapes + M₂.tapes + 3) *
          ((4 + 4 * M₁.tapes) * (4 + 4 * M₂.tapes + Nat.size M₂.states) * (2 + Nat.size a₁)) := by
          gcongr
      _ = 378 * a₁ * (3 ^ M₁.tapes * (4 + 4 * M₁.tapes)) *
          (6 * M₂.states * 3 ^ M₂.tapes * (4 + 4 * M₂.tapes + Nat.size M₂.states)) *
          (Nat.size a₁ + 2) := by rw [pow_add, pow_add]; ring
      _ ≤ 378 * a₁ * a₁ * a₂ * (Nat.size a₁ + 2) := by gcongr
      _ = _ := by ring
  set Q := a₁ ^ 2 * a₂ * (Nat.size a₁ + 2)
  have hQ1 : a₁ ≤ Q := by
    calc a₁ = a₁ * 1 * 1 * 1 := by ring
      _ ≤ a₁ * a₁ * a₂ * (Nat.size a₁ + 2) := by gcongr <;> omega
      _ = Q := by ring
  have hQ2 : a₂ ≤ Q := by
    calc a₂ = 1 * 1 * a₂ * 1 := by ring
      _ ≤ a₁ * a₁ * a₂ * (Nat.size a₁ + 2) := by gcongr <;> omega
      _ = Q := by ring
  rw [Machine.cost, Machine.time_andThen]
  calc 4 * M₁.time + 9 + M₂.time + (M₁.andThen M₂).descLen ≤ 14 * Q + 378 * Q := by
        have : 1 ≤ a₁ := h1
        linarith
    _ = 392 * a₁ ^ 2 * a₂ * (Nat.size a₁ + 2) := by simp only [Q]; ring

end SigabaNeo
