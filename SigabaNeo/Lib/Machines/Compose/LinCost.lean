import SigabaNeo.Lib.Machines.Compose.AndThenLin
import SigabaNeo.Lib.Machines.Compose.Cost

/-!
# Explicit bounds for `Machine.andThenLin`

* `tapes_andThenLin`, `states_andThenLin`, `time_andThenLin`: `k₁ + k₂ + 3` tapes,
  `h + 2 s₁ + s₂ + 11` states (`h = (clockDigits M₁.tapes M₁.time).length ≤ Nat.size M₁.time`), the
  clock `dprepTime + 3 T + 4 + M₂.time ≤ 11 T + 10 + M₂.time` (`time_andThenLin_le`);
* `digit_core`: `3 ^ k * (s + h) * (k + 1 + Nat.size s + h) ≤ 60 * A.cost` for the digits of the
  clock of `A` in base `2 ^ (A.tapes + 1)`;
* `descLen_andThenLin_le`: `descLen ≤ 498960 * M₁.cost * M₂.descLen`;
* `cost_andThenLin_le_mul`: `cost ≤ 500000 * M₁.cost * M₂.cost`, hence
  `cost_andThenLin_le`: `cost ≤ 125000 * (M₁.cost + M₂.cost) ^ 2`, and the bounds linear in either
  machine for a fixed other one (`cost_andThenLin_le_first`, `cost_andThenLin_le_second`);
* three stages: `run_andThenLin_andThenLin`, `acceptProb_andThenLin_andThenLin`,
  `cost_andThenLin_andThenLin_le`.

The `h` states of the preparation each have a row for every symbol combination of all
`k₁ + k₂ + 3` tapes, but `h * 3 ^ k₁` (times the entry width) is linear in `M₁.cost` (`digit_core`,
as in `Inline.LinCost`), so the description length is at most a constant times
`M₁.cost * M₂.descLen`.
-/

namespace SigabaNeo

open Cslib Turing MultiTapeMachine Compose Inline DigitPrep

variable (M₁ M₂ : Machine)

@[simp] theorem Machine.tapes_andThenLin :
    (M₁.andThenLin M₂).tapes = M₁.tapes + M₂.tapes + 3 := rfl

theorem Machine.states_andThenLin :
    (M₁.andThenLin M₂).states =
      (clockDigits M₁.tapes M₁.time).length + 2 * M₁.states + M₂.states + 11 := by
  simp only [Machine.andThenLin, Machine.states_ofPTMOps, Machine.AndThenLinState, Clock.Control,
    Fintype.card_sum, Fintype.card_prod, Fintype.card_option, Fintype.card_bool, Fintype.card_fin,
    Inline.LStep.card]
  ring

theorem Machine.time_andThenLin :
    (M₁.andThenLin M₂).time = dprepTime M₁.tapes M₁.time + 3 * M₁.time + 4 + M₂.time := by
  simp only [Machine.andThenLin, Machine.time_ofPTMOps, Machine.andThenLinTime]
  ring

theorem Machine.time_andThenLin_le : (M₁.andThenLin M₂).time ≤ 11 * M₁.time + 10 + M₂.time := by
  have h1 := dprepTime_le M₁.tapes M₁.time
  have h2 := clockDigits_length_le_size M₁.tapes M₁.time
  have h3 := size_le_self' M₁.time
  rw [Machine.time_andThenLin]
  omega

/-! ### The digits of the clock against the cost -/

theorem digit_core_aux (k s T h X : ℕ) (hs : 1 ≤ s) (hTX : T ≤ X)
    (hDX : 6 * s * 3 ^ k * (4 + 4 * k + Nat.size s) ≤ X) (hhs : h ≤ Nat.size T)
    (hkh : (k + 1) * h ≤ Nat.size T + k + 1) (hdig : h = 0 ∨ (k + 1) * (h - 1) < Nat.size T) :
    3 ^ k * (s + h) * (k + 1 + Nat.size s + h) ≤ 60 * X := by
  have hsG : Nat.size (3 ^ k) ≤ 2 * k + 1 := size_three_pow k
  have hwV : Nat.size s ≤ 2 * s := (size_le_self' s).trans (by omega)
  have hVu : 3 ^ k * s * (k + 1 + Nat.size s) ≤ X := by
    calc 3 ^ k * s * (k + 1 + Nat.size s) = 1 * s * 3 ^ k * (k + 1 + Nat.size s) := by ring
      _ ≤ 6 * s * 3 ^ k * (4 + 4 * k + Nat.size s) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num)))
            (by omega)
      _ ≤ X := hDX
  have P4 := sq_mul_le_of_digits k h T hdig
  generalize 3 ^ k = G at *
  generalize hu : k + 1 + Nat.size s = u at *
  have hu1 : 1 ≤ u := by omega
  have hku : k + 1 ≤ u := by omega
  have hGV : Nat.size (G * s) ≤ 2 * u := (Compose.size_mul_le _ _).trans (by omega)
  have P1 := piece_mul T h (G * s) u hhs hGV hu1
  have P2 := piece_tapes T h G k hkh hsG
  have P2' : G * (k + 1) ≤ G * s * u :=
    calc G * (k + 1) ≤ G * u := Nat.mul_le_mul_left _ hku
      _ ≤ G * s * u := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hs)
  have P3 := piece_w T h G (Nat.size s) k s u hhs hsG hwV (by omega) hku
  have e : G * (s + h) * (u + h) =
      G * s * u + G * s * h + G * h * (k + 1) + G * h * Nat.size s + h * h * G := by
    rw [← hu]; ring
  have P4' : 2 * (k + 1) * h * G = 2 * (G * h * (k + 1)) := by ring
  rw [e]
  linarith

/-- **The digits of the clock against the cost**: with `h` the number of digits of `A.time` in
base `2 ^ (A.tapes + 1)`, `3 ^ A.tapes * (A.states + h) * (A.tapes + 1 + Nat.size A.states + h)` is
at most `60 * A.cost`. -/
theorem Machine.digit_core (A : Machine) :
    3 ^ A.tapes * (A.states + (clockDigits A.tapes A.time).length) *
      (A.tapes + 1 + Nat.size A.states + (clockDigits A.tapes A.time).length) ≤ 60 * A.cost := by
  have hD := A.descLen_le_cost
  rw [Machine.descLen_eq] at hD
  exact digit_core_aux _ _ _ _ _ A.one_le_states A.time_le_cost hD
    (clockDigits_length_le_size _ _) (clockDigits_mul_le _ _) (clockDigits_length_digits _ _)

/-! ### Description length and cost -/

/-- **Description length of the composition with a short preparation.** -/
theorem Machine.descLen_andThenLin_le :
    (M₁.andThenLin M₂).descLen ≤ 498960 * M₁.cost * M₂.descLen := by
  have hcore := M₁.digit_core
  have hs₁ := M₁.one_le_states
  have hs₂ := M₂.one_le_states
  rw [Machine.descLen_eq, Machine.states_andThenLin, Machine.tapes_andThenLin,
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
  have hS : h + 2 * s₁ + s₂ + 11 ≤ 14 * (V * s₂) := by
    have e1 : V ≤ V * s₂ := Nat.le_mul_of_pos_right _ (by omega)
    have e2 : s₂ ≤ V * s₂ := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hsizeS : Nat.size (h + 2 * s₁ + s₂ + 11) ≤ 4 + Nat.size V + Nat.size s₂ := by
    have e1 := Nat.size_le_size hS
    have e2 : 14 * (V * s₂) = (14 * V) * s₂ := by ring
    rw [e2] at e1
    have e3 := Compose.size_mul_le (14 * V) s₂
    have e4 := Compose.size_mul_le 14 V
    have h14 : Nat.size 14 = 4 := by decide
    omega
  have hsizeV : Nat.size V ≤ Nat.size s₁ + h + 1 := by
    have e1 := size_add_le' s₁ h
    rw [← hV] at e1
    have := size_le_self' h
    omega
  have hE : 4 + 4 * (k₁ + k₂ + 3) + Nat.size (h + 2 * s₁ + s₂ + 11) ≤ 22 * (u * e₂) := by
    have e1 : u ≤ u * e₂ := Nat.le_mul_of_pos_right _ he1
    have e2 : e₂ ≤ u * e₂ := Nat.le_mul_of_pos_left _ hu1
    omega
  calc 6 * (h + 2 * s₁ + s₂ + 11) * 3 ^ (k₁ + k₂ + 3) *
        (4 + 4 * (k₁ + k₂ + 3) + Nat.size (h + 2 * s₁ + s₂ + 11))
      ≤ 6 * (14 * (V * s₂)) * 3 ^ (k₁ + k₂ + 3) * (22 * (u * e₂)) := by gcongr
    _ = 8316 * (3 ^ k₁ * V * u) * (6 * s₂ * 3 ^ k₂ * e₂) := by rw [pow_add, pow_add]; ring
    _ ≤ 8316 * (60 * X) * (6 * s₂ * 3 ^ k₂ * e₂) := by gcongr
    _ = 498960 * X * (6 * s₂ * 3 ^ k₂ * e₂) := by ring

/-- **The cost of the composition with a short preparation**: at most a constant times the product
of the costs. -/
theorem Machine.cost_andThenLin_le_mul :
    (M₁.andThenLin M₂).cost ≤ 500000 * M₁.cost * M₂.cost := by
  have ht := M₁.time_andThenLin_le M₂
  have hd := M₁.descLen_andThenLin_le M₂
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
  have e3 : 498960 * a * M₂.descLen ≤ 498960 * a * b := Nat.mul_le_mul_left _ hD₂
  have e4 : 500000 * a * b = 500000 * (a * b) := by ring
  have e5 : 498960 * a * b = 498960 * (a * b) := by ring
  omega

theorem four_mul_le_sq (a b : ℕ) : 4 * a * b ≤ (a + b) ^ 2 := by
  zify; nlinarith [sq_nonneg ((a : ℤ) - b)]

/-- **The cost of the composition with a short preparation**, quadratically in the two costs. -/
theorem Machine.cost_andThenLin_le :
    (M₁.andThenLin M₂).cost ≤ 125000 * (M₁.cost + M₂.cost) ^ 2 := by
  have h := M₁.cost_andThenLin_le_mul M₂
  have := four_mul_le_sq M₁.cost M₂.cost
  calc (M₁.andThenLin M₂).cost ≤ 500000 * M₁.cost * M₂.cost := h
    _ = 125000 * (4 * M₁.cost * M₂.cost) := by ring
    _ ≤ 125000 * (M₁.cost + M₂.cost) ^ 2 := Nat.mul_le_mul_left _ this

/-- The factor of the cost bound for a fixed first machine. -/
def Machine.andThenLinFactor (M₁ : Machine) : ℕ := 500000 * M₁.cost

/-- **Linear cost in the second machine.** -/
theorem Machine.cost_andThenLin_le_first :
    (M₁.andThenLin M₂).cost ≤ M₁.andThenLinFactor * M₂.cost :=
  M₁.cost_andThenLin_le_mul M₂

/-- **Linear cost in the first machine.** -/
theorem Machine.cost_andThenLin_le_second :
    (M₁.andThenLin M₂).cost ≤ M₂.andThenLinFactor * M₁.cost := by
  have := M₁.cost_andThenLin_le_mul M₂
  rw [Machine.andThenLinFactor]
  calc (M₁.andThenLin M₂).cost ≤ 500000 * M₁.cost * M₂.cost := this
    _ = 500000 * M₂.cost * M₁.cost := by ring

/-! ### Three stages -/

section Three

variable (P M D : Machine)

/-- The output law of three stages. -/
theorem Machine.run_andThenLin_andThenLin (x : List Bool) :
    (P.andThenLin (M.andThenLin D)).run x = ((P.run x).bind M.run).bind D.run := by
  rw [Machine.run_andThenLin, PMF.bind_bind]
  congr 1; funext y; rw [Machine.run_andThenLin]

/-- **Acceptance of three stages**: `D` on the output law of `M` on the output law of `P`. -/
theorem Machine.acceptProb_andThenLin_andThenLin (μ : PMF (List Bool)) :
    (P.andThenLin (M.andThenLin D)).acceptProb μ = D.acceptProb ((μ.bind P.run).bind M.run) := by
  rw [Machine.acceptProb_andThenLin, Machine.acceptProb_andThenLin, PMF.bind_bind]

/-- **Cost of three stages** with a fixed first stage `P`: a factor depending only on `P` times
`125000 * (M.cost + D.cost) ^ 2`. -/
theorem Machine.cost_andThenLin_andThenLin_le :
    (P.andThenLin (M.andThenLin D)).cost ≤
      P.andThenLinFactor * (125000 * (M.cost + D.cost) ^ 2) :=
  (Machine.cost_andThenLin_le_first P _).trans
    (Nat.mul_le_mul_left _ (Machine.cost_andThenLin_le M D))

/-- **Cost of three stages**, with the product of the last two costs. -/
theorem Machine.cost_andThenLin_andThenLin_le_mul :
    (P.andThenLin (M.andThenLin D)).cost ≤
      P.andThenLinFactor * (500000 * M.cost * D.cost) :=
  (Machine.cost_andThenLin_le_first P _).trans
    (Nat.mul_le_mul_left _ (Machine.cost_andThenLin_le_mul M D))

end Three

end SigabaNeo
