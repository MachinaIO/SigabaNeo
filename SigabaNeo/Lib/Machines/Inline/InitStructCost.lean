import SigabaNeo.Lib.Machines.Inline.InitCost
import SigabaNeo.Lib.Machines.Compose.GuardCost

/-!
# Structured cost bounds for compositions with an inlined machine

The product bounds (`cost_andThenLin_le_mul`, `cost_inlineOracleInit_le`, …) multiply whole costs,
so the cost of a chain is bounded by the product of the costs of its stages. Structurally the
description length of a composition is `6 · (sum of the states) · 3 ^ (sum of the tapes) · (entry
bits)`, and its clock is a sum. Here these are kept apart for the chain

`P.andThenLin (((A.inlineOracleInit H w₀ E Q L).andThenLin Post).andThenGuard D)`

(a fixed preparation `P`, the inlined machine of `A`, a fixed post-processing `Post`, a guarded
distinguisher `D`):

* `clockDigits_length_le_of_le_mul`: the digits of a clock `T ≤ c · T₀` in a base
  `2 ^ (k + 1)` with `k₀ ≤ k` are at most those of `T₀` in base `2 ^ (k₀ + 1)` plus `Nat.size c`;
* `Machine.descLen_ge`, `Machine.digit_core_cost`: the lower bounds on `A.cost` absorbing the factors
  of `A` (`6 · states · 3 ^ tapes · (4 + 4 tapes + size states) ≤ A.descLen`, and the same with the
  digits of `A.cost`, up to `60`);
* `Machine.states_chain`, `Machine.tapes_chain`: the exact numbers;
* `Machine.descLen_chain_le`: `descLen ≤ 60 · R · 3 ^ K₀ · e · A.cost · D.descLen`, where
  `R = chainStates …` is (up to digits) `2 s_P + 2 s_Post + 4 · 3 ^ ops · Z · (|w₀| + 3)` with
  `Z = 1 + ∑ (9 + handler states)`, `K₀ = chainTapes … = k_P + k_Post + 2 ops + m + 11` and
  `e = 5 + 4 K₀ + Nat.size R`;
* `Machine.time_chain_le`: `time ≤ 11 P.time + 23 + 11 · chainSlope · A.cost + D.time`;
* `Machine.cost_chain_le`: `cost ≤ chainConst … · A.cost · D.cost`, with
  `chainConst = 60 · R · 3 ^ K₀ · e + 11 P.time + 11 · chainSlope + 24`: the preparation enters
  additively, through its states (in `R`), its tapes (in `K₀`) and its time.
* `three_pow_le_two_pow`: `3 ^ K ≤ 2 ^ (65 K / 41 + 1)`, for exponent arithmetic.
-/

namespace SigabaNeo

open Cslib Turing MultiTapeMachine Compose Inline DigitPrep

variable {ops m : ℕ}

/-! ### Digits of clocks -/

theorem size_le_mul_clockDigits (k T : ℕ) : Nat.size T ≤ (k + 1) * (clockDigits k T).length := by
  rw [Nat.size_le]
  have hb : 1 < baseB k := by have := baseB_two_le (kA := k); omega
  calc T < baseB k ^ (Nat.digits (baseB k) T).length := Nat.lt_base_pow_length_digits hb
    _ = 2 ^ ((k + 1) * (clockDigits k T).length) := by rw [baseB, ← pow_mul]; rfl

theorem clockDigits_length_mono (k : ℕ) {T T' : ℕ} (h : T ≤ T') :
    (clockDigits k T).length ≤ (clockDigits k T').length :=
  Nat.le_length_digits_le _ _ _ h

/-- **Digits of a larger clock in a larger base**: if `T ≤ c · T₀` and `k₀ ≤ k`, the digits of `T`
in base `2 ^ (k + 1)` are at most those of `T₀` in base `2 ^ (k₀ + 1)` plus `Nat.size c`. -/
theorem clockDigits_length_le_of_le_mul {k₀ k T₀ T c : ℕ} (hk : k₀ ≤ k) (hT : T ≤ c * T₀) :
    (clockDigits k T).length ≤ (clockDigits k₀ T₀).length + Nat.size c := by
  rcases clockDigits_length_digits k T with h | h
  · omega
  have h1 : Nat.size T ≤ Nat.size c + Nat.size T₀ :=
    (Nat.size_le_size hT).trans (Compose.size_mul_le _ _)
  have h2 := size_le_mul_clockDigits k₀ T₀
  have h3 : (k₀ + 1) * (clockDigits k₀ T₀).length ≤ (k + 1) * (clockDigits k₀ T₀).length :=
    Nat.mul_le_mul_right _ (by omega)
  have h5 : Nat.size c ≤ (k + 1) * Nat.size c := Nat.le_mul_of_pos_left _ (by omega)
  have h4 : (k + 1) * ((clockDigits k T).length - 1) <
      (k + 1) * (Nat.size c + (clockDigits k₀ T₀).length) := by
    rw [Nat.mul_add]; omega
  have := Nat.lt_of_mul_lt_mul_left h4
  omega

/-! ### Lower bounds on the cost -/

theorem Machine.one_le_states' (A : Machine ops) : 1 ≤ A.states := Fin.pos A.machine.initial

/-- The description length of a machine with oracles is at least that of its tapes and states. -/
theorem Machine.descLen_ge (A : Machine ops) :
    6 * A.states * 3 ^ A.tapes * (4 + 4 * A.tapes + Nat.size A.states) ≤ A.descLen := by
  unfold Machine.descLen Machine.entryBits
  have : 1 ≤ 3 ^ ops := Nat.one_le_pow _ _ (by norm_num)
  have he : 4 + 4 * A.tapes + Nat.size A.states ≤
      4 + 4 * A.tapes + 4 * ops + Nat.size ops + Nat.size A.states := by omega
  calc 6 * A.states * 3 ^ A.tapes * (4 + 4 * A.tapes + Nat.size A.states)
      = 6 * A.states * 3 ^ A.tapes * 1 * (4 + 4 * A.tapes + Nat.size A.states) := by ring
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ this) he

/-- **The digits of the cost against the cost**: with `h` the number of digits of `A.cost` in base
`2 ^ (A.tapes + 1)`, `3 ^ A.tapes · (A.states + h) · (A.tapes + 1 + Nat.size A.states + h)` is at
most `60 · A.cost`. -/
theorem Machine.digit_core_cost (A : Machine ops) :
    3 ^ A.tapes * (A.states + (clockDigits A.tapes A.cost).length) *
      (A.tapes + 1 + Nat.size A.states + (clockDigits A.tapes A.cost).length) ≤ 60 * A.cost :=
  digit_core_aux _ _ _ _ _ A.one_le_states' le_rfl
    (A.descLen_ge.trans (by unfold Machine.cost; omega))
    (clockDigits_length_le_size _ _) (clockDigits_mul_le _ _) (clockDigits_length_digits _ _)

/-! ### Powers of three -/

/-- `3 ^ K ≤ 2 ^ (65 K / 41 + 1)` (`3 ^ 41 ≤ 2 ^ 65`; `65 / 41 ≈ 1.5854 > log₂ 3 ≈ 1.58496`). -/
theorem three_pow_le_two_pow (K : ℕ) : 3 ^ K ≤ 2 ^ (65 * K / 41 + 1) := by
  induction K using Nat.strong_induction_on with
  | _ K ih =>
    rcases Nat.lt_or_ge K 41 with hK | hK
    · interval_cases K <;> norm_num
    · obtain ⟨j, rfl⟩ : ∃ j, K = j + 41 := ⟨K - 41, by omega⟩
      have h := ih j (by omega)
      have e : 65 * (j + 41) / 41 + 1 = (65 * j / 41 + 1) + 65 := by omega
      rw [e, pow_add, pow_add]
      exact Nat.mul_le_mul h (by norm_num)

/-! ### The chain -/

/-- The slope of the clock of the inlined machine in `A.cost`. -/
def inlSlope (ops Q L E : ℕ) : ℕ := Q + 2 * L + 4 * ops + 4 * E + 38

/-- The slope of the clock of the inlined machine followed by the post-processing in `A.cost`, for
a post-processing of time at most `pt · A.cost`. -/
def chainSlope (ops Q L E pt : ℕ) : ℕ := 11 * inlSlope ops Q L E + 10 + pt

/-- The states of the chain per state of `A` and of `D` (with the digits of the clocks). -/
def chainStates (P Post : Machine) (H : Fin ops → Routine (m + 3)) (Q L E pt wl : ℕ) : ℕ :=
  (clockDigits P.tapes P.time).length + 2 * P.states + 2 * Post.states +
    4 * (3 ^ ops * (1 + ∑ o, (9 + (H o).states))) * (wl + 3) +
    2 * Nat.size (inlSlope ops Q L E) + Nat.size (chainSlope ops Q L E pt) + 108

/-- The tapes of the chain besides those of `A` and `D`. -/
def chainTapes (P Post : Machine) (ops m : ℕ) : ℕ := P.tapes + Post.tapes + 2 * ops + m + 11

/-- **The constant of the structured cost bound of the chain.** -/
def chainConst (P Post : Machine) (H : Fin ops → Routine (m + 3)) (Q L E pt wl : ℕ) : ℕ :=
  60 * chainStates P Post H Q L E pt wl * 3 ^ chainTapes P Post ops m *
      (5 + 4 * chainTapes P Post ops m + Nat.size (chainStates P Post H Q L E pt wl)) +
    11 * P.time + 11 * chainSlope ops Q L E pt + 24

section Chain

variable (P Post D : Machine) (A : Machine ops) (H : Fin ops → Routine (m + 3)) (w₀ : List Bool)
  (E Q L : ℕ)

theorem Machine.tapes_chain :
    (P.andThenLin (((A.inlineOracleInit H w₀ E Q L).andThenLin Post).andThenGuard D)).tapes =
      chainTapes P Post ops m + A.tapes + D.tapes := by
  simp only [Machine.tapes_andThenLin, Machine.tapes_andThenGuard, Machine.tapes_inlineOracleInit,
    chainTapes]
  ring

theorem Machine.time_inl_le_cost :
    (A.inlineOracleInit H w₀ E Q L).time ≤ inlSlope ops Q L E * A.cost := by
  have h := A.time_inlineOracleInit_le H w₀ E Q L
  have hT : A.time ≤ A.cost := by unfold Machine.cost; omega
  have h1 := A.one_le_cost
  have e1 : A.time * (Q + 2 * L + 4 * ops + 17) ≤ A.cost * (Q + 2 * L + 4 * ops + 17) :=
    Nat.mul_le_mul_right _ hT
  have e2 : 4 * E + 21 ≤ (4 * E + 21) * A.cost := Nat.le_mul_of_pos_right _ h1
  calc _ ≤ _ := h
    _ ≤ A.cost * (Q + 2 * L + 4 * ops + 17) + (4 * E + 21) * A.cost := by omega
    _ = inlSlope ops Q L E * A.cost := by unfold inlSlope; ring

theorem Machine.time_mid_le_cost (pt : ℕ) (hPostT : Post.time ≤ pt * A.cost) :
    ((A.inlineOracleInit H w₀ E Q L).andThenLin Post).time ≤ chainSlope ops Q L E pt * A.cost := by
  have h := Machine.time_andThenLin_le (A.inlineOracleInit H w₀ E Q L) Post
  have hI := Machine.time_inl_le_cost A H w₀ E Q L
  have h1 := A.one_le_cost
  have e : chainSlope ops Q L E pt * A.cost =
      11 * (inlSlope ops Q L E * A.cost) + 10 * A.cost + pt * A.cost := by
    unfold chainSlope; ring
  rw [e]
  omega

/-- **The clock of the chain**. -/
theorem Machine.time_chain_le (pt : ℕ) (hPostT : Post.time ≤ pt * A.cost) :
    (P.andThenLin (((A.inlineOracleInit H w₀ E Q L).andThenLin Post).andThenGuard D)).time ≤
      11 * P.time + 23 + 11 * (chainSlope ops Q L E pt * A.cost) + D.time := by
  have h1 := Machine.time_andThenLin_le P
    (((A.inlineOracleInit H w₀ E Q L).andThenLin Post).andThenGuard D)
  have h2 := Machine.time_andThenGuard_le ((A.inlineOracleInit H w₀ E Q L).andThenLin Post) D
  have h3 := Machine.time_mid_le_cost Post A H w₀ E Q L pt hPostT
  omega

/-- **The description length of the chain**: at most `60 · R · 3 ^ K₀ · e · A.cost · D.descLen`. -/
theorem Machine.descLen_chain_le (pt : ℕ) (hPostT : Post.time ≤ pt * A.cost) :
    (P.andThenLin (((A.inlineOracleInit H w₀ E Q L).andThenLin Post).andThenGuard D)).descLen ≤
      60 * chainStates P Post H Q L E pt w₀.length * 3 ^ chainTapes P Post ops m *
        (5 + 4 * chainTapes P Post ops m + Nat.size (chainStates P Post H Q L E pt w₀.length)) *
        A.cost * D.descLen := by
  set Inl := A.inlineOracleInit H w₀ E Q L with hInl
  set M1 := Inl.andThenLin Post with hM1
  set M2 := M1.andThenGuard D with hM2
  have hK := Machine.tapes_chain P Post D A H w₀ E Q L
  rw [← hInl, ← hM1, ← hM2] at hK
  have hS : (P.andThenLin M2).states = (clockDigits P.tapes P.time).length + 2 * P.states +
      ((clockDigits M1.tapes M1.time).length + 2 * ((clockDigits Inl.tapes Inl.time).length +
        2 * Inl.states + Post.states + 11) + D.states + 15) + 11 := by
    rw [Machine.states_andThenLin, Machine.states_andThenGuard, Machine.states_andThenLin]
  have hsI : Inl.states = ((clockDigits A.tapes (A.time + 1)).length + 4) +
      3 ^ ops * (1 + ∑ o, (9 + (H o).states)) + 9 +
      A.states * (w₀.length + 2) * (3 ^ ops * (1 + ∑ o, (9 + (H o).states))) := by
    rw [hInl, Machine.states_inlineOracleInit, inlineStatesInit]; ring
  set h := (clockDigits A.tapes A.cost).length with hh
  have hA1 : A.time + 1 ≤ A.cost := by
    have := A.descLen_ge
    have := A.one_le_states'
    have := Nat.one_le_pow A.tapes 3 (by norm_num)
    have : 1 ≤ 6 * A.states * 3 ^ A.tapes * (4 + 4 * A.tapes + Nat.size A.states) :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    unfold Machine.cost; omega
  have hA : (clockDigits A.tapes (A.time + 1)).length ≤ h := clockDigits_length_mono _ hA1
  have hI : (clockDigits Inl.tapes Inl.time).length ≤ h + Nat.size (inlSlope ops Q L E) :=
    clockDigits_length_le_of_le_mul (by simp [Inl]; omega) (Machine.time_inl_le_cost A H w₀ E Q L)
  have hM : (clockDigits M1.tapes M1.time).length ≤ h + Nat.size (chainSlope ops Q L E pt) :=
    clockDigits_length_le_of_le_mul (by simp [M1, Inl]; omega)
      (Machine.time_mid_le_cost Post A H w₀ E Q L pt hPostT)
  have hcore := A.digit_core_cost
  rw [← hh] at hcore
  rw [Machine.descLen_eq (P.andThenLin M2), hS, hK, hsI, Machine.descLen_eq D]
  unfold chainStates
  -- abstract everything
  generalize (clockDigits A.tapes (A.time + 1)).length = hA' at *
  generalize (clockDigits Inl.tapes Inl.time).length = hI' at *
  generalize (clockDigits M1.tapes M1.time).length = hM' at *
  generalize (clockDigits P.tapes P.time).length = hP at *
  generalize 3 ^ ops * (1 + ∑ o, (9 + (H o).states)) = GZ at *
  generalize Nat.size (inlSlope ops Q L E) = zI at *
  generalize Nat.size (chainSlope ops Q L E pt) = zM at *
  generalize chainTapes P Post ops m = K₀ at *
  generalize A.cost = a at *
  have hsA := A.one_le_states'
  have hsD := D.one_le_states
  generalize A.states = sA at *
  generalize D.states = sD at *
  generalize A.tapes = kA at *
  generalize D.tapes = kD at *
  generalize w₀.length = wl at *
  generalize P.states = sP at *
  generalize Post.states = sPo at *
  clear_value h
  -- the states
  set R := hP + 2 * sP + 2 * sPo + 4 * GZ * (wl + 3) + 2 * zI + zM + 108 with hR
  set V := sA + h with hV
  have hY : 1 ≤ V * sD := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hVY : V ≤ V * sD := Nat.le_mul_of_pos_right _ (by omega)
  have hDY : sD ≤ V * sD := Nat.le_mul_of_pos_left _ (by omega)
  have hSt : hP + 2 * sP + (hM' + 2 * (hI' + 2 * (hA' + 4 + GZ + 9 + sA * (wl + 2) * GZ) + sPo + 11) +
      sD + 15) + 11 ≤ R * V * sD := by
    set B := hP + 2 * sP + 2 * sPo + 4 * GZ + 2 * zI + zM + 100 with hB
    set Y := V * sD with hYd
    set W := GZ * (wl + 2) with hW
    have e1 : W * sA ≤ W * Y := Nat.mul_le_mul_left _ (by omega)
    have e2 : B ≤ B * Y := Nat.le_mul_of_pos_right _ hY
    have e3 : R * V * sD = B * Y + 4 * (W * Y) + 8 * Y := by
      rw [hR, hB, hW, Nat.mul_assoc R]; ring
    have e4 : sA * (wl + 2) * GZ = W * sA := by rw [hW]; ring
    rw [e3, e4]
    have hAh : hA' ≤ Y := by omega
    generalize W * sA = x at *
    generalize W * Y = y at *
    generalize B * Y = z at *
    omega
  set S := hP + 2 * sP + (hM' + 2 * (hI' + 2 * (hA' + 4 + GZ + 9 + sA * (wl + 2) * GZ) + sPo + 11) +
      sD + 15) + 11 with hSd
  -- the entry bits
  have hsz : Nat.size S ≤ Nat.size R + (Nat.size sA + h + 1) + Nat.size sD := by
    have e1 := (Nat.size_le_size hSt).trans (Compose.size_mul_le _ _)
    have e2 := Compose.size_mul_le R V
    have e3 : Nat.size V ≤ Nat.size sA + Nat.size h + 1 := size_add_le' sA h
    have e4 := size_le_self' h
    omega
  set u := kA + 1 + Nat.size sA + h with hu
  set eD := 4 + 4 * kD + Nat.size sD with heD
  set eR := 5 + 4 * K₀ + Nat.size R with heR
  have hE : 4 + 4 * (K₀ + kA + kD) + Nat.size S ≤ eR * u * eD := by
    have hle : 4 + 4 * (K₀ + kA + kD) + Nat.size S + 4 ≤ eR + 4 * u + eD := by omega
    have hx : 5 ≤ eR := by omega
    have hy : 1 ≤ u := by omega
    have hz : 4 ≤ eD := by omega
    have : eR + 4 * u + eD ≤ eR * u * eD := by
      have k1 : eR * u * eD ≥ eR * u * 4 := Nat.mul_le_mul_left _ hz
      have k2 : eR * u ≥ 5 * u := Nat.mul_le_mul_right _ hx
      have k3 : eR * u ≥ eR := Nat.le_mul_of_pos_right _ hy
      have k4 : eR * u * eD ≥ 5 * eD := by
        calc eR * u * eD ≥ 5 * 1 * eD := by gcongr
          _ = 5 * eD := by ring
      omega
    omega
  calc 6 * S * 3 ^ (K₀ + kA + kD) * (4 + 4 * (K₀ + kA + kD) + Nat.size S)
      ≤ 6 * (R * V * sD) * 3 ^ (K₀ + kA + kD) * (eR * u * eD) := by gcongr
    _ = (R * 3 ^ K₀ * eR) * (3 ^ kA * V * u) * (6 * sD * 3 ^ kD * eD) := by
        rw [pow_add, pow_add]; ring
    _ ≤ (R * 3 ^ K₀ * eR) * (60 * a) * (6 * sD * 3 ^ kD * eD) := by gcongr
    _ = 60 * R * 3 ^ K₀ * eR * a * (6 * sD * 3 ^ kD * eD) := by ring

/-- **The structured cost of the chain**: `cost ≤ chainConst … · A.cost · D.cost`. -/
theorem Machine.cost_chain_le (pt : ℕ) (hPostT : Post.time ≤ pt * A.cost) :
    (P.andThenLin (((A.inlineOracleInit H w₀ E Q L).andThenLin Post).andThenGuard D)).cost ≤
      chainConst P Post H Q L E pt w₀.length * A.cost * D.cost := by
  have ht := Machine.time_chain_le P Post D A H w₀ E Q L pt hPostT
  have hd := Machine.descLen_chain_le P Post D A H w₀ E Q L pt hPostT
  have ha := A.one_le_cost
  have hdc := D.one_le_cost
  have hTD := D.time_le_cost
  have hDD := D.descLen_le_cost
  rw [Machine.cost]
  unfold chainConst
  generalize 60 * chainStates P Post H Q L E pt w₀.length * 3 ^ chainTapes P Post ops m *
      (5 + 4 * chainTapes P Post ops m + Nat.size (chainStates P Post H Q L E pt w₀.length)) = F
    at hd ⊢
  generalize chainSlope ops Q L E pt = c at ht ⊢
  generalize A.cost = a at *
  generalize D.cost = d at *
  have hY : 1 ≤ a * d := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have e1 : F * a * D.descLen ≤ F * a * d := Nat.mul_le_mul_left _ hDD
  have e2 : 11 * P.time + 23 ≤ (11 * P.time + 23) * (a * d) := Nat.le_mul_of_pos_right _ hY
  have e3 : 11 * (c * a) ≤ 11 * c * (a * d) := by
    calc 11 * (c * a) = 11 * c * a * 1 := by ring
      _ ≤ 11 * c * a * d := by gcongr
      _ = _ := by ring
  have e4 : D.time ≤ a * d := hTD.trans (Nat.le_mul_of_pos_left _ (by omega))
  calc _ ≤ 11 * P.time + 23 + 11 * (c * a) + D.time + F * a * D.descLen := by omega
    _ ≤ (11 * P.time + 23) * (a * d) + 11 * c * (a * d) + a * d + F * a * d := by omega
    _ = (F + 11 * P.time + 11 * c + 24) * a * d := by ring

end Chain

end SigabaNeo
