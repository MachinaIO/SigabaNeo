import SigabaNeo.Lib.Machines.Inline.LinMain

/-!
# Inlining an oracle handler with a short preparation: explicit bounds

* `Machine.tapes_inlineOracleLin`, `Machine.states_inlineOracleLin`, `Machine.time_inlineOracleLin`:
  the exact numbers of tapes and states, and the clock;
* `clockDigits_length_le_size`: the preparation has at most `Nat.size A.time + 4` states;
* `Machine.time_inlineOracleLin_le`: `time ≤ A.time * (Q + 2 L + 4 ops + 17) + 5`;
* `Machine.descLen_inlineOracleLin_le`: `descLen ≤ linDescFactor H * A.cost`;
* `Machine.cost_inlineOracleLin_le`: `cost ≤ linFactor H Q L * A.cost`.

The description length is linear in `A.cost = A.time + A.descLen` although the preparation has
`h ≈ Nat.size A.time / (A.tapes + 1)` states, each with `3 ^ A.tapes` rows of width `≈ 4 A.tapes`
(times factors depending only on the handlers): the cross term `h * 3 ^ A.tapes * A.tapes` is at
most `Nat.size A.time * 3 ^ A.tapes`, and `a * b ≤ T + b * (2 Nat.size b + 4)` whenever
`a ≤ Nat.size T` (`mul_le_of_le_size`); the term `h ^ 2 * 3 ^ A.tapes` is handled by
`sq_mul_le_of_digits`.
-/

namespace SigabaNeo

open Cslib Turing MultiTapeMachine Inline

variable {ops m : ℕ}

/-! ### Arithmetic -/

theorem size_le_self' (n : ℕ) : Nat.size n ≤ n :=
  Nat.size_le.mpr Nat.lt_two_pow_self

theorem size_add_le' (a b : ℕ) : Nat.size (a + b) ≤ Nat.size a + Nat.size b + 1 := by
  rw [Nat.size_le]
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  have h1 : 2 ^ Nat.size a ≤ 2 ^ (Nat.size a + Nat.size b) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ Nat.size b ≤ 2 ^ (Nat.size a + Nat.size b) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]
  omega

theorem size_three_pow (k : ℕ) : Nat.size (3 ^ k) ≤ 2 * k + 1 := by
  rw [Nat.size_le]
  calc 3 ^ k ≤ 4 ^ k := Nat.pow_le_pow_left (by norm_num) _
    _ = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
    _ < 2 ^ (2 * k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem two_mul_le_two_pow (r : ℕ) : 2 * r ≤ 2 ^ r := by
  rcases r with _ | r
  · simp
  · have := Nat.lt_two_pow_self (n := r)
    rw [pow_succ]
    omega

/-- **A product with a small factor**: if `a ≤ Nat.size T` then `a * b ≤ T + b * (2 Nat.size b + 4)`
(either `a` is at most twice the size of `b`, or `b` is so small that `a * b ≤ 2 ^ (a - 1) ≤ T`). -/
theorem mul_le_of_le_size (T a b : ℕ) (ha : a ≤ Nat.size T) :
    a * b ≤ T + b * (2 * Nat.size b + 4) := by
  by_cases hab : a ≤ 2 * Nat.size b + 4
  · calc a * b ≤ (2 * Nat.size b + 4) * b := Nat.mul_le_mul_right _ hab
      _ = b * (2 * Nat.size b + 4) := by ring
      _ ≤ _ := Nat.le_add_left _ _
  · set j := Nat.size b
    have hb : b < 2 ^ j := Nat.lt_size_self b
    have hT : 2 ^ (a - 1) ≤ T := Nat.lt_size.mp (by omega)
    set r := a - 1 - j with hr
    have hr2 : a ≤ 2 * r := by omega
    have h2r := two_mul_le_two_pow r
    have hsplit : 2 ^ (a - 1) = 2 ^ j * 2 ^ r := by rw [← pow_add]; congr 1; omega
    calc a * b ≤ a * 2 ^ j := Nat.mul_le_mul_left _ hb.le
      _ ≤ 2 ^ r * 2 ^ j := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ (a - 1) := by rw [hsplit]; ring
      _ ≤ T := hT
      _ ≤ _ := Nat.le_add_right _ _

theorem sq_le_two_pow_succ (h : ℕ) : h * h ≤ 2 ^ (h + 1) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rcases Nat.lt_or_ge h 3 with hh | hh
    · interval_cases h <;> norm_num
    · rw [pow_succ]
      nlinarith

/-- The square of the number of digits: `h ^ 2 * 3 ^ k ≤ 4 T + 2 (k + 1) h 3 ^ k`, when the `h`
digits of base `2 ^ (k + 1)` encode `T`. -/
theorem sq_mul_le_of_digits (k h T : ℕ) (hh : h = 0 ∨ (k + 1) * (h - 1) < Nat.size T) :
    h * h * 3 ^ k ≤ 4 * T + 2 * (k + 1) * h * 3 ^ k := by
  rcases Nat.lt_or_ge h (k + 3) with h1 | h1
  · have : h * h ≤ 2 * (k + 1) * h := by nlinarith
    calc h * h * 3 ^ k ≤ 2 * (k + 1) * h * 3 ^ k := Nat.mul_le_mul_right _ this
      _ ≤ _ := Nat.le_add_left _ _
  · rcases hh with hh | hh
    · omega
    have hT : 2 ^ ((k + 1) * (h - 1)) ≤ T := Nat.lt_size.mp hh
    have hsq := sq_le_two_pow_succ h
    have h3 : 3 ^ k ≤ 2 ^ (k * (h - 1)) :=
      calc 3 ^ k ≤ 4 ^ k := Nat.pow_le_pow_left (by norm_num) _
        _ = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
        _ ≤ 2 ^ (k * (h - 1)) := Nat.pow_le_pow_right (by norm_num)
          (by rw [mul_comm 2 k]; exact Nat.mul_le_mul_left k (by omega))
    have hsplit : 2 ^ (h + 1) * 2 ^ (k * (h - 1)) = 4 * 2 ^ ((k + 1) * (h - 1)) := by
      rw [← pow_add, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      have : h + 1 = (h - 1) + 2 := by omega
      rw [this]; ring
    calc h * h * 3 ^ k ≤ 2 ^ (h + 1) * 2 ^ (k * (h - 1)) := Nat.mul_le_mul hsq h3
      _ = 4 * 2 ^ ((k + 1) * (h - 1)) := hsplit
      _ ≤ 4 * T := Nat.mul_le_mul_left _ hT
      _ ≤ _ := Nat.le_add_right _ _

/-! ### The digits of the clock -/

theorem clockDigits_length_lt (kA T : ℕ) (hT : T ≠ 0) :
    (kA + 1) * ((clockDigits kA T).length - 1) < Nat.size T := by
  have hB : 1 < baseB kA := by have := baseB_two_le (kA := kA); omega
  have hle := Nat.base_pow_length_digits_le (baseB kA) T hB hT
  have hne : (clockDigits kA T) ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hT
  have hpos : 0 < (clockDigits kA T).length := List.length_pos_iff.mpr hne
  apply Nat.lt_size.mpr
  have : baseB kA ^ ((clockDigits kA T).length - 1) ≤ T := by
    have e : baseB kA ^ (clockDigits kA T).length =
        baseB kA * baseB kA ^ ((clockDigits kA T).length - 1) := by
      rw [← pow_succ']; congr 1; omega
    unfold clockDigits at e
    rw [e] at hle
    exact Nat.le_of_mul_le_mul_left hle (by omega)
  calc 2 ^ ((kA + 1) * ((clockDigits kA T).length - 1))
      = baseB kA ^ ((clockDigits kA T).length - 1) := by rw [pow_mul]
    _ ≤ T := this

theorem clockDigits_length_digits (kA T : ℕ) :
    (clockDigits kA T).length = 0 ∨
      (kA + 1) * ((clockDigits kA T).length - 1) < Nat.size T := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · left; simp [clockDigits]
  · right; exact clockDigits_length_lt kA T (by omega)

/-- The number of digits of the clock is at most its size. -/
theorem clockDigits_length_le_size (kA T : ℕ) : (clockDigits kA T).length ≤ Nat.size T := by
  rcases clockDigits_length_digits kA T with h | h
  · omega
  · have : (clockDigits kA T).length - 1 ≤ (kA + 1) * ((clockDigits kA T).length - 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega

theorem clockDigits_mul_le (kA T : ℕ) :
    (kA + 1) * (clockDigits kA T).length ≤ Nat.size T + kA + 1 := by
  rcases Nat.eq_zero_or_pos (clockDigits kA T).length with h0 | h0
  · rw [h0]; omega
  rcases clockDigits_length_digits kA T with h | h
  · omega
  · have e : (kA + 1) * (clockDigits kA T).length =
        (kA + 1) * ((clockDigits kA T).length - 1) + (kA + 1) := by
      rw [← Nat.mul_succ]; congr 1; omega
    omega

/-! ### Tapes, states, clock -/

@[simp] theorem Machine.tapes_inlineOracleLin (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (Q L : ℕ) : (A.inlineOracleLin H Q L).tapes = A.tapes + 2 * ops + 2 + m := rfl

@[simp] theorem Machine.time_inlineOracleLin (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (Q L : ℕ) :
    (A.inlineOracleLin H Q L).time =
      inlineTimeLin A.time (clockDigits A.tapes A.time).length Q L ops := rfl

/-- The number of states of the inlined machine with a short preparation. -/
def inlineStatesLin (A : Machine ops) (H : Fin ops → Routine (m + 3)) : ℕ :=
  ((clockDigits A.tapes A.time).length + 4) + A.states * 3 ^ ops * (1 + ∑ o, (9 + (H o).states))

theorem Machine.states_inlineOracleLin (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (Q L : ℕ) : (A.inlineOracleLin H Q L).states = inlineStatesLin A H := by
  simp only [Machine.inlineOracleLin, Machine.states_ofPTMOps, LState, Ctl, inlineStatesLin,
    Fintype.card_sum, Fintype.card_fin, Fintype.card_prod, Fintype.card_option,
    Fintype.card_sigma, Fintype.card_pi, AFlag.card, QStep.card, LStep.card, Finset.prod_const,
    Finset.card_univ, Routine.states]
  ring

/-- The number of states: `Nat.size A.time + 4` for the preparation, plus the simulation. -/
theorem Machine.states_inlineOracleLin_le (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (Q L : ℕ) : (A.inlineOracleLin H Q L).states ≤
      Nat.size A.time + 4 + A.states * 3 ^ ops * (1 + ∑ o, (9 + (H o).states)) := by
  rw [Machine.states_inlineOracleLin, inlineStatesLin]
  have := clockDigits_length_le_size A.tapes A.time
  omega

theorem Machine.time_inlineOracleLin_le (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (Q L : ℕ) :
    (A.inlineOracleLin H Q L).time ≤ A.time * (Q + 2 * L + 4 * ops + 17) + 5 := by
  have h1 := clockDigits_length_le_size A.tapes A.time
  have h2 := size_le_self' A.time
  simp only [Machine.time_inlineOracleLin, inlineTimeLin]
  nlinarith

/-! ### Description length and cost -/

theorem piece_mul (T h b u : ℕ) (hhs : h ≤ Nat.size T) (hsb : Nat.size b ≤ 2 * u) (hu : 1 ≤ u) :
    b * h ≤ T + 8 * (b * u) := by
  have h1 := mul_le_of_le_size T h b hhs
  have h2 : b * (2 * Nat.size b + 4) ≤ b * (4 * u + 4) := Nat.mul_le_mul_left _ (by omega)
  have h3 : b * (4 * u + 4) ≤ 8 * (b * u) := by
    have : b ≤ b * u := Nat.le_mul_of_pos_right _ hu
    calc b * (4 * u + 4) = 4 * (b * u) + 4 * b := by ring
      _ ≤ 8 * (b * u) := by omega
  calc b * h = h * b := by ring
    _ ≤ _ := by omega

theorem piece_tapes (T h G k : ℕ) (hkh : (k + 1) * h ≤ Nat.size T + k + 1)
    (hsG : Nat.size G ≤ 2 * k + 1) : G * h * (k + 1) ≤ T + 7 * (G * (k + 1)) := by
  have h1 := mul_le_of_le_size T (Nat.size T) G le_rfl
  have h2 : G * h * (k + 1) ≤ Nat.size T * G + G * (k + 1) :=
    calc G * h * (k + 1) = G * ((k + 1) * h) := by ring
      _ ≤ G * (Nat.size T + k + 1) := Nat.mul_le_mul_left _ hkh
      _ = Nat.size T * G + G * (k + 1) := by ring
  have h3 : G * (2 * Nat.size G + 4) ≤ 6 * (G * (k + 1)) :=
    calc G * (2 * Nat.size G + 4) ≤ G * (6 * (k + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 6 * (G * (k + 1)) := by ring
  omega

theorem piece_w (T h G w k V u : ℕ) (hhs : h ≤ Nat.size T) (hsG : Nat.size G ≤ 2 * k + 1)
    (hwV : w ≤ 2 * V) (hwu : w ≤ u) (hku : k + 1 ≤ u) : G * h * w ≤ T + 16 * (G * V * u) := by
  have h1 := mul_le_of_le_size T h (G * w) hhs
  have hsGw : Nat.size (G * w) ≤ 2 * k + 1 + w :=
    (size_mul_le' _ _).trans (by have := size_le_self' w; omega)
  have h2 : G * w * (2 * Nat.size (G * w) + 4) ≤ G * (2 * V) * (8 * u) :=
    calc G * w * (2 * Nat.size (G * w) + 4) ≤ G * w * (8 * u) :=
          Nat.mul_le_mul_left _ (by omega)
      _ ≤ G * (2 * V) * (8 * u) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hwV)
  have e : G * (2 * V) * (8 * u) = 16 * (G * V * u) := by ring
  calc G * h * w = h * (G * w) := by ring
    _ ≤ _ := by omega

/-- The factor of the description length bound: it depends only on `ops`, `m` and the numbers of
states of the handlers. -/
def linDescFactor (H : Fin ops → Routine (m + 3)) : ℕ :=
  let Z := 1 + ∑ o, (9 + (H o).states)
  360 * 3 ^ (2 * ops + 2 + m) * (Z + 4) * (4 * (2 * ops + 2 + m) + 14 + Nat.size Z)

/-- **Description length of the inlined machine with a short preparation**:
`descLen ≤ linDescFactor H * A.cost`. -/
theorem Machine.descLen_inlineOracleLin_le (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (Q L : ℕ) : (A.inlineOracleLin H Q L).descLen ≤ linDescFactor H * A.cost := by
  obtain ⟨k, hk⟩ : ∃ k, k = A.tapes := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s, s = A.states := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T, T = A.time := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D, D = A.descLen := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h, h = (clockDigits k T).length := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 1 + ∑ o, (9 + (H o).states) := ⟨_, rfl⟩
  obtain ⟨K', hK'⟩ : ∃ K', K' = 2 * ops + 2 + m := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, X = A.cost := ⟨_, rfl⟩
  obtain ⟨cW, hcW⟩ : ∃ cW, cW = 4 * K' + 14 + Nat.size Z := ⟨_, rfl⟩
  obtain ⟨S', hS'⟩ : ∃ S', S' = inlineStatesLin A H := ⟨_, rfl⟩
  have hS'e : S' = (h + 4) + s * 3 ^ ops * Z := by
    rw [hS', inlineStatesLin, hh, hk, hTdef, hsdef, hZ]
  have hs : 0 < s := hsdef ▸ Fin.pos A.machine.initial
  have hTX : T ≤ X := by rw [hX, hTdef, Machine.cost]; omega
  have hDX : D ≤ X := by rw [hX, hDdef, Machine.cost]; omega
  have hDe : D = 6 * s * 3 ^ k * 3 ^ ops * Machine.entryBits k s ops := by
    rw [hDdef, Machine.descLen, hk, hsdef]
  have hdesc : (A.inlineOracleLin H Q L).descLen =
      6 * S' * (3 ^ k * 3 ^ K') * Machine.entryBits (k + K') S' 0 := by
    rw [Machine.descLen, Machine.states_inlineOracleLin, Machine.tapes_inlineOracleLin, ← hS',
      ← hk, pow_zero, Nat.mul_one, ← pow_add, hK']
    simp only [Nat.add_assoc]
  have hhs : h ≤ Nat.size T := hh ▸ clockDigits_length_le_size k T
  have hkh : (k + 1) * h ≤ Nat.size T + k + 1 := hh ▸ clockDigits_mul_le k T
  have hdig : h = 0 ∨ (k + 1) * (h - 1) < Nat.size T := hh ▸ clockDigits_length_digits k T
  have hfac : linDescFactor H = 360 * 3 ^ K' * (Z + 4) * cW := by
    simp only [linDescFactor]; rw [hcW, hK', hZ]
  rw [hdesc, hfac, ← hX]
  have hsG : Nat.size (3 ^ k) ≤ 2 * k + 1 := size_three_pow k
  have hG1 : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have hsV : Nat.size (s * 3 ^ ops) ≤ Nat.size s + 2 * ops + 1 :=
    (size_mul_le' _ _).trans (by have := size_three_pow ops; omega)
  have hV1 : 1 ≤ s * 3 ^ ops := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hwV : Nat.size s + ops ≤ 2 * (s * 3 ^ ops) := by
    have h1 : Nat.size s ≤ s * 3 ^ ops :=
      (size_le_self' s).trans (Nat.le_mul_of_pos_right _ (by positivity))
    have h2 : ops ≤ s * 3 ^ ops := (Nat.lt_pow_self (by norm_num : 1 < 3)).le.trans
      (Nat.le_mul_of_pos_left _ hs)
    omega
  have hE : k + 1 + Nat.size s + ops ≤ Machine.entryBits k s ops := by
    simp only [Machine.entryBits]; omega
  have hVu : 3 ^ k * (s * 3 ^ ops) * (k + 1 + Nat.size s + ops) ≤ D := by
    rw [hDe]
    calc 3 ^ k * (s * 3 ^ ops) * (k + 1 + Nat.size s + ops)
        = 1 * s * 3 ^ k * 3 ^ ops * (k + 1 + Nat.size s + ops) := by ring
      _ ≤ 6 * s * 3 ^ k * 3 ^ ops * Machine.entryBits k s ops := by gcongr; omega
  have hSs : Nat.size S' ≤ h + Nat.size s + 2 * ops + Nat.size Z + 6 := by
    rw [hS'e]
    have := size_add_le' (h + 4) (s * 3 ^ ops * Z)
    have := size_le_self' (h + 4)
    have := size_mul_le' (s * 3 ^ ops) Z
    omega
  have P4 := sq_mul_le_of_digits k h T hdig
  clear hS' hh hDdef hdesc hfac hX hk hsdef hTdef hDe hE hZ hK'
  generalize 3 ^ k = G at *
  generalize s * 3 ^ ops = V at *
  generalize hu : k + 1 + Nat.size s + ops = u at *
  have hu1 : 1 ≤ u := by omega
  have hwu : Nat.size s + ops ≤ u := by omega
  have hku : k + 1 ≤ u := by omega
  -- the pieces of `G (V + h) (u + h)`
  have hGV : Nat.size (G * V) ≤ 2 * u := (size_mul_le' _ _).trans (by omega)
  have P1 := piece_mul T h (G * V) u hhs hGV hu1
  have P2 := piece_tapes T h G k hkh hsG
  have P2' : G * (k + 1) ≤ G * V * u :=
    calc G * (k + 1) ≤ G * u := Nat.mul_le_mul_left _ hku
      _ ≤ G * V * u := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hV1)
  have P3 := piece_w T h G (Nat.size s + ops) k V u hhs hsG hwV hwu hku
  have P4' : h * h * G = G * h * h := by ring
  have P4'' : 2 * (k + 1) * h * G = 2 * (G * h * (k + 1)) := by ring
  have hcore : G * (V + h) * (u + h) ≤ 60 * X := by
    have e : G * (V + h) * (u + h) =
        G * V * u + G * V * h + G * h * (k + 1) + G * h * (Nat.size s + ops) + G * h * h := by
      rw [← hu]; ring
    rw [e]
    linarith
  -- the number of states and the entry width
  have hS'le : S' ≤ (Z + 4) * (V + h) := by
    rw [hS'e]
    have : V ≤ V * Z + 4 * V := Nat.le_add_left _ _ |>.trans' (by omega)
    nlinarith
  have hW : Machine.entryBits (k + K') S' 0 ≤ cW * (u + h) := by
    simp only [Machine.entryBits, Nat.size_zero]
    have e : cW * (u + h) = 4 * u + (4 * K' + 10 + Nat.size Z) * u + cW * h := by
      rw [hcW]; ring
    have h1 : 4 * K' + 10 + Nat.size Z ≤ (4 * K' + 10 + Nat.size Z) * u :=
      Nat.le_mul_of_pos_right _ hu1
    have h2 : h ≤ cW * h := Nat.le_mul_of_pos_left _ (by omega)
    omega
  calc 6 * S' * (G * 3 ^ K') * Machine.entryBits (k + K') S' 0
      ≤ 6 * ((Z + 4) * (V + h)) * (G * 3 ^ K') * (cW * (u + h)) := by gcongr
    _ = 6 * 3 ^ K' * (Z + 4) * cW * (G * (V + h) * (u + h)) := by ring
    _ ≤ 6 * 3 ^ K' * (Z + 4) * cW * (60 * X) := Nat.mul_le_mul_left _ hcore
    _ = 360 * 3 ^ K' * (Z + 4) * cW * X := by ring

/-- The factor of the cost bound: it depends only on `ops`, `m`, the numbers of states of the
handlers, `Q` and `L`. -/
def linFactor (H : Fin ops → Routine (m + 3)) (Q L : ℕ) : ℕ :=
  linDescFactor H + (Q + 2 * L + 4 * ops + 22)

/-- **Cost of the inlined machine with a short preparation**: `cost ≤ linFactor H Q L * A.cost`. -/
theorem Machine.cost_inlineOracleLin_le (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (Q L : ℕ) : (A.inlineOracleLin H Q L).cost ≤ linFactor H Q L * A.cost := by
  have ht := A.time_inlineOracleLin_le H Q L
  have hd := A.descLen_inlineOracleLin_le H Q L
  have h1 := A.one_le_cost
  have hT : A.time ≤ A.cost := by unfold Machine.cost; omega
  have h2 := Nat.mul_le_mul_left (Q + 2 * L + 4 * ops + 17) hT
  rw [Machine.cost, linFactor]
  nlinarith

end SigabaNeo
