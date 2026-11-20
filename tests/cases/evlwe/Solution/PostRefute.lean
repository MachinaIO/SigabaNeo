import Solution.Post
import Solution.AttackPPT
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Post is distinguishable

The attack's advantage is at least `1 − errA − errB`, where `errA` bounds its rejection
probability on `postReal` and `errB` its acceptance probability on `postRandom`:
`errA + errB ≤ 1/64 + 7/8 + 6400 (κ + 1)^6 / 2^κ`. So for all large `κ` the advantage is at least
`1/32`, which is not negligible: `not_post`.
-/

namespace TestCase.EvLWE

open SigabaNeo.Lattices

open TestCase TestCase.EvLWE Cslib Cslib.Crypto Cslib.Probability Filter
open scoped ENNReal NNReal Matrix Topology

/-! ### `ℝ≥0∞` to `ℝ` -/

theorem natCast_div_eq {a b : ℕ} (hb : 0 < b) :
    (a : ℝ≥0∞) / (b : ℝ≥0∞) = ENNReal.ofReal ((a : ℝ) / b) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hb), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]

theorem natCast_div_le {a b : ℕ} {x : ℝ} (hb : 0 < b) (h : (a : ℝ) ≤ x * b) :
    (a : ℝ≥0∞) / (b : ℝ≥0∞) ≤ ENNReal.ofReal x := by
  rw [natCast_div_eq hb]
  exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ (by exact_mod_cast hb)).mpr h)

theorem natCast_mul_ofReal (a : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (a : ℝ≥0∞) * ENNReal.ofReal x = ENNReal.ofReal (a * x) := by
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

section
variable (κ : ℕ)

/-- `h = ⌊q/2⌋`. -/
noncomputable abbrev hq : ℕ := (q κ - 1) / 2

noncomputable def errA : ℝ :=
  1 / 64 + k κ * (3 * (1 / 2) ^ m κ) + m κ * (6 * (1 / 4) ^ m κ) +
    k κ * ((Δn κ + 2) / (hq κ + 1))

noncomputable def errB : ℝ :=
  (7 * (hq κ + 1) + 16) / (8 * (hq κ + 1)) + (q κ : ℝ) ^ n κ / (q κ : ℝ) ^ m κ +
    k κ * (1 / (q κ : ℝ) ^ n κ)

theorem card_badT_le :
    (Finset.univ.filter fun t : Fin (hq κ + 1) => ¬ GoodT κ t).card ≤ Δn κ + 2 := by
  have hqe : q κ = 2 * hq κ + 1 := q_eq_two_h κ
  calc (Finset.univ.filter fun t : Fin (hq κ + 1) => ¬ GoodT κ t).card
      = ((Finset.univ.filter fun t : Fin (hq κ + 1) => ¬ GoodT κ t).map Fin.valEmbedding).card :=
        (Finset.card_map _).symm
    _ ≤ (Finset.range ((Δn κ + 1) / 2) ∪ Finset.Ico (hq κ - Δn κ / 2) (hq κ + 1)).card := by
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_map] at hx
        obtain ⟨t, ht, rfl⟩ := hx
        have ht' : ¬ GoodT κ t := (Finset.mem_filter.mp ht).2
        unfold GoodT at ht'
        rw [not_and_or, not_le, not_lt] at ht'
        have := t.isLt
        simp only [Fin.valEmbedding_apply, Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
        omega
    _ ≤ _ := (Finset.card_union_le _ _).trans (by simp; omega)

theorem errReal_le : errReal κ ≤ ENNReal.ofReal (errA κ) := by
  classical
  have hB : ev (PMF.uniformOfFintype (Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ))))
      (fun B => ind (¬ dualMassE B (τ κ) ≤ 1 / 2)) ≤ ENNReal.ofReal (1 / 64) := by
    rw [ev_uniform_ind, card_matrix]
    have hc := card_bad_le κ
    have hfilt : (Finset.univ.filter fun B : Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ)) =>
        ¬ dualMassE B (τ κ) ≤ 1 / 2) = Finset.univ.filter fun B => 1 / 2 < dualMassE B (τ κ) := by
      ext B; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    rw [hfilt]
    refine natCast_div_le (pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) _) ?_
    have : ((64 * (Finset.univ.filter fun B : Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ)) =>
        1 / 2 < dualMassE B (τ κ)).card : ℕ) : ℝ) ≤ ((q κ ^ (n κ * m κ) : ℕ) : ℝ) := by
      exact_mod_cast hc
    push_cast at this ⊢
    linarith
  have hT : ev (PMF.uniformOfFintype (Matrix (Fin (ell κ)) (Fin (k κ)) (Fin (hq κ + 1))))
      (fun T => ind (∃ j ∈ Finset.univ, T (i0 κ) j ∈ Finset.univ.filter fun t => ¬ GoodT κ t)) ≤
      ENNReal.ofReal (k κ * ((Δn κ + 2) / (hq κ + 1))) := by
    refine (ev_badT_le _).trans ?_
    rw [← natCast_mul_ofReal _ (by positivity)]
    gcongr
    refine natCast_div_le (by omega) ?_
    have := card_badT_le κ
    push_cast
    rw [div_mul_cancel₀ _ (by positivity)]
    exact_mod_cast this
  unfold errReal errA
  calc _ ≤ ENNReal.ofReal (1 / 64) + ENNReal.ofReal (k κ * (3 * (1 / 2) ^ m κ)) +
        ENNReal.ofReal (m κ * (6 * (1 / 4) ^ m κ)) +
        ENNReal.ofReal (k κ * ((Δn κ + 2) / (hq κ + 1))) := by
        rw [← natCast_mul_ofReal _ (by positivity), ← natCast_mul_ofReal _ (by positivity)]
        gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]

theorem randAcc_le :
    ev (postRandom κ) (fun w => ind (parityOut κ w = true)) ≤ ENNReal.ofReal (errB κ) := by
  refine (ev_rand_acc_le κ).trans ?_
  have hq0 : (0 : ℝ) < q κ := q_pos κ
  have hρ : ρ κ = ENNReal.ofReal ((7 * (hq κ + 1) + 16) / (8 * (hq κ + 1))) := by
    unfold ρ; rw [natCast_div_eq (by omega)]; push_cast; rfl
  have hns := ev_not_surj_le (n := n κ) (m := m κ) (q := q κ)
  have hns' : ((q κ : ℝ≥0∞) ^ n κ / (q κ : ℝ≥0∞) ^ m κ) =
      ENNReal.ofReal ((q κ : ℝ) ^ n κ / (q κ : ℝ) ^ m κ) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow hq0.le,
      ENNReal.ofReal_pow hq0.le, ENNReal.ofReal_natCast]
  have hz := ev_zero_col_le (n := n κ) (q := q κ) (k κ)
  have hz' : (k κ : ℝ≥0∞) * (1 / (q κ : ℝ≥0∞) ^ n κ) =
      ENNReal.ofReal (k κ * (1 / (q κ : ℝ) ^ n κ)) := by
    rw [← natCast_mul_ofReal _ (by positivity), ENNReal.ofReal_div_of_pos (by positivity),
      ENNReal.ofReal_one, ENNReal.ofReal_pow hq0.le, ENNReal.ofReal_natCast]
  unfold errB
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity), ← hρ, ← hns', ← hz']
  push_cast at hns hz ⊢
  gcongr

/-! ### The advantage -/

theorem game_true (X : PMF (List Bool)) :
    (distinguishingGame X (attack κ)) true = ev X (fun w => ind (parityOut κ w = true)) := by
  rw [distinguishingGame_eq_bind]
  simp only [attack, ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.bind_apply]
  unfold ev ind
  refine tsum_congr fun w => ?_
  congr 1
  rw [PMF.pure_apply]
  split_ifs with h1 h2 h2 <;> simp_all

theorem adv_ge :
    1 - errA κ - errB κ ≤ (Game.advantage (distinguishingGame (postReal κ) (attack κ))
      (distinguishingGame (postRandom κ) (attack κ)) : ℝ) := by
  rw [Game.coe_advantage]
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, game_true]
  set P1 := ev (postReal κ) (fun w => ind (parityOut κ w = true))
  set R1 := ev (postReal κ) (fun w => ind (¬ parityOut κ w = true))
  set P2 := ev (postRandom κ) (fun w => ind (parityOut κ w = true))
  have hsum : P1 + R1 = 1 := ev_ind_add_not _ _
  have hR1 : R1 ≤ ENNReal.ofReal (errA κ) := (ev_real_rej_le κ).trans (errReal_le κ)
  have hP2 : P2 ≤ ENNReal.ofReal (errB κ) := randAcc_le κ
  have hA0 : 0 ≤ errA κ := by unfold errA; positivity
  have hB0 : 0 ≤ errB κ := by unfold errB; positivity
  have hR1t : R1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hsum ▸ le_add_self)
  have hP1t : P1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hsum ▸ le_self_add)
  have h1 : P1.toReal + R1.toReal = 1 := by
    rw [← ENNReal.toReal_add hP1t hR1t, hsum, ENNReal.toReal_one]
  have h2 : R1.toReal ≤ errA κ := ENNReal.toReal_le_of_le_ofReal hA0 hR1
  have h3 : P2.toReal ≤ errB κ := ENNReal.toReal_le_of_le_ofReal hB0 hP2
  have := le_abs_self (P1.toReal - P2.toReal)
  linarith

end

/-! ### The error terms vanish -/

/-- `(κ + 1)^6 / 2^κ`. -/
noncomputable def G (κ : ℕ) : ℝ := ((κ : ℝ) + 1) ^ 6 / 2 ^ κ

theorem tendsto_G : Tendsto G atTop (𝓝 0) := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt 6 (by norm_num : (1 : ℝ) < 2)
  have h1 := (Filter.tendsto_add_atTop_iff_nat 1).mpr h
  have h2 := h1.const_mul 2
  rw [mul_zero] at h2
  refine h2.congr fun κ => ?_
  unfold G; push_cast; rw [pow_succ]; field_simp; ring

section
variable (κ : ℕ)

theorem m_ge_real : (κ : ℝ) ≤ m κ := by unfold m n w; push_cast; nlinarith

theorem m_ge_n : n κ + 1 ≤ m κ := by unfold m n w; nlinarith

theorem hq1_ge : (2 : ℝ) ^ (8 * κ + 7) ≤ hq κ + 1 := by
  have hqe : (q κ : ℝ) = 2 * (hq κ : ℝ) + 1 := by exact_mod_cast q_eq_two_h κ
  have hg := q_gt κ
  have hw : (2 : ℝ) ^ w κ = 2 * 2 ^ (8 * κ + 7) := by
    unfold w; rw [show 8 * (κ + 1) = (8 * κ + 7) + 1 by ring, pow_succ]; ring
  rw [hw] at hg
  linarith

theorem q_ge_X : (2 : ℝ) ^ κ ≤ q κ := by
  have hg := q_gt κ
  have : (2 : ℝ) ^ κ ≤ 2 ^ w κ := pow_le_pow_right₀ (by norm_num) (by unfold w; omega)
  linarith

theorem errAB_le : errA κ + errB κ ≤ 1 / 64 + 7 / 8 + 6400 * G κ := by
  set c : ℝ := (κ : ℝ) + 1 with hc
  set X : ℝ := 2 ^ κ with hX
  have hc1 : 1 ≤ c := by rw [hc]; linarith [(Nat.cast_nonneg κ : (0 : ℝ) ≤ κ)]
  have hX1 : 1 ≤ X := one_le_pow₀ (by norm_num)
  have hX0 : 0 < X := by positivity
  have hm : (m κ : ℝ) ≤ 18 * c ^ 2 := by rw [hc]; exact m_le_real κ
  have hmκ : κ ≤ m κ := by unfold m n w; nlinarith
  have hm0 : (0 : ℝ) ≤ m κ := Nat.cast_nonneg _
  have hk : (k κ : ℝ) = m κ + 1 := by rw [k_eq]; push_cast; ring
  have hG : G κ = c ^ 6 / X := rfl
  set g := c ^ 6 / X with hg
  have hg0 : 0 ≤ g := by positivity
  have hc6 : 1 ≤ c ^ 6 := one_le_pow₀ hc1
  have hc2 : c ^ 2 ≤ c ^ 6 := pow_le_pow_right₀ hc1 (by norm_num)
  have hc4 : 1 ≤ c ^ 4 := one_le_pow₀ hc1
  have hgX : 1 / X ≤ g := by rw [hg]; gcongr
  have hc2g : c ^ 2 / X ≤ g := by rw [hg]; gcongr
  have hhalf : (1 / 2 : ℝ) ^ m κ ≤ 1 / X := by
    rw [one_div_pow, hX]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hmκ)
  have hquarter : (1 / 4 : ℝ) ^ m κ ≤ 1 / X :=
    le_trans (pow_le_pow_left₀ (by norm_num) (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2) _) hhalf
  have hh := hq1_ge κ
  have hX8 : (2 : ℝ) ^ (8 * κ + 7) = 128 * X ^ 8 := by
    rw [hX, show 8 * κ + 7 = κ * 8 + 7 by ring, pow_add, pow_mul]; ring
  rw [hX8] at hh
  have hX8' : X ≤ X ^ 8 := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ 8 := pow_le_pow_right₀ hX1 (by norm_num)
  have hpos : (0 : ℝ) < hq κ + 1 := by positivity
  -- term by term
  have t1 : (7 * ((hq κ : ℝ) + 1) + 16) / (8 * ((hq κ : ℝ) + 1)) ≤ 7 / 8 + 2 * g := by
    have hcx : 1 ≤ g * (hq κ + 1) := by
      calc (1 : ℝ) = 1 / X * X := by field_simp
        _ ≤ g * (hq κ + 1) := by
          apply mul_le_mul hgX (by nlinarith) hX0.le hg0
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have t2 : (k κ : ℝ) * (3 * (1 / 2) ^ m κ) ≤ 57 * g := by
    rw [hk]
    calc ((m κ : ℝ) + 1) * (3 * (1 / 2) ^ m κ) ≤ (18 * c ^ 2 + 1) * (3 * (1 / X)) :=
          mul_le_mul (by linarith) (by gcongr) (by positivity) (by positivity)
      _ = 54 * (c ^ 2 / X) + 3 * (1 / X) := by ring
      _ ≤ 54 * g + 3 * g := by gcongr
      _ = 57 * g := by ring
  have t3 : (m κ : ℝ) * (6 * (1 / 4) ^ m κ) ≤ 108 * g := by
    calc (m κ : ℝ) * (6 * (1 / 4) ^ m κ) ≤ (18 * c ^ 2) * (6 * (1 / X)) :=
          mul_le_mul hm (by gcongr) (by positivity) (by positivity)
      _ = 108 * (c ^ 2 / X) := by ring
      _ ≤ 108 * g := by gcongr
  have t4 : (k κ : ℝ) * ((Δn κ + 2) / (hq κ + 1)) ≤ 6194 * g := by
    have hΔ : (Δn κ : ℝ) = (m κ : ℝ) ^ 2 * (128 * X ^ 5) := by
      unfold Δn; push_cast
      rw [hX, show 5 * κ + 7 = κ * 5 + 7 by ring, pow_add, pow_mul]; ring
    have hm2 : (m κ : ℝ) ^ 2 ≤ 324 * c ^ 4 := by nlinarith
    have hX5 : 1 ≤ X ^ 5 := one_le_pow₀ hX1
    have hN : ((m κ : ℝ) + 1) * ((m κ : ℝ) ^ 2 * (128 * X ^ 5) + 2) ≤
        6194 * 128 * c ^ 6 * X ^ 5 := by
      have h1 : (m κ : ℝ) + 1 ≤ 19 * c ^ 2 := by nlinarith
      have h2 : (m κ : ℝ) ^ 2 * (128 * X ^ 5) + 2 ≤ 326 * c ^ 4 * (128 * X ^ 5) := by nlinarith
      calc _ ≤ (19 * c ^ 2) * (326 * c ^ 4 * (128 * X ^ 5)) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = _ := by ring
    rw [hk, hΔ, mul_div_assoc']
    calc ((m κ : ℝ) + 1) * ((m κ : ℝ) ^ 2 * (128 * X ^ 5) + 2) / (hq κ + 1)
        ≤ 6194 * 128 * c ^ 6 * X ^ 5 / (128 * X ^ 8) := by
          apply div_le_div₀ (by positivity) hN (by positivity) hh
      _ = 6194 * (c ^ 6 / X ^ 3) := by field_simp
      _ ≤ 6194 * g := by
          rw [hg]; gcongr
          calc X = X ^ 1 := (pow_one X).symm
            _ ≤ X ^ 3 := pow_le_pow_right₀ hX1 (by norm_num)
  have hq0 : (0 : ℝ) < q κ := q_pos κ
  have hqX := q_ge_X κ
  have hq1 : (1 : ℝ) ≤ q κ := le_trans hX1 hqX
  have t5 : (q κ : ℝ) ^ n κ / (q κ : ℝ) ^ m κ ≤ g := by
    obtain ⟨d, hd⟩ : ∃ d, m κ = n κ + 1 + d := ⟨m κ - (n κ + 1), by have := m_ge_n κ; omega⟩
    rw [hd, pow_add, pow_add, pow_one]
    have hqn : (0 : ℝ) < (q κ : ℝ) ^ n κ := by positivity
    calc (q κ : ℝ) ^ n κ / ((q κ : ℝ) ^ n κ * q κ * (q κ : ℝ) ^ d)
        = 1 / (q κ * (q κ : ℝ) ^ d) := by field_simp
      _ ≤ 1 / q κ := by
          apply one_div_le_one_div_of_le hq0
          nlinarith [one_le_pow₀ hq1 (n := d)]
      _ ≤ 1 / X := one_div_le_one_div_of_le hX0 hqX
      _ ≤ g := hgX
  have t6 : (k κ : ℝ) * (1 / (q κ : ℝ) ^ n κ) ≤ 19 * g := by
    have hn1 : 1 ≤ n κ := by unfold n; omega
    have hqn : (q κ : ℝ) ≤ (q κ : ℝ) ^ n κ := by
      calc (q κ : ℝ) = (q κ : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ hq1 hn1
    rw [hk]
    calc ((m κ : ℝ) + 1) * (1 / (q κ : ℝ) ^ n κ) ≤ (19 * c ^ 2) * (1 / X) :=
          mul_le_mul (by nlinarith) (one_div_le_one_div_of_le hX0 (hqX.trans hqn))
            (by positivity) (by positivity)
      _ = 19 * (c ^ 2 / X) := by ring
      _ ≤ 19 * g := by gcongr
  unfold errA errB
  rw [hG]
  linarith

theorem eventually_adv :
    ∀ᶠ κ in atTop, (1 / 32 : ℝ≥0) ≤ Game.advantage (distinguishingGame (postReal κ) (attack κ))
      (distinguishingGame (postRandom κ) (attack κ)) := by
  have hev := tendsto_G.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 81920 by norm_num))
  filter_upwards [hev] with κ hκ
  have h1 := adv_ge κ
  have h2 := errAB_le κ
  have h3 : ((1 / 32 : ℝ≥0) : ℝ) ≤ (Game.advantage (distinguishingGame (postReal κ) (attack κ))
      (distinguishingGame (postRandom κ) (attack κ)) : ℝ) := by
    rw [show ((1 / 32 : ℝ≥0) : ℝ) = 1 / 32 by norm_num]
    linarith
  exact NNReal.coe_le_coe.mp h3

/-- Post is not computationally indistinguishable. -/
theorem not_post : ¬ ComputationallyIndistinguishable postReal postRandom := by
  intro h
  have hn := h attack attack_isPPT
  exact not_negligible_const (by norm_num : (1 / 32 : ℝ≥0) ≠ 0)
    (negligible_of_eventually_le hn eventually_adv)

end

end TestCase.EvLWE
