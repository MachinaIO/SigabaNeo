import Solution.Pre2PPT
import Solution.PostRefute
import CslibFrontier.Crypto.Game.CloseTo.UniformNat
import CslibFrontier.Crypto.Negligible.Dyadic

/-!
# Pre2 from LWE

For a Pre2 distinguisher `D`, the reduction `red D` (`Solution/Pre2PPT.lean`) has, at every `κ`,

  `adv_D(Pre2) ≤ 2 · adv_{red D}(LWE) + 4 · M/2^{width} + 2 · δ₂`  (`adv_le`).

With `x` exactly uniform below `M` (`idealPair`), `h, R, T` are uniform (`dec`); the real LWE game is
then `½ Pr[D(Y₀) = 1] + ½ Pr[D(Y₁) = 0]` and the random one is `½` (`real_ideal`, `rand_ideal`),
and `Y_h` is within `δ₂` of Pre2 (`closeTo_Yd`). The sampled `x` is within `M/2^{width}`
(cslib-frontier's `advantage_bind_sampleModNat_fin_le`). Both errors are negligible, so
`lwe → ComputationallyIndistinguishable pre2Real pre2Random` (`pre2_of_lwe`).
-/

namespace TestCase.EvLWE

open SigabaNeo.Lattices

open TestCase TestCase.EvLWE Cslib Cslib.Crypto Cslib.Probability
open scoped ENNReal NNReal Matrix

section
variable (D : Distinguisher) (κ : ℕ)

/-- `D`'s game on a word distribution. -/
noncomputable def gD (X : PMF (List Bool)) : Game := X.bind fun w => ProbComp.eval (D κ w)

/-- Run `D` and XOR its bit with `h`. -/
noncomputable def Kx (h : Bool) (w : List Bool) : Game :=
  (ProbComp.eval (D κ w)).map fun o => o ^^ h

/-- The reduction with `x` exactly uniform below `M`. -/
noncomputable def idealPair (pair : LWEPair κ) : Game :=
  (PMF.uniformOfFintype Bool).bind fun h => (inner κ pair h).bind (Kx D κ h)

instance : NeZero (Mq κ) := ⟨by unfold Mq bigR RRc; positivity⟩

theorem eval_red (word : List Bool) :
    ProbComp.eval (red D κ word) =
      (ProbComp.eval (ProbComp.sampleModNat (width κ) (Mval κ word))).bind fun x =>
        Kx D κ (hbit κ word x) (build κ word x) := by
  simp only [red, ProbComp.eval_bind, ProbComp.eval_pure, Kx, PMF.map, Function.comp_def]

theorem uniform_dec_bind {β : Type} (F : Bool × RMat κ × TMat κ → PMF β) :
    (PMF.uniformOfFintype (Fin (Mq κ))).bind (fun x => F (dec κ x)) =
      (PMF.uniformOfFintype Bool).bind fun h => (PMF.uniformOfFintype (RMat κ)).bind fun R =>
        (PMF.uniformOfFintype (TMat κ)).bind fun T => F (h, R, T) := by
  rw [show (fun x => F (dec κ x)) = F ∘ dec κ from rfl, ← PMF.bind_map,
    PMF.uniformOfFintype_map_equiv, ← PMF.uniformOfFintype_prod, PMF.bind_bind]
  congr 1; funext h
  rw [PMF.bind_map, ← PMF.uniformOfFintype_prod, PMF.bind_bind]
  congr 1; funext R
  rw [PMF.bind_map]
  rfl

theorem ideal_eq (pair : LWEPair κ) :
    (PMF.uniformOfFintype (Fin (Mq κ))).bind (fun x =>
      Kx D κ (hbit κ (encLWE κ pair) x.val) (build κ (encLWE κ pair) x.val)) = idealPair D κ pair := by
  have : (fun x : Fin (Mq κ) =>
      Kx D κ (hbit κ (encLWE κ pair) x.val) (build κ (encLWE κ pair) x.val)) =
      fun x => (fun y : Bool × RMat κ × TMat κ => Kx D κ y.1 (hybLWE κ pair y.1 y.2.1 y.2.2))
        (dec κ x) := by
    funext x; rw [hbit_encLWE, build_encLWE]
  rw [this]
  refine (uniform_dec_bind κ (fun y => Kx D κ y.1 (hybLWE κ pair y.1 y.2.1 y.2.2))).trans ?_
  unfold idealPair inner
  simp only [PMF.bind_bind, PMF.pure_bind]

/-- The sampled `x` against the uniform one. -/
theorem adv_red_ideal (pair : LWEPair κ) :
    Game.advantage (ProbComp.eval (red D κ (encLWE κ pair))) (idealPair D κ pair) ≤
      (Mq κ : ℝ≥0) / 2 ^ width κ := by
  rw [eval_red, Mval_encLWE, ← ideal_eq]
  exact Game.advantage_bind_sampleModNat_fin_le (width κ) (Mq κ)
    (fun x => Kx D κ (hbit κ (encLWE κ pair) x) (build κ (encLWE κ pair) x))

/-! ### The ideal games -/

theorem real_ideal :
    (ModuleLWE.sampleLaw (lweSecret κ) (lweError κ)).bind (idealPair D κ) =
      (PMF.uniformOfFintype Bool).bind fun h => (Yd κ h true).bind (Kx D κ h) := by
  unfold idealPair
  rw [PMF.bind_comm]
  congr 1; funext h
  rw [← real_hyb, PMF.bind_bind]

theorem rand_ideal :
    (PMF.uniformOfFintype (LWEPair κ)).bind (idealPair D κ) =
      (PMF.uniformOfFintype Bool).bind fun h => (Zu κ).bind (Kx D κ h) := by
  unfold idealPair
  rw [PMF.bind_comm]
  congr 1; funext h
  rw [← rand_hyb κ h, PMF.bind_bind]

/-- The probability of `true`. -/
noncomputable def pt (g : Game) : ℝ := (g true).toReal

theorem pt_false (g : Game) : (g false).toReal = 1 - pt g := by
  have h := PMF.sum_toReal g
  rw [Fintype.sum_bool] at h
  unfold pt; linarith

theorem bind_Kx_false (X : PMF (List Bool)) : X.bind (Kx D κ false) = gD D κ X := by
  unfold Kx gD
  congr 1; funext w
  simp only [Bool.xor_false]
  exact PMF.map_id _

theorem pt_bind_Kx_true (X : PMF (List Bool)) : pt (X.bind (Kx D κ true)) = 1 - pt (gD D κ X) := by
  have : X.bind (Kx D κ true) = (gD D κ X).map not := by
    unfold Kx gD; rw [PMF.map_bind]; simp
  rw [this, ← pt_false]
  unfold pt
  rw [PMF.map_apply, tsum_eq_single false]
  · simp
  · intro b hb; cases b <;> simp_all

theorem pt_mix (f : Bool → Game) :
    pt ((PMF.uniformOfFintype Bool).bind f) = (pt (f false) + pt (f true)) / 2 := by
  unfold pt
  rw [PMF.bind_apply, tsum_fintype, Fintype.sum_bool, ENNReal.toReal_add
    (ENNReal.mul_ne_top (by simp) (PMF.apply_ne_top _ _))
    (ENNReal.mul_ne_top (by simp) (PMF.apply_ne_top _ _))]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, ENNReal.toReal_mul,
    ENNReal.toReal_inv]
  norm_num
  ring

theorem pt_real_ideal :
    pt ((ModuleLWE.sampleLaw (lweSecret κ) (lweError κ)).bind (idealPair D κ)) =
      (pt (gD D κ (Yd κ false true)) + (1 - pt (gD D κ (Yd κ true true)))) / 2 := by
  rw [real_ideal, pt_mix, bind_Kx_false, pt_bind_Kx_true]

theorem pt_rand_ideal :
    pt ((PMF.uniformOfFintype (LWEPair κ)).bind (idealPair D κ)) = 1 / 2 := by
  rw [rand_ideal, pt_mix, bind_Kx_false, pt_bind_Kx_true]
  ring

theorem pt_Yd_close (h : Bool) :
    |pt (gD D κ (Yd κ h true)) - pt (gD D κ (Yd κ h false))| ≤ δ₂ κ := by
  have hc := (closeTo_Yd κ h).bind_left fun w => ProbComp.eval (D κ w)
  have := hc.abs_toReal_sub_le (δ₂_nonneg κ) {true}
  simpa only [PMF.toOuterMeasure_apply_singleton, pt, gD] using this

/-! ### The bound -/

theorem coe_adv (g₁ g₂ : Game) : (Game.advantage g₁ g₂ : ℝ) = |pt g₁ - pt g₂| := by
  rw [Game.coe_advantage]
  simp [Game.succProbability, pt]

theorem gD_eq (X : PMF (List Bool)) : distinguishingGame X (D κ) = gD D κ X := by
  rw [distinguishingGame_eq_bind]; rfl

/-- The reduction's games, by LWE pairs. -/
theorem game_red_real :
    distinguishingGame (lweReal κ) (red D κ) =
      (ModuleLWE.sampleLaw (lweSecret κ) (lweError κ)).bind fun pair =>
        ProbComp.eval (red D κ (encLWE κ pair)) := by
  rw [distinguishingGame_eq_bind]; unfold lweReal
  simp only [PMF.monad_bind_eq_bind, PMF.bind_map]; rfl

theorem game_red_rand :
    distinguishingGame (lweRandom κ) (red D κ) =
      (PMF.uniformOfFintype (LWEPair κ)).bind fun pair =>
        ProbComp.eval (red D κ (encLWE κ pair)) := by
  rw [distinguishingGame_eq_bind]; unfold lweRandom
  simp only [PMF.monad_bind_eq_bind, PMF.bind_map]; rfl

/-- The sampling error. -/
noncomputable def εs : ℝ := (Mq κ : ℝ) / 2 ^ width κ

theorem adv_le :
    (Game.advantage (distinguishingGame (pre2Real κ) (D κ))
      (distinguishingGame (pre2Random κ) (D κ)) : ℝ) ≤
      2 * Game.advantage (distinguishingGame (lweReal κ) (red D κ))
        (distinguishingGame (lweRandom κ) (red D κ)) + 4 * εs κ + 2 * δ₂ κ := by
  rw [coe_adv, coe_adv, game_red_real, game_red_rand, gD_eq, gD_eq]
  have h1 := Game.advantage_bind_le_nnreal (ModuleLWE.sampleLaw (lweSecret κ) (lweError κ)) _ _
    (adv_red_ideal D κ)
  have h2 := Game.advantage_bind_le_nnreal (PMF.uniformOfFintype (LWEPair κ)) _ _
    (adv_red_ideal D κ)
  rw [← NNReal.coe_le_coe, coe_adv] at h1 h2
  have hε : (((Mq κ : ℝ≥0) / 2 ^ width κ : ℝ≥0) : ℝ) = εs κ := by unfold εs; push_cast; rfl
  rw [hε] at h1 h2
  rw [pt_real_ideal] at h1
  rw [pt_rand_ideal] at h2
  have h3 := pt_Yd_close D κ false
  have h4 := pt_Yd_close D κ true
  rw [← pre2Real_eq] at h3
  rw [← pre2Random_eq] at h4
  set r := pt ((ModuleLWE.sampleLaw (lweSecret κ) (lweError κ)).bind fun pair =>
    ProbComp.eval (red D κ (encLWE κ pair)))
  set s := pt ((PMF.uniformOfFintype (LWEPair κ)).bind fun pair =>
    ProbComp.eval (red D κ (encLWE κ pair)))
  set y0 := pt (gD D κ (Yd κ false true))
  set y1 := pt (gD D κ (Yd κ true true))
  set a := pt (gD D κ (pre2Real κ))
  set b := pt (gD D κ (pre2Random κ))
  rw [abs_le] at h1 h2 h3 h4 ⊢
  have hrs := le_abs_self (r - s)
  have hsr := neg_abs_le (r - s)
  constructor <;> linarith

end

/-! ### Negligibility -/

section
variable (κ : ℕ)

theorem q_le_nat : q κ ≤ 2 * 2 ^ w κ := (exists_q κ).choose_spec.2.2

theorem Mq_mul_le : Mq κ * 2 ^ κ ≤ 2 ^ width κ := by
  have hR : RRc κ ≤ 2 ^ (2 * κ + 3) := by
    unfold RRc κR
    have : 1 ≤ 2 ^ (2 * κ + 2) := Nat.one_le_two_pow
    have h3 : 2 ^ (2 * κ + 3) = 2 * 2 ^ (2 * κ + 2) := by ring
    omega
  have hN : NT κ ≤ 2 ^ (8 * κ + 9) := by
    have h1 := NT_le_q κ
    have h2 := q_le_nat κ
    have : 2 * 2 ^ w κ = 2 ^ (8 * κ + 9) := by
      unfold w; rw [← pow_succ']; ring_nf
    omega
  unfold Mq bigR width
  calc 2 * (RRc κ ^ (n κ * k κ) * NT κ ^ k κ) * 2 ^ κ
      ≤ 2 * ((2 ^ (2 * κ + 3)) ^ (n κ * k κ) * (2 ^ (8 * κ + 9)) ^ k κ) * 2 ^ κ := by gcongr
    _ = 2 ^ ((2 * κ + 3) * (n κ * k κ) + (8 * κ + 9) * k κ + κ + 1) := by
        rw [← pow_mul, ← pow_mul]; ring

theorem εs_le : εs κ ≤ 1 / 2 ^ κ := by
  unfold εs
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  exact_mod_cast Mq_mul_le κ

theorem εs_nonneg : 0 ≤ εs κ := by unfold εs; positivity

theorem δ₂_le : δ₂ κ ≤ (8 * ((m κ : ℝ) + 1) ^ 2) * (1 / 2 ^ κ) := by
  have hm1 : (1 : ℝ) ≤ m κ := by exact_mod_cast m_pos κ
  have hmκ : (κ : ℝ) ≤ m κ := m_ge_real κ
  have hsq : Real.sqrt (m κ) ≤ m κ := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hNT : (2 : ℝ) ^ (8 * κ + 7) ≤ NT κ := by
    have := hq1_ge κ
    simpa [NT] using this
  have hk : (k κ : ℝ) = m κ + 1 := by rw [k_eq]; push_cast; ring
  have hX : (0 : ℝ) < 2 ^ κ := by positivity
  have h1 : (k κ : ℝ) * (σLWE κ * Real.sqrt (m κ)) / NT κ ≤ ((m κ : ℝ) + 1) ^ 2 * (1 / 2 ^ κ) := by
    rw [hk, div_le_iff₀ (by linarith [hNT, (by positivity : (0 : ℝ) < 2 ^ (8 * κ + 7))])]
    have hσ : σLWE κ = 2 * 2 ^ κ := by unfold σLWE; rw [pow_succ]; ring
    have h8 : (2 : ℝ) ^ (8 * κ + 7) = 2 ^ κ * 2 ^ κ * 2 ^ (6 * κ + 7) := by
      rw [← pow_add, ← pow_add]; ring_nf
    have h6 : (2 : ℝ) ≤ 2 ^ (6 * κ + 7) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (6 * κ + 7) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [hσ]
    calc ((m κ : ℝ) + 1) * (2 * 2 ^ κ * Real.sqrt (m κ))
        ≤ ((m κ : ℝ) + 1) * (2 * 2 ^ κ * ((m κ : ℝ) + 1)) := by gcongr; linarith
      _ = ((m κ : ℝ) + 1) ^ 2 * (1 / 2 ^ κ) * (2 * 2 ^ κ * 2 ^ κ) := by field_simp
      _ ≤ ((m κ : ℝ) + 1) ^ 2 * (1 / 2 ^ κ) * (2 ^ κ * 2 ^ κ * 2 ^ (6 * κ + 7)) := by
          have hXX : (0 : ℝ) ≤ 2 ^ κ * 2 ^ κ := by positivity
          have : (2 : ℝ) * 2 ^ κ * 2 ^ κ ≤ 2 ^ κ * 2 ^ κ * 2 ^ (6 * κ + 7) := by
            nlinarith [mul_le_mul_of_nonneg_left h6 hXX]
          have h0 : (0 : ℝ) ≤ ((m κ : ℝ) + 1) ^ 2 * (1 / 2 ^ κ) := by positivity
          exact mul_le_mul_of_nonneg_left this h0
      _ ≤ ((m κ : ℝ) + 1) ^ 2 * (1 / 2 ^ κ) * NT κ := by rw [← h8]; gcongr
  have h2 : (k κ : ℝ) * (6 * (1 / 4) ^ m κ) ≤ 6 * ((m κ : ℝ) + 1) * (1 / 2 ^ κ) := by
    have hp : (1 / 4 : ℝ) ^ m κ ≤ 1 / 2 ^ κ := by
      rw [one_div_pow]
      apply one_div_le_one_div_of_le hX
      calc (2 : ℝ) ^ κ ≤ 2 ^ m κ := pow_le_pow_right₀ (by norm_num) (by exact_mod_cast hmκ)
        _ ≤ 4 ^ m κ := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    rw [hk]
    calc ((m κ : ℝ) + 1) * (6 * (1 / 4) ^ m κ) ≤ ((m κ : ℝ) + 1) * (6 * (1 / 2 ^ κ)) := by gcongr
      _ = _ := by ring
  unfold δ₂
  have h1' : 0 ≤ (1 : ℝ) / 2 ^ κ := by positivity
  have hA : 6 * ((m κ : ℝ) + 1) ≤ 7 * ((m κ : ℝ) + 1) ^ 2 := by nlinarith
  have hB := mul_le_mul_of_nonneg_right hA h1'
  linarith [h1, h2, hB]

/-- `48 (m + 1)^2` is polynomially bounded. -/
theorem polyBound : PolynomiallyBounded fun κ => 48 * (m κ + 1) ^ 2 := by
  rw [polynomiallyBounded_iff_le]
  refine ⟨48 * 361, 4, fun κ => ?_⟩
  have : m κ + 1 ≤ 19 * (κ + 1) ^ 2 := by unfold m n w; nlinarith
  calc 48 * (m κ + 1) ^ 2 ≤ 48 * (19 * (κ + 1) ^ 2) ^ 2 := by gcongr
    _ = 48 * 361 * (κ + 1) ^ 4 := by ring

theorem negligible_bound :
    Negligible fun κ => ((48 * (m κ + 1) ^ 2 : ℕ) : ℝ≥0) * ((1 : ℝ≥0) / 2 ^ κ) :=
  negligible_one_div_two_pow.polynomiallyBounded_mul polyBound

end

/-- **Pre2 holds under LWE.** -/
theorem pre2_of_lwe (hlwe : lwe) : ComputationallyIndistinguishable pre2Real pre2Random := by
  intro D hD
  have hred := lwe_iff.mp hlwe (red D) (red_isPPT hD)
  have h2 : Negligible fun κ => 2 * Game.advantage (distinguishingGame (lweReal κ) (red D κ))
      (distinguishingGame (lweRandom κ) (red D κ)) :=
    negligible_of_le (hred.add hred) fun κ => le_of_eq (by rw [Pi.add_apply, two_mul])
  refine negligible_of_le (h2.add negligible_bound) fun κ => ?_
  rw [← NNReal.coe_le_coe, Pi.add_apply]
  have h := adv_le D κ
  have he := εs_le κ
  have hd := δ₂_le κ
  have hX : (0 : ℝ) ≤ 1 / 2 ^ κ := by positivity
  have hm1 : (1 : ℝ) ≤ ((m κ : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ m κ := Nat.cast_nonneg _
    nlinarith
  have hXm : (1 : ℝ) / 2 ^ κ ≤ ((m κ : ℝ) + 1) ^ 2 * (1 / 2 ^ κ) := le_mul_of_one_le_left hX hm1
  simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_pow, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  linarith
