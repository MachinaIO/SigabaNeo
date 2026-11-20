import SigabaNeo.Lib.Lattices.Trapdoor.Family.Pacc
import SigabaNeo.Lib.Lattices.Gaussian.Z

/-!
# Trapdoor sampler: the law of the `D_{Z,τ}` sampler

Write `g = D_{Z,τ}` (`gaussZ`), `Z = ρ_τ(Z)`, `X = Gsum / 2^{A+1}` and `S = Σ_v pacc v`. The loop
puts mass `X · pacc v` on the proposal `zOf v` and `q^{Rt}` on `0` (`samp1_apply`), and
`X · S = 1 − q^{Rt}` (`X_mul_S`, the truncated geometric series). With
`c_L Z g(z) ≤ pacc ≤ c_H Z g(z)` on the proposals and `c_L Z (1 − t) ≤ S ≤ c_H Z`
(`t` the mass of `g` outside the proposals):

* `samp1_ge`: `a₁ g(z) ≤ μ₁(z)` for `|z| < 2^A`, with `a₁ = (1 − q^{Rt}) c_L / c_H`;
* `samp1_le`: `μ₁(z) ≤ b₁ g(z)` everywhere, with `b₁ = c_H / (c_L (1 − t)) + q^{Rt} Z`;
* `qfail_le`: `q ≤ 1 − c_L Z (1 − t) / 2^{A+1}`.
-/

namespace SigabaNeo.Lattices.Trapdoor.Family

open SigabaNeo.Lattices Cslib Cslib.Probability
open scoped ENNReal

theorem ev_finset_sum {α ι : Type*} (p : PMF α) (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    ev p (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, ev p (f i) := by
  unfold ev
  simp only [Finset.mul_sum]
  exact Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable

/-- The truncated geometric series. -/
theorem geom_trunc (q : ℝ≥0∞) (hq : q ≤ 1) (R : ℕ) :
    (∑ i ∈ Finset.range R, q ^ i) * (1 - q) + q ^ R = 1 := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ, add_mul, add_assoc, pow_succ]
    have : q ^ R * (1 - q) + q ^ R * q = q ^ R := by
      rw [← mul_add, tsub_add_cancel_of_le hq, mul_one]
    rw [this, ih]

section
variable (κ : ℕ)

theorem pacc_le_one (v : ℕ) : pacc κ v ≤ 1 := by
  unfold pacc
  rw [ENNReal.div_le_iff (by positivity) (by simp), one_mul]
  have := Finset.card_filter_le (Finset.range (2 ^ Tbits κ)) fun u => accept κ v u = true
  rw [Finset.card_range] at this
  exact_mod_cast this

theorem ev_attempt_good :
    ev (ProbComp.eval (attempt κ)) (fun t => ind (accept t.1 t.2.1 t.2.2 = true)) =
      (∑ v ∈ Finset.range (2 ^ (Aex κ + 1)), pacc κ v) / 2 ^ (Aex κ + 1) := by
  rw [ev_attempt]
  refine congrArg (fun x => x / (2 : ℝ≥0∞) ^ (Aex κ + 1)) (Finset.sum_congr rfl fun v _ => ?_)
  unfold pacc
  refine congrArg (fun x => x / (2 : ℝ≥0∞) ^ Tbits κ) ?_
  rw [Finset.card_filter]; push_cast
  refine Finset.sum_congr rfl fun u _ => ?_
  unfold ind; split_ifs <;> simp_all

theorem qfail_add :
    qfail κ + (∑ v ∈ Finset.range (2 ^ (Aex κ + 1)), pacc κ v) / 2 ^ (Aex κ + 1) = 1 := by
  unfold qfail
  rw [toOuterMeasure_eq_ev, ← ev_attempt_good, add_comm]
  exact ev_ind_add_not _ (fun t : ℕ × ℕ × ℕ => accept t.1 t.2.1 t.2.2 = true)

theorem qfail_le_one : qfail κ ≤ 1 := by
  rw [← qfail_add κ]; exact le_self_add

/-- `X · S = 1 − q^{Rt}`. -/
theorem X_mul_S :
    Gsum κ / 2 ^ (Aex κ + 1) * ∑ v ∈ Finset.range (2 ^ (Aex κ + 1)), pacc κ v =
      1 - qfail κ ^ Rt κ := by
  have hg := geom_trunc (qfail κ) (qfail_le_one κ) (Rt κ)
  have h1 : 1 - qfail κ = (∑ v ∈ Finset.range (2 ^ (Aex κ + 1)), pacc κ v) / 2 ^ (Aex κ + 1) := by
    rw [← qfail_add κ]; exact ENNReal.add_sub_cancel_left (ne_top_of_le_ne_top ENNReal.one_ne_top
      (qfail_le_one κ))
  rw [h1] at hg
  refine ENNReal.eq_sub_of_add_eq (ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top
    (qfail_le_one κ))) ?_
  rw [← hg]
  refine congrArg (· + qfail κ ^ Rt κ) ?_
  unfold Gsum
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  ring

theorem samp1_apply (z : ℤ) :
    ProbComp.eval (samp1 κ) z =
      Gsum κ * ((∑ v ∈ Finset.range (2 ^ (Aex κ + 1)), pacc κ v * ind (zOf κ v = z)) /
        2 ^ (Aex κ + 1)) + qfail κ ^ Rt κ * ind (0 = z) := by
  rw [← ev_point, ev_samp1]

/-- The proposals are `−2^A ≤ z < 2^A`. -/
theorem sum_ind_zOf (z : ℤ) (f : ℕ → ℝ≥0∞) :
    ∑ v ∈ Finset.range (2 ^ (Aex κ + 1)), f v * ind (zOf κ v = z) =
      if -(2 : ℤ) ^ Aex κ ≤ z ∧ z < 2 ^ Aex κ then f (z + 2 ^ Aex κ).toNat else 0 := by
  classical
  have h2 : (2 : ℤ) ^ (Aex κ + 1) = 2 * 2 ^ Aex κ := by ring
  have hc : ((2 ^ (Aex κ + 1) : ℕ) : ℤ) = 2 ^ (Aex κ + 1) := by push_cast; rfl
  split_ifs with h
  · rw [Finset.sum_eq_single (z + 2 ^ Aex κ).toNat]
    · rw [ind_of (by unfold zOf; omega), mul_one]
    · intro b _ hb; rw [ind_of_not (by unfold zOf; omega), mul_zero]
    · intro hn; exfalso; apply hn; rw [Finset.mem_range]
      have : ((z + 2 ^ Aex κ).toNat : ℤ) < ((2 ^ (Aex κ + 1) : ℕ) : ℤ) := by
        rw [hc, h2]; omega
      exact_mod_cast this
  · refine Finset.sum_eq_zero fun v hv => ?_
    rw [ind_of_not, mul_zero]
    intro hz; apply h
    have hv' : ((v : ℕ) : ℤ) < ((2 ^ (Aex κ + 1) : ℕ) : ℤ) := by
      exact_mod_cast Finset.mem_range.mp hv
    rw [hc, h2] at hv'
    unfold zOf at hz
    omega

theorem mem_range_index (z : ℤ) (h : -(2 : ℤ) ^ Aex κ ≤ z ∧ z < 2 ^ Aex κ) :
    (z + 2 ^ Aex κ).toNat < 2 ^ (Aex κ + 1) ∧ zOf κ (z + 2 ^ Aex κ).toNat = z := by
  have h2 : (2 : ℤ) ^ (Aex κ + 1) = 2 * 2 ^ Aex κ := by ring
  constructor
  · have : ((z + 2 ^ Aex κ).toNat : ℤ) < ((2 ^ (Aex κ + 1) : ℕ) : ℤ) := by
      push_cast; rw [h2]; omega
    exact_mod_cast this
  · unfold zOf; omega

/-! ### The constants -/

/-- `exp(π 4^{Lg+1})`: `1/gw` on the proposals. -/
noncomputable def eK : ℝ := Real.exp (Real.pi * 4 ^ (Lg κ + 1))

noncomputable def cL : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-δP κ))
noncomputable def cH : ℝ≥0∞ := ENNReal.ofReal (Real.exp (δP κ) * ηN κ + eK κ / 2 ^ Tbits κ)
noncomputable def Zm : ℝ≥0∞ := ENNReal.ofReal (Mz (τ κ))
/-- The mass of `D_{Z,τ}` outside the proposals, bounded. -/
noncomputable def tq : ℝ≥0∞ := ENNReal.ofReal (6 * (1 / 4) ^ (4 ^ (Lg κ + 1)))

theorem Zm_ne_zero : Zm κ ≠ 0 := (ENNReal.ofReal_pos.mpr (Mz_pos (τ_pos κ))).ne'
theorem Zm_ne_top : Zm κ ≠ ⊤ := ENNReal.ofReal_ne_top

theorem ηN_ge : 1 ≤ ηN κ := by
  unfold ηN; exact one_le_pow₀ (by have : (0 : ℝ) ≤ 2 / (Nterms κ).factorial := by positivity
                                   linarith)

theorem cH_pos : cH κ ≠ 0 := by
  unfold cH
  refine (ENNReal.ofReal_pos.mpr ?_).ne'
  have := ηN_ge κ
  have : 0 < Real.exp (δP κ) * ηN κ := mul_pos (Real.exp_pos _) (by linarith)
  have : 0 ≤ eK κ / 2 ^ Tbits κ := by unfold eK; positivity
  linarith

theorem cL_pos : cL κ ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

theorem tq_lt_one : tq κ < 1 := by
  unfold tq
  rw [ENNReal.ofReal_lt_one]
  have h : 4 ≤ 4 ^ (Lg κ + 1) := by
    calc 4 = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ (Lg κ + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 6 * (1 / 4 : ℝ) ^ (4 ^ (Lg κ + 1)) ≤ 6 * (1 / 4) ^ 4 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) h) (by norm_num)
    _ < 1 := by norm_num

/-- `ρ_τ(z) = Z · g(z)`. -/
theorem ofReal_gw (z : ℤ) : ENNReal.ofReal (gw (τ κ) z) = Zm κ * gaussZ (τ κ) (τ_pos κ) z := by
  rw [gaussZ_apply]; exact (ENNReal.mul_div_cancel (Zm_ne_zero κ) (Zm_ne_top κ)).symm

theorem gw_ge_on (v : ℕ) (hv : v < 2 ^ (Aex κ + 1)) : 1 ≤ eK κ * gw (τ κ) (zOf κ v) := by
  rw [gw_eq_exp, eK, ← Real.exp_add]
  apply Real.one_le_exp
  have h := zsq_le κ v hv
  have : Real.pi * (((zOf κ v : ℤ) : ℝ) ^ 2 / τ κ ^ 2) ≤ Real.pi * 4 ^ (Lg κ + 1) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast h) Real.pi_pos.le
  linarith

theorem pacc_ge' (v : ℕ) (hv : v < 2 ^ (Aex κ + 1)) :
    cL κ * Zm κ * gaussZ (τ κ) (τ_pos κ) (zOf κ v) ≤ pacc κ v := by
  refine le_trans (le_of_eq ?_) (pacc_ge κ v hv)
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ofReal_gw, cL, mul_assoc]

theorem pacc_le' (v : ℕ) (hv : v < 2 ^ (Aex κ + 1)) :
    pacc κ v ≤ cH κ * Zm κ * gaussZ (τ κ) (τ_pos κ) (zOf κ v) := by
  have hη := ηN_ge κ
  have hK : 0 ≤ eK κ / 2 ^ Tbits κ := by unfold eK; positivity
  have hc : 0 ≤ Real.exp (δP κ) * ηN κ + eK κ / 2 ^ Tbits κ := by
    have : 0 ≤ Real.exp (δP κ) * ηN κ := mul_nonneg (Real.exp_pos _).le (by linarith)
    linarith
  calc pacc κ v ≤ _ := pacc_le κ v hv
    _ ≤ ENNReal.ofReal ((Real.exp (δP κ) * ηN κ + eK κ / 2 ^ Tbits κ) * gw (τ κ) (zOf κ v)) := by
        apply ENNReal.ofReal_le_ofReal
        have h1 := gw_ge_on κ v hv
        have hT : (0 : ℝ) < 2 ^ Tbits κ := by positivity
        have : 1 / 2 ^ Tbits κ ≤ eK κ / 2 ^ Tbits κ * gw (τ κ) (zOf κ v) := by
          rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right h1 hT.le
        linarith
    _ = cH κ * Zm κ * gaussZ (τ κ) (τ_pos κ) (zOf κ v) := by
        rw [ENNReal.ofReal_mul hc, ofReal_gw, cH, mul_assoc]

/-- The mass of `g` on the proposals. -/
noncomputable def gIn : ℝ≥0∞ :=
  ∑ v ∈ Finset.range (2 ^ (Aex κ + 1)), gaussZ (τ κ) (τ_pos κ) (zOf κ v)

theorem gIn_eq : gIn κ = ev (gaussZ (τ κ) (τ_pos κ))
    (fun z => ∑ v ∈ Finset.range (2 ^ (Aex κ + 1)), 1 * ind (zOf κ v = z)) := by
  rw [ev_finset_sum]
  unfold gIn
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [one_mul]
  rw [← ev_point]
  congr 1; funext z; congr 1; exact propext eq_comm

theorem gIn_le : gIn κ ≤ 1 := by
  rw [gIn_eq]
  refine ev_le_const _ fun z => ?_
  rw [sum_ind_zOf]; split_ifs <;> simp

theorem two_pow_Aex : (2 : ℝ) ^ Aex κ = τ κ * Real.sqrt ((4 ^ (Lg κ + 1) : ℕ) : ℝ) := by
  have : Real.sqrt ((4 ^ (Lg κ + 1) : ℕ) : ℝ) = 2 ^ (Lg κ + 1) := by
    rw [show ((4 ^ (Lg κ + 1) : ℕ) : ℝ) = ((2 : ℝ) ^ (Lg κ + 1)) ^ 2 by
      push_cast; rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]; ring_nf]
    exact Real.sqrt_sq (by positivity)
  rw [this, τ, Aex, ← pow_add]; congr 1; ring

theorem gIn_ge : 1 - tq κ ≤ gIn κ := by
  rw [tsub_le_iff_right]
  have ht := gaussZ_tail (one_le_τ κ) (τ_pos κ) (4 ^ (Lg κ + 1))
  rw [← two_pow_Aex, toOuterMeasure_eq_ev] at ht
  calc (1 : ℝ≥0∞) = ev (gaussZ (τ κ) (τ_pos κ)) (fun _ => 1) := (ev_const _ 1).symm
    _ ≤ ev (gaussZ (τ κ) (τ_pos κ)) (fun z =>
          (∑ v ∈ Finset.range (2 ^ (Aex κ + 1)), 1 * ind (zOf κ v = z)) +
            ind (z ∈ {x : ℤ | (2 : ℝ) ^ Aex κ ≤ |(x : ℝ)|})) := by
        refine ev_mono _ fun z => ?_
        rw [sum_ind_zOf]
        split_ifs with h
        · exact le_self_add
        · rw [ind_of, add_comm]; · exact le_self_add
          simp only [Set.mem_ofPred_eq]
          have : (2 : ℤ) ^ Aex κ ≤ |z| := by
            rw [le_abs']; omega
          exact_mod_cast this
    _ = gIn κ + _ := by rw [ev_add, gIn_eq]
    _ ≤ gIn κ + tq κ := add_le_add le_rfl ht

/-! ### The bounds -/

theorem S_le : ∑ v ∈ Finset.range (2 ^ (Aex κ + 1)), pacc κ v ≤ cH κ * Zm κ := by
  calc ∑ v ∈ Finset.range (2 ^ (Aex κ + 1)), pacc κ v
      ≤ ∑ v ∈ Finset.range (2 ^ (Aex κ + 1)), cH κ * Zm κ * gaussZ (τ κ) (τ_pos κ) (zOf κ v) :=
        Finset.sum_le_sum fun v hv => pacc_le' κ v (Finset.mem_range.mp hv)
    _ = cH κ * Zm κ * gIn κ := by rw [gIn, Finset.mul_sum]
    _ ≤ cH κ * Zm κ * 1 := by gcongr; exact gIn_le κ
    _ = cH κ * Zm κ := mul_one _

theorem S_ge : cL κ * Zm κ * (1 - tq κ) ≤ ∑ v ∈ Finset.range (2 ^ (Aex κ + 1)), pacc κ v := by
  calc cL κ * Zm κ * (1 - tq κ) ≤ cL κ * Zm κ * gIn κ := by gcongr; exact gIn_ge κ
    _ = ∑ v ∈ Finset.range (2 ^ (Aex κ + 1)), cL κ * Zm κ * gaussZ (τ κ) (τ_pos κ) (zOf κ v) := by
        rw [gIn, Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun v hv => pacc_ge' κ v (Finset.mem_range.mp hv)

noncomputable def a1 : ℝ≥0∞ := (1 - qfail κ ^ Rt κ) * cL κ * (cH κ)⁻¹
noncomputable def b1 : ℝ≥0∞ := cH κ * (cL κ * (1 - tq κ))⁻¹ + qfail κ ^ Rt κ * Zm κ

theorem samp1_eq_X (z : ℤ) :
    ProbComp.eval (samp1 κ) z =
      Gsum κ / 2 ^ (Aex κ + 1) *
        (if -(2 : ℤ) ^ Aex κ ≤ z ∧ z < 2 ^ Aex κ then pacc κ (z + 2 ^ Aex κ).toNat else 0) +
        qfail κ ^ Rt κ * ind (0 = z) := by
  rw [samp1_apply, sum_ind_zOf]
  refine congrArg (· + qfail κ ^ Rt κ * ind (0 = z)) ?_
  simp only [div_eq_mul_inv]; ring

theorem samp1_ge (z : ℤ) (hz : -(2 : ℤ) ^ Aex κ ≤ z ∧ z < 2 ^ Aex κ) :
    a1 κ * gaussZ (τ κ) (τ_pos κ) z ≤ ProbComp.eval (samp1 κ) z := by
  obtain ⟨hv, hzv⟩ := mem_range_index κ z hz
  set v := (z + 2 ^ Aex κ).toNat
  set X := Gsum κ / 2 ^ (Aex κ + 1)
  set g := gaussZ (τ κ) (τ_pos κ) z
  have hcHt : cH κ ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [samp1_eq_X, ite_eq_left_of_eq_true _ _ (eq_true hz)]
  refine le_trans ?_ le_self_add
  have hp := pacc_ge' κ v hv
  rw [hzv] at hp
  calc a1 κ * g = X * (∑ v ∈ Finset.range (2 ^ (Aex κ + 1)), pacc κ v) * cL κ * (cH κ)⁻¹ * g := by
        rw [X_mul_S]; rfl
    _ ≤ X * (cH κ * Zm κ) * cL κ * (cH κ)⁻¹ * g :=
        mul_le_mul_left (mul_le_mul_left (mul_le_mul_left (mul_le_mul_right (S_le κ) X) _) _) _
    _ = X * (cL κ * Zm κ * g) * (cH κ * (cH κ)⁻¹) := by ring
    _ = X * (cL κ * Zm κ * g) := by rw [ENNReal.mul_inv_cancel (cH_pos κ) hcHt, mul_one]
    _ ≤ X * pacc κ v := mul_le_mul_right hp X

theorem X_Zm_le : Gsum κ / 2 ^ (Aex κ + 1) * Zm κ ≤ (cL κ * (1 - tq κ))⁻¹ := by
  rw [ENNReal.le_inv_iff_mul_le]
  calc Gsum κ / 2 ^ (Aex κ + 1) * Zm κ * (cL κ * (1 - tq κ)) =
        Gsum κ / 2 ^ (Aex κ + 1) * (cL κ * Zm κ * (1 - tq κ)) := by ring
    _ ≤ Gsum κ / 2 ^ (Aex κ + 1) * ∑ v ∈ Finset.range (2 ^ (Aex κ + 1)), pacc κ v :=
        mul_le_mul_right (S_ge κ) _
    _ = 1 - qfail κ ^ Rt κ := X_mul_S κ
    _ ≤ 1 := tsub_le_self

theorem ind_zero_le (z : ℤ) : ind (0 = z) ≤ Zm κ * gaussZ (τ κ) (τ_pos κ) z := by
  by_cases h : 0 = z
  · subst h; rw [ind_of rfl, ← ofReal_gw, gw_zero, ENNReal.ofReal_one]
  · rw [ind_of_not h]; exact bot_le

theorem samp1_le (z : ℤ) : ProbComp.eval (samp1 κ) z ≤ b1 κ * gaussZ (τ κ) (τ_pos κ) z := by
  set X := Gsum κ / 2 ^ (Aex κ + 1)
  set g := gaussZ (τ κ) (τ_pos κ) z
  rw [samp1_eq_X, b1, add_mul]
  refine add_le_add ?_ ?_
  · split_ifs with hz
    · obtain ⟨hv, hzv⟩ := mem_range_index κ z hz
      have hp := pacc_le' κ _ hv
      rw [hzv] at hp
      calc X * pacc κ (z + 2 ^ Aex κ).toNat ≤ X * (cH κ * Zm κ * g) := mul_le_mul_right hp X
        _ = cH κ * (X * Zm κ) * g := by ring
        _ ≤ cH κ * (cL κ * (1 - tq κ))⁻¹ * g :=
          mul_le_mul_left (mul_le_mul_right (X_Zm_le κ) _) _
    · rw [mul_zero]; exact bot_le
  · rw [mul_assoc]; exact mul_le_mul_right (ind_zero_le κ z) _

end

end SigabaNeo.Lattices.Trapdoor.Family
