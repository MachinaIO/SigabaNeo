import SigabaNeoStd.Lattices.Trapdoor.Family.Law

/-!
# Trapdoor sampler: the ideal column law is close to the coset Gaussian

For `B = [Ā | G − Ā R]` with `R ∈ {−1, 0, 1}` and smooth `Λ^⊥(B)` (`dualMassE B τ ≤ 1/2`), the law
`colLaw Ā R u` of `y + xPre R (u − B y)`, `y ← D_{Z^m,τ}`, is within
`2θ + m·6·4^{−m} + 3·2^m·4^{−m²}` of the coset Gaussian `D_{Λ^⊥_u(B),τ}` (`colLaw_close`), where
`θ = π m (mb² + 2 τ m · mb) / τ²` (`θT`).

On the box `|x_j| < τ m`, every `ρ_τ(x − xPre R v)` is within the factor `e^{±θ}` of `ρ_τ(x)`
(`rho_shift_ge`, `rho_shift_le`), so the sampler's mass is `c · e^{±θ}` times the coset Gaussian's,
for one constant `c`. The tails of both laws outside the box (`gaussVec_tail`,
`cosetGauss_tail_M`) pin `c ≥ (1 − tail) e^{−θ}`, and `closeTo_of_ge` concludes.
-/

namespace SigabaNeo.Lattices.Trapdoor.Family

open SigabaNeo.Lattices ZLattice ProbabilityTheory Cslib.Probability MeasureTheory
open scoped ENNReal Matrix

/-- A law dominating `a · ν` on `S` is close to `ν`. -/
theorem closeTo_of_ge {α : Type} (μ ν : PMF α) (S : Set α) {a : ℝ≥0∞}
    (h : ∀ x ∈ S, a * ν x ≤ μ x) :
    CloseTo μ ν ((1 - a) + ν.toOuterMeasure Sᶜ) := by
  refine CloseTo.symm fun E => ?_
  have hsplit : ν.toOuterMeasure E ≤ ν.toOuterMeasure (E ∩ S) + ν.toOuterMeasure Sᶜ := by
    calc ν.toOuterMeasure E ≤ ν.toOuterMeasure ((E ∩ S) ∪ Sᶜ) :=
          measure_mono fun x hx => by
            by_cases hs : x ∈ S
            · exact Or.inl ⟨hx, hs⟩
            · exact Or.inr hs
      _ ≤ _ := measure_union_le _ _
  have hES : a * ν.toOuterMeasure (E ∩ S) ≤ μ.toOuterMeasure E := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun x => ?_
    by_cases hx : x ∈ E ∩ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx.1]; exact h x hx.2
    · rw [Set.indicator_of_notMem hx, mul_zero]; exact zero_le
  have hle1 : ν.toOuterMeasure (E ∩ S) ≤ 1 := PMF.toOuterMeasure_le_one _ _
  calc ν.toOuterMeasure E ≤ ν.toOuterMeasure (E ∩ S) + ν.toOuterMeasure Sᶜ := hsplit
    _ ≤ (a * ν.toOuterMeasure (E ∩ S) + (1 - a)) + ν.toOuterMeasure Sᶜ := by
        gcongr
        by_cases ha : a ≤ 1
        · calc ν.toOuterMeasure (E ∩ S) = a * ν.toOuterMeasure (E ∩ S) +
                (1 - a) * ν.toOuterMeasure (E ∩ S) := by
                rw [← add_mul, add_tsub_cancel_of_le ha, one_mul]
            _ ≤ _ := by gcongr; exact mul_le_of_le_one_right zero_le hle1
        · push Not at ha
          calc ν.toOuterMeasure (E ∩ S) ≤ 1 * ν.toOuterMeasure (E ∩ S) := by rw [one_mul]
            _ ≤ a * ν.toOuterMeasure (E ∩ S) := by gcongr
            _ ≤ _ := le_self_add
    _ ≤ μ.toOuterMeasure E + (1 - a) + ν.toOuterMeasure Sᶜ := by gcongr
    _ = μ.toOuterMeasure E + ((1 - a) + ν.toOuterMeasure Sᶜ) := by ring

section
variable (κ : ℕ)

/-- The box radius `τ m`. -/
noncomputable def Rr : ℝ := τ κ * m κ

/-- The box `|x_j| < τ m`. -/
def Box : Set (Fin (m κ) → ℤ) := {x | ∀ j, |((x j : ℤ) : ℝ)| < Rr κ}

/-- `θ = π m (mb² + 2 τ m · mb)/τ²`. -/
noncomputable def θT : ℝ := Real.pi * m κ * ((mb κ : ℝ) ^ 2 + 2 * Rr κ * mb κ) / τ κ ^ 2

theorem rhoV_eq (x : Fin (m κ) → ℤ) :
    rhoV κ x = Real.exp (-Real.pi * (∑ j, ((x j : ℤ) : ℝ) ^ 2) / τ κ ^ 2) := by
  unfold rhoV gw
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum, Finset.sum_div]

theorem rhoV_eq_weight (x : Fin (m κ) → ℤ) : rhoV κ x = gaussianWeight (τ κ) (embed (m κ) x) := by
  rw [rhoV_eq]
  unfold gaussianWeight
  congr 1
  rw [EuclideanSpace.norm_sq_eq]
  simp [embed]

theorem rhoV_pos (x : Fin (m κ) → ℤ) : 0 < rhoV κ x := by rw [rhoV_eq]; exact Real.exp_pos _

theorem shift_bound (x d : Fin (m κ) → ℤ) (hx : x ∈ Box κ) (hd : ∀ j, |d j| ≤ mb κ) :
    |∑ j, ((((x - d) j : ℤ) : ℝ) ^ 2 - ((x j : ℤ) : ℝ) ^ 2)| ≤
      m κ * ((mb κ : ℝ) ^ 2 + 2 * Rr κ * mb κ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ j, |(((x - d) j : ℤ) : ℝ) ^ 2 - ((x j : ℤ) : ℝ) ^ 2| ≤
      (mb κ : ℝ) ^ 2 + 2 * Rr κ * mb κ := by
    intro j
    have h1 : |((d j : ℤ) : ℝ)| ≤ mb κ := by exact_mod_cast hd j
    have h2 := (hx j).le
    have : (((x - d) j : ℤ) : ℝ) ^ 2 - ((x j : ℤ) : ℝ) ^ 2 =
        ((d j : ℤ) : ℝ) ^ 2 - 2 * ((x j : ℤ) : ℝ) * ((d j : ℤ) : ℝ) := by
      simp only [Pi.sub_apply, Int.cast_sub]; ring
    rw [this]
    refine (abs_sub _ _).trans ?_
    rw [abs_pow, abs_mul, abs_mul, abs_two]
    have h0 : 0 ≤ |((d j : ℤ) : ℝ)| := abs_nonneg _
    have h0' : 0 ≤ |((x j : ℤ) : ℝ)| := abs_nonneg _
    nlinarith
  calc ∑ j, |(((x - d) j : ℤ) : ℝ) ^ 2 - ((x j : ℤ) : ℝ) ^ 2|
      ≤ ∑ _j : Fin (m κ), ((mb κ : ℝ) ^ 2 + 2 * Rr κ * mb κ) := Finset.sum_le_sum fun j _ => hterm j
    _ = _ := by simp; ring

theorem rho_shift_ge (x d : Fin (m κ) → ℤ) (hx : x ∈ Box κ) (hd : ∀ j, |d j| ≤ mb κ) :
    Real.exp (-θT κ) * rhoV κ x ≤ rhoV κ (x - d) := by
  rw [rhoV_eq, rhoV_eq, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := abs_le.mp (shift_bound κ x d hx hd)
  have hτ : 0 < τ κ ^ 2 := by have := τ_pos κ; positivity
  set A := ∑ j, ((x j : ℤ) : ℝ) ^ 2
  set D := ∑ j, ((((x - d) j : ℤ) : ℝ) ^ 2 - ((x j : ℤ) : ℝ) ^ 2)
  have hsum : ∑ j, ((((x - d) j : ℤ) : ℝ) ^ 2) = A + D := by
    simp only [A, D, Finset.sum_sub_distrib]; ring
  rw [hsum]
  have e : -θT κ + -Real.pi * A / τ κ ^ 2 =
      -Real.pi * (A + m κ * ((mb κ : ℝ) ^ 2 + 2 * Rr κ * mb κ)) / τ κ ^ 2 := by
    unfold θT; field_simp; ring
  rw [e]
  apply div_le_div_of_nonneg_right _ hτ.le
  nlinarith [Real.pi_pos, h.2]

theorem rho_shift_le (x d : Fin (m κ) → ℤ) (hx : x ∈ Box κ) (hd : ∀ j, |d j| ≤ mb κ) :
    rhoV κ (x - d) ≤ Real.exp (θT κ) * rhoV κ x := by
  rw [rhoV_eq, rhoV_eq, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := abs_le.mp (shift_bound κ x d hx hd)
  have hτ : 0 < τ κ ^ 2 := by have := τ_pos κ; positivity
  set A := ∑ j, ((x j : ℤ) : ℝ) ^ 2
  set D := ∑ j, ((((x - d) j : ℤ) : ℝ) ^ 2 - ((x j : ℤ) : ℝ) ^ 2)
  have hsum : ∑ j, ((((x - d) j : ℤ) : ℝ) ^ 2) = A + D := by
    simp only [A, D, Finset.sum_sub_distrib]; ring
  rw [hsum]
  have e : θT κ + -Real.pi * A / τ κ ^ 2 =
      -Real.pi * (A - m κ * ((mb κ : ℝ) ^ 2 + 2 * Rr κ * mb κ)) / τ κ ^ 2 := by
    unfold θT; field_simp; ring
  rw [e]
  apply div_le_div_of_nonneg_right _ hτ.le
  nlinarith [Real.pi_pos, h.1]


/-! ### Tails -/

theorem one_le_τ : 1 ≤ τ κ := by unfold τ; exact one_le_pow₀ (by norm_num)

theorem m_ge_four : 4 ≤ m κ := by unfold m n w; nlinarith

theorem radius_le : τ κ * Real.sqrt (m κ) + mb κ ≤ Rr κ := by
  have hm4 : (4 : ℝ) ≤ m κ := by exact_mod_cast m_ge_four κ
  have hsq : Real.sqrt (m κ) ≤ m κ / 2 := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hmb : (mb κ : ℝ) = m κ / 2 := by
    have := m_eq_mb κ; rw [this]; push_cast; ring
  have hτ : (8 : ℝ) ≤ τ κ := by
    unfold τ; calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (κ + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
  unfold Rr
  rw [hmb]
  nlinarith

theorem gaussVec_tail :
    (gaussVec κ).toOuterMeasure {y | ∃ j, τ κ * Real.sqrt (m κ) ≤ |((y j : ℤ) : ℝ)|} ≤
      (m κ : ℝ≥0∞) * ENNReal.ofReal (6 * (1 / 4) ^ m κ) := by
  rw [toOuterMeasure_eq_ev]
  unfold gaussVec
  rw [ev_map]
  have hB : 0 < τ κ * Real.sqrt (m κ) :=
    mul_pos (τ_pos κ) (Real.sqrt_pos.mpr (by exact_mod_cast m_pos κ))
  refine (ev_mono _ fun l => ind_mono (Q := ∃ x ∈ l, τ κ * Real.sqrt (m κ) ≤ |((x : ℤ) : ℝ)|) ?_).trans
    (ev_sampleList_exists _ _ ?_ (m κ))
  · rintro ⟨j, hj⟩
    simp only [Set.mem_setOf_eq, List.getD_eq_getElem?_getD] at hj
    cases hx : l[(j : ℕ)]? with
    | none => rw [hx] at hj; simp at hj; linarith
    | some x => rw [hx] at hj; exact ⟨x, List.mem_of_getElem? hx, hj⟩
  · exact (toOuterMeasure_eq_ev (gaussZ (τ κ) (τ_pos κ))
      {x : ℤ | τ κ * Real.sqrt (m κ) ≤ |(x : ℝ)|}).symm.le.trans
      (gaussZ_tail (one_le_τ κ) (τ_pos κ) (m κ))

theorem colLaw_tail (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)))
    (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (hR : ∀ i j, |R i j| ≤ 1)
    (u : Fin (n κ) → ZMod (q κ)) :
    (colLaw κ Abar R u).toOuterMeasure (Box κ)ᶜ ≤
      (m κ : ℝ≥0∞) * ENNReal.ofReal (6 * (1 / 4) ^ m κ) := by
  unfold colLaw
  rw [PMF.toOuterMeasure_map_apply]
  refine le_trans (measure_mono ?_) (gaussVec_tail κ)
  intro y hy
  simp only [Set.mem_preimage, Set.mem_compl_iff, Box, Set.mem_setOf_eq, not_forall,
    not_lt] at hy
  obtain ⟨j, hj⟩ := hy
  refine ⟨j, ?_⟩
  have hd := abs_xPre_le κ R hR (u - Bmat κ Abar R *ᵥ castV κ y) j
  have hd' : |((xPre κ R (u - Bmat κ Abar R *ᵥ castV κ y) j : ℤ) : ℝ)| ≤ mb κ := by
    exact_mod_cast hd
  have hsum : ((gsyn κ Abar R u y j : ℤ) : ℝ) =
      ((y j : ℤ) : ℝ) + ((xPre κ R (u - Bmat κ Abar R *ᵥ castV κ y) j : ℤ) : ℝ) := by
    simp [gsyn]
  rw [hsum] at hj
  have := abs_add_le ((y j : ℤ) : ℝ) ((xPre κ R (u - Bmat κ Abar R *ᵥ castV κ y) j : ℤ) : ℝ)
  have hr := radius_le κ
  linarith

theorem cosetGauss_tail_M {nn mm qq : ℕ} [NeZero qq] (B : Matrix (Fin nn) (Fin mm) (ZMod qq))
    (u : Fin nn → ZMod qq) {τ : ℝ} (hτ : 0 < τ) (hB : dualMassE B τ ≤ 1 / 2)
    {d : PMF (Fin mm → ℤ)} (hd : cosetGauss B u τ hτ = some d) (M : ℕ) :
    d.toOuterMeasure {x | τ * Real.sqrt M ≤ ‖embed mm x‖} ≤
      ENNReal.ofReal (3 * 2 ^ mm * (1 / 4) ^ M) := by
  unfold cosetGauss at hd
  split_ifs at hd with h
  obtain rfl := Option.some.inj hd
  have hb : (ZLattice.discreteGaussian (perp B) τ hτ (-(embed mm h.choose)) >>= fun a =>
      pure (a : EuclideanSpace ℝ (Fin mm))) =
      (ZLattice.discreteGaussian (perp B) τ hτ (-(embed mm h.choose))).map Subtype.val := rfl
  rw [PMF.toOuterMeasure_map_apply, hb, PMF.toOuterMeasure_map_apply]
  refine le_trans (measure_mono ?_) (gauss_tail_gen B hτ hB _ M)
  intro z hz
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hz ⊢
  obtain ⟨y, -, hy⟩ := Submodule.mem_map.mp z.2
  have : embed mm (h.choose + toInt (z : EuclideanSpace ℝ (Fin mm))) =
      (z : EuclideanSpace ℝ (Fin mm)) - -embed mm h.choose := by
    rw [map_add, ← hy, toInt_embed, sub_neg_eq_add, add_comm]
  rwa [this] at hz

theorem coset_box_tail (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)))
    (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (u : Fin (n κ) → ZMod (q κ))
    (hB : dualMassE (Bmat κ Abar R) (τ κ) ≤ 1 / 2) {p : PMF (Fin (m κ) → ℤ)}
    (hp : cosetGauss (Bmat κ Abar R) u (τ κ) (τ_pos κ) = some p) :
    p.toOuterMeasure (Box κ)ᶜ ≤ ENNReal.ofReal (3 * 2 ^ m κ * (1 / 4) ^ (m κ ^ 2)) := by
  refine le_trans (measure_mono ?_) (cosetGauss_tail_M _ u (τ_pos κ) hB hp (m κ ^ 2))
  intro x hx
  simp only [Set.mem_compl_iff, Box, Set.mem_setOf_eq, not_forall, not_lt] at hx
  obtain ⟨j, hj⟩ := hx
  simp only [Set.mem_setOf_eq]
  have : τ κ * Real.sqrt ((m κ ^ 2 : ℕ) : ℝ) = Rr κ := by
    unfold Rr; push_cast; rw [Real.sqrt_sq (by positivity)]
  rw [this]
  exact hj.trans (abs_le_norm_embed x j)


/-! ### The ideal column law -/

theorem one_sub_mul_le (s t : ℝ≥0∞) (hs : s ≤ 1) : 1 - s * (1 - t) ≤ (1 - s) + t := by
  rw [tsub_le_iff_right]
  calc (1 : ℝ≥0∞) = s + (1 - s) := (add_tsub_cancel_of_le hs).symm
    _ ≤ s * (1 - t) + s * t + (1 - s) := by
        gcongr
        calc s = s * 1 := (mul_one s).symm
          _ ≤ s * ((1 - t) + t) := by gcongr; exact le_tsub_add
          _ = _ := by rw [mul_add]
    _ ≤ s * (1 - t) + t + (1 - s) := by gcongr; exact mul_le_of_le_one_left zero_le hs
    _ = (1 - s) + t + s * (1 - t) := by ring

/-- **The ideal column law is close to the coset Gaussian.** -/
theorem colLaw_close (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)))
    (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (hR : ∀ i j, |R i j| ≤ 1)
    (u : Fin (n κ) → ZMod (q κ)) (hB : dualMassE (Bmat κ Abar R) (τ κ) ≤ 1 / 2)
    {p : PMF (Fin (m κ) → ℤ)} (hp : cosetGauss (Bmat κ Abar R) u (τ κ) (τ_pos κ) = some p) :
    CloseTo (colLaw κ Abar R u) p
      (ENNReal.ofReal (2 * θT κ) + (m κ : ℝ≥0∞) * ENNReal.ofReal (6 * (1 / 4) ^ m κ) +
        ENNReal.ofReal (3 * 2 ^ m κ * (1 / 4) ^ (m κ ^ 2))) := by
  classical
  obtain ⟨M, hM, hpx⟩ := cosetGauss_apply _ u (τ_pos κ) hp
  set B := Bmat κ Abar R
  set C : Set (Fin (m κ) → ℤ) := {x | B *ᵥ castV κ x = u}
  set Z := ENNReal.ofReal (Mz (τ κ)) ^ m κ
  set Mc := ENNReal.ofReal M
  set Qn : ℝ≥0∞ := (Fintype.card (Fin (n κ) → ZMod (q κ)) : ℝ≥0∞)
  set c := Qn * Mc / Z
  set tg := (m κ : ℝ≥0∞) * ENNReal.ofReal (6 * (1 / 4) ^ m κ)
  set θ := θT κ
  set P := colLaw κ Abar R u
  have hMc0 : Mc ≠ 0 := (ENNReal.ofReal_pos.mpr hM).ne'
  have hMct : Mc ≠ ⊤ := ENNReal.ofReal_ne_top
  have hZ0 : Z ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr (Mz_pos (τ_pos κ))).ne'
  have hZt : Z ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  -- masses on the coset
  have hp_on : ∀ x ∈ C, p x = ENNReal.ofReal (rhoV κ x) / Mc := by
    intro x hx
    rw [hpx, if_pos (show (B *ᵥ fun i => ((x i : ℤ) : ZMod (q κ))) = u from hx), rhoV_eq_weight]
  have hp_off : ∀ x ∉ C, p x = 0 := by
    intro x hx; rw [hpx, if_neg (show ¬ (B *ᵥ fun i => ((x i : ℤ) : ZMod (q κ))) = u from hx)]
  have hcp : ∀ x ∈ C, c * p x = Qn * ENNReal.ofReal (rhoV κ x) / Z := by
    intro x hx
    rw [hp_on x hx]
    simp only [c, div_eq_mul_inv]
    calc Qn * Mc * Z⁻¹ * (ENNReal.ofReal (rhoV κ x) * Mc⁻¹)
        = Qn * ENNReal.ofReal (rhoV κ x) * Z⁻¹ * (Mc * Mc⁻¹) := by ring
      _ = _ := by rw [ENNReal.mul_inv_cancel hMc0 hMct, mul_one]
  have hP_on : ∀ x ∈ C, P x = (∑ v : Fin (n κ) → ZMod (q κ),
      ENNReal.ofReal (rhoV κ (x - xPre κ R v))) / Z := by
    intro x hx
    rw [colLaw_apply κ Abar R u x hx]
    simp only [gaussVec_apply, ENNReal.div_eq_inv_mul, ← Finset.mul_sum]
    rfl
  have hd : ∀ v j, |xPre κ R v j| ≤ mb κ := fun v j => abs_xPre_le κ R hR v j
  have hlow : ∀ x ∈ Box κ, x ∈ C → ENNReal.ofReal (Real.exp (-θ)) * (c * p x) ≤ P x := by
    intro x hb hx
    rw [hcp x hx, hP_on x hx]
    simp only [ENNReal.div_eq_inv_mul]
    calc ENNReal.ofReal (Real.exp (-θ)) * (Z⁻¹ * (Qn * ENNReal.ofReal (rhoV κ x)))
        = Z⁻¹ * ∑ _v : Fin (n κ) → ZMod (q κ), ENNReal.ofReal (Real.exp (-θ) * rhoV κ x) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ENNReal.ofReal_mul (Real.exp_pos _).le]
          ring
      _ ≤ _ := by
          gcongr with v
          exact rho_shift_ge κ x _ hb (hd v)
  have hup : ∀ x ∈ Box κ, x ∈ C → P x ≤ ENNReal.ofReal (Real.exp θ) * (c * p x) := by
    intro x hb hx
    rw [hcp x hx, hP_on x hx]
    simp only [ENNReal.div_eq_inv_mul]
    calc Z⁻¹ * ∑ v : Fin (n κ) → ZMod (q κ), ENNReal.ofReal (rhoV κ (x - xPre κ R v))
        ≤ Z⁻¹ * ∑ _v : Fin (n κ) → ZMod (q κ), ENNReal.ofReal (Real.exp θ * rhoV κ x) := by
          gcongr with v
          exact rho_shift_le κ x _ hb (hd v)
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ENNReal.ofReal_mul (Real.exp_pos _).le]
          ring
  -- `c` from the tails
  have hPC : P.toOuterMeasure Cᶜ = 0 := by
    rw [PMF.toOuterMeasure_apply]
    refine ENNReal.tsum_eq_zero.mpr fun x => ?_
    by_cases hx : x ∈ Cᶜ
    · rw [Set.indicator_of_mem hx]; exact colLaw_apply_off κ Abar R u x hx
    · rw [Set.indicator_of_notMem hx]
  have hPbox : P.toOuterMeasure (Box κ ∩ C) ≤ ENNReal.ofReal (Real.exp θ) * c := by
    rw [PMF.toOuterMeasure_apply]
    calc ∑' x, (Box κ ∩ C).indicator P x ≤ ∑' x, ENNReal.ofReal (Real.exp θ) * c * p x := by
          refine ENNReal.tsum_le_tsum fun x => ?_
          by_cases hx : x ∈ Box κ ∩ C
          · rw [Set.indicator_of_mem hx, mul_assoc]; exact hup x hx.1 hx.2
          · rw [Set.indicator_of_notMem hx]; exact zero_le
      _ = ENNReal.ofReal (Real.exp θ) * c := by rw [ENNReal.tsum_mul_left, p.tsum_coe, mul_one]
  have h1 : 1 ≤ ENNReal.ofReal (Real.exp θ) * c + tg := by
    have hsplit : (1 : ℝ≥0∞) ≤ P.toOuterMeasure (Box κ ∩ C) + P.toOuterMeasure (Box κ)ᶜ := by
      calc (1 : ℝ≥0∞) = P.toOuterMeasure Set.univ := by
            rw [eq_comm, PMF.toOuterMeasure_apply_eq_one_iff]; intro x _; trivial
        _ ≤ P.toOuterMeasure ((Box κ ∩ C) ∪ ((Box κ)ᶜ ∪ Cᶜ)) := measure_mono fun x _ => by
            by_cases h1 : x ∈ Box κ <;> by_cases h2 : x ∈ C
            · exact Or.inl ⟨h1, h2⟩
            · exact Or.inr (Or.inr h2)
            · exact Or.inr (Or.inl h1)
            · exact Or.inr (Or.inl h1)
        _ ≤ P.toOuterMeasure (Box κ ∩ C) + (P.toOuterMeasure (Box κ)ᶜ + P.toOuterMeasure Cᶜ) :=
            (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
        _ = _ := by rw [hPC, add_zero]
    calc (1 : ℝ≥0∞) ≤ P.toOuterMeasure (Box κ ∩ C) + P.toOuterMeasure (Box κ)ᶜ := hsplit
      _ ≤ _ := add_le_add hPbox (colLaw_tail κ Abar R hR u)
  have hc : 1 - tg ≤ ENNReal.ofReal (Real.exp θ) * c := tsub_le_iff_right.mpr h1
  -- the domination
  set a := ENNReal.ofReal (Real.exp (-(2 * θ))) * (1 - tg)
  have hdom : ∀ x ∈ Box κ, a * p x ≤ P x := by
    intro x hb
    by_cases hx : x ∈ C
    · calc a * p x = ENNReal.ofReal (Real.exp (-θ)) * ENNReal.ofReal (Real.exp (-θ)) *
            (1 - tg) * p x := by
            simp only [a]
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; ring_nf
        _ ≤ ENNReal.ofReal (Real.exp (-θ)) * ENNReal.ofReal (Real.exp (-θ)) *
            (ENNReal.ofReal (Real.exp θ) * c) * p x := by gcongr
        _ = ENNReal.ofReal (Real.exp (-θ)) * (c * p x) := by
            have : ENNReal.ofReal (Real.exp (-θ)) * ENNReal.ofReal (Real.exp θ) = 1 := by
              rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel,
                Real.exp_zero, ENNReal.ofReal_one]
            calc _ = (ENNReal.ofReal (Real.exp (-θ)) * ENNReal.ofReal (Real.exp θ)) *
                ENNReal.ofReal (Real.exp (-θ)) * (c * p x) := by ring
              _ = _ := by rw [this, one_mul]
        _ ≤ P x := hlow x hb hx
    · rw [hp_off x hx, mul_zero]; exact zero_le
  refine (closeTo_of_ge P p (Box κ) hdom).mono ?_
  have hθ : 0 ≤ θ := by
    simp only [θ, θT, Rr]; have := τ_pos κ; positivity
  have hs1 : ENNReal.ofReal (Real.exp (-(2 * θ))) ≤ 1 :=
    ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have h1s : 1 - ENNReal.ofReal (Real.exp (-(2 * θ))) ≤ ENNReal.ofReal (2 * θ) := by
    rw [tsub_le_iff_right, ← ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le]
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    linarith [Real.add_one_le_exp (-(2 * θ))]
  calc 1 - a + p.toOuterMeasure (Box κ)ᶜ
      ≤ (1 - ENNReal.ofReal (Real.exp (-(2 * θ))) + tg) +
        ENNReal.ofReal (3 * 2 ^ m κ * (1 / 4) ^ (m κ ^ 2)) := by
        gcongr
        · exact one_sub_mul_le _ _ hs1
        · exact coset_box_tail κ Abar R u hB hp
    _ ≤ _ := by gcongr

end

end SigabaNeo.Lattices.Trapdoor.Family
