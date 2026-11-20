import SigabaNeo.Lib.Lattices.Trapdoor.Family.Close

/-!
# Trapdoor sampler: column laws over an approximate Gaussian

`colLaw_close` with `D_{Z^m,τ}` replaced by any law `μ` whose mass is within the factors `a`, `b` of
`ρ_τ(y)/ρ_τ(Z)^m` (the lower factor on the enlarged box `|y_j| < τ m + mb`, the upper one
everywhere): the shifted law `colLawOf μ` is within `(1 − (a/b) e^{−2θ} (1 − t)) + tail` of the coset
Gaussian (`colLawOf_close`), where `t` bounds the mass `μ` puts outside `|y_j| < τ √m`.
-/

namespace SigabaNeo.Lattices.Trapdoor.Family

open SigabaNeo.Lattices ZLattice ProbabilityTheory Cslib.Probability MeasureTheory
open scoped ENNReal Matrix

section
variable (κ : ℕ)

/-- The column sampler over a base law `μ`. -/
noncomputable def colLawOf (μ : PMF (Fin (m κ) → ℤ)) (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)))
    (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (u : Fin (n κ) → ZMod (q κ)) :
    PMF (Fin (m κ) → ℤ) :=
  μ.map (gsyn κ Abar R u)

theorem colLawOf_apply (μ : PMF (Fin (m κ) → ℤ)) (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)))
    (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (u : Fin (n κ) → ZMod (q κ)) (x : Fin (m κ) → ℤ)
    (hx : Bmat κ Abar R *ᵥ castV κ x = u) :
    colLawOf κ μ Abar R u x = ∑ v : Fin (n κ) → ZMod (q κ), μ (x - xPre κ R v) := by
  classical
  have hinj : Function.Injective fun v : Fin (n κ) → ZMod (q κ) => x - xPre κ R v := by
    intro v v' h
    have h' : xPre κ R v = xPre κ R v' := by simpa using h
    rw [← B_xPre κ Abar R v, ← B_xPre κ Abar R v', h']
  unfold colLawOf
  rw [PMF.map_apply, tsum_eq_sum (s := Finset.univ.image fun v => x - xPre κ R v)]
  · rw [Finset.sum_image fun a _ b _ h => hinj h]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [if_pos (gsyn_preimage κ Abar R u x hx v).symm]
  · intro y hy
    rw [if_neg]
    intro h
    apply hy
    refine Finset.mem_image.mpr ⟨u - Bmat κ Abar R *ᵥ castV κ y, Finset.mem_univ _, ?_⟩
    rw [h]; unfold gsyn; abel

theorem colLawOf_apply_off (μ : PMF (Fin (m κ) → ℤ)) (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)))
    (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (u : Fin (n κ) → ZMod (q κ)) (x : Fin (m κ) → ℤ)
    (hx : Bmat κ Abar R *ᵥ castV κ x ≠ u) : colLawOf κ μ Abar R u x = 0 :=
  map_apply_of_not_mem _ x fun y h => hx (h ▸ B_gsyn κ Abar R u y)

theorem colLawOf_tail (μ : PMF (Fin (m κ) → ℤ)) (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)))
    (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (hR : ∀ i j, |R i j| ≤ 1)
    (u : Fin (n κ) → ZMod (q κ)) :
    (colLawOf κ μ Abar R u).toOuterMeasure (Box κ)ᶜ ≤
      μ.toOuterMeasure {y | ∃ j, τ κ * Real.sqrt (m κ) ≤ |((y j : ℤ) : ℝ)|} := by
  unfold colLawOf
  rw [PMF.toOuterMeasure_map_apply]
  refine measure_mono ?_
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

/-- The enlarged box. -/
def BoxE : Set (Fin (m κ) → ℤ) := {y | ∀ j, |((y j : ℤ) : ℝ)| < Rr κ + mb κ}

theorem sub_mem_BoxE (x d : Fin (m κ) → ℤ) (hx : x ∈ Box κ) (hd : ∀ j, |d j| ≤ mb κ) :
    x - d ∈ BoxE κ := by
  intro j
  have h1 := hx j
  have h2 : |((d j : ℤ) : ℝ)| ≤ mb κ := by exact_mod_cast hd j
  have := abs_sub ((x j : ℤ) : ℝ) ((d j : ℤ) : ℝ)
  simp only [Pi.sub_apply, Int.cast_sub]
  linarith

/-- **A column law over an approximate Gaussian is close to the coset Gaussian.** -/
theorem colLawOf_close (μ : PMF (Fin (m κ) → ℤ)) {a b : ℝ≥0∞} (hb0 : b ≠ 0) (hbt : b ≠ ⊤)
    (hlo : ∀ y ∈ BoxE κ, a * (ENNReal.ofReal (rhoV κ y) / ENNReal.ofReal (Mz (τ κ)) ^ m κ) ≤ μ y)
    (hhi : ∀ y, μ y ≤ b * (ENNReal.ofReal (rhoV κ y) / ENNReal.ofReal (Mz (τ κ)) ^ m κ))
    {tg : ℝ≥0∞} (htg : μ.toOuterMeasure {y | ∃ j, τ κ * Real.sqrt (m κ) ≤ |((y j : ℤ) : ℝ)|} ≤ tg)
    (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)))
    (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (hR : ∀ i j, |R i j| ≤ 1)
    (u : Fin (n κ) → ZMod (q κ)) (hB : dualMassE (Bmat κ Abar R) (τ κ) ≤ 1 / 2)
    {p : PMF (Fin (m κ) → ℤ)} (hp : cosetGauss (Bmat κ Abar R) u (τ κ) (τ_pos κ) = some p) :
    CloseTo (colLawOf κ μ Abar R u) p
      ((1 - a * b⁻¹ * ENNReal.ofReal (Real.exp (-(2 * θT κ))) * (1 - tg)) +
        ENNReal.ofReal (3 * 2 ^ m κ * (1 / 4) ^ (m κ ^ 2))) := by
  classical
  obtain ⟨M, hM, hpx⟩ := cosetGauss_apply _ u (τ_pos κ) hp
  set B := Bmat κ Abar R
  set C : Set (Fin (m κ) → ℤ) := {x | B *ᵥ castV κ x = u}
  set Z := ENNReal.ofReal (Mz (τ κ)) ^ m κ
  set Mc := ENNReal.ofReal M
  set Qn : ℝ≥0∞ := (Fintype.card (Fin (n κ) → ZMod (q κ)) : ℝ≥0∞)
  set c := Qn * Mc / Z
  set θ := θT κ
  set P := colLawOf κ μ Abar R u
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
  have hP_on : ∀ x ∈ C, P x = ∑ v : Fin (n κ) → ZMod (q κ), μ (x - xPre κ R v) :=
    fun x hx => colLawOf_apply κ μ Abar R u x hx
  have hd : ∀ v j, |xPre κ R v j| ≤ mb κ := fun v j => abs_xPre_le κ R hR v j
  have hsum : ∀ k : ℝ≥0∞, ∑ _v : Fin (n κ) → ZMod (q κ), k = Qn * k := fun k => by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hlow : ∀ x ∈ Box κ, x ∈ C → a * ENNReal.ofReal (Real.exp (-θ)) * (c * p x) ≤ P x := by
    intro x hb hx
    rw [hcp x hx, hP_on x hx]
    calc a * ENNReal.ofReal (Real.exp (-θ)) * (Qn * ENNReal.ofReal (rhoV κ x) / Z)
        = ∑ _v : Fin (n κ) → ZMod (q κ), a * (ENNReal.ofReal (Real.exp (-θ) * rhoV κ x) / Z) := by
          rw [hsum, ENNReal.ofReal_mul (Real.exp_pos _).le]
          simp only [div_eq_mul_inv]; ring
      _ ≤ ∑ v : Fin (n κ) → ZMod (q κ), a * (ENNReal.ofReal (rhoV κ (x - xPre κ R v)) / Z) := by
          gcongr with v
          exact rho_shift_ge κ x _ hb (hd v)
      _ ≤ _ := Finset.sum_le_sum fun v _ => hlo _ (sub_mem_BoxE κ x _ hb (hd v))
  have hup : ∀ x ∈ Box κ, x ∈ C → P x ≤ b * ENNReal.ofReal (Real.exp θ) * (c * p x) := by
    intro x hb hx
    rw [hcp x hx, hP_on x hx]
    calc ∑ v : Fin (n κ) → ZMod (q κ), μ (x - xPre κ R v)
        ≤ ∑ v : Fin (n κ) → ZMod (q κ), b * (ENNReal.ofReal (rhoV κ (x - xPre κ R v)) / Z) :=
          Finset.sum_le_sum fun v _ => hhi _
      _ ≤ ∑ _v : Fin (n κ) → ZMod (q κ), b * (ENNReal.ofReal (Real.exp θ * rhoV κ x) / Z) := by
          gcongr with v
          exact rho_shift_le κ x _ hb (hd v)
      _ = _ := by
          rw [hsum, ENNReal.ofReal_mul (Real.exp_pos _).le]
          simp only [div_eq_mul_inv]; ring
  have hPC : P.toOuterMeasure Cᶜ = 0 := by
    rw [PMF.toOuterMeasure_apply]
    refine ENNReal.tsum_eq_zero.mpr fun x => ?_
    by_cases hx : x ∈ Cᶜ
    · rw [Set.indicator_of_mem hx]; exact colLawOf_apply_off κ μ Abar R u x hx
    · rw [Set.indicator_of_notMem hx]
  have hPbox : P.toOuterMeasure (Box κ ∩ C) ≤ b * ENNReal.ofReal (Real.exp θ) * c := by
    rw [PMF.toOuterMeasure_apply]
    calc ∑' x, (Box κ ∩ C).indicator P x ≤ ∑' x, b * ENNReal.ofReal (Real.exp θ) * c * p x := by
          refine ENNReal.tsum_le_tsum fun x => ?_
          by_cases hx : x ∈ Box κ ∩ C
          · rw [Set.indicator_of_mem hx, mul_assoc]; exact hup x hx.1 hx.2
          · rw [Set.indicator_of_notMem hx]; exact zero_le
      _ = b * ENNReal.ofReal (Real.exp θ) * c := by rw [ENNReal.tsum_mul_left, p.tsum_coe, mul_one]
  have h1 : 1 ≤ b * ENNReal.ofReal (Real.exp θ) * c + tg := by
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
      _ ≤ _ := add_le_add hPbox ((colLawOf_tail κ μ Abar R hR u).trans htg)
  have hc : 1 - tg ≤ b * ENNReal.ofReal (Real.exp θ) * c := tsub_le_iff_right.mpr h1
  set a' := a * b⁻¹ * ENNReal.ofReal (Real.exp (-(2 * θ))) * (1 - tg)
  have hdom : ∀ x ∈ Box κ, a' * p x ≤ P x := by
    intro x hb
    by_cases hx : x ∈ C
    · have hee : ENNReal.ofReal (Real.exp (-(2 * θ))) * ENNReal.ofReal (Real.exp θ) =
          ENNReal.ofReal (Real.exp (-θ)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; ring_nf
      calc a' * p x ≤ a * b⁻¹ * ENNReal.ofReal (Real.exp (-(2 * θ))) *
            (b * ENNReal.ofReal (Real.exp θ) * c) * p x := by simp only [a']; gcongr
        _ = a * (b⁻¹ * b) * (ENNReal.ofReal (Real.exp (-(2 * θ))) * ENNReal.ofReal (Real.exp θ)) *
            (c * p x) := by ring
        _ = a * ENNReal.ofReal (Real.exp (-θ)) * (c * p x) := by
            rw [ENNReal.inv_mul_cancel hb0 hbt, hee, mul_one]
        _ ≤ P x := hlow x hb hx
    · rw [hp_off x hx, mul_zero]; exact zero_le
  refine (closeTo_of_ge P p (Box κ) hdom).mono ?_
  gcongr
  exact coset_box_tail κ Abar R u hB hp

end

end SigabaNeo.Lattices.Trapdoor.Family
