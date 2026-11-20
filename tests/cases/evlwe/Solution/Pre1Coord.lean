import SigabaNeo.Lib.Lattices.Gaussian.Facts
import Solution.Pre2Lwe

/-!
# Pre1, one coordinate: `2t + e` is close to uniform mod `q`

For `t` uniform below `N = (q − 1)/2 + 1` and `e ← D_{Z,σ'}`, the residue `2t + e mod q` is within
`εc κ = σ'√m/N + 6·4^{−m} + 3/σ' + 1/(q + 1)` of uniform (`closeTo_coord`):

1. write `e = 2a + b` with `b = e mod 2`; `t + a` is close to `t` (`closeTo_shift`), outside the
   unlikely event `|e| ≥ σ'√m`;
2. `b` is close to a fair bit (`closeTo_par`, from the parity bound of `Solution/GaussFacts.lean`);
3. with a fair bit, `2t + b` hits every residue with probability at least `1/(2N) = 1/(q + 1)`
   (`coord_fair_ge`), which is `(1 − 1/(q+1))` times the uniform mass.
-/

namespace TestCase.EvLWE

open SigabaNeo.Lattices

open TestCase TestCase.EvLWE Cslib.Probability
open scoped ENNReal

section
variable (κ : ℕ)

/-- `2t + e mod q`. -/
noncomputable def cz (t : Fin (NT κ)) (e : ℤ) : ZMod (q κ) := ((2 * (t : ℕ) : ℤ) + e : ℤ)

/-- The law of one coordinate. -/
noncomputable def L1 : PMF (ZMod (q κ)) :=
  (PMF.uniformOfFintype (Fin (NT κ))).bind fun t => (gaussZ (σ' κ) (σ'_pos κ)).map (cz κ t)

/-- `e mod 2` as a bit. -/
def par (e : ℤ) : Bool := decide (e % 2 = 1)

/-- `2t + b`. -/
noncomputable def L2b (b : Bool) : PMF (ZMod (q κ)) :=
  (PMF.uniformOfFintype (Fin (NT κ))).map fun t => cz κ t (if b then 1 else 0)

noncomputable def εc : ℝ :=
  σ' κ * Real.sqrt (m κ) / NT κ + 6 * (1 / 4) ^ m κ + 3 / σ' κ + 1 / (q κ + 1)

theorem εc_nonneg : 0 ≤ εc κ := by
  unfold εc σ'; positivity

theorem emod_two_eq (e : ℤ) : e % 2 = if par e then 1 else 0 := by
  unfold par
  rcases Int.emod_two_eq_zero_or_one e with h | h <;> simp [h]

theorem cz_split (t : Fin (NT κ)) (e : ℤ) :
    cz κ t e = (fun y : ℤ => ((2 * y + (if par e then 1 else 0) : ℤ) : ZMod (q κ)))
      ((t : ℕ) + e / 2) := by
  unfold cz
  congr 1
  rw [← emod_two_eq]
  push_cast
  omega

/-- Step 1: absorb `e / 2` into `t`. -/
theorem closeTo_L1_L2 :
    CloseTo (L1 κ) ((gaussZ (σ' κ) (σ'_pos κ)).bind fun e => L2b κ (par e))
      (ENNReal.ofReal (σ' κ * Real.sqrt (m κ) / NT κ) + ENNReal.ofReal (6 * (1 / 4) ^ m κ)) := by
  have hL1 : L1 κ = (gaussZ (σ' κ) (σ'_pos κ)).bind fun e =>
      (PMF.uniformOfFintype (Fin (NT κ))).map fun t => cz κ t e := by
    refine pmf_ext_ev fun f => ?_
    unfold L1
    simp only [ev_bind, ev_map]
    exact ev_comm _ _ _
  rw [hL1]
  have hB : 0 < σ' κ * Real.sqrt (m κ) :=
    mul_pos (σ'_pos κ) (Real.sqrt_pos.mpr (by exact_mod_cast m_pos κ))
  refine (closeTo_bind_good _ _ _ (fun e => |((e : ℤ) : ℝ)| < σ' κ * Real.sqrt (m κ))
    (ε := ENNReal.ofReal (σ' κ * Real.sqrt (m κ) / NT κ)) fun e _ he => ?_).mono ?_
  · have h := (closeTo_shift (NT κ) (-(e / 2))).map
      (fun y : ℤ => ((2 * y + (if par e then 1 else 0) : ℤ) : ZMod (q κ)))
    rw [PMF.map_comp, PMF.map_comp] at h
    have h1 : ((fun y : ℤ => ((2 * y + (if par e then 1 else 0) : ℤ) : ZMod (q κ))) ∘
        fun t : Fin (NT κ) => ((t : ℕ) : ℤ) - -(e / 2)) = fun t => cz κ t e := by
      funext t; rw [Function.comp_apply, cz_split, sub_neg_eq_add]
    have h2 : ((fun y : ℤ => ((2 * y + (if par e then 1 else 0) : ℤ) : ZMod (q κ))) ∘
        fun t : Fin (NT κ) => ((t : ℕ) : ℤ)) = fun t => cz κ t (if par e then 1 else 0) := by
      funext t; simp [cz]
    rw [h1, h2] at h
    refine h.mono ?_
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast NT_pos κ), ENNReal.ofReal_natCast]
    gcongr
    rw [Int.natAbs_neg]
    have hle : ((e / 2).natAbs : ℝ) ≤ |((e : ℤ) : ℝ)| := by
      have h0 : (e / 2).natAbs ≤ e.natAbs := by omega
      calc ((e / 2).natAbs : ℝ) ≤ (e.natAbs : ℝ) := Nat.cast_le.mpr h0
        _ = |((e : ℤ) : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hle.trans he.le)
  · gcongr
    refine (ev_mono _ fun e => ind_mono (Q := σ' κ * Real.sqrt (m κ) ≤ |((e : ℤ) : ℝ)|)
      fun h => by push Not at h; exact h).trans ?_
    exact (toOuterMeasure_eq_ev (gaussZ (σ' κ) (σ'_pos κ))
      {x : ℤ | σ' κ * Real.sqrt (m κ) ≤ |(x : ℝ)|}).symm.le.trans
      (gaussZ_tail (one_le_pow₀ (by norm_num) : (1 : ℝ) ≤ 2 ^ (2 * κ + 2)) (σ'_pos κ) (m κ))


/-! ### Step 2: the parity -/

/-- The law of `e mod 2`. -/
noncomputable def parLaw : PMF Bool := (gaussZ (σ' κ) (σ'_pos κ)).map par

theorem parLaw_apply (c : Bool) (b : ℤ) (hb : b = if c then 1 else 0) :
    parLaw κ c = ev (gaussZ (σ' κ) (σ'_pos κ)) (fun e => ind (e % 2 = b)) := by
  unfold parLaw ev
  rw [PMF.map_apply]
  refine tsum_congr fun e => ?_
  unfold par
  subst hb
  cases c <;> rcases Int.emod_two_eq_zero_or_one e with h | h <;> simp [h, ind]

theorem closeTo_bool_unif (μ : PMF Bool) (ε : ℝ≥0∞) (h1 : μ true ≤ 1 / 2 + ε)
    (h0 : μ false ≤ 1 / 2 + ε) : CloseTo μ (PMF.uniformOfFintype Bool) ε := by
  have hsum : μ false + μ true = 1 := by
    have := μ.tsum_coe; rwa [tsum_fintype, Fintype.sum_bool, add_comm] at this
  intro E
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, tsum_fintype, tsum_fintype,
    Fintype.sum_bool, Fintype.sum_bool]
  have hu : ∀ b, (PMF.uniformOfFintype Bool) b = 1 / 2 := fun b => by
    rw [PMF.uniformOfFintype_apply, Fintype.card_bool, one_div]; rfl
  by_cases ht : true ∈ E <;> by_cases hf : false ∈ E
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem hf, Set.indicator_of_mem ht,
      Set.indicator_of_mem hf, hu, hu, add_comm, hsum, ENNReal.add_halves]
    exact le_self_add
  · rw [Set.indicator_of_mem ht, Set.indicator_of_notMem hf, Set.indicator_of_mem ht,
      Set.indicator_of_notMem hf, hu, add_zero, add_zero]
    exact h1
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_mem hf, Set.indicator_of_notMem ht,
      Set.indicator_of_mem hf, hu, zero_add, zero_add]
    exact h0
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem hf]
    simp

theorem closeTo_par : CloseTo (parLaw κ) (PMF.uniformOfFintype Bool) (ENNReal.ofReal (3 / σ' κ)) := by
  apply closeTo_bool_unif
  · rw [parLaw_apply κ true 1 rfl]
    exact ev_par_le (σ'_pos κ) 1 0 (by norm_num) (Or.inr rfl) (odd_le_even _)
  · rw [parLaw_apply κ false 0 rfl]
    exact ev_par_le (σ'_pos κ) 0 1 (by norm_num) (Or.inl rfl) (even_le_odd _)

/-! ### Step 3: a fair bit -/

theorem two_NT : 2 * NT κ = q κ + 1 := by
  have := q_odd κ
  unfold NT; omega

theorem coord_fair_ge (x : ZMod (q κ)) :
    (2 : ℝ≥0∞)⁻¹ * (NT κ : ℝ≥0∞)⁻¹ ≤ ((PMF.uniformOfFintype Bool).bind (L2b κ)) x := by
  have hv := ZMod.val_lt x
  have hq := two_NT κ
  have hNT : NT κ = (q κ - 1) / 2 + 1 := rfl
  have ht0 : x.val / 2 < NT κ := by omega
  let c0 : Bool := decide (x.val % 2 = 1)
  let t0 : Fin (NT κ) := ⟨x.val / 2, ht0⟩
  have hcz : cz κ t0 (if c0 then 1 else 0) = x := by
    unfold cz
    have : ((2 * (t0 : ℕ) : ℤ) + (if c0 then 1 else 0) : ℤ) = (x.val : ℤ) := by
      have hd := Nat.div_add_mod x.val 2
      show ((2 * (x.val / 2 : ℕ) : ℤ) + (if decide (x.val % 2 = 1) then 1 else 0) : ℤ) = _
      split_ifs with hc
      · simp only [decide_eq_true_eq] at hc; push_cast; omega
      · simp only [decide_eq_true_eq] at hc; push_cast; omega
    rw [this, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [PMF.bind_apply]
  refine le_trans ?_ (ENNReal.le_tsum c0)
  rw [PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat]
  gcongr
  unfold L2b
  rw [PMF.map_apply]
  refine le_trans ?_ (ENNReal.le_tsum t0)
  rw [if_pos hcz.symm, PMF.uniformOfFintype_apply, Fintype.card_fin]

theorem closeTo_fair :
    CloseTo ((PMF.uniformOfFintype Bool).bind (L2b κ)) (PMF.uniformOfFintype (ZMod (q κ)))
      (ENNReal.ofReal (1 / (q κ + 1))) := by
  apply CloseTo.of_le_apply (by positivity)
  intro x
  refine le_trans (le_of_eq ?_) (coord_fair_ge κ x)
  rw [PMF.uniformOfFintype_apply, ZMod.card]
  have hq : (0 : ℝ) < q κ := q_pos κ
  have hNp : (0 : ℝ) < NT κ := by exact_mod_cast NT_pos κ
  have h2 : (2 : ℝ) * NT κ = q κ + 1 := by exact_mod_cast two_NT κ
  have hL : ENNReal.ofReal (1 - 1 / ((q κ : ℝ) + 1)) * ((q κ : ℕ) : ℝ≥0∞)⁻¹ =
      ENNReal.ofReal (1 / ((q κ : ℝ) + 1)) := by
    rw [← ENNReal.ofReal_natCast (q κ), ← ENNReal.ofReal_inv_of_pos hq,
      ← ENNReal.ofReal_mul (by rw [sub_nonneg, div_le_one (by positivity)]; linarith)]
    congr 1
    field_simp
    ring
  have hR : (2 : ℝ≥0∞)⁻¹ * ((NT κ : ℕ) : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / ((q κ : ℝ) + 1)) := by
    rw [← ENNReal.mul_inv (by simp) (by simp), ← ENNReal.ofReal_natCast (NT κ),
      show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_inv_of_pos (by positivity), h2, one_div]
  rw [hL, hR]

/-- **One coordinate.** -/
theorem closeTo_coord :
    CloseTo (L1 κ) (PMF.uniformOfFintype (ZMod (q κ))) (ENNReal.ofReal (εc κ)) := by
  have h12 := closeTo_L1_L2 κ
  have h2 : (gaussZ (σ' κ) (σ'_pos κ)).bind (fun e => L2b κ (par e)) = (parLaw κ).bind (L2b κ) := by
    unfold parLaw; rw [PMF.bind_map]; rfl
  rw [h2] at h12
  have h23 := (closeTo_par κ).bind_left (L2b κ)
  have h34 := closeTo_fair κ
  refine ((h12.trans h23).trans h34).mono (le_of_eq ?_)
  unfold εc
  have hσ := σ'_pos κ
  have hA : 0 ≤ σ' κ * Real.sqrt (m κ) / NT κ :=
    div_nonneg (mul_nonneg hσ.le (Real.sqrt_nonneg _)) (Nat.cast_nonneg _)
  have hB : (0 : ℝ) ≤ 6 * (1 / 4) ^ m κ := by positivity
  have hC : 0 ≤ 3 / σ' κ := div_nonneg (by norm_num) hσ.le
  have hD : (0 : ℝ) ≤ 1 / ((q κ : ℝ) + 1) := by positivity
  rw [ENNReal.ofReal_add (add_nonneg (add_nonneg hA hB) hC) hD,
    ENNReal.ofReal_add (add_nonneg hA hB) hC, ENNReal.ofReal_add hA hB]

end

end TestCase.EvLWE
