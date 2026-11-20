import SigabaNeo.Lib.Lattices.Gaussian.Z
import SigabaNeo.Lib.Lattices.Prob
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Point masses and parity of `D_{Z,σ}`

* `gaussZ_apply`: `D_{Z,σ}(x) = ρ_σ(x) / ρ_σ(Z)` with `ρ_σ(x) = exp(−π x²/σ²)`.
* `Mz_ge`: `ρ_σ(Z) ≥ σ/6` (the integers `0, …, ⌊σ/2⌋` each weigh at least `e^{−1} > 1/3`).
* `gaussZ_le`: every point has mass at most `6/σ`.
* `odd_le`, `even_le`: the odd and even parts of `ρ_σ(Z)` differ by at most `ρ_σ(0) = 1`, since
  `ρ_σ` decreases in `|x|`; so `D_{Z,σ}` is odd with probability within `3/σ` of `1/2`
  (`ev_odd_le`, `ev_even_le`).
-/

namespace SigabaNeo.Lattices

open SigabaNeo.Lattices ZLattice ProbabilityTheory
open scoped ENNReal

/-- `ρ_σ(x)`. -/
noncomputable def gw (σ : ℝ) (x : ℤ) : ℝ := Real.exp (-Real.pi * (x : ℝ) ^ 2 / σ ^ 2)

/-- `ρ_σ(Z)`. -/
noncomputable def Mz (σ : ℝ) : ℝ := gaussianMass (perp B0) σ 0

theorem mem_perp_B0 (y : Fin 1 → ℤ) : embed 1 y ∈ perp B0 :=
  Submodule.mem_map.mpr ⟨y, Subsingleton.elim _ _, rfl⟩

/-- The lattice point of an integer. -/
noncomputable def ptZ (x : ℤ) : perp B0 := ⟨embed 1 (fun _ => x), mem_perp_B0 _⟩

theorem toInt_ptZ (x : ℤ) : toInt ((ptZ x : perp B0) : EuclideanSpace ℝ (Fin 1)) 0 = x := by
  simp [ptZ, toInt_embed]

theorem eq_ptZ (z : perp B0) : z = ptZ (toInt (z : EuclideanSpace ℝ (Fin 1)) 0) := by
  obtain ⟨y, -, hy⟩ := Submodule.mem_map.mp z.2
  apply Subtype.ext
  simp only [ptZ]
  rw [← hy, toInt_embed]
  congr 1
  funext i
  rw [Subsingleton.elim i 0]

theorem gw_ptZ (σ : ℝ) (x : ℤ) :
    gaussianWeight σ (((ptZ x : perp B0) : EuclideanSpace ℝ (Fin 1)) - 0) = gw σ x := by
  unfold gaussianWeight gw
  rw [sub_zero, show ((ptZ x : perp B0) : EuclideanSpace ℝ (Fin 1)) = embed 1 (fun _ => x) from rfl,
    norm_embed_one, sq_abs]

theorem gaussZ_apply {σ : ℝ} (hs : 0 < σ) (x : ℤ) :
    gaussZ σ hs x = ENNReal.ofReal (gw σ x) / ENNReal.ofReal (Mz σ) := by
  unfold gaussZ
  have hb : (discreteGaussian (perp B0) σ hs 0 >>= fun a =>
      pure (a : EuclideanSpace ℝ (Fin 1))) =
      (discreteGaussian (perp B0) σ hs 0).map Subtype.val := rfl
  rw [hb, PMF.map_comp, PMF.map_apply, tsum_eq_single (ptZ x)]
  · have hc : x = ((fun z => toInt z 0) ∘ Subtype.val) (ptZ x) := (toInt_ptZ x).symm
    rw [if_pos hc, discreteGaussian_apply, gw_ptZ]; rfl
  · intro z hz
    rw [if_neg]
    intro hx
    exact hz ((eq_ptZ z).trans (congrArg ptZ hx.symm))

theorem Mz_pos {σ : ℝ} (hs : 0 < σ) : 0 < Mz σ := gaussianMass_pos _ σ hs 0

theorem tsum_gw {σ : ℝ} (hs : 0 < σ) :
    ∑' x : ℤ, ENNReal.ofReal (gw σ x) = ENNReal.ofReal (Mz σ) := by
  have h := (gaussZ σ hs).tsum_coe
  simp only [gaussZ_apply hs, ENNReal.div_eq_inv_mul, ENNReal.tsum_mul_left] at h
  have hM : ENNReal.ofReal (Mz σ) ≠ 0 := (ENNReal.ofReal_pos.mpr (Mz_pos hs)).ne'
  have hM' : ENNReal.ofReal (Mz σ) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc ∑' x : ℤ, ENNReal.ofReal (gw σ x)
      = ENNReal.ofReal (Mz σ) * ((ENNReal.ofReal (Mz σ))⁻¹ *
          ∑' x : ℤ, ENNReal.ofReal (gw σ x)) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hM hM', one_mul]
    _ = ENNReal.ofReal (Mz σ) := by rw [h, mul_one]

theorem gw_zero (σ : ℝ) : gw σ 0 = 1 := by simp [gw]

theorem gw_neg (σ : ℝ) (x : ℤ) : gw σ (-x) = gw σ x := by simp [gw]

theorem gw_le_one (σ : ℝ) (x : ℤ) : gw σ x ≤ 1 := by
  unfold gw
  rw [Real.exp_le_one_iff]
  have : 0 ≤ Real.pi * (x : ℝ) ^ 2 / σ ^ 2 := by positivity
  linarith [show -Real.pi * (x : ℝ) ^ 2 / σ ^ 2 = -(Real.pi * (x : ℝ) ^ 2 / σ ^ 2) by ring]

/-- `ρ_σ` decreases on `ℕ`. -/
theorem gw_succ_le (σ : ℝ) (n : ℕ) : gw σ ((n + 1 : ℕ) : ℤ) ≤ gw σ (n : ℤ) := by
  unfold gw
  apply Real.exp_le_exp.mpr
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h : ((n : ℤ) : ℝ) ^ 2 ≤ (((n + 1 : ℕ) : ℤ) : ℝ) ^ 2 := by push_cast; nlinarith
  have hs : 0 ≤ Real.pi / σ ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left h hs
  calc -Real.pi * (((n + 1 : ℕ) : ℤ) : ℝ) ^ 2 / σ ^ 2
      = -(Real.pi / σ ^ 2 * (((n + 1 : ℕ) : ℤ) : ℝ) ^ 2) := by ring
    _ ≤ -(Real.pi / σ ^ 2 * ((n : ℤ) : ℝ) ^ 2) := by linarith
    _ = -Real.pi * ((n : ℤ) : ℝ) ^ 2 / σ ^ 2 := by ring

theorem Mz_ge {σ : ℝ} (hs : 0 < σ) : σ / 6 ≤ Mz σ := by
  set N := ⌊σ / 2⌋₊
  have hN : σ / 2 < N + 1 := Nat.lt_floor_add_one _
  have hterm : ∀ n ∈ Finset.range (N + 1), ENNReal.ofReal (1 / 3) ≤ ENNReal.ofReal (gw σ (n : ℤ)) := by
    intro n hn
    apply ENNReal.ofReal_le_ofReal
    have hn' : (n : ℝ) ≤ σ / 2 := by
      have := Finset.mem_range.mp hn
      have h1 : n ≤ N := by omega
      exact (Nat.cast_le.mpr h1).trans (Nat.floor_le (by positivity))
    have hx : Real.pi * ((n : ℤ) : ℝ) ^ 2 / σ ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      push_cast
      have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      nlinarith [Real.pi_lt_four, mul_le_mul hn' hn' h0 (by positivity)]
    unfold gw
    calc (1 : ℝ) / 3 ≤ Real.exp (-1) := by
          rw [Real.exp_neg, inv_eq_one_div]
          exact one_div_le_one_div_of_le (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three])
      _ ≤ _ := Real.exp_le_exp.mpr (by
          rw [show -Real.pi * ((n : ℤ) : ℝ) ^ 2 / σ ^ 2 = -(Real.pi * ((n : ℤ) : ℝ) ^ 2 / σ ^ 2) by
            ring]
          linarith)
  have hsum : ((N + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / 3) ≤ ENNReal.ofReal (Mz σ) := by
    rw [← tsum_gw hs]
    calc ((N + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / 3)
        = ∑ n ∈ Finset.range (N + 1), ENNReal.ofReal (1 / 3) := by simp
      _ ≤ ∑ n ∈ Finset.range (N + 1), ENNReal.ofReal (gw σ (n : ℤ)) := Finset.sum_le_sum hterm
      _ = ∑ x ∈ (Finset.range (N + 1)).map Nat.castEmbedding, ENNReal.ofReal (gw σ x) := by
          rw [Finset.sum_map]; rfl
      _ ≤ ∑' x : ℤ, ENNReal.ofReal (gw σ x) := sum_le_tsum _
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (Mz_pos hs).le] at hsum
  push_cast at hsum
  linarith

theorem gaussZ_le {σ : ℝ} (hs : 0 < σ) (x : ℤ) : gaussZ σ hs x ≤ ENNReal.ofReal (6 / σ) := by
  rw [gaussZ_apply hs]
  have hM := Mz_pos hs
  rw [← ENNReal.ofReal_div_of_pos hM]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_div_iff₀ hM hs]
  have := Mz_ge hs
  have := gw_le_one σ x
  nlinarith [(Real.exp_pos _ : 0 < gw σ x)]

/-! ### Parity -/

/-- Split a sum over `ℕ` into even and odd indices. -/
theorem tsum_nat_even_odd (f : ℕ → ℝ≥0∞) :
    ∑' n, f n = ∑' j, f (2 * j) + ∑' j, f (2 * j + 1) :=
  (tsum_even_add_odd CompleteLattice.summable CompleteLattice.summable).symm

theorem int_emod_two_neg (n : ℕ) : (-((n : ℤ) + 1)) % 2 = ((n : ℤ) + 1) % 2 := Int.neg_emod_two _

/-- The weight of odd (`b = 1`) or even (`b = 0`) integers. -/
noncomputable def parMass (σ : ℝ) (b : ℤ) : ℝ≥0∞ :=
  ∑' x : ℤ, ind (x % 2 = b) * ENNReal.ofReal (gw σ x)

theorem parMass_eq (σ : ℝ) (b : ℤ) :
    parMass σ b = ∑' n : ℕ, ind ((n : ℤ) % 2 = b) * ENNReal.ofReal (gw σ n) +
      ∑' n : ℕ, ind (((n + 1 : ℕ) : ℤ) % 2 = b) * ENNReal.ofReal (gw σ ((n + 1 : ℕ) : ℤ)) := by
  unfold parMass
  rw [tsum_int_ennreal]
  congr 1
  refine tsum_congr fun n => ?_
  rw [show (-((n : ℤ) + 1)) = -(((n + 1 : ℕ) : ℤ)) by push_cast; ring, gw_neg, Int.neg_emod_two]

theorem emod_two_even (j : ℕ) : ((2 * j : ℕ) : ℤ) % 2 = 0 := by push_cast; omega
theorem emod_two_odd (j : ℕ) : ((2 * j + 1 : ℕ) : ℤ) % 2 = 1 := by push_cast; omega

/-- With `a_n = ρ_σ(n)`: odd mass `2 Σ a_{2j+1}`. -/
theorem parMass_one (σ : ℝ) :
    parMass σ 1 = 2 * ∑' j : ℕ, ENNReal.ofReal (gw σ ((2 * j + 1 : ℕ) : ℤ)) := by
  rw [parMass_eq, tsum_nat_even_odd, tsum_nat_even_odd (fun n => ind (((n + 1 : ℕ) : ℤ) % 2 = 1) * _)]
  have e1 : ∀ j : ℕ, ind (((2 * j : ℕ) : ℤ) % 2 = 1) = 0 := fun j => ind_of_not (by rw [emod_two_even]; omega)
  have e2 : ∀ j : ℕ, ind (((2 * j + 1 : ℕ) : ℤ) % 2 = 1) = 1 := fun j => ind_of (emod_two_odd j)
  have e3 : ∀ j : ℕ, ind (((2 * j + 1 + 1 : ℕ) : ℤ) % 2 = 1) = 0 := fun j =>
    ind_of_not (by rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, emod_two_even]; omega)
  simp only [e1, e2, e3, zero_mul, one_mul, tsum_zero, zero_add, add_zero]
  ring

/-- Even mass `a_0 + 2 Σ a_{2j+2}`, written as `Σ a_{2j} + Σ a_{2j+2}`. -/
theorem parMass_zero (σ : ℝ) :
    parMass σ 0 = ∑' j : ℕ, ENNReal.ofReal (gw σ ((2 * j : ℕ) : ℤ)) +
      ∑' j : ℕ, ENNReal.ofReal (gw σ ((2 * j + 1 + 1 : ℕ) : ℤ)) := by
  rw [parMass_eq, tsum_nat_even_odd, tsum_nat_even_odd (fun n => ind (((n + 1 : ℕ) : ℤ) % 2 = 0) * _)]
  have e1 : ∀ j : ℕ, ind (((2 * j : ℕ) : ℤ) % 2 = 0) = 1 := fun j => ind_of (emod_two_even j)
  have e2 : ∀ j : ℕ, ind (((2 * j + 1 : ℕ) : ℤ) % 2 = 0) = 0 := fun j =>
    ind_of_not (by rw [emod_two_odd]; omega)
  have e3 : ∀ j : ℕ, ind (((2 * j + 1 + 1 : ℕ) : ℤ) % 2 = 0) = 1 := fun j =>
    ind_of (by rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, emod_two_even])
  simp only [e1, e2, e3, zero_mul, one_mul, tsum_zero, zero_add, add_zero]

theorem tsum_even_split (σ : ℝ) :
    ∑' j : ℕ, ENNReal.ofReal (gw σ ((2 * j : ℕ) : ℤ)) =
      1 + ∑' j : ℕ, ENNReal.ofReal (gw σ ((2 * j + 1 + 1 : ℕ) : ℤ)) := by
  rw [tsum_eq_zero_add' CompleteLattice.summable]
  simp only [Nat.mul_zero, Nat.cast_zero, gw_zero, ENNReal.ofReal_one]
  congr 1

theorem odd_le_even (σ : ℝ) : parMass σ 1 ≤ parMass σ 0 + 1 := by
  rw [parMass_one, parMass_zero, two_mul]
  have h1 : ∑' j : ℕ, ENNReal.ofReal (gw σ ((2 * j + 1 : ℕ) : ℤ)) ≤
      ∑' j : ℕ, ENNReal.ofReal (gw σ ((2 * j : ℕ) : ℤ)) :=
    tsum_le_tsum fun j => ENNReal.ofReal_le_ofReal (gw_succ_le σ (2 * j))
  calc _ ≤ ∑' j : ℕ, ENNReal.ofReal (gw σ ((2 * j : ℕ) : ℤ)) +
        ∑' j : ℕ, ENNReal.ofReal (gw σ ((2 * j : ℕ) : ℤ)) := add_le_add h1 h1
    _ = _ := by rw [tsum_even_split σ]; ring

theorem even_le_odd (σ : ℝ) : parMass σ 0 ≤ parMass σ 1 + 1 := by
  rw [parMass_one, parMass_zero, tsum_even_split, two_mul]
  have h1 : ∑' j : ℕ, ENNReal.ofReal (gw σ ((2 * j + 1 + 1 : ℕ) : ℤ)) ≤
      ∑' j : ℕ, ENNReal.ofReal (gw σ ((2 * j + 1 : ℕ) : ℤ)) :=
    tsum_le_tsum fun j => ENNReal.ofReal_le_ofReal (gw_succ_le σ (2 * j + 1))
  calc _ ≤ 1 + ∑' j : ℕ, ENNReal.ofReal (gw σ ((2 * j + 1 : ℕ) : ℤ)) +
        ∑' j : ℕ, ENNReal.ofReal (gw σ ((2 * j + 1 : ℕ) : ℤ)) := by gcongr
    _ = _ := by ring

theorem parMass_add (σ : ℝ) {s : ℝ} (hs : 0 < s) (hσ : σ = s) :
    parMass σ 0 + parMass σ 1 = ENNReal.ofReal (Mz σ) := by
  subst hσ
  rw [← tsum_gw hs]
  unfold parMass
  rw [← tsum_add]
  refine tsum_congr fun x => ?_
  rw [← add_mul]
  rcases Int.emod_two_eq_zero_or_one x with h | h
  · rw [ind_of h, ind_of_not (by omega), add_zero, one_mul]
  · rw [ind_of_not (by omega), ind_of h, zero_add, one_mul]

theorem ev_parity {σ : ℝ} (hs : 0 < σ) (b : ℤ) :
    ev (gaussZ σ hs) (fun x => ind (x % 2 = b)) = parMass σ b / ENNReal.ofReal (Mz σ) := by
  unfold ev parMass
  simp only [gaussZ_apply hs, ENNReal.div_eq_inv_mul, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun x => ?_
  ring

/-- `Pr[x odd] ≤ 1/2 + 3/σ` and `Pr[x even] ≤ 1/2 + 3/σ`. -/
theorem ev_par_le {σ : ℝ} (hs : 0 < σ) (b b' : ℤ) (hb : b' = 1 - b) (hb01 : b = 0 ∨ b = 1)
    (hle : parMass σ b ≤ parMass σ b' + 1) :
    ev (gaussZ σ hs) (fun x => ind (x % 2 = b)) ≤ 1 / 2 + ENNReal.ofReal (3 / σ) := by
  rw [ev_parity hs]
  have hM := Mz_pos hs
  have hadd : parMass σ b + parMass σ b' = ENNReal.ofReal (Mz σ) := by
    rcases hb01 with rfl | rfl
    · subst hb; norm_num; exact parMass_add σ hs rfl
    · subst hb; norm_num; rw [add_comm]; exact parMass_add σ hs rfl
  have hfin : parMass σ b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hadd ▸ le_self_add)
  have hfin' : parMass σ b' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hadd ▸ le_add_self)
  -- in reals
  set A := (parMass σ b).toReal
  set B := (parMass σ b').toReal
  have hAB : A + B = Mz σ := by
    rw [← ENNReal.toReal_add hfin hfin', hadd, ENNReal.toReal_ofReal hM.le]
  have hle' : A ≤ B + 1 := by
    have := ENNReal.toReal_mono (by simp [hfin']) hle
    rwa [ENNReal.toReal_add hfin' (by simp), ENNReal.toReal_one] at this
  have hMz := Mz_ge hs
  rw [show parMass σ b = ENNReal.ofReal A from (ENNReal.ofReal_toReal hfin).symm,
    ← ENNReal.ofReal_div_of_pos hM, show (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp,
    ← ENNReal.ofReal_add (by norm_num) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_iff₀ hM]
  have h1 : A ≤ Mz σ / 2 + 1 / 2 := by linarith
  have h2 : (1 : ℝ) / 2 ≤ 3 / σ * Mz σ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hs]; linarith
  nlinarith

end SigabaNeo.Lattices
