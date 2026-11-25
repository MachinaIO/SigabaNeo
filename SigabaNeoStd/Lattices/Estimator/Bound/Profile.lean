import SigabaNeoStd.Lattices.Estimator.Bound.Guess

/-!
# The Babai success probability of the primal attacks

`NumPrimal.profile` sums, over blocks of coordinates of the GSA profile, the `log₂` of the
probability that Babai's algorithm handles the coordinate. Every term is at most `0`
(`profile_nonpos`). Far down the profile (`l ≤ −55`) the coordinate length underflows to `0` and
the term is the constant `c0 ≈ −29.9` per coordinate (`profile_tail`): a profile that drops by
more than 55 bits within its first `k` coordinates has a tiny success probability.
-/

namespace SigabaNeo.Lattices.Estimator

open Fx NumPrimal

/-- Induction along `List.range'` for a loop that always yields. -/
theorem forIn_range'_ind {β : Type} (s n : ℕ) (b : β) (f : ℕ → β → Id (ForInStep β))
    (I : ℕ → β → Prop) (h0 : I s b)
    (hf : ∀ i, s ≤ i → i < s + n → ∀ x, I i x → ∃ y, f i x = ForInStep.yield y ∧ I (i + 1) y) :
    I (s + n) (forIn (m := Id) (List.range' s n) b f) := by
  induction n generalizing s b with
  | zero => exact h0
  | succ n ih =>
    rw [List.range'_succ, List.forIn_cons]
    obtain ⟨y, hy, hI⟩ := hf s le_rfl (by omega) b h0
    rw [hy]
    have := ih (s + 1) y hI (fun i h1 h2 => hf i (by omega) (by omega))
    rwa [show s + 1 + n = s + (n + 1) by omega] at this

/-- The term of a coordinate whose length underflows. -/
def NumPrimal.c0 : Fx := log2 (max 1 (min ONE (NumPrimal.erf 0)))

theorem NumPrimal.c0_eq : NumPrimal.c0 = -8415352336624928 := by decide +kernel

theorem NumPrimal.strideOf_pos (step : Fx) : 1 ≤ strideOf step := le_max_left _ _

theorem log2_clamp_nonpos (v : Fx) : log2 (max 1 (min ONE v)) ≤ 0 :=
  log2_nonpos (max_le (le_of_lt (by decide)) (min_le_left _ _))

theorem NumPrimal.step_le (total : Fx) (w : ℕ) (v : Fx) :
    (pure (ForInStep.yield (total + (w : ℤ) * log2 (max 1 (min ONE v)))) : Id (ForInStep Fx)).run.value
      ≤ total := by
  show total + (w : ℤ) * log2 (max 1 (min ONE v)) ≤ total
  have := log2_clamp_nonpos v
  have : (w : ℤ) * log2 (max 1 (min ONE v)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) this
  linarith

theorem NumPrimal.profile_nonpos (k : ℕ) (first step : Fx) (mitm : Bool) :
    profile k first step mitm ≤ 0 := by
  unfold profile
  simp only [Id.run_bind]
  apply forIn_inv (β := Fx) (I := (· ≤ 0))
  · exact le_rfl
  · intro j _ total ht
    split_ifs <;> first | exact ht | exact (step_le _ _ _).trans ht

theorem Fx.mul_zero_left (a : Fx) : mul 0 a = 0 := by simp [mul]

theorem Fx.div_zero_left (a : Fx) : div 0 a = 0 := by simp [div]

theorem NumPrimal.c0_neg : NumPrimal.c0 < 0 := by rw [c0_eq]; decide

/-- Far down the profile, each coordinate contributes `c0`. -/
theorem NumPrimal.profile_tail (k : ℕ) (first step : Fx) (hstep : 0 ≤ step) (jstar : ℕ)
    (hj : first + 55 * ONE ≤ step * ((jstar * strideOf step : ℕ) : ℤ)) :
    profile k first step false ≤ c0 * max 0 ((k : ℤ) - (jstar * strideOf step : ℕ)) := by
  have hs := strideOf_pos step
  set s := strideOf step with hsdef
  have hc0 := c0_neg
  unfold profile
  simp only [Id.run_bind, Id.run_pure, ← hsdef]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  set J := (k + s - 1) / s with hJ
  have hJs : k ≤ J * s := by
    have h1 := Nat.div_add_mod (k + s - 1) s
    have h2 := Nat.mod_lt (k + s - 1) (show 0 < s by omega)
    rw [← hJ, mul_comm] at h1
    omega
  have e : (k : ℤ) - ((jstar * s : ℕ) : ℤ) = ((min k ((0 + J) * s) : ℕ) : ℤ) - ((jstar * s : ℕ) : ℤ) := by
    rw [zero_add, min_eq_left hJs]
  rw [e]
  refine forIn_range'_ind 0 J (0 : Fx) _
    (fun j (total : Fx) => total ≤ c0 * max 0 ((min k (j * s) : ℕ) - ((jstar * s : ℕ) : ℤ))) ?_ ?_
  · have : ((min k (0 * s) : ℕ) : ℤ) - ((jstar * s : ℕ) : ℤ) ≤ 0 := by simp; positivity
    show (0 : Fx) ≤ _
    rw [max_eq_left this, mul_zero]
  · intro i _ hi total ht
    have his : i * s < k := by
      have h1 : (i + 1) * s ≤ J * s := Nat.mul_le_mul_right _ (by omega)
      have h2 : J * s ≤ k + s - 1 := Nat.div_mul_le_self _ _
      have h3 : (i + 1) * s = i * s + s := by ring
      omega
    by_cases hij : i < jstar
    · -- before the tail: the term is at most `0`, and the bound is `0`
      have hm : ((min k ((i + 1) * s) : ℕ) : ℤ) - ((jstar * s : ℕ) : ℤ) ≤ 0 := by
        have h' : min k ((i + 1) * s) ≤ jstar * s :=
          (min_le_right _ _).trans (Nat.mul_le_mul_right _ hij)
        have := (Nat.cast_le (α := ℤ)).mpr h'
        linarith
      have h0 : total ≤ 0 := ht.trans (mul_nonpos_of_nonpos_of_nonneg (le_of_lt hc0) (le_max_left _ _))
      split_ifs
      all_goals first
        | (refine ⟨_, rfl, ?_⟩; rw [max_eq_left hm, mul_zero]; exact h0)
        | (refine ⟨_, rfl, ?_⟩; rw [max_eq_left hm, mul_zero]
           exact (step_le _ _ _).trans h0)
    · -- in the tail: the coordinate length underflows
      push Not at hij
      have hl : first - step * ((i * s : ℕ) : ℤ) - step * ((min (k - i * s) s - 1 : ℕ) : ℤ) / 2 ≤
          -55 * ONE := by
        have h1 : step * ((jstar * s : ℕ) : ℤ) ≤ step * ((i * s : ℕ) : ℤ) :=
          Int.mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.mul_le_mul_right _ hij) hstep
        have h2 : 0 ≤ step * ((min (k - i * s) s - 1 : ℕ) : ℤ) / 2 :=
          Int.ediv_nonneg (mul_nonneg hstep (by positivity)) (by norm_num)
        linarith
      have hx := exp2_eq_zero hl
      have hk : ¬ ((0 : Fx) ≥ ofInt (k : ℤ)) := by
        unfold ofInt; have := ONE_pos; push Not
        exact mul_pos (by exact_mod_cast (show 0 < k by omega)) this
      have h9 : ¬ ((0 : Fx) ≥ 9 * ONE) := by decide
      have hlt : first - step * ((i * s : ℕ) : ℤ) - step * ((min (k - i * s) s - 1 : ℕ) : ℤ) / 2 <
          (if false = true then 48 else 4) * ONE := lt_of_le_of_lt hl (by decide)
      simp only [hlt, ↓reduceIte]
      simp only [hx, Bool.false_eq_true, ite_false, Int.zero_ediv, Fx.mul_zero_left, hk, h9,
        decide_false, Bool.or_false, Fx.div_zero_left, Int.zero_ediv, add_zero]
      refine ⟨_, rfl, ?_⟩
      show total + ((min (k - i * s) s : ℕ) : ℤ) * c0 ≤ _
      have e1 : ((min k ((i + 1) * s) : ℕ) : ℤ) = ((i * s : ℕ) : ℤ) + ((min (k - i * s) s : ℕ) : ℤ) := by
        rw [add_mul, one_mul]; push_cast; omega
      have e2 : ((min k (i * s) : ℕ) : ℤ) = ((i * s : ℕ) : ℤ) := by
        rw [min_eq_right (le_of_lt his)]
      have hpos : (0 : ℤ) ≤ ((i * s : ℕ) : ℤ) - ((jstar * s : ℕ) : ℤ) := by
        have := Nat.mul_le_mul_right s hij; push_cast; omega
      rw [e2, max_eq_right hpos] at ht
      have hw : (0 : ℤ) ≤ ((min (k - i * s) s : ℕ) : ℤ) := by positivity
      rw [e1, max_eq_right (by linarith)]
      nlinarith

end SigabaNeo.Lattices.Estimator
