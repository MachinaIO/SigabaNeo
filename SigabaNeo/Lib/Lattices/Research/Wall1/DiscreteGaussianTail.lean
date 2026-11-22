module

public import SigabaNeo.Lib.Lattices.Research.Wall1.KleinFactorization

/-!
# Truncation of a shifted integer Gaussian (Part 141, Lemma 6)

The two rays outside a real interval start at possibly different fractional offsets.
Each ray is bounded by a geometric series, uniformly in the centre.
-/

@[expose] public section

namespace SigabaNeo.Wall1

open Real

noncomputable section

/-- The Gaussian on the integers with centre c, using the sign convention of theta1. -/
def dg1 (s c : ℝ) (k : ℤ) : ℝ := gs s (k - c) / theta1 s (-c)

private theorem gs_shift_hasSum {s : ℝ} (hs : 0 < s) (c : ℝ) :
    HasSum (fun k : ℤ ↦ gs s (k-c)) (theta1 s (-c)) := by
  simpa [thetaQ_eq one_ne_zero, sub_eq_add_neg] using hasSum_coset hs one_ne_zero (-c)

private theorem theta_shift_pos {s : ℝ} (hs : 0 < s) (c : ℝ) : 0 < theta1 s (-c) := by
  simpa [thetaQ_eq one_ne_zero] using thetaQ_pos hs one_ne_zero (-c)

theorem dg1_hasSum {s : ℝ} (hs : 0 < s) (c : ℝ) : HasSum (dg1 s c) 1 := by
  unfold dg1
  simpa [(theta_shift_pos hs c).ne'] using (gs_shift_hasSum hs c).div_const (theta1 s (-c))

theorem dg1_nonneg {s : ℝ} (hs : 0 < s) (c : ℝ) (k : ℤ) : 0 ≤ dg1 s c k :=
  div_nonneg (gs_pos _ _).le (theta_shift_pos hs c).le

private def rightWeight (s c R : ℝ) (k : ℤ) : ℝ := if R < k - c then gs s (k-c) else 0

private theorem right_summable {s : ℝ} (hs : 0 < s) (c R : ℝ) :
    Summable (rightWeight s c R) :=
  Summable.of_nonneg_of_le
    (fun k ↦ by unfold rightWeight; split_ifs <;> first | exact (gs_pos _ _).le | rfl)
    (fun k ↦ by unfold rightWeight; split_ifs <;> first | exact (gs_pos _ _).le | rfl)
    (gs_shift_hasSum hs c).summable

private theorem right_tail {s R : ℝ} (hs : 0 < s) (hR : 0 < R) (c : ℝ) :
    ∑' k, rightWeight s c R k ≤ gs s R / (1 - exp (-2 * π * R / s^2)) := by
  let j : ℤ := ⌊c+R⌋ + 1
  let f (n : ℕ) := j + (n : ℤ)
  have hf : Function.Injective f := fun a b h ↦ by simpa [f] using h
  have hsupport : Function.support (rightWeight s c R) ⊆ Set.range f := by
    intro k hk
    have h : R < k - c := by
      by_contra hn
      exact hk (by simp [rightWeight, hn])
    have hk' : ⌊c+R⌋ < k := Int.floor_lt.mpr (by linarith)
    exact ⟨(k-j).toNat, by dsimp [f,j] at *; omega⟩
  rw [← hf.tsum_eq hsupport]
  have hj : c+R < (j : ℝ) := by simp [j]
  let r := exp (-2 * π * R / s^2)
  have hr : r < 1 := Real.exp_lt_one_iff.mpr (by
    have hp : 0 < 2 * π * R / s^2 := by positivity
    simpa only [neg_mul, neg_div] using neg_lt_zero.mpr hp)
  have hgeom := (hasSum_geometric_of_lt_one (Real.exp_pos _).le hr).mul_left (gs s R)
  have hpt (n : ℕ) : rightWeight s c R (f n) ≤ gs s R * r^n := by
    have hbase : R + n ≤ (f n : ℝ) - c := by simp [f]; linarith
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hsq := sq_le_sq' (a := R + n) (b := (f n : ℝ) - c) (by linarith) hbase
    have hx : R < (f n : ℝ) - c := by simp [f]; linarith
    simp only [rightWeight, hx, ite_true]
    rw [gs, gs, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    apply (le_of_sub_nonneg ?_)
    have h : 0 ≤ ((f n : ℝ) - c)^2 - R^2 - 2*R*n := by nlinarith [sq_nonneg (n : ℝ)]
    convert mul_nonneg (show 0 ≤ π / s^2 by positivity) h using 1
    ring
  have hsum := (right_summable hs c R).comp_injective hf
  exact (hsum.tsum_le_tsum hpt hgeom.summable).trans_eq (by rw [hgeom.tsum_eq]; rfl)

/-- Geometric bound for the probability outside the closed interval [c−R,c+R].
Any positive lower bound on the normalizer may be used. -/
theorem dg1_tail_le_of_normalizer {s R b : ℝ} (hs : 0 < s) (hR : 0 < R) (c : ℝ)
    (hb0 : 0 < b) (hlo : b ≤ theta1 s (-c)) :
    (∑' k : ℤ, if R < |(k : ℝ) - c| then dg1 s c k else 0) ≤
      2 * gs s R / ((1 - exp (-2 * π * R / s^2)) * b) := by
  let e := Equiv.neg ℤ
  have he (k : ℤ) : e k = -k := rfl
  have hspl (k : ℤ) : (if R < |(k : ℝ) - c| then dg1 s c k else 0) =
      (rightWeight s c R k + rightWeight s (-c) R (e k)) / theta1 s (-c) := by
    have hsym : gs s (-(k : ℝ) - -c) = gs s (k-c) := by unfold gs; ring_nf
    simp only [he, rightWeight, Int.cast_neg, hsym, dg1, lt_abs]
    rw [show -(k : ℝ) - -c = -(k-c) by ring]
    simp only [neg_sub]
    by_cases h : R < (k : ℝ) - c
    · have hn : ¬R < c - (k : ℝ) := by linarith
      simp [h, hn]
    · by_cases hn : R < c - (k : ℝ) <;> simp [h, hn]
  have hrefl : Summable (fun k ↦ rightWeight s (-c) R (e k)) :=
    e.summable_iff.mpr (right_summable hs (-c) R)
  rw [tsum_congr hspl, tsum_div_const,
    (right_summable hs c R).tsum_add hrefl, e.tsum_eq]
  have hb := add_le_add (right_tail hs hR c) (right_tail hs hR (-c))
  have hg : 0 < 1 - exp (-2 * π * R / s^2) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by
      have hp : 0 < 2 * π * R / s^2 := by positivity
      simpa only [neg_mul, neg_div] using neg_lt_zero.mpr hp))
  have hquot := div_nonneg (gs_pos s R).le hg.le
  calc
    _ ≤ (gs s R / (1 - exp (-2 * π * R / s^2)) +
        gs s R / (1 - exp (-2 * π * R / s^2))) / b :=
      div_le_div₀ (add_nonneg hquot hquot) hb hb0 hlo
    _ = _ := by rw [← add_div, div_div, ← two_mul]

/-- The uniform-in-c bound obtained from the one-dimensional theta estimate. -/
theorem dg1_tail_le {s R : ℝ} (hs : 0 < s) (hR : 0 < R) (hτ : tau s < 1) (c : ℝ) :
    (∑' k : ℤ, if R < |(k : ℝ) - c| then dg1 s c k else 0) ≤
      2 * gs s R / ((1 - exp (-2 * π * R / s^2)) * (s * (1 - tau s))) :=
  dg1_tail_le_of_normalizer hs hR c (mul_pos hs (sub_pos.mpr hτ)) (theta1_mem hs (-c)).1

/-- An explicit bound for every positive scale. Even below smoothing, the nearest integer
contributes at least the Gaussian weight at distance 1/2. -/
theorem dg1_tail_le_all_scales {s R : ℝ} (hs : 0 < s) (hR : 0 < R) (c : ℝ) :
    (∑' k : ℤ, if R < |(k : ℝ) - c| then dg1 s c k else 0) ≤
      2 * gs s R / ((1 - exp (-2 * π * R / s^2)) * gs s (1/2)) := by
  apply dg1_tail_le_of_normalizer hs hR c (gs_pos _ _)
  let k : ℤ := ⌊c + 1/2⌋
  have hlow := Int.lt_floor_add_one (c + 1/2)
  have hhigh := Int.floor_le (c + 1/2)
  have hd : ((k : ℝ)-c)^2 ≤ (1/2 : ℝ)^2 :=
    sq_le_sq' (by dsimp [k]; linarith) (by dsimp [k]; linarith)
  have hweight : gs s (1/2) ≤ gs s (k-c) := by
    unfold gs
    exact exp_le_exp.mpr (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonpos_left hd (neg_nonpos.mpr pi_pos.le)) (sq_nonneg s))
  have hm := gs_shift_hasSum hs c
  exact hweight.trans ((hm.summable.le_tsum k (fun i _ ↦ (gs_pos _ _).le)).trans_eq hm.tsum_eq)

end
end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.dg1_hasSum
#print axioms SigabaNeo.Wall1.dg1_nonneg
#print axioms SigabaNeo.Wall1.dg1_tail_le_of_normalizer
#print axioms SigabaNeo.Wall1.dg1_tail_le
#print axioms SigabaNeo.Wall1.dg1_tail_le_all_scales
