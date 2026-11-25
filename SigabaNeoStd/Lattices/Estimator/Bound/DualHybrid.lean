import SigabaNeoStd.Lattices.Estimator.Bound.Guess

/-!
# A lower bound for the dual hybrid

A candidate of `DualHybrid.cost` (modulus, `k` enumerated and `t` FFT coordinates, block size `b`)
costs at least its guessing part, which is at least `k + t` bits, and at least the reduction cost
`redLB b`. It is infinite when the dual vectors are too long (`v > 10`). With secret and error of
the same law, `v` only grows with the lattice dimension `d = 2n − k − t`, so when `k + t < kb` it
is at least its value `vLow` at `d₀ = 2n − kb + 1`. Hence: if every block size `b < maxBeta` has
`redLB b ≥ K` or `vLow b > 10`, and `kb · 2^P ≥ K`, the dual hybrid costs at least `K`.
-/

namespace SigabaNeo.Lattices.Estimator

open Fx Reduction DualHybrid

/-- `v` at the smallest lattice dimension `d₀ = 2n − kb + 1` (secret and error of the same law). -/
def DualHybrid.vLow (n : ℕ) (lq le : Fx) (kb b : ℕ) : Fx :=
  let d₀ := 2 * n - kb + 1
  le + (-((n : ℤ) * lq)) / (d₀ : ℤ) + log2 (ofRat 4 3) / 2 + (log2Nat b - log2TwoPiE) / 2 +
    ((d₀ : ℤ) - b) * log2Delta b

/-- The per-block-size check of the dual hybrid. -/
def DualHybrid.check (K : Fx) (n : ℕ) (lq le : Fx) (kb b : ℕ) : Bool :=
  decide (K ≤ redLB b) || (decide (0 ≤ log2Delta b) && decide (10 * ONE < vLow n lq le kb b))

theorem DualHybrid.candidate_ge {K : Fx} {d k t b : ℕ} {base extra fft coeff enumCost : Fx}
    (hb : 20 ≤ b) (hextra : log2 LN2 ≤ extra) (hfft : t ≠ 0 → ((t : ℤ) + 1) * ONE ≤ fft)
    (hcoeff : 0 ≤ coeff) (henum : ONE ≤ enumCost)
    (hcase : K ≤ ((k : ℤ) + t) * ONE ∨ K ≤ redLB b ∨
      10 * ONE < base + (log2Nat b - log2TwoPiE) / 2 + ((d : ℤ) - b) * log2Delta b) :
    CostGe K (DualHybrid.candidate d k t base extra fft coeff enumCost b) := by
  intro x hx
  unfold DualHybrid.candidate at hx
  simp only [] at hx
  split at hx
  · exact absurd hx (by simp)
  rename_i hv
  obtain ⟨r, hr, hx⟩ := Option.bind_eq_some_iff.mp hx
  have hx := Option.some.inj hx
  subst hx
  have hT : (0 : ℤ) ≤ log2Nat 640 + log2 LN2 := by decide +kernel
  set count := mul (4 * mul PI PI) (mul LOG2E (exp2 (2 * (base + (log2Nat b - log2TwoPiE) / 2 +
    ((d : ℤ) - b) * log2Delta b)))) + extra
  have hc0 : 0 ≤ mul (4 * mul PI PI) (mul LOG2E (exp2 (2 * (base + (log2Nat b - log2TwoPiE) / 2 +
      ((d : ℤ) - b) * log2Delta b)))) := by
    unfold mul
    have h1 : (0 : ℤ) ≤ 4 * Int.fdiv (PI * PI) ONE := by decide
    have h2 := exp2_nonneg (2 * (base + (log2Nat b - log2TwoPiE) / 2 + ((d : ℤ) - b) * log2Delta b))
    have h3 : (0 : ℤ) ≤ LOG2E := by decide
    exact Int.fdiv_nonneg (mul_nonneg h1 (Int.fdiv_nonneg (mul_nonneg h3 h2) (le_of_lt ONE_pos)))
      (le_of_lt ONE_pos)
  have htable : 0 ≤ log2Nat 640 + count := by linarith
  have hguess : ((k : ℤ) + t) * ONE ≤ coeff + ↑k * enumCost +
      (if (t == 0) = true then log2Nat 640 + count else log2Add (log2Nat 640 + count) fft) := by
    have hk : (k : ℤ) * ONE ≤ k * enumCost := Int.mul_le_mul_of_nonneg_left henum (by positivity)
    split
    · rename_i ht; simp at ht; subst ht; push_cast; linarith
    · rename_i ht; simp at ht
      have := (hfft ht).trans (le_log2Add_right (log2Nat 640 + count) fft)
      have : (t : ℤ) * ONE ≤ ((t : ℤ) + 1) * ONE := by have := ONE_pos; nlinarith
      nlinarith
  rcases hcase with h | h | h
  · exact h.trans (hguess.trans (le_log2Add_right _ _))
  · exact h.trans ((redLB_le hb _).trans ((NumDual.shortBits_ge hr).trans (le_log2Add_left _ _)))
  · exact absurd h (not_lt.mpr (not_lt.mp hv))

end SigabaNeo.Lattices.Estimator

namespace SigabaNeo.Lattices.Estimator

open Fx Reduction DualHybrid

theorem Int.ediv_le_ediv_of_nonpos {a : ℤ} {c c' : ℤ} (ha : a ≤ 0) (hc : 0 < c) (hcc : c ≤ c') :
    a / c ≤ a / c' := by
  rw [Int.le_ediv_iff_mul_le (by omega)]
  have h1 : a / c ≤ 0 := Int.ediv_nonpos_of_nonpos_of_neg ha hc
  have h2 := Int.ediv_mul_le a (ne_of_gt hc)
  nlinarith

/-- The `base` term of the dual hybrid only grows with the dimension. -/
theorem DualHybrid.base_ge (n lat d₀ : ℕ) (le lq : ℤ) (hlq : 0 ≤ lq) (hd₀ : 0 < d₀)
    (hd : d₀ ≤ lat + n) :
    le + (-((n : ℤ) * lq)) / (d₀ : ℤ) ≤ ((n : ℤ) * le + (lat : ℤ) * (le + lq)) / ((lat + n : ℕ) : ℤ) - lq := by
  have hD : (0 : ℤ) < ((lat + n : ℕ) : ℤ) := by omega
  have e1 : (n : ℤ) * le + (lat : ℤ) * (le + lq) =
      (-((n : ℤ) * lq)) + (le + lq) * ((lat + n : ℕ) : ℤ) := by push_cast; ring
  rw [e1, Int.add_mul_ediv_right _ _ (ne_of_gt hD)]
  have := Int.ediv_le_ediv_of_nonpos (a := -((n : ℤ) * lq)) (by nlinarith) (by omega : (0 : ℤ) < d₀)
    (show (d₀ : ℤ) ≤ ((lat + n : ℕ) : ℤ) by omega)
  linarith

theorem DualHybrid.cost_ge {p : LWEParams} {K : Fx} {kb : ℕ}
    (hls : log2 p.normalize.Xs.stddev = log2 p.normalize.Xe.stddev)
    (hcoeff : 0 ≤ coeffOf p.normalize.Xs.stddev) (henum : ONE ≤ enumCostOf p.normalize.Xs.stddev)
    (hh : 0 ≤ hOf p.normalize.Xs.stddev) (halpha : 0 ≤ alphaOf p.normalize.Xs.stddev)
    (hK : K ≤ (kb : ℤ) * ONE) (hkb : kb ≤ p.normalize.n)
    (hb : ∀ b, 40 ≤ b → b < maxBeta → DualHybrid.check K p.normalize.n (log2Nat p.normalize.q)
      (log2 p.normalize.Xe.stddev) kb b = true) :
    CostGe K (DualHybrid.cost p) := by
  unfold DualHybrid.cost
  simp only []
  split
  · simp
  split
  · simp
  simp only [Id.run_bind]
  apply forIn_inv (β := Cost) (I := CostGe K)
  · simp
  intro modulus hmod best hbest
  simp only [Std.Legacy.Range.size, List.mem_range'_1] at hmod
  have hlp : ONE ≤ log2Nat modulus := by
    have h1 := log2Nat_ge modulus
    have h2 : 1 ≤ Nat.log2 modulus := by
      rw [Nat.log2_eq_log_two]; exact Nat.le_log_of_pow_le (by norm_num) (by omega)
    have : (ONE : ℤ) ≤ (Nat.log2 modulus : ℤ) * ONE := by
      have := ONE_pos; nlinarith [show (1 : ℤ) ≤ Nat.log2 modulus by exact_mod_cast h2]
    linarith
  simp only [Id.run_bind]
  generalize hr : (forIn (m := Id) (_ : Std.Legacy.Range) ((none : Cost), (0 : ℕ)) _ :
    Id (Cost × ℕ)) = r
  have hr1 : CostGe K r.1 := by
    rw [← hr]
    apply forIn_inv (β := Cost × ℕ) (I := fun s => CostGe K s.1)
    · simp
    intro k _ s hs
    simp only [Id.run_bind]
    generalize hr2 : (forIn (m := Id) (_ : Std.Legacy.Range) ((none : Cost), (0 : ℕ)) _ :
      Id (Cost × ℕ)) = r2
    have hr21 : CostGe K r2.1 := by
      rw [← hr2]
      apply forIn_inv (β := Cost × ℕ) (I := fun s => CostGe K s.1)
      · simp
      intro t _ s' hs'
      split
      · exact hs'
      show CostGe K (DualHybrid.localMin _ _)
      apply DualHybrid.localMin_ge
      intro b hb1 hb2
      have hbmax : b < maxBeta := lt_of_lt_of_le hb2 (max_le (by decide) (min_le_left _ _))
      apply DualHybrid.candidate_ge (by omega)
      · -- the extra term
        have e1 : 0 ≤ mul ((t : ℤ) * alphaOf p.normalize.Xs.stddev / (3 * modulus * modulus)) LOG2E := by
          unfold mul
          exact Int.fdiv_nonneg (mul_nonneg (Int.ediv_nonneg (mul_nonneg (by positivity) halpha)
            (by positivity)) (by decide)) (le_of_lt ONE_pos)
        have e2 : 0 ≤ mul ((t : ℤ) * log2Nat modulus) LN2 := by
          unfold mul
          exact Int.fdiv_nonneg (mul_nonneg (mul_nonneg (by positivity) (log2Nat_nonneg _))
            (by decide)) (le_of_lt ONE_pos)
        have e3 : log2 LN2 ≤ log2 ((k : ℤ) * hOf p.normalize.Xs.stddev +
            mul ((t : ℤ) * log2Nat modulus) LN2 + LN2) :=
          log2_mono (by have := mul_nonneg (show (0 : ℤ) ≤ k by positivity) hh; linarith)
        linarith
      · intro ht
        have := log2Nat_nonneg t
        have : ((t + 1 : ℕ) : ℤ) * ONE ≤ ((t + 1 : ℕ) : ℤ) * log2Nat modulus :=
          Int.mul_le_mul_of_nonneg_left hlp (by positivity)
        push_cast at this ⊢
        have : (0 : ℤ) ≤ 10 * ONE := by decide
        linarith
      · exact hcoeff
      · exact henum
      · by_cases hkt : kb ≤ k + t
        · left
          refine hK.trans (Int.mul_le_mul_of_nonneg_right ?_ (le_of_lt ONE_pos))
          exact_mod_cast hkt
        right
        have hc := hb b (by omega) hbmax
        unfold DualHybrid.check at hc
        rcases Bool.or_eq_true_iff.mp hc with hc | hc
        · left; exact of_decide_eq_true hc
        right
        obtain ⟨hδ, hv⟩ := Bool.and_eq_true_iff.mp hc
        have hδ := of_decide_eq_true hδ
        have hv := of_decide_eq_true hv
        unfold DualHybrid.vLow at hv
        refine lt_of_lt_of_le hv ?_
        have hd : 2 * p.normalize.n - kb + 1 ≤ p.normalize.n - k - t + p.normalize.n := by omega
        have hbase := DualHybrid.base_ge p.normalize.n (p.normalize.n - k - t)
          (2 * p.normalize.n - kb + 1) (log2 p.normalize.Xe.stddev) (log2Nat p.normalize.q)
          (log2Nat_nonneg _) (by omega) hd
        rw [hls]
        have hdb : (((2 * p.normalize.n - kb + 1 : ℕ) : ℤ) - b) * log2Delta b ≤
            (((p.normalize.n - k - t + p.normalize.n : ℕ) : ℤ) - b) * log2Delta b :=
          Int.mul_le_mul_of_nonneg_right (by omega) hδ
        push_cast at hbase hdb ⊢
        linarith
    split
    · exact hs
    · exact hr21
  split
  · exact hbest
  split
  · exact hr1
  · exact hr1

end SigabaNeo.Lattices.Estimator
