import SigabaNeoStd.Lattices.Estimator.Bound.RedLB

/-!
# Lower bounds for exhaustive search and MITM

* `Guess.exhaustiveCost_eq_none`: with a bounded secret of width at least 2 in dimension
  `n ≥ 10050`, the search space has more than `2^10049` points, so exhaustive search exceeds the
  estimator's `2^10000` cap (`Cost.sanity_check`) and is infinite. The search space itself is never
  computed.
* `Guess.mitmCost_eq`: at `q = 2^e` above the error width, `mitm` is `mitmCostW p true 0`, which
  does not compute `q`.
-/

namespace SigabaNeo.Lattices.Estimator

open Fx NumMisc

theorem Fx.log2_ge_neg (x : Fx) : -((P : ℤ) * ONE) ≤ log2 x := by
  unfold log2; have := log2Nat_nonneg x.toNat; linarith

theorem Fx.le_ceil_mul (a : Fx) : a ≤ ceil a * ONE := by
  unfold ceil
  rw [Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt ONE_pos)]
  have := Int.ediv_mul_le (-a) (ne_of_gt ONE_pos)
  linarith

/-- The tail of exhaustive search after the search space (`size` bits) is known. -/
theorem Guess.exhaustive_jp_none (p : LWEParams) (prob size : Fx) (hs : 10049 * ONE ≤ size) :
    (let s := mul PI p.Xe.stddev / (p.q : ℤ)
     let exponent := 4 * mul s s
     do
       guard (exponent ≤ 10000 * LN2)
       let m : Fx := 8 * mul (exp exponent) (mul size LN2 - ln (-(ln prob)))
       let bits : ℤ := ONE + size + log2 m
       guard ((p.mGe (ceil m).toNat && decide (bits ≤ 10000 * ONE)) = true)
       pure bits : Option ℤ) = none := by
  dsimp only
  generalize 4 * mul (mul PI p.Xe.stddev / (p.q : ℤ)) (mul PI p.Xe.stddev / (p.q : ℤ)) = ex
  have h1 := Fx.log2_ge_neg (8 * mul (exp ex) (mul size LN2 - ln (-(ln prob))))
  have h2 : ¬ (ONE + size + log2 (8 * mul (exp ex) (mul size LN2 - ln (-(ln prob)))) ≤
      10000 * ONE) := by
    have : (P : ℤ) = 48 := rfl
    have := ONE_pos
    nlinarith
  by_cases h : ex ≤ 10000 * LN2 <;> simp [h, h2, guard]

theorem Guess.exhaustiveCost_eq_none {p : LWEParams} (hk : ∀ s, p.normalize.Xs.kind ≠ .gauss s)
    (hw : 2 ≤ floor (width p.normalize.Xs)) (hn : 10050 ≤ p.normalize.n) :
    Guess.exhaustiveCost p = none := by
  have hprob : ONE / 2 ≤ Fx.sqrt (ofRat 99 100) := by decide +kernel
  set n := p.normalize.n with hn'
  set w := floor (width p.normalize.Xs)
  have hsize : 10049 * ONE ≤ log2Nat (ceil (Fx.sqrt (ofRat 99 100) * w ^ n)).toNat := by
    have hpow : (2 : ℤ) ^ n ≤ w ^ n := pow_le_pow_left₀ (by norm_num) hw n
    have hx : (ONE / 2) * 2 ^ n ≤ Fx.sqrt (ofRat 99 100) * w ^ n :=
      mul_le_mul hprob hpow (by positivity) (le_trans (by decide) hprob)
    have hc := Fx.le_ceil_mul (Fx.sqrt (ofRat 99 100) * w ^ n)
    have hONE : ONE = 2 * (ONE / 2) := by decide
    have hc2 : (2 : ℤ) ^ (n - 1) ≤ ceil (Fx.sqrt (ofRat 99 100) * w ^ n) := by
      have h2n : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hO : ONE = 2 * (ONE / 2) := by decide
      have hpos : (0 : ℤ) < ONE / 2 := by decide
      set c := ceil (Fx.sqrt (ofRat 99 100) * w ^ n)
      set H := ONE / 2
      have key : H * (2 * 2 ^ (n - 1)) ≤ c * (2 * H) := by
        rw [← h2n, ← hO]; exact hx.trans hc
      have : 2 ^ (n - 1) * H ≤ c * H := by nlinarith
      exact le_of_mul_le_mul_right this hpos
    have hN : 2 ^ (n - 1) ≤ (ceil (Fx.sqrt (ofRat 99 100) * w ^ n)).toNat := by
      have h' : ((2 ^ (n - 1) : ℕ) : ℤ) ≤ ceil (Fx.sqrt (ofRat 99 100) * w ^ n) := by
        push_cast; exact hc2
      omega
    have := log2Nat_mono hN
    rw [log2Nat_two_pow] at this
    have : ((n - 1 : ℕ) : ℤ) * ONE ≥ 10049 * ONE :=
      Int.mul_le_mul_of_nonneg_right (by omega) (le_of_lt ONE_pos)
    linarith
  unfold Guess.exhaustiveCost
  dsimp only
  split
  · rename_i s hs; exact absurd hs (hk s)
  · exact Guess.exhaustive_jp_none _ _ _ hsize

theorem Guess.mitmCost_eq {p : LWEParams} {e : ℕ} (hq : p.q = 2 ^ e)
    (h0 : 0 ≤ width p.normalize.Xe) (h1 : width p.normalize.Xe < 2 ^ e) :
    Guess.mitmCost p = Guess.mitmCostW p.normalize true 0 := by
  unfold Guess.mitmCost
  simp only [LWEParams.normalize_q, hq]
  congr 1
  · simp only [decide_eq_true_eq]; unfold ofInt; push_cast
    have := ONE_pos; nlinarith
  · push_cast; exact Int.ediv_eq_zero_of_lt h0 h1

end SigabaNeo.Lattices.Estimator
