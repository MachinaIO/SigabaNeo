import SigabaNeo.Lib.Lattices.Estimator.Bound.Cbd

/-!
# Lower bounds at a centered binomial secret and error, any large modulus, a range of samples

`Bound/Cbd.lean` certifies `kb ≤ estimatorBits` at `q = 2^e` and one sample count. Here the
modulus is any `q ≥ 2^1024` given by its fixed-point logarithm `lq` (`log2Nat q = lq` and
`log₂ (q · 2^P) = lq + P`, e.g. `q = 2^e − 1`: `log2Nat_two_pow_sub_one`), and the bound holds at
**every** sample count `M` in a range `[M₀, M₁]`:

* `cbdPq n q M`: dimension `n`, modulus `q`, `CBD(16)` secret and error, `M` samples.
* `cbdCheckQ n lq M₀ kb W b`: the check of block size `b`. It never reads the sample count beyond
  `M₀`: uSVP passes by the reduction bound or because `solveForD` has no solution (which does not
  depend on the sample count, `Usvp.solveForD_isNone_m`), the dual by the reduction bound or at
  the candidate whose optimal sample count `Dual.optOf` is at most `M₀` (then equal at all
  `M ≥ M₀`, `Dual.candidate_eq_of_opt`).
* `cbdFactsQ n kb W ZA K₀ R`: the closed facts; MITM is evaluated without a sample bound
  (`Guess.mitmCostW_of_some`: a bound on the unbounded instance bounds every instance).
* **`cbd16q_estimatorBits_ge`**: `kb ≤ estimatorBits (cbdPq n q M)` for `M₀ ≤ M` with
  `maxBeta + 1 + W + kb + 22 ≤ M + n` and `56 M ≤ (n − ZA) · R^6`.

`W` (the primal attacks' margin, `90` in `Bound/Cbd.lean`), and the Arora–Ge constants `ZA` (the
guessing depth, `600` there), `K₀` (`50`) and `R` (`2^20`, which needs `n ≥ 102 (R + 1) + ZA`) are
parameters (`cbd_single_geR`).
-/

namespace SigabaNeo.Lattices.Estimator

open Fx Reduction NumMisc

/-! ### `log₂` of `2^e − 1` -/

theorem Fx.log2_shift (v k : ℕ) (hv : 0 < v) :
    Nat.log2 (v * 2 ^ k) = Nat.log2 v + k := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, Nat.log_mul_base (by norm_num) (by positivity), ih]; ring

theorem Fx.log2Nat_mul_two_pow (v k : ℕ) (hv : 0 < v) :
    log2Nat (v * 2 ^ k) = log2Nat v + (k : ℤ) * ONE := by
  rw [log2Nat_eq', log2Nat_eq', Fx.log2_shift v k hv]
  have : ((v * 2 ^ k) <<< K) >>> (Nat.log2 v + k) = (v <<< K) >>> Nat.log2 v := by
    simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, pow_add]
    rw [show v * 2 ^ k * 2 ^ K = (v * 2 ^ K) * 2 ^ k by ring,
      Nat.mul_div_mul_right _ _ (by positivity)]
  rw [this]; push_cast; ring

/-- `log₂` of an integer, as a fixed-point number, is `log2Nat`. -/
theorem Fx.log2_ofInt (v : ℕ) (hv : 0 < v) : log2 (ofInt (v : ℤ)) = log2Nat v := by
  unfold log2 ofInt
  rw [ONE_eq, show ((v : ℤ) * ((2 ^ P : ℕ) : ℤ)).toNat = v * 2 ^ P by
    rw [← Nat.cast_mul, Int.toNat_natCast], Fx.log2Nat_mul_two_pow v P hv, ← ONE_eq]
  ring

theorem Fx.frac_top : frac (2 ^ (K + 1) - 1) = 2 ^ P - 1 := by decide +kernel

/-- `log2Nat (2^e − 1) = e · 2^P − 1` for `e > K` (the mantissa is `2^(K+1) − 1`). -/
theorem Fx.log2Nat_two_pow_sub_one {e : ℕ} (he : K + 1 < e) :
    log2Nat (2 ^ e - 1) = (e : ℤ) * ONE - 1 := by
  have hpos : 0 < 2 ^ e - 1 := by
    have : 2 ≤ 2 ^ e := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hlog : Nat.log2 (2 ^ e - 1) = e - 1 := by
    rw [Nat.log2_eq_log_two]
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · have : 2 ^ (e - 1) * 2 = 2 ^ e := by rw [← pow_succ]; congr 1; omega
      have : 1 ≤ 2 ^ (e - 1) := Nat.one_le_two_pow
      omega
    · rw [show e - 1 + 1 = e by omega]; omega
  have hm : ((2 ^ e - 1) <<< K) >>> (e - 1) = 2 ^ (K + 1) - 1 := by
    simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    have h1 : 2 ^ e = 2 ^ (e - 1) * 2 := by rw [← pow_succ]; congr 1; omega
    have hK1 : 2 ^ (K + 1) = 2 ^ K * 2 := pow_succ 2 K
    have hKe : 2 ^ K ≤ 2 ^ (e - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hK0 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
    rw [h1, hK1]
    generalize 2 ^ K = A at hKe hK0 ⊢
    generalize 2 ^ (e - 1) = B at hKe hK0 ⊢
    apply Nat.div_eq_of_lt_le
    · rw [Nat.sub_mul, Nat.sub_mul, one_mul, one_mul, show A * 2 * B = B * 2 * A by ring]
      exact Nat.sub_le_sub_left hKe _
    · rw [Nat.sub_add_cancel (by nlinarith), Nat.sub_mul, one_mul,
        show A * 2 * B = B * 2 * A by ring]
      exact Nat.sub_lt (by nlinarith) (by omega)
  rw [log2Nat_eq', hlog, hm, Fx.frac_top]
  have : (1 : ℕ) ≤ 2 ^ P := Nat.one_le_two_pow
  rw [ONE_eq]; push_cast [this]; rw [Nat.cast_sub (by omega : 1 ≤ e)]; push_cast; ring

theorem Fx.log2_ofInt_two_pow_sub_one {e : ℕ} (he : K + 1 < e) :
    log2 (ofInt ((2 ^ e - 1 : ℕ) : ℤ)) = (e : ℤ) * ONE - 1 := by
  have : 0 < 2 ^ e - 1 := by
    have : 2 ≤ 2 ^ e := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [Fx.log2_ofInt _ this, Fx.log2Nat_two_pow_sub_one he]

/-! ### The modulus enters only through `log₂ q` -/

theorem Usvp.cost_eq_log2 (p : LWEParams) : Usvp.cost p = Usvp.costQ (log2 (ofInt p.q)) p := rfl

theorem Dual.cost_eq_log2 {p : LWEParams} (hq : p.q ≠ 0) :
    Dual.cost p = Dual.costQ (log2Nat p.q) false p := by
  unfold Dual.cost; congr 1; simpa using hq

theorem Bkw.cost_eq_none_ge {p : LWEParams} {e : ℕ} (hq : 2 ^ e ≤ p.q) (he : 1024 ≤ e)
    (hs : ¬ p.normalize.Xs.stddev > p.normalize.Xe.stddev) (hz : 0 ≤ zOf p.normalize)
    (herf : Bkw.erf (div (zOf p.normalize) (Fx.sqrt (2 * p.normalize.Xe.stddev))) = ONE) :
    Bkw.cost p = none := by
  have hq' : 2 ^ e ≤ p.normalize.q := by rw [LWEParams.normalize_q]; exact hq
  have hcand : ∀ {lq : Fx} {b steps : ℕ}, 0 ≤ lq → 1 ≤ b → Bkw.candidate p.normalize
      p.normalize.Xe.stddev lq b steps = none := by
    intro lq b steps hlq hb
    have htab : (2 : ℤ) ^ e ≤ (p.normalize.q : ℤ) ^ b := by
      calc (2 : ℤ) ^ e = ((2 ^ e : ℕ) : ℤ) := by push_cast; rfl
        _ ≤ (p.normalize.q : ℤ) := by exact_mod_cast hq'
        _ ≤ (p.normalize.q : ℤ) ^ b := by
          have h1 : (1 : ℤ) ≤ p.normalize.q := by
            have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
            exact_mod_cast le_trans this hq'
          calc (p.normalize.q : ℤ) = (p.normalize.q : ℤ) ^ 1 := (pow_one _).symm
            _ ≤ _ := pow_le_pow_right₀ h1 hb
    have htab1 : (1 : ℤ) ≤ (p.normalize.q : ℤ) ^ b := le_trans (one_le_pow₀ (by norm_num)) htab
    cases h : Bkw.candidate p.normalize p.normalize.Xe.stddev lq b steps with
    | none => rfl
    | some r =>
      exfalso
      unfold Bkw.candidate at h
      simp only [] at h
      obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
      rw [Bkw.finish_none (K := e) (Bkw.accum_nonneg hs ?_ ?_ (Bkw.samplesNeeded_nonneg _) ?_ rfl)
        (Bkw.samplesNeeded_nonneg _) hz herf hlq htab he] at h
      · exact absurd h (by simp)
      · exact (Nat.mul_le_mul_right b (min_le_left _ _)).trans (Nat.div_mul_le_self _ _)
      · exact (min_le_right _ _).trans ((List.countP_le_length ..).trans (by simp))
      · apply Int.ediv_nonneg _ (by norm_num)
        exact mul_nonneg (by linarith) (le_of_lt ONE_pos)
  have hjoin : ∀ budget, (NumMisc.search 2 (3 * (ceil (log2Nat p.normalize.q)).toNat)
      (fun b => (NumMisc.search 2 (max 3 (p.normalize.n / b))
        (Bkw.candidate p.normalize p.normalize.Xe.stddev (log2Nat p.normalize.q) b)
        (Bkw.smaller budget)).join) (Bkw.smaller budget)).join = none := by
    intro budget
    apply NumMisc.search_inv_range (Q := fun o => o.join = none)
    · rfl
    intro b hb _
    show (NumMisc.search 2 _ _ _).join = none
    apply NumMisc.search_inv_range (Q := fun o => o.join = none)
    · rfl
    intro steps _ _
    rw [hcand (log2Nat_nonneg _) (by omega)]; rfl
  unfold Bkw.cost
  simp only []
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size]
  rw [show (p.normalize.m.getD 0 + 2 - 0 + 1 - 1) / 1 = (p.normalize.m.getD 0 + 1) + 1 by omega,
    List.range'_succ, List.forIn_cons]
  simp [hjoin]

theorem Guess.mitmCost_eq_ge {p : LWEParams} {e : ℕ} (hq : 2 ^ e ≤ p.q)
    (h0 : 0 ≤ width p.normalize.Xe) (h1 : width p.normalize.Xe < 2 ^ e) :
    Guess.mitmCost p = Guess.mitmCostW p.normalize true 0 := by
  unfold Guess.mitmCost
  simp only [LWEParams.normalize_q]
  have hq' : ((2 ^ e : ℕ) : ℤ) ≤ (p.q : ℤ) := by exact_mod_cast hq
  push_cast at hq'
  congr 1
  · simp only [decide_eq_true_eq]; unfold ofInt
    have := ONE_pos; nlinarith
  · exact Int.ediv_eq_zero_of_lt h0 (lt_of_lt_of_le h1 hq')

/-! ### Sample counts: what the checks read -/

/-- `solveForD` reads the instance only through `n` and the error's standard deviation. -/
theorem Usvp.solveForD_congr {p p' : LWEParams} (hn : p.n = p'.n)
    (hs : p.Xe.stddev = p'.Xe.stddev) (m : Option ℕ) (β : ℕ) (x a b c : Fx) :
    Usvp.solveForD p m β x a b c = Usvp.solveForD p' m β x a b c := by
  unfold Usvp.solveForD; rw [hn, hs]

/-- Whether `solveForD` has a solution does not depend on the sample count. -/
theorem Usvp.solveForD_isNone_m (p : LWEParams) (m m' : Option ℕ) (β : ℕ) (x a b c : Fx)
    (h : Usvp.solveForD p m β x a b c = none) : Usvp.solveForD p m' β x a b c = none := by
  unfold Usvp.solveForD at *
  simp only [] at *
  split_ifs at * <;> simp_all

theorem Usvp.costGsaQ_none {l2q : Fx} {β : ℕ} {p : LWEParams} {m : Option ℕ}
    (h : Usvp.solveForD p m β (Reduction.log2Delta β) (log2 p.Xe.stddev) (log2Xi p) l2q = none) :
    Usvp.costGsaQ l2q β p m = none := by
  unfold Usvp.costGsaQ; simp only [] at *; rw [h]

/-- The optimal sample count of the dual candidate at block size `b` (`Dual.candidate`'s `opt`). -/
def Dual.optOf (n : ℕ) (c : Fx) (b : ℕ) : ℕ :=
  max 1 ((ceil (sqrt (div (n * c) (log2Delta b)))).toNat - n)

/-- When the optimum `optOf` is available, the dual candidate does not depend on the sample count
beyond it. -/
theorem Dual.candidate_eq_of_opt {p p' : LWEParams} {xs c : Fx} {b M : ℕ} (hn : p.n = p'.n)
    (hm : p.m = some M) (hm' : p'.m = none) (ho : Dual.optOf p.n c b ≤ M) :
    Dual.candidate p xs c b = Dual.candidate p' xs c b := by
  unfold Dual.optOf at ho
  unfold Dual.candidate
  rw [hm, hm', ← hn]
  simp only [Option.getD_some, Option.getD_none, min_self, min_eq_left ho]

theorem Guess.guard_bind_pure {α : Type} {c : Prop} [Decidable c] {v x : α}
    (h : (guard c >>= fun _ => pure v : Option α) = some x) : (pure v : Option α) = some x := by
  by_cases hc : c <;> simp_all [guard]

/-- MITM with a sample bound succeeds only with the value it has without one (non-sparse
secret). -/
theorem Guess.mitmCostW_of_some {n q q' M : ℕ} {Xs Xe Xe' : ND} (hk : Xe.kind = Xe'.kind)
    (hsp : Xs.isSparse = false) {d : Fx} {K : Fx}
    (h : CostGe K (Guess.mitmCostW ⟨n, q', Xs, Xe', none⟩ true d)) :
    CostGe K (Guess.mitmCostW ⟨n, q, Xs, Xe, some M⟩ true d) := by
  intro x hx
  apply h x
  have ht : tail Xe = tail Xe' := by unfold tail; rw [hk]
  unfold Guess.mitmCostW at hx ⊢
  simp only [LWEParams.mGe, ht, hsp, Bool.false_eq_true, ↓reduceIte, guard_true, pure_bind]
    at hx ⊢
  exact Guess.guard_bind_pure hx

/-! ### Arora–Ge with free constants -/

/-- `single` at a `CBD(16)` instance of dimension `n'` with `M` samples costs at least the bound of
`gb_ge` at `K₀` and `R` (`cbd_single_ge` fixes `K₀ = 50`, `R = 2^20`). -/
theorem cbd_single_geR {n' q M K₀ R : ℕ} {X Y : ND} (hX : X.kind = .cbd 16) (hY : Y.kind = .cbd 16)
    {K : Fx} (hR : 2 ≤ R) (hR1 : 2 * (K₀ + 1) * (R + 1) ≤ n') (hR2 : 56 * M ≤ n' * R ^ 6)
    (hR3 : 8 * 33 ≤ R ^ (33 - 1))
    (hK : K ≤ 2 * log2Nat ((n' + (K₀ + 1)).choose (K₀ + 1))) :
    CostGe K (AroraGB.single (LWEParams.mk' n' q X Y (some M))) := by
  have hN := mk'_cbd_normalize n' q (some M) X Y hX hY
  have hσs : (LWEParams.mk' n' q X Y (some M)).Xs.stddev = cbdSigma := by
    simp [LWEParams.mk', ND.resize, ND.stddev, hX, cbdSigma, ND.cbd]
  have hσe : (LWEParams.mk' n' q X Y (some M)).Xe.stddev = cbdSigma := by
    simp [LWEParams.mk', ND.resize, ND.stddev, hY, cbdSigma, ND.cbd]
  have hs33 : AroraGB.sOf (LWEParams.mk' n' q X Y (some M)) = 33 := by
    unfold AroraGB.sOf
    rw [hσs, hσe]; simp only [lt_irrefl, ↓reduceIte]
    simp [LWEParams.mk', ND.resize, hX, NumMisc.width, ND.bounds]
    decide
  have hw : (floor (NumMisc.width (LWEParams.mk' n' q X Y (some M)).Xe)).toNat = 33 := by
    simp [LWEParams.mk', ND.resize, hY, NumMisc.width, ND.bounds]; decide
  have hc3 : (ceil (LWEParams.mk' n' q X Y (some M)).Xe.stddev).toNat = 3 := by
    rw [hσe]; decide +kernel
  apply AroraGB.single_ge
  · intro d m' s' hd hm hs'
    rw [hN] at hm hs' ⊢
    rw [hs33] at hs'
    subst hs'
    have hm' : m' ≤ M := hm M rfl
    have hg := AroraGB.gb_ge (n := n') (d := d) (m := m') (s := 33) (K₀ := K₀) (R := R)
      (by omega) (by omega) hR hR1 (AroraGB.hmd_of hR hm' hR2 d hd) (fun _ => hR3)
    exact hg.mono hK
  · rw [hN, hw]; norm_num
  · rw [hN, hc3]

/-! ### The instance, the checks and the facts -/

/-- The instance: dimension `n`, modulus `q`, `CBD(16)` secret and error, `M` samples. -/
def cbdPq (n q M : ℕ) : LWEParams := LWEParams.mk' n q (ND.cbd 16) (ND.cbd 16) (some M)

/-- The same instance without a sample bound (and modulus `0`, never read): what the checks
evaluate. -/
def cbdPn (n : ℕ) : LWEParams := LWEParams.mk' n 0 (ND.cbd 16) (ND.cbd 16) none

/-- The uSVP check of block size `β`, for every sample count: the reduction bound, or no `d`
solves the uSVP condition. -/
def Usvp.checkFree (k l2q : Fx) (n β : ℕ) : Bool :=
  decide (k ≤ redLB β) ||
    (Usvp.solveForD (cbdPn n) none β (log2Delta β) (log2 cbdSigma) 0 l2q).isNone

/-- The dual check of block size `b`, for every sample count `≥ M₀`: the reduction bound, or the
candidate at its optimal sample count, when that is at most `M₀`. -/
def Dual.checkFree (k lq : Fx) (n M₀ b : ℕ) : Bool :=
  decide (k ≤ redLB b) ||
    (decide (Dual.optOf n (log2 cbdSigma + lq - log2 cbdSigma) b ≤ M₀) &&
      costGeB k (Dual.candidate (cbdPn n) (log2 cbdSigma) (log2 cbdSigma + lq - log2 cbdSigma) b))

/-- The check of block size `b` at the target `kb` bits, `log₂ q = lq`, every sample count
`≥ M₀`, and the primal margin `W`. -/
def cbdCheckQ (n : ℕ) (lq : Fx) (M₀ kb W b : ℕ) : Bool :=
  PrimalHybrid.check ((kb : ℤ) * ONE) (n - (kb + 22)) lq 0 (log2 cbdSigma) W b &&
    (decide (b < 40) || decide (maxBeta ≤ b) ||
      (Usvp.checkFree ((kb : ℤ) * ONE) lq n b && Dual.checkFree ((kb : ℤ) * ONE) lq n M₀ b &&
        DualHybrid.check ((kb : ℤ) * ONE) n lq (log2 cbdSigma) kb b))

/-- The closed numeric facts (no modulus, no sample count). -/
def cbdFactsQ (n kb W ZA K₀ R : ℕ) : Bool :=
  decide (kb ≤ 4673) &&
    (decide (10050 ≤ n) &&
    (costGeB ((kb : ℤ) * ONE) (Guess.mitmCostW (cbdPn n) true 0) &&
    (decide (Bkw.erf (div (Bkw.zOf (cbdPn n)) (Fx.sqrt (2 * cbdSigma))) = ONE) &&
    (decide (0 ≤ Bkw.zOf (cbdPn n)) &&
    (decide (0 ≤ DualHybrid.coeffOf cbdSigma) &&
    (decide (ONE ≤ DualHybrid.enumCostOf cbdSigma) &&
    (decide (0 ≤ DualHybrid.hOf cbdSigma) &&
    (decide (0 ≤ DualHybrid.alphaOf cbdSigma) &&
    (decide (kb ≤ n) &&
    (decide ((cbdPn n).Xs.hammingWeight.toNat ≤ n) &&
    (decide (4 * (n - (cbdPn n).Xs.hammingWeight.toNat) ≤ n) &&
    (decide ((kb : ℤ) * ONE + 20 * ONE ≤ (2 * (cbdPn n).Xs.hammingWeight.toNat : ℤ) * ONE) &&
    (decide (NumPrimal.c0 * W ≤ -((kb : ℤ) * ONE + 21 * ONE)) &&
    (decide (maxBeta + 1 + W ≤ n - (kb + 22)) &&
    (decide ((kb : ℤ) * ONE ≤ ZA * log2Nat 33) &&
    (decide (2 ≤ R) &&
    (decide (2 * (K₀ + 1) * (R + 1) ≤ n - ZA) &&
    (decide (8 * 33 ≤ R ^ (33 - 1)) &&
    (decide ((kb : ℤ) * ONE ≤ 2 * log2Nat (PrimalHybrid.choose (n - ZA + (K₀ + 1)) (K₀ + 1))) &&
    (decide (ZA ≤ n) &&
    (decide ((cbdPn n).Xs.isSparse = false) &&
    decide ((floor (NumMisc.width (cbdPn n).Xs)).toNat = 33))))))))))))))))))))))

theorem cbdPq_normalize (n q M : ℕ) : (cbdPq n q M).normalize = cbdPq n q M :=
  mk'_cbd_normalize n q (some M) _ _ rfl rfl

theorem cbdPq_Xs (n q M : ℕ) : (cbdPq n q M).Xs.stddev = cbdSigma := rfl
theorem cbdPq_Xe (n q M : ℕ) : (cbdPq n q M).Xe.stddev = cbdSigma := rfl

theorem cbdPq_log2Xi (n q M : ℕ) : Usvp.log2Xi (cbdPq n q M) = 0 := by
  unfold Usvp.log2Xi; rw [cbdPq_Xs, cbdPq_Xe]; simp

/-- **`kb ≤ estimatorBits (cbdPq n q M)`** for a modulus `q ≥ 2^1024` with `log₂ q = lq` and every
sample count `M ≥ M₀` with `maxBeta + 1 + W + kb + 22 ≤ M + n` and `56 M ≤ (n − ZA) · R^6`, from
the closed facts and the per-block-size checks. -/
theorem cbd16q_estimatorBits_ge {n q e M M₀ kb W ZA K₀ R : ℕ} {lq : Fx} (hq : 2 ^ e ≤ q)
    (he : 1024 ≤ e) (hlq : log2Nat q = lq) (hl2q : log2 (ofInt (q : ℤ)) = lq) (hM₀ : M₀ ≤ M)
    (hMlo : maxBeta + 1 + W + (kb + 22) ≤ M + n) (hMhi : 56 * M ≤ (n - ZA) * R ^ 6)
    (hf : cbdFactsQ n kb W ZA K₀ R = true)
    (hc : ∀ b < maxBeta + 2, cbdCheckQ n lq M₀ kb W b = true) :
    kb ≤ estimatorBits (cbdPq n q M) := by
  simp only [cbdFactsQ, Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨hkb, hn, hmitm, herf, hz, hcoeff, henum, hh, halpha, hkbn, hhn, h4, hK2, hW, hDu,
    hpen, hR, hR1, hR3, hbound, hZA, hsparse, hw33⟩ := hf
  set P := cbdPq n q M with hP
  have hN := cbdPq_normalize n q M
  set K : Fx := (kb : ℤ) * ONE
  have hO := ONE_pos
  have hq0 : q ≠ 0 := by have : 1 ≤ 2 ^ e := Nat.one_le_two_pow; omega
  have hlqP : log2Nat P.q = lq := hlq
  have hlq0 : 0 ≤ lq := hlq ▸ log2Nat_nonneg q
  apply estimatorBits_ge_of hkb
  · -- arora
    have hkindXs : (cbdPq n q M).Xs.kind = .cbd 16 := rfl
    have hkindXe : (cbdPq n q M).Xe.kind = .cbd 16 := rfl
    have hch : ∀ n', (n' + (K₀ + 1)).choose (K₀ + 1) =
        PrimalHybrid.choose (n' + (K₀ + 1)) (K₀ + 1) :=
      fun n' => (PrimalHybrid.choose_eq _ _).symm
    have hK' : ∀ n', n - ZA ≤ n' → K ≤ 2 * log2Nat ((n' + (K₀ + 1)).choose (K₀ + 1)) := by
      intro n' hn'
      refine hbound.trans ?_
      rw [← hch]
      have := log2Nat_mono (Nat.choose_le_choose (K₀ + 1)
        (show n - ZA + (K₀ + 1) ≤ n' + (K₀ + 1) by omega))
      linarith
    apply AroraGB.cost_ge ZA (by rw [hN]; exact hsparse) (by rw [hN]; intro s hs; cases hs)
      (by rw [hN, show (floor (NumMisc.width (cbdPq n q M).Xs)).toNat = 33 from hw33]; exact hpen)
    · rw [hN]
      show CostGe K (AroraGB.single (LWEParams.mk' n q (ND.cbd 16) (ND.cbd 16) (some M)))
      exact cbd_single_geR (n' := n) (q := q) (M := M) (K₀ := K₀) (R := R) (X := ND.cbd 16)
        (Y := ND.cbd 16) rfl rfl hR (le_trans hR1 (Nat.sub_le n ZA))
        (le_trans hMhi (Nat.mul_le_mul_right _ (Nat.sub_le n ZA))) hR3 (hK' n (Nat.sub_le n ZA))
    · intro z hz
      have hzle : n - ZA ≤ n - z := Nat.sub_le_sub_left (le_of_lt hz) n
      rw [hN]
      show CostGe K (AroraGB.single (LWEParams.mk' (n - z) q (cbdPq n q M).Xs (cbdPq n q M).Xe
        (some M)))
      exact cbd_single_geR (n' := n - z) (q := q) (M := M) (K₀ := K₀) (R := R) (X := (cbdPq n q M).Xs)
        (Y := (cbdPq n q M).Xe) hkindXs hkindXe hR (le_trans hR1 hzle)
        (le_trans hMhi (Nat.mul_le_mul_right _ hzle)) hR3 (hK' _ hzle)
    · intro z
      rw [hN]
      show CostGe 0 (AroraGB.single (LWEParams.mk' (n - z) q (cbdPq n q M).Xs (cbdPq n q M).Xe
        (some M)))
      exact cbd_single_nonneg (n' := n - z) (q := q) (M := M) (X := (cbdPq n q M).Xs)
        (Y := (cbdPq n q M).Xe) hkindXs hkindXe
  · -- bkw
    rw [Bkw.cost_eq_none_ge (e := e) hq he
      (by rw [hN, cbdPq_Xs, cbdPq_Xe]; exact lt_irrefl _)
      (by rw [hN]; exact hz) (by rw [hN, cbdPq_Xe]; exact herf)]
    exact costGe_none _
  · -- usvp
    rw [Usvp.cost_eq_log2]
    show CostGe K (Usvp.costQ (log2 (ofInt (q : ℤ))) P)
    rw [hl2q]
    apply Usvp.costQ_ge
    intro β hβ1 hβ2
    have := hc β (by omega)
    simp only [cbdCheckQ, Usvp.checkFree, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at this
    obtain ⟨-, h⟩ := this
    rcases h with (h | h) | h
    · omega
    · omega
    · rcases h.1.1 with h | h
      · intro x hx; exact h.trans (Usvp.costGsaQ_ge_redLB (by omega) hx)
      · rw [Usvp.costGsaQ_none]
        · exact costGe_none _
        rw [hN, cbdPq_Xe, cbdPq_log2Xi]
        apply Usvp.solveForD_isNone_m _ none
        rw [Usvp.solveForD_congr (p := cbdPq n q M) (p' := cbdPn n) rfl rfl]
        simpa using h
  · -- bdd
    show CostGe K (PrimalHybrid.estimate P false true)
    apply PrimalHybrid.estimate_ge (Z₁ := kb + 22) (W := W) (a := -16) (b := 16)
    · rw [hN]; intro s hs; cases hs
    · rw [hN]; rfl
    · decide
    · rw [hN]; exact hhn
    · rw [hN]; exact h4
    · rw [hN, hlqP, cbdPq_log2Xi, sub_zero]; exact hlq0
    · push_cast; linarith
    · rw [hN]; exact hK2
    · exact hW
    · rw [hN]; exact hDu
    · rw [hN, cbdPq_Xs, cbdPq_Xe, ite_eq_left_of_eq_true _ _ (eq_true (le_refl cbdSigma))]
      intro M' hM'
      simp only [cbdPq, LWEParams.mk', Option.map_some, Option.some.injEq] at hM'
      omega
    · intro b hb
      have := hc b hb
      simp only [cbdCheckQ, Bool.and_eq_true] at this
      rw [hN, hlqP, cbdPq_log2Xi, cbdPq_Xe]
      exact this.1
  · -- bdd hybrid
    show CostGe K (PrimalHybrid.estimate P false false)
    apply PrimalHybrid.estimate_ge (Z₁ := kb + 22) (W := W) (a := -16) (b := 16)
    · rw [hN]; intro s hs; cases hs
    · rw [hN]; rfl
    · decide
    · rw [hN]; exact hhn
    · rw [hN]; exact h4
    · rw [hN, hlqP, cbdPq_log2Xi, sub_zero]; exact hlq0
    · push_cast; linarith
    · rw [hN]; exact hK2
    · exact hW
    · rw [hN]; exact hDu
    · rw [hN, cbdPq_Xs, cbdPq_Xe, ite_eq_left_of_eq_true _ _ (eq_true (le_refl cbdSigma))]
      intro M' hM'
      simp only [cbdPq, LWEParams.mk', Option.map_some, Option.some.injEq] at hM'
      omega
    · intro b hb
      have := hc b hb
      simp only [cbdCheckQ, Bool.and_eq_true] at this
      rw [hN, hlqP, cbdPq_log2Xi, cbdPq_Xe]
      exact this.1
  · -- mitm hybrid
    show CostGe K (PrimalHybrid.estimate P true false)
    apply PrimalHybrid.estimate_ge (Z₁ := kb + 22) (W := W) (a := -16) (b := 16)
    · rw [hN]; intro s hs; cases hs
    · rw [hN]; rfl
    · decide
    · rw [hN]; exact hhn
    · rw [hN]; exact h4
    · rw [hN, hlqP, cbdPq_log2Xi, sub_zero]; exact hlq0
    · push_cast; linarith
    · rw [hN]; exact hK2
    · exact hW
    · rw [hN]; exact hDu
    · rw [hN, cbdPq_Xs, cbdPq_Xe, ite_eq_left_of_eq_true _ _ (eq_true (le_refl cbdSigma))]
      intro M' hM'
      simp only [cbdPq, LWEParams.mk', Option.map_some, Option.some.injEq] at hM'
      omega
    · intro b hb
      have := hc b hb
      simp only [cbdCheckQ, Bool.and_eq_true] at this
      rw [hN, hlqP, cbdPq_log2Xi, cbdPq_Xe]
      exact this.1
  · -- dual
    rw [Dual.cost_eq_log2 hq0, hlqP]
    apply Dual.costQ_ge
    intro b hb1 hb2
    have := hc b (by omega)
    simp only [cbdCheckQ, Dual.checkFree, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at this
    obtain ⟨-, h⟩ := this
    rcases h with (h | h) | h
    · omega
    · omega
    · rcases h.1.2 with h | ⟨hopt, h⟩
      · intro x hx; exact h.trans (Dual.candidate_ge_redLB (by omega) hx)
      · rw [hN, cbdPq_Xs, cbdPq_Xe,
          Dual.candidate_eq_of_opt (p := cbdPq n q M) (p' := cbdPn n) rfl rfl rfl (le_trans hopt hM₀)]
        exact costGe_iff.mpr h
  · -- dual hybrid
    apply DualHybrid.cost_ge (kb := kb) (by rw [hN]; rfl) (by rw [hN]; exact hcoeff)
      (by rw [hN]; exact henum) (by rw [hN]; exact hh) (by rw [hN]; exact halpha) le_rfl
      (by rw [hN]; exact hkbn)
    intro b hb1 hb2
    have := hc b (by omega)
    simp only [cbdCheckQ, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at this
    obtain ⟨-, h⟩ := this
    rcases h with (h | h) | h
    · omega
    · omega
    · rw [hN, hlqP, cbdPq_Xe]; exact h.2
  · -- exhaustive search
    rw [Guess.exhaustiveCost_eq_none (by rw [hN]; intro s hs; cases hs)
      (by rw [hN]; exact (by decide : (2 : ℤ) ≤ floor (NumMisc.width (ND.cbd 16))))
      (by rw [hN]; exact hn)]
    exact costGe_none _
  · -- mitm
    rw [Guess.mitmCost_eq_ge (e := e) hq
      (by rw [hN]; exact (by decide : (0 : ℤ) ≤ NumMisc.width (ND.cbd 16))) (by
      rw [hN]
      calc NumMisc.width P.Xe = 33 * ONE := rfl
        _ < 2 ^ 54 := by decide
        _ ≤ 2 ^ e := pow_le_pow_right₀ (by norm_num) (by omega)), hN]
    exact Guess.mitmCostW_of_some (n := n) (q := q) (q' := 0) (Xe' := ND.cbd 16) rfl hsparse (costGe_iff.mpr hmitm)

end SigabaNeo.Lattices.Estimator
