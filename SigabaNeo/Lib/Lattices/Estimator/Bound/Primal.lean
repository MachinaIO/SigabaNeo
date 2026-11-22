import SigabaNeo.Lib.Lattices.Estimator.Bound.Profile
import SigabaNeo.Lib.Lattices.Estimator.Bound.Binom

/-!
# Lower bounds for the primal attacks (BDD, BDD hybrid, MITM hybrid)

Every candidate of `PrimalHybrid.estimate` (guessed coordinates `z`, block size `b`, dimension `d`,
search-space weight `w`) costs `log₂ (red + svp·|S|) + repetitions`, at least

* the reduction cost, hence `redLB b` (`evalAt_ge`, first case);
* `a − t − lp − 20`, where `a` (the guessing cost) and `−t` (the miss probability) together give at
  least `z − 1` bits (`weights`, below), and `lp ≤ 0` is the `log₂` of Babai's success probability.

When the block size is small, the GSA profile falls by more than 55 bits well before the last
`maxBeta + 1` coordinates, so `−lp` is large (`Profile.lean`); this is checked per block size with
an AM–GM bound uniform in the dimension `d`.
-/

namespace SigabaNeo.Lattices.Estimator

open Fx NumPrimal PrimalHybrid

/-- `etaFor` stays below its initial upper end. -/
theorem PrimalHybrid.etaFor_le (avg delta : Fx) (d : ℕ) :
    etaFor avg delta d ≤ (if d > 4096 then min d maxBeta else d) + 1 := by
  unfold etaFor
  simp only [Id.run_bind, Id.run_pure]
  generalize hH : (if d > 4096 then min d maxBeta else d) = H
  generalize hr : (forIn (m := Id) (_ : Std.Legacy.Range) (H, 0) _ : Id (ℕ × ℕ)) = r
  have : r.1 ≤ H ∧ r.2 ≤ H := by
    rw [← hr]
    apply forIn_inv (β := ℕ × ℕ) (I := fun s => s.1 ≤ H ∧ s.2 ≤ H)
    · exact ⟨le_rfl, Nat.zero_le _⟩
    · intro j _ st hst
      split
      · exact hst
      · rename_i h
        split
        · exact ⟨hst.1, by show (st.2 + st.1 + 1) / 2 ≤ H; omega⟩
        · exact ⟨by show (st.2 + st.1 + 1) / 2 - 1 ≤ H; omega, hst.2⟩
  exact Nat.succ_le_succ this.2

theorem NumPrimal.repetitions_nonneg (x : Fx) : 0 ≤ repetitions x := by
  unfold repetitions
  have hc : (0 : Fx) ≤ log2 (ln (100 * ONE)) := by decide +kernel
  have := ONE_pos
  split
  · exact le_rfl
  split
  · linarith
  · exact log2Nat_nonneg _

theorem NumPrimal.repetitions_ge (x : Fx) : -x - 20 * ONE ≤ repetitions x := by
  unfold repetitions
  have hc : (0 : Fx) ≤ log2 (ln (100 * ONE)) := by decide +kernel
  have h99 : (-20 : ℤ) * ONE ≤ log2 (ofRat 99 100) := by decide +kernel
  have := ONE_pos
  split
  · linarith
  split
  · linarith
  · have := log2Nat_nonneg ((ceil (div (-(ln (100 * ONE))) (ln (ONE - exp2 x))))).toNat
    linarith

/-- The loop `choose` is the binomial coefficient. -/
theorem PrimalHybrid.choose_eq (n k : ℕ) : PrimalHybrid.choose n k = n.choose k := by
  unfold PrimalHybrid.choose
  split
  · rename_i h; simp only [Id.run_pure]; exact (Nat.choose_eq_zero_of_lt (by omega)).symm
  rename_i h
  simp only [Id.run_bind, Id.run_pure]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  have e : n.choose k = n.choose (0 + min k (n - k)) := by
    rw [zero_add]
    rcases le_total k (n - k) with h' | h'
    · rw [min_eq_left h']
    · rw [min_eq_right h', Nat.choose_symm (by omega)]
  rw [e]
  refine forIn_range'_ind 0 (min k (n - k)) 1 _ (fun j a => a = n.choose j) (by simp) ?_
  intro j _ hj a ha
  refine ⟨_, rfl, ?_⟩
  show a * (n - j) / (j + 1) = n.choose (j + 1)
  rw [ha, ← Nat.choose_succ_right_eq, Nat.mul_div_cancel _ (Nat.succ_pos j)]

end SigabaNeo.Lattices.Estimator

namespace SigabaNeo.Lattices.Estimator

open Fx NumPrimal PrimalHybrid Finset

/-- The entries of `weights`: for each weight `w ∈ [lo, hi]`, the `log₂` of the search space and
of the hit probability. -/
theorem PrimalHybrid.weights_spec (p : LWEParams) (z : ℕ) (mitm : Bool) (a b : ℤ)
    (hab : p.Xs.bounds.getD (0, 0) = (a, b)) :
    ∀ e ∈ weights p z mitm, ∃ w, p.Xs.hammingWeight.toNat - (p.n - z) ≤ w ∧
      w ≤ (match p.Xs.kind with | .gauss _ => 0 | _ => min z p.Xs.hammingWeight.toNat) ∧
      e.1 = log2Nat (∑ w' ∈ Ico (p.Xs.hammingWeight.toNat - (p.n - z)) (w + 1),
          z.choose w' * (b - a).toNat ^ w') / (if mitm then 2 else 1) ∧
      e.2 = log2Nat (∑ w' ∈ Ico (p.Xs.hammingWeight.toNat - (p.n - z)) (w + 1),
          p.Xs.hammingWeight.toNat.choose w' * (p.n - p.Xs.hammingWeight.toNat).choose (z - w')) -
        log2Nat (p.n.choose z) := by
  set h := p.Xs.hammingWeight.toNat
  set lo := h - (p.n - z)
  set hi := (match p.Xs.kind with | .gauss _ => 0 | _ => min z h)
  unfold weights
  simp only [hab, Id.run_bind, Id.run_pure, choose_eq]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
  generalize hr : (forIn (m := Id) (List.range' lo (hi + 1 - lo))
    ((0 : ℕ), (0 : ℕ), (#[] : Array (Fx × Fx))) _ : Id (ℕ × ℕ × Array (Fx × Fx))) = r
  set Inv := (fun j (st : ℕ × ℕ × Array (Fx × Fx)) => st.1 = ∑ w' ∈ Ico lo j, z.choose w' * (b - a).toNat ^ w' ∧
      st.2.1 = ∑ w' ∈ Ico lo j, h.choose w' * (p.n - h).choose (z - w') ∧
      ∀ e ∈ st.2.2, ∃ w, lo ≤ w ∧ w < j ∧
        e.1 = log2Nat (∑ w' ∈ Ico lo (w + 1), z.choose w' * (b - a).toNat ^ w') /
          (if mitm then 2 else 1) ∧
        e.2 = log2Nat (∑ w' ∈ Ico lo (w + 1), h.choose w' * (p.n - h).choose (z - w')) -
          log2Nat (p.n.choose z)) with hInv
  have key : Inv (lo + (hi + 1 - lo)) r := by
    rw [← hr]
    refine forIn_range'_ind lo (hi + 1 - lo) ((0 : ℕ), (0 : ℕ), (#[] : Array (Fx × Fx))) _ Inv
      ?_ ?_
    · simp [hInv]
    · intro j hj1 hj2 st ⟨h1, h2, h3⟩
      refine ⟨_, rfl, ?_, ?_, ?_⟩
      · show st.1 + z.choose j * (b - a).toNat ^ j = _
        rw [sum_Ico_succ_top hj1, h1]
      · show st.2.1 + h.choose j * (p.n - h).choose (z - j) = _
        rw [sum_Ico_succ_top hj1, h2]
      · intro e he
        rw [Array.mem_push] at he
        rcases he with he | he
        · obtain ⟨w, hw1, hw2, hw3⟩ := h3 e he
          exact ⟨w, hw1, by omega, hw3⟩
        · refine ⟨j, hj1, by omega, ?_, ?_⟩
          · rw [he, sum_Ico_succ_top hj1, h1]
          · rw [he, sum_Ico_succ_top hj1, h2]
  intro e' he'
  obtain ⟨w, hw1, hw2, hw3⟩ := key.2.2 e' he'
  exact ⟨w, hw1, by omega, hw3⟩

end SigabaNeo.Lattices.Estimator

namespace SigabaNeo.Lattices.Estimator

open Fx NumPrimal PrimalHybrid Finset

theorem log2Nat_ge_of_two_pow_le {v k : ℕ} (h : 2 ^ k ≤ v) : (k : ℤ) * ONE ≤ log2Nat v := by
  have := log2Nat_mono h; rwa [log2Nat_two_pow] at this

/-- Every entry of `weights` pays, in guessing cost plus miss probability, at least
`min (z − 1, 2h)` bits (a dense secret: `4 (n − h) ≤ n`, and at least 16 values per coordinate). -/
theorem PrimalHybrid.weights_bound (p : LWEParams) (z : ℕ) (mitm : Bool) (a b : ℤ)
    (hab : p.Xs.bounds.getD (0, 0) = (a, b)) (hk : ∀ s, p.Xs.kind ≠ .gauss s)
    (hB : 16 ≤ (b - a).toNat) (hhn : p.Xs.hammingWeight.toNat ≤ p.n)
    (h4 : 4 * (p.n - p.Xs.hammingWeight.toNat) ≤ p.n) :
    ∀ e ∈ weights p z mitm, 0 ≤ e.1 ∧
      min ((z : ℤ) - 1) (2 * p.Xs.hammingWeight.toNat) * ONE ≤ e.1 - e.2 := by
  intro e he
  obtain ⟨w, hw1, hw2, he1, he2⟩ := weights_spec p z mitm a b hab e he
  set h := p.Xs.hammingWeight.toNat
  set n := p.n
  have hhi : (match p.Xs.kind with | .gauss _ => 0 | _ => min z h) = min z h := by
    cases hkind : p.Xs.kind with
    | gauss s => exact absurd hkind (hk s)
    | cbd _ => rfl
    | uniform _ _ => rfl
  rw [hhi] at hw2
  have hO := ONE_pos
  set S := ∑ w' ∈ Ico (h - (n - z)) (w + 1), z.choose w' * (b - a).toNat ^ w'
  set H := ∑ w' ∈ Ico (h - (n - z)) (w + 1), h.choose w' * (n - h).choose (z - w')
  -- the guessing cost
  have hS : 2 ^ (4 * w) ≤ S := by
    have h1 : z.choose w * (b - a).toNat ^ w ≤ S :=
      single_le_sum (f := fun w' => z.choose w' * (b - a).toNat ^ w') (fun _ _ => Nat.zero_le _)
        (mem_Ico.mpr ⟨hw1, by omega⟩)
    have h2 : 2 ^ (4 * w) ≤ (b - a).toNat ^ w := by
      rw [pow_mul]; exact Nat.pow_le_pow_left (by norm_num; exact hB) w
    have h3 : 1 ≤ z.choose w := Nat.choose_pos (by omega)
    calc 2 ^ (4 * w) ≤ (b - a).toNat ^ w := h2
      _ ≤ z.choose w * (b - a).toNat ^ w := Nat.le_mul_of_pos_left _ h3
      _ ≤ S := h1
  have ha : (2 * w : ℤ) * ONE ≤ e.1 := by
    rw [he1]
    have := log2Nat_ge_of_two_pow_le hS
    split
    · rw [Int.le_ediv_iff_mul_le (by norm_num)]; push_cast at this ⊢; linarith
    · rw [Int.ediv_one]; push_cast at this ⊢; nlinarith
  refine ⟨le_trans (by positivity) ha, ?_⟩
  rcases le_or_gt z n with hz | hz
  · -- the hit probability
    have hH := Binom.hit_mul_le (lo := h - (n - z)) (n := n) (h := h) (z := z) (w := w) (by omega) hz
      hhn h4
    have hH0 : 0 < H := Binom.hit_pos hz hhn rfl hw1
    have hC0 : 0 < n.choose z := Nat.choose_pos hz
    have hlog : Nat.log2 H + 2 * (z - w) ≤ Nat.log2 (n.choose z) + z := by
      rw [← Binom.log2_mul_two_pow hH0, ← Binom.log2_mul_two_pow hC0]
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      apply Nat.log_mono_right
      rw [pow_mul]; norm_num; exact hH
    have h1 := log2Nat_lt H
    have h2 := log2Nat_ge (n.choose z)
    have h3 : ((Nat.log2 H : ℤ) + 1) * ONE + ((2 * (z - w) : ℕ) : ℤ) * ONE ≤
        ((Nat.log2 (n.choose z) : ℤ) + z + 1) * ONE := by
      rw [← add_mul]; apply Int.mul_le_mul_of_nonneg_right _ (le_of_lt hO); push_cast; omega
    rw [he2]
    have : (min ((z : ℤ) - 1) (2 * h)) * ONE ≤ ((z : ℤ) - 1) * ONE :=
      Int.mul_le_mul_of_nonneg_right (min_le_left _ _) (le_of_lt hO)
    have e2 : ((2 * (z - w) : ℕ) : ℤ) = 2 * (z : ℤ) - 2 * w := by push_cast; omega
    rw [e2] at h3
    nlinarith
  · -- no subset fits: the hit count and `C(n, z)` vanish
    have hC : n.choose z = 0 := Nat.choose_eq_zero_of_lt hz
    have hH : H = 0 := by
      apply sum_eq_zero; intro w' hw'; rw [mem_Ico] at hw'
      rw [Nat.choose_eq_zero_of_lt (n := n - h) (k := z - w') (by omega), mul_zero]
    rw [he2, hC, hH, log2Nat_zero, sub_zero]
    have hwh : h ≤ w := by omega
    have : (min ((z : ℤ) - 1) (2 * h)) * ONE ≤ (2 * h : ℤ) * ONE :=
      Int.mul_le_mul_of_nonneg_right (min_le_right _ _) (le_of_lt hO)
    have : (2 * h : ℤ) * ONE ≤ (2 * w : ℤ) * ONE :=
      Int.mul_le_mul_of_nonneg_right (by omega) (le_of_lt hO)
    linarith

end SigabaNeo.Lattices.Estimator

