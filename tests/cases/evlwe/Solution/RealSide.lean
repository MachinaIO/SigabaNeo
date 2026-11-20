import Solution.Decode
import Solution.Elim

/-!
# The attack accepts good real samples

`parityOut_good`: on a Post sample `(C, K mod q, aux)` with integer `K` whose entries satisfy
`2|K_rj| < q`, if `C·K_j − aux_j = e·K_j + 2t_j (mod q)` with `0 ≤ e·K_j + 2t_j < q` for every column,
the attack outputs `true`. Its dependency `u` has `Σ_{j∈u} K_j ≡ 0 (mod 2)`, so
`Σ_{j∈u} (e·K_j + 2t_j) = e·Σ_{j∈u} K_j + 2Σ t_j` is even.
-/

namespace TestCase.EvLWE

open SigabaNeo.Lattices

open TestCase TestCase.EvLWE

/-! ### Bits of xor sums and of `colVec` -/

theorem xorSum_testBit (f : ℕ → ℕ) (u r : ℕ) : ∀ N,
    (xorSum f N u).testBit r =
      decide ((∑ j ∈ Finset.range N, if u.testBit j then ((f j).testBit r).toNat else 0) % 2 = 1)
  | 0 => by simp [xorSum_zero]
  | N + 1 => by
    rw [xorSum_succ, Nat.testBit_xor, xorSum_testBit f u r N, Finset.sum_range_succ]
    generalize (∑ j ∈ Finset.range N, if u.testBit j then ((f j).testBit r).toNat else 0) = S
    rcases Nat.mod_two_eq_zero_or_one S with h | h <;>
      cases hu : u.testBit N <;> cases hb : (f N).testBit r <;> simp [hb, h, Nat.add_mod]

theorem testBit_sum_pow (b : ℕ → ℕ) (hb : ∀ i, b i ≤ 1) (r : ℕ) : ∀ M, r < M →
    (∑ i ∈ Finset.range M, b i * 2 ^ i).testBit r = decide (b r = 1)
  | 0, h => absurd h (Nat.not_lt_zero _)
  | M + 1, h => by
    have hlt : ∑ i ∈ Finset.range M, b i * 2 ^ i < 2 ^ M := by
      clear h
      induction M with
      | zero => simp
      | succ M ih =>
        rw [Finset.sum_range_succ, pow_succ]
        have h1 : b M * 2 ^ M ≤ 2 ^ M := (Nat.mul_le_mul_right _ (hb M)).trans (by simp)
        omega
    rw [Finset.sum_range_succ, add_comm, mul_comm, Nat.testBit_two_pow_mul_add _ hlt]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]; exact testBit_sum_pow b hb r M h
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl _)), Nat.sub_self]
      have := hb r
      interval_cases (b r) <;> simp

/-! ### The real case -/

section
variable {κ : ℕ}

theorem q_odd (κ : ℕ) : q κ % 2 = 1 := by
  have hp : (q κ).Prime := Fact.out
  have hgt : 2 < q κ := by
    have := (exists_q κ).choose_spec.2.1
    have h1 : 2 ≤ 2 ^ w κ := by
      have : 1 ≤ w κ := by unfold w; omega
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ w κ := Nat.pow_le_pow_right (by norm_num) this
    exact lt_of_le_of_lt h1 this
  rcases hp.eq_two_or_odd with h | h <;> omega

/-- The representative of an integer of absolute value below `q/2`. -/
theorem val_intCast_eq (K : ℤ) (hK : 2 * |K| < q κ) :
    (((K : ZMod (q κ)).val : ℕ) : ℤ) = if 0 ≤ K then K else K + q κ := by
  rw [ZMod.val_intCast]
  split_ifs with h
  · exact Int.emod_eq_of_lt h (by rw [abs_of_nonneg h] at hK; omega)
  · rw [← Int.add_emod_right K]
    exact Int.emod_eq_of_lt (by rw [abs_of_neg (by omega)] at hK; omega)
      (by omega)

variable (Cq : Matrix (Fin (ell κ)) (Fin (m κ)) (ZMod (q κ))) (Kz : Matrix (Fin (m κ)) (Fin (k κ)) ℤ)
  (Aq : Matrix (Fin (ell κ)) (Fin (k κ)) (ZMod (q κ)))

theorem kBit_postWord (hK : ∀ r j, 2 * |Kz r j| < q κ) (r : Fin (m κ)) (j : Fin (k κ)) :
    kBit κ (postWord Cq (intMod (q κ) Kz) Aq) r j = (Kz r j % 2).toNat := by
  have hv := val_intCast_eq (Kz r j) (hK r j)
  have hodd := q_odd κ
  have hk : kAt κ (postWord Cq (intMod (q κ) Kz) Aq) r j = ((Kz r j : ZMod (q κ))).val := by
    rw [kAt_postWord]; rfl
  unfold kBit
  rw [hk, qOf_postWord]
  have habs := hK r j
  set x := ((Kz r j : ZMod (q κ))).val
  split_ifs at hv with h0
  · rw [abs_of_nonneg h0] at habs
    split_ifs <;> omega
  · rw [abs_of_neg (by omega)] at habs
    split_ifs <;> omega

theorem colVec_testBit (hK : ∀ r j, 2 * |Kz r j| < q κ) (r : Fin (m κ)) (j : Fin (k κ)) :
    (colVec κ (postWord Cq (intMod (q κ) Kz) Aq) j).testBit r =
      decide ((Kz r j % 2).toNat = 1) := by
  unfold colVec
  rw [listSum_range', testBit_sum_pow _ (fun i => kBit_le κ _ i j) r _ r.isLt,
    kBit_postWord Cq Kz Aq hK]

/-- The dependency is even in every row. -/
theorem dep_even (hK : ∀ r j, 2 * |Kz r j| < q κ) (r : Fin (m κ)) :
    (∑ j : Fin (k κ), if (depMask κ (postWord Cq (intMod (q κ) Kz) Aq)).testBit j then Kz r j
      else 0) % 2 = 0 := by
  set word := postWord Cq (intMod (q κ) Kz) Aq
  obtain ⟨-, -, hx⟩ := depMask_spec κ word
  have hb := xorSum_testBit (colVec κ word) (depMask κ word) r (m κ + 1)
  rw [hx, Nat.zero_testBit] at hb
  have hsum : (∑ j ∈ Finset.range (m κ + 1), if (depMask κ word).testBit j then
      ((colVec κ word j).testBit r).toNat else 0) % 2 = 0 := by
    have := hb.symm; simp only [decide_eq_false_iff_not] at this; omega
  rw [show m κ + 1 = k κ from rfl, Finset.sum_range (fun j => if (depMask κ word).testBit j then
      ((colVec κ word j).testBit r).toNat else 0)] at hsum
  have hterm : ∀ j : Fin (k κ), ((if (depMask κ word).testBit j then
      ((colVec κ word j).testBit r).toNat else 0 : ℕ) : ℤ) =
      (if (depMask κ word).testBit j then Kz r j else 0) % 2 := by
    intro j
    rw [colVec_testBit Cq Kz Aq hK r j]
    split_ifs
    · rcases Int.emod_two_eq_zero_or_one (Kz r j) with h | h <;> simp [h]
    · simp
  have hcast := congrArg (fun n : ℕ => (n : ℤ)) hsum
  simp only [Nat.cast_sum, Int.natCast_emod, Nat.cast_ofNat, Nat.cast_zero] at hcast
  rw [Finset.sum_int_mod]
  have : (∑ j : Fin (k κ), ((if (depMask κ word).testBit j then
      ((colVec κ word j).testBit r).toNat else 0 : ℕ) : ℤ)) =
      ∑ j : Fin (k κ), (if (depMask κ word).testBit j then Kz r j else 0) % 2 :=
    Finset.sum_congr rfl fun j _ => hterm j
  rw [← this]
  exact_mod_cast hcast

/-- The attack's `wAt` is the integer `e·K_j + 2t_j`. -/
theorem wAt_postWord (z : ℤ) (j : Fin (k κ))
    (hrel : (∑ r, Cq (i0 κ) r * (Kz r j : ZMod (q κ))) - Aq (i0 κ) j = (z : ZMod (q κ)))
    (hz0 : 0 ≤ z) (hzq : z < q κ) :
    (wAt κ (postWord Cq (intMod (q κ) Kz) Aq) j : ℤ) = z := by
  set word := postWord Cq (intMod (q κ) Kz) Aq
  have hq : 0 < q κ := Nat.pos_of_ne_zero (NeZero.ne _)
  have hsum : ((List.range (m κ)).map fun r => cAt κ word r * kAt κ word r j).sum =
      ∑ r : Fin (m κ), (Cq (i0 κ) r).val * ((Kz r j : ZMod (q κ))).val := by
    rw [listSum_range', Finset.sum_range]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [cAt_postWord, kAt_postWord]; rfl
  have haux := auxAt_postWord Cq (intMod (q κ) Kz) Aq j
  have hlt : auxAt κ word j ≤ q κ := haux ▸ (ZMod.val_lt _).le
  unfold wAt
  rw [qOf_postWord, hsum]
  set n := (∑ r : Fin (m κ), (Cq (i0 κ) r).val * ((Kz r j : ZMod (q κ))).val +
    (q κ - auxAt κ word j)) % q κ
  have hn : (n : ZMod (q κ)) = (z : ZMod (q κ)) := by
    rw [← hrel, ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub hlt, haux, Nat.cast_sum]
    simp [ZMod.natCast_val, sub_eq_add_neg]
  have hnq : n < q κ := Nat.mod_lt _ hq
  have h1 := congrArg ZMod.val hn
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hnq] at h1
  have h2 := ZMod.val_intCast (n := q κ) z
  rw [← h1] at h2
  rw [h2, Int.emod_eq_of_lt hz0 hzq]

/-- The attack accepts. -/
theorem parityOut_good (E : Fin (m κ) → ℤ) (T : Fin (k κ) → ℕ)
    (hK : ∀ r j, 2 * |Kz r j| < q κ)
    (hrel : ∀ j, (∑ r, Cq (i0 κ) r * (Kz r j : ZMod (q κ))) - Aq (i0 κ) j =
      ((∑ r, E r * Kz r j + 2 * T j : ℤ) : ZMod (q κ)))
    (hz0 : ∀ j, 0 ≤ ∑ r, E r * Kz r j + 2 * (T j : ℤ))
    (hzq : ∀ j, ∑ r, E r * Kz r j + 2 * (T j : ℤ) < q κ) :
    parityOut κ (postWord Cq (intMod (q κ) Kz) Aq) = true := by
  set word := postWord Cq (intMod (q κ) Kz) Aq
  set u := depMask κ word
  unfold parityOut
  rw [decide_eq_true_iff, listSum_range', show m κ + 1 = k κ from rfl, Finset.sum_range]
  have hw : ∀ j : Fin (k κ), ((if u.testBit j then wAt κ word j else 0 : ℕ) : ℤ) =
      ∑ r, E r * (if u.testBit j then Kz r j else 0) + 2 * (if u.testBit j then (T j : ℤ) else 0) := by
    intro j
    split_ifs
    · rw [wAt_postWord Cq Kz Aq _ j (hrel j) (hz0 j) (hzq j)]
    · simp
  have hZ : ((∑ j : Fin (k κ), (if u.testBit j then wAt κ word j else 0 : ℕ) : ℕ) : ℤ) =
      ∑ r, E r * (∑ j : Fin (k κ), if u.testBit j then Kz r j else 0) +
        2 * ∑ j : Fin (k κ), (if u.testBit j then (T j : ℤ) else 0) := by
    rw [Nat.cast_sum, Finset.sum_congr rfl fun j _ => hw j, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_comm]
    simp only [Finset.mul_sum]
  have heven : (∑ r, E r * (∑ j : Fin (k κ), if u.testBit j then Kz r j else 0)) % 2 = 0 := by
    rw [Finset.sum_int_mod]
    have : ∀ r : Fin (m κ), (E r * (∑ j : Fin (k κ), if u.testBit j then Kz r j else 0)) % 2 = 0 :=
      fun r => by rw [Int.mul_emod, dep_even Cq Kz Aq hK r, mul_zero, Int.zero_emod]
    rw [Finset.sum_congr rfl fun r _ => this r]; simp
  have hu : u = depMask κ word := rfl
  rw [hu] at hZ heven
  omega

end

end TestCase.EvLWE
