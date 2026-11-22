import SigabaNeo.Lib.Lattices.Estimator.Bound.Loops

/-!
# The searches return candidates

Each search of the attack models (`DualHybrid.localMin`, `NumPrimal.localMinimum`,
`NumPrimal.minimize`, `NumMisc.search`) only returns values of the function it searches, so a lower
bound on the function is a lower bound on the result.
-/

namespace SigabaNeo.Lattices.Estimator

open Fx

theorem DualHybrid.localMin_ge {k : Fx} (f : ℕ → Cost) (stop : ℕ)
    (hf : ∀ x, 40 ≤ x → x < stop → CostGe k (f x)) :
    CostGe k (DualHybrid.localMin f stop) := by
  unfold DualHybrid.localMin
  simp only [Id.run_bind, Id.run_pure]
  apply forIn_inv (β := ℕ × ℕ × ℕ × ℤ × List ℕ × Cost) (I := fun s => CostGe k s.2.2.2.2.2)
  · simp
  · intro a _ s hs
    split_ifs with h1 <;> simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt,
      ge_iff_le, not_le] at h1 <;> first | exact hs | exact hf _ (by omega) (by omega)

theorem NumPrimal.minimize_ge {k : Fx} (lo hi : ℕ) (f : ℕ → Cost) (hf : ∀ x, CostGe k (f x)) :
    CostGe k (NumPrimal.minimize lo hi f).2 := by
  unfold NumPrimal.minimize
  simp only [Id.run_bind, Id.run_pure]
  apply forIn_inv (β := ℕ × ℕ × ℕ × Cost) (I := fun s => CostGe k s.2.2.2)
  · simp
  · intro a _ s hs
    split
    · simpa using hs
    · simp only [Id.run_bind]
      generalize hr : (forIn (m := Id) (_ : List ℕ) (s.2.2.1, s.2.2.2) _ : Id (ℕ × Cost)) = r
      have hin : CostGe k r.2 := by
        rw [← hr]
        apply list_forIn_inv (β := ℕ × Cost) (I := fun s => CostGe k s.2)
        · exact hs
        · intro i _ t ht
          split
          · split
            · rename_i v hv _; simpa [← hv] using hf i
            · simpa using ht
          · simpa using ht
      split <;> exact hin

theorem NumMisc.search_inv {α : Type} (Q : Option α → Prop) (start stop : ℕ) (eval : ℕ → α)
    (smaller : α → α → Bool) (h0 : Q none) (hf : ∀ x, Q (some (eval x))) :
    Q (NumMisc.search start stop eval smaller) := by
  unfold NumMisc.search
  simp only [Id.run_bind, Id.run_pure]
  apply forIn_inv (β := ℤ × ℤ × ℤ × ℤ × Option α × List ℤ) (I := fun s => Q s.2.2.2.2.1)
  · simpa using h0
  · intro a _ s hs
    split_ifs <;> simp_all

theorem NumPrimal.localMinimum_inv (P : Cost → Prop) (h0 : P none) (start stop precision : ℕ)
    (f : ℕ → Cost) (hf : ∀ x, start ≤ x → x < stop → P (f x)) (hst : 0 < stop) :
    P (NumPrimal.localMinimum start stop precision f).2 ∧
      (NumPrimal.localMinimum start stop precision f).1 < stop := by
  unfold NumPrimal.localMinimum
  simp only [Id.run_bind]
  generalize hr : (forIn (m := Id) (_ : Std.Legacy.Range) _ _ :
    Id (ℕ × ℕ × ℕ × ℤ × ℕ × Cost × List ℕ)) = r
  have hin : P r.2.2.2.2.2.1 ∧ r.2.2.2.2.1 < stop := by
    rw [← hr]
    apply forIn_inv (β := ℕ × ℕ × ℕ × ℤ × ℕ × Cost × List ℕ)
      (I := fun s => P s.2.2.2.2.2.1 ∧ s.2.2.2.2.1 < stop)
    · refine ⟨h0, ?_⟩
      show (stop / precision - 1) * precision < stop
      rcases Nat.eq_zero_or_pos precision with h | h
      · simp [h, hst]
      · have := Nat.div_mul_le_self stop precision
        rcases Nat.eq_zero_or_pos (stop / precision) with h' | h'
        · simp [h', hst]
        · rw [Nat.sub_mul, one_mul]; omega
    · intro a _ s hs
      split_ifs with h1 <;> simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt,
        ge_iff_le, not_le] at h1
      all_goals first
        | exact hs
        | (have h2 : s.2.2.1 * precision < stop := by
             have := Nat.div_mul_le_self stop precision
             have h3 := h1.1.2
             have : (s.2.2.1 + 1) * precision ≤ stop / precision * precision :=
               Nat.mul_le_mul_right _ h3
             rw [add_mul, one_mul] at this
             rcases Nat.eq_zero_or_pos precision with hp | hp
             · simp [hp] at h3
             · omega
           exact ⟨hf _ h1.1.1 h2, h2⟩)
  split
  · simp only [Id.run_bind]
    have h2 := forIn_inv (β := ℕ × Cost) (I := fun s => P s.2 ∧ s.1 < stop)
      [max start (r.2.2.2.2.1 - precision):min stop (r.2.2.2.2.1 + precision)]
      (r.2.2.2.2.1, r.2.2.2.2.2.1) (fun j __s =>
        if (Option.isNone __s.2 || Option.any (fun x => Option.all (fun x_1 => decide (x ≤ x_1)) __s.2)
            (f j)) = true then (pure (ForInStep.yield (j, f j)) : Id (ForInStep (ℕ × Cost)))
        else pure (ForInStep.yield (__s.1, __s.2))) ⟨hin.1, hin.2⟩ (by
          intro j hj t ht
          simp only [Std.Legacy.Range.size, List.mem_range'_1] at hj
          split
          · show P (f j) ∧ j < stop
            have : j < stop := by
              have := min_le_left stop (r.2.2.2.2.1 + precision); omega
            exact ⟨hf j (by omega) this, this⟩
          · exact ht)
    exact h2
  · exact hin

theorem NumPrimal.localMinimum_ge {k : Fx} (start stop precision : ℕ) (f : ℕ → Cost)
    (hf : ∀ x, start ≤ x → x < stop → CostGe k (f x)) (hst : 0 < stop) :
    CostGe k (NumPrimal.localMinimum start stop precision f).2 ∧
      (NumPrimal.localMinimum start stop precision f).1 < stop :=
  NumPrimal.localMinimum_inv (CostGe k) (costGe_none k) start stop precision f hf hst

end SigabaNeo.Lattices.Estimator
