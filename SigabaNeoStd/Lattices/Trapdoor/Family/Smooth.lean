import SigabaNeoStd.Lattices.Trapdoor.Family.Close

/-!
# Trapdoor sampler: `Λ^⊥([Ā | G − Ā R])` is smooth

The trapdoor gives `m` short independent vectors of `Λ^⊥(B)` ([MP12], Lemma 5.3):

* `sA a = [e_a + R w_a; w_a]` with `G w_a = −Ā e_a` (`w_a = gInv (−Ā e_a)`), for `a < mb`;
* `sG c = [R g_c; g_c]` with `g_c` in the kernel of the gadget: `2 e_{(r,t)} − e_{(r,t+1)}` for
  `t < w`, and the binary digits of `q` in row `r` for `t = w`.

Their entries are at most `mb + 2` (`abs_sv_le`), they lie in the kernel (`sv_mem_kernel`), and
they are linearly independent over `ℝ` (`sv_indep`). A nonzero dual vector `y` therefore has a
nonzero integer vector `(⟨y, s_i⟩)_i` of squared norm at most `‖y‖² Σ‖s_i‖²`, and the nonzero dual
mass at width `1/τ` is at most that of `Z^m` at width `√(Σ‖s_i‖²)/τ` (`dualMassE_le_wt1`).
-/

namespace SigabaNeo.Lattices.Trapdoor.Family

open SigabaNeo.Lattices ZLattice ProbabilityTheory
open scoped ENNReal Matrix RealInnerProductSpace

section
variable (κ : ℕ)

/-- The gadget column `(r, t)`. -/
def gIdx (r : Fin (n κ)) (t : Fin (w κ + 1)) : Fin (mb κ) := finProdFinEquiv (r, t)

theorem gRow_gIdx (r : Fin (n κ)) (t : Fin (w κ + 1)) : gRow κ (gIdx κ r t) = r := by
  simp [gRow, gIdx]

theorem gBit_gIdx (r : Fin (n κ)) (t : Fin (w κ + 1)) : gBit κ (gIdx κ r t) = t := by
  simp [gBit, gIdx]

/-- `G` applied to an integer vector, row by row. -/
theorem gadget_mulVec_apply (f : Fin (mb κ) → ℤ) (i : Fin (n κ)) :
    (gadget κ *ᵥ fun c => (f c : ZMod (q κ))) i =
      ∑ t : Fin (w κ + 1), (2 : ZMod (q κ)) ^ (t : ℕ) * (f (gIdx κ i t) : ZMod (q κ)) := by
  simp only [Matrix.mulVec, dotProduct, gadget]
  rw [← (finProdFinEquiv (m := n κ) (n := w κ + 1)).sum_comp]
  simp only [gRow, gBit, Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_eq_single i]
  · simp [gIdx]
  · intro b _ hb; simp [hb]
  · simp

/-- A kernel vector of the gadget. -/
noncomputable def gk (c : Fin (mb κ)) : Fin (mb κ) → ℤ := fun c' =>
  if gRow κ c' ≠ gRow κ c then 0
  else if (gBit κ c : ℕ) < w κ then
    (if gBit κ c' = gBit κ c then 2 else if (gBit κ c' : ℕ) = gBit κ c + 1 then -1 else 0)
  else if (q κ).testBit (gBit κ c') then 1 else 0

theorem gadget_gk (c : Fin (mb κ)) : gadget κ *ᵥ (fun c' => (gk κ c c' : ZMod (q κ))) = 0 := by
  funext i
  rw [gadget_mulVec_apply]
  simp only [Pi.zero_apply]
  by_cases hi : i = gRow κ c
  · subst hi
    simp only [gk, gRow_gIdx, ne_eq, not_true_eq_false, if_false, gBit_gIdx]
    split_ifs with ht
    · -- `2 · 2^t − 2^{t+1}`
      set t0 := gBit κ c
      let t1 : Fin (w κ + 1) := ⟨(t0 : ℕ) + 1, by omega⟩
      have hterm : ∀ t : Fin (w κ + 1), (2 : ZMod (q κ)) ^ (t : ℕ) *
          (((if t = t0 then 2 else if (t : ℕ) = t0 + 1 then -1 else 0 : ℤ)) : ZMod (q κ)) =
          (if t = t0 then (2 : ZMod (q κ)) ^ (t0 : ℕ) * 2 else 0) +
          (if t = t1 then -((2 : ZMod (q κ)) ^ (t1 : ℕ)) else 0) := by
        intro t
        by_cases h0 : t = t0
        · have : t0 ≠ t1 := by intro h; have := congrArg Fin.val h; simp [t1] at this
          rw [h0]
          simp [this]
        · by_cases h1 : t = t1
          · rw [h1]
            have h1' : t1 ≠ t0 := by intro h; exact h0 (h1.trans h)
            have : (t1 : ℕ) = t0 + 1 := rfl
            simp [h1', this]
          · have : (t : ℕ) ≠ t0 + 1 := fun h => h1 (Fin.ext h)
            simp [h0, h1, this]
      rw [Finset.sum_congr rfl fun t _ => hterm t, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
      simp only [t1, pow_succ]
      ring
    · have hlt : q κ < 2 ^ (w κ + 1) := by
        have h1 := q_le_two_pow κ
        have h2 := q_odd κ
        rcases h1.lt_or_eq with h | h
        · exact h
        · exfalso; rw [h, pow_succ] at h2; omega
      have hq := sum_testBit_pow (q κ) (w κ + 1)
      rw [Nat.mod_eq_of_lt hlt] at hq
      calc ∑ t : Fin (w κ + 1), (2 : ZMod (q κ)) ^ (t : ℕ) *
            (((if (q κ).testBit t then 1 else 0 : ℤ)) : ZMod (q κ))
          = (((∑ t : Fin (w κ + 1), (if (q κ).testBit t then 2 ^ (t : ℕ) else 0) : ℕ)) :
              ZMod (q κ)) := by
            push_cast
            refine Finset.sum_congr rfl fun t _ => ?_
            split_ifs <;> simp
        _ = 0 := by rw [hq, ZMod.natCast_self]
  · simp only [gk]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_pos (by rw [gRow_gIdx]; exact hi), Int.cast_zero, mul_zero]


/-! ### The short vectors -/

/-- `w_a = gInv (−Ā e_a)`. -/
noncomputable def wA (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ))) (a : Fin (mb κ)) :
    Fin (mb κ) → ℤ := gInv κ (fun i => -Abar i a)

/-- The two halves of the `i`-th short vector. -/
noncomputable def svPair (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)))
    (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (i : Fin (m κ)) :
    (Fin (mb κ) → ℤ) × (Fin (mb κ) → ℤ) :=
  match colEquiv κ i with
  | Sum.inl a => (Pi.single a 1 + R *ᵥ wA κ Abar a, wA κ Abar a)
  | Sum.inr c => (R *ᵥ gk κ c, gk κ c)

/-- The `i`-th short vector of `Λ^⊥(B)`. -/
noncomputable def sv (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)))
    (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (i : Fin (m κ)) : Fin (m κ) → ℤ :=
  Sum.elim (svPair κ Abar R i).1 (svPair κ Abar R i).2 ∘ colEquiv κ

theorem cast_mulVec (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (f : Fin (mb κ) → ℤ) :
    (fun c => ((R *ᵥ f) c : ZMod (q κ))) =
      R.map (Int.cast : ℤ → ZMod (q κ)) *ᵥ fun c => (f c : ZMod (q κ)) := by
  funext c; simp [Matrix.mulVec, dotProduct]

theorem Bmat_mulVec_split (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)))
    (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (top bot : Fin (mb κ) → ℤ) :
    Bmat κ Abar R *ᵥ castV κ (Sum.elim top bot ∘ colEquiv κ) =
      Abar *ᵥ (fun c => (top c : ZMod (q κ))) +
        (gadget κ - Abar * R.map (Int.cast : ℤ → ZMod (q κ))) *ᵥ fun c => (bot c : ZMod (q κ)) := by
  have hx : castV κ (Sum.elim top bot ∘ colEquiv κ) =
      (Sum.elim (fun c => (top c : ZMod (q κ))) (fun c => (bot c : ZMod (q κ)))) ∘ colEquiv κ := by
    funext j
    simp only [castV, Function.comp_apply]
    cases colEquiv κ j <;> rfl
  rw [hx, Bmat, Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
  rw [Matrix.fromCols_mulVec_sumElim]

theorem sv_mem_kernel (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)))
    (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (i : Fin (m κ)) :
    Bmat κ Abar R *ᵥ castV κ (sv κ Abar R i) = 0 := by
  unfold sv
  rw [Bmat_mulVec_split]
  unfold svPair
  cases colEquiv κ i with
  | inl a =>
    simp only
    have h1 : (fun c => (((Pi.single a (1 : ℤ) + R *ᵥ wA κ Abar a : Fin (mb κ) → ℤ) c : ℤ) :
        ZMod (q κ))) =
        Pi.single a 1 + R.map (Int.cast : ℤ → ZMod (q κ)) *ᵥ fun c => (wA κ Abar a c : ZMod (q κ)) := by
      rw [← cast_mulVec]; funext c; simp [Pi.single_apply]
    rw [h1, Matrix.mulVec_add, Matrix.sub_mulVec, Matrix.mulVec_mulVec, wA, gadget_mulVec_gInv,
      Matrix.mulVec_single_one]
    funext r; simp
  | inr c =>
    simp only
    rw [cast_mulVec, Matrix.sub_mulVec, Matrix.mulVec_mulVec, gadget_gk]
    abel

theorem abs_gk_le (c c' : Fin (mb κ)) : |gk κ c c'| ≤ 2 := by
  unfold gk; split_ifs <;> simp

theorem abs_mulVec_le (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (hR : ∀ i j, |R i j| ≤ 1)
    (f : Fin (mb κ) → ℤ) (hf : ∀ c, |f c| ≤ 2) (a : Fin (mb κ)) : |(R *ᵥ f) a| ≤ 2 * mb κ := by
  simp only [Matrix.mulVec, dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ c, |R a c * f c| ≤ ∑ _c : Fin (mb κ), (2 : ℤ) := Finset.sum_le_sum fun c _ => by
        rw [abs_mul]
        calc |R a c| * |f c| ≤ 1 * 2 := mul_le_mul (hR a c) (hf c) (abs_nonneg _) (by norm_num)
          _ = 2 := by ring
    _ = 2 * mb κ := by simp; ring

/-- The bound on the entries of the short vectors. -/
def Lb : ℕ := 2 * mb κ + 2

theorem abs_sv_le (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)))
    (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (hR : ∀ i j, |R i j| ≤ 1) (i j : Fin (m κ)) :
    |sv κ Abar R i j| ≤ Lb κ := by
  have hw : ∀ a c, |wA κ Abar a c| ≤ 2 := fun a c => (abs_gInv_le κ _ c).trans (by norm_num)
  unfold sv svPair Lb
  push_cast
  simp only [Function.comp_apply]
  cases colEquiv κ i with
  | inl a =>
    cases colEquiv κ j with
    | inl b =>
      simp only [Sum.elim_inl, Pi.add_apply]
      refine (abs_add_le _ _).trans ?_
      have h1 : |(Pi.single a (1 : ℤ) : Fin (mb κ) → ℤ) b| ≤ 1 := by
        simp [Pi.single_apply]; split_ifs <;> simp
      have h2 := abs_mulVec_le κ R hR _ (hw a) b
      push_cast at h2
      linarith
    | inr b =>
      simp only [Sum.elim_inr]
      have : (0 : ℤ) ≤ (n κ : ℤ) * ((w κ : ℤ) + 1) := by positivity
      linarith [hw a b]
  | inr c =>
    cases colEquiv κ j with
    | inl b =>
      simp only [Sum.elim_inl]
      have h2 := abs_mulVec_le κ R hR _ (abs_gk_le κ c) b
      push_cast at h2
      linarith
    | inr b =>
      simp only [Sum.elim_inr]
      have : (0 : ℤ) ≤ (n κ : ℤ) * ((w κ : ℤ) + 1) := by positivity
      linarith [abs_gk_le κ c b]


/-! ### Independence -/

theorem sum_split (f : Fin (m κ) → ℝ) :
    ∑ j, f j = ∑ a, f ((colEquiv κ).symm (Sum.inl a)) + ∑ c, f ((colEquiv κ).symm (Sum.inr c)) := by
  rw [← (colEquiv κ).symm.sum_comp, Fintype.sum_sum_type]

theorem sum_row (f : Fin (mb κ) → ℝ) (c : Fin (mb κ)) :
    ∑ c', f c' * (gk κ c c' : ℝ) =
      ∑ t : Fin (w κ + 1), f (gIdx κ (gRow κ c) t) * (gk κ c (gIdx κ (gRow κ c) t) : ℝ) := by
  rw [← (finProdFinEquiv (m := n κ) (n := w κ + 1)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_eq_single (gRow κ c)]
  · rfl
  · intro r _ hr
    refine Finset.sum_eq_zero fun t _ => ?_
    have : gk κ c (finProdFinEquiv (r, t)) = 0 := by
      unfold gk
      rw [if_pos]
      show gRow κ (gIdx κ r t) ≠ gRow κ c
      rw [gRow_gIdx]; exact hr
    rw [this]; simp
  · simp

theorem gk_eq_on_row_lt (c : Fin (mb κ)) (ht : (gBit κ c : ℕ) < w κ) (t : Fin (w κ + 1)) :
    (gk κ c (gIdx κ (gRow κ c) t) : ℝ) =
      if t = gBit κ c then 2 else if (t : ℕ) = gBit κ c + 1 then -1 else 0 := by
  unfold gk
  simp only [gRow_gIdx, gBit_gIdx, ne_eq, not_true_eq_false, if_false, if_pos ht]
  split_ifs <;> simp

theorem gk_eq_on_row_top (c : Fin (mb κ)) (ht : ¬ (gBit κ c : ℕ) < w κ) (t : Fin (w κ + 1)) :
    (gk κ c (gIdx κ (gRow κ c) t) : ℝ) = if (q κ).testBit t then 1 else 0 := by
  unfold gk
  simp only [gRow_gIdx, gBit_gIdx, ne_eq, not_true_eq_false, if_false, if_neg ht]
  split_ifs <;> simp

theorem gk_on_row_lt (r : Fin (n κ)) (t0 : Fin (w κ + 1)) (ht : (t0 : ℕ) < w κ)
    (t : Fin (w κ + 1)) :
    (gk κ (gIdx κ r t0) (gIdx κ r t) : ℝ) =
      if t = t0 then 2 else if (t : ℕ) = t0 + 1 then -1 else 0 := by
  unfold gk
  simp only [gRow_gIdx, gBit_gIdx, ne_eq, not_true_eq_false, if_false, if_pos ht]
  split_ifs <;> simp

theorem gk_on_row_top (r : Fin (n κ)) (t0 : Fin (w κ + 1)) (ht : ¬ (t0 : ℕ) < w κ)
    (t : Fin (w κ + 1)) :
    (gk κ (gIdx κ r t0) (gIdx κ r t) : ℝ) = if (q κ).testBit t then 1 else 0 := by
  unfold gk
  simp only [gRow_gIdx, gBit_gIdx, ne_eq, not_true_eq_false, if_false, if_neg ht]
  split_ifs <;> simp

theorem gIdx_row_bit (c : Fin (mb κ)) : gIdx κ (gRow κ c) (gBit κ c) = c := by
  unfold gIdx gRow gBit; rw [Prod.mk.eta]; exact Equiv.apply_symm_apply _ _

theorem sum_two_terms (Y : Fin (w κ + 1) → ℝ) (t0 : Fin (w κ + 1)) (ht : (t0 : ℕ) < w κ) :
    ∑ t, Y t * (if t = t0 then (2 : ℝ) else if (t : ℕ) = t0 + 1 then -1 else 0) =
      2 * Y t0 - Y ⟨(t0 : ℕ) + 1, by omega⟩ := by
  set t1 : Fin (w κ + 1) := ⟨(t0 : ℕ) + 1, by omega⟩
  have hterm : ∀ t, Y t * (if t = t0 then (2 : ℝ) else if (t : ℕ) = t0 + 1 then -1 else 0) =
      (if t = t0 then 2 * Y t0 else 0) + (if t = t1 then -Y t1 else 0) := by
    intro t
    by_cases h0 : t = t0
    · have : t0 ≠ t1 := by intro h; have := congrArg Fin.val h; simp [t1] at this
      rw [h0]; simp [this]; ring
    · by_cases h1 : t = t1
      · rw [h1]
        have h1' : t1 ≠ t0 := by intro h; exact h0 (h1.trans h)
        have : (t1 : ℕ) = t0 + 1 := rfl
        simp [h1', this]
      · have : (t : ℕ) ≠ t0 + 1 := fun h => h1 (Fin.ext h)
        simp [h0, h1, this]
  rw [Finset.sum_congr rfl fun t _ => hterm t, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
  ring

theorem q_lt_two_pow : q κ < 2 ^ (w κ + 1) := by
  have h1 := q_le_two_pow κ
  have h2 := q_odd κ
  rcases h1.lt_or_eq with h | h
  · exact h
  · exfalso; rw [h, pow_succ] at h2; omega

/-- A vector orthogonal to the gadget kernel vectors is zero. -/
theorem gadget_orth (y : Fin (mb κ) → ℝ) (h : ∀ c, ∑ c', y c' * (gk κ c c' : ℝ) = 0) : y = 0 := by
  funext c0
  set r := gRow κ c0
  set Y : Fin (w κ + 1) → ℝ := fun t => y (gIdx κ r t)
  have hstep : ∀ t : ℕ, (ht : t < w κ) →
      Y ⟨t + 1, by omega⟩ = 2 * Y ⟨t, by omega⟩ := by
    intro t ht
    have h1 := h (gIdx κ r ⟨t, by omega⟩)
    rw [sum_row, gRow_gIdx] at h1
    simp only [gk_on_row_lt κ r ⟨t, by omega⟩ ht] at h1
    have := sum_two_terms κ Y ⟨t, by omega⟩ ht
    rw [this] at h1
    linarith
  have hpow : ∀ t : ℕ, (ht : t ≤ w κ) → Y ⟨t, by omega⟩ = 2 ^ t * Y ⟨0, by omega⟩ := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro ht
      rw [hstep t (by omega), ih (by omega), pow_succ]; ring
  have hpowF : ∀ t : Fin (w κ + 1), y (gIdx κ r t) = 2 ^ (t : ℕ) * y (gIdx κ r 0) :=
    fun t => hpow t.val (by omega)
  have htop := h (gIdx κ r ⟨w κ, by omega⟩)
  rw [sum_row, gRow_gIdx] at htop
  simp only [gk_on_row_top κ r ⟨w κ, by omega⟩ (by simp)] at htop
  have hq := sum_testBit_pow (q κ) (w κ + 1)
  rw [Nat.mod_eq_of_lt (q_lt_two_pow κ)] at hq
  have hqr : (∑ t : Fin (w κ + 1), (if (q κ).testBit t then (2 : ℝ) ^ (t : ℕ) else 0)) = q κ := by
    exact_mod_cast hq
  have hsum : ∑ t : Fin (w κ + 1), y (gIdx κ r t) * (if (q κ).testBit t then (1 : ℝ) else 0) =
      (q κ : ℝ) * y (gIdx κ r 0) := by
    calc ∑ t : Fin (w κ + 1), y (gIdx κ r t) * (if (q κ).testBit t then (1 : ℝ) else 0)
        = ∑ t : Fin (w κ + 1), (if (q κ).testBit t then (2 : ℝ) ^ (t : ℕ) else 0) *
            y (gIdx κ r 0) := Finset.sum_congr rfl fun t _ => by
          rw [hpowF t]; split_ifs <;> ring
      _ = _ := by rw [← Finset.sum_mul, hqr]
  rw [hsum] at htop
  have hq0 : (q κ : ℝ) ≠ 0 := (q_pos κ).ne'
  have hY0 : y (gIdx κ r 0) = 0 := by
    rcases mul_eq_zero.mp htop with h | h
    · exact absurd h hq0
    · exact h
  have := hpowF (gBit κ c0)
  rw [hY0, mul_zero, gIdx_row_bit] at this
  exact this

theorem sv_indep (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)))
    (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (d : Fin (m κ) → ℝ)
    (h : ∀ i, ∑ j, d j * (sv κ Abar R i j : ℝ) = 0) : d = 0 := by
  set d1 : Fin (mb κ) → ℝ := fun a => d ((colEquiv κ).symm (Sum.inl a))
  set d2 : Fin (mb κ) → ℝ := fun c => d ((colEquiv κ).symm (Sum.inr c))
  have hsplit : ∀ i, ∑ j, d j * (sv κ Abar R i j : ℝ) =
      ∑ a, d1 a * ((svPair κ Abar R i).1 a : ℝ) + ∑ c, d2 c * ((svPair κ Abar R i).2 c : ℝ) := by
    intro i
    rw [sum_split]
    simp [sv, d1, d2]
  set y : Fin (mb κ) → ℝ := fun c => ∑ a, d1 a * (R a c : ℝ) + d2 c
  have hmv : ∀ f : Fin (mb κ) → ℤ, ∑ a, d1 a * (((R *ᵥ f) a : ℤ) : ℝ) + ∑ c, d2 c * (f c : ℝ) =
      ∑ c, y c * (f c : ℝ) := by
    intro f
    simp only [y, Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Finset.mul_sum,
      add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  have hy : y = 0 := by
    apply gadget_orth κ y
    intro c
    have := h ((colEquiv κ).symm (Sum.inr c))
    rw [hsplit] at this
    simp only [svPair, Equiv.apply_symm_apply] at this
    rwa [hmv] at this
  have hd1 : d1 = 0 := by
    funext a
    have := h ((colEquiv κ).symm (Sum.inl a))
    rw [hsplit] at this
    simp only [svPair, Equiv.apply_symm_apply, Pi.add_apply, Int.cast_add, mul_add,
      Finset.sum_add_distrib] at this
    have h2 := hmv (wA κ Abar a)
    rw [hy] at h2
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at h2
    have h3 : ∑ a', d1 a' * (((Pi.single a (1 : ℤ) : Fin (mb κ) → ℤ) a' : ℤ) : ℝ) = d1 a := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb; simp [Pi.single_apply, hb]
      · simp
    simp only [Pi.zero_apply]
    linarith
  have hd2 : d2 = 0 := by
    funext c
    have := congrFun hy c
    simp only [y, hd1, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add] at this
    exact this
  funext j
  have hj : j = (colEquiv κ).symm (colEquiv κ j) := by simp
  rw [hj]
  cases colEquiv κ j with
  | inl a => exact congrFun hd1 a
  | inr c => exact congrFun hd2 c


/-! ### The dual mass -/

/-- `Σ ‖s_i‖² ≤ m · m · Lb²`. -/
noncomputable def S2 : ℝ := (m κ : ℝ) * (m κ * (Lb κ : ℝ) ^ 2)

theorem S2_pos : 0 < S2 κ := by
  unfold S2 Lb; have := m_pos κ; positivity

theorem dual_int (B : Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ))) (y : dualPerp B)
    (x : Fin (m κ) → ℤ) (hx : x ∈ kernel B) :
    ∃ k : ℤ, (k : ℝ) = ⟪(y : EuclideanSpace ℝ (Fin (m κ))), embed (m κ) x⟫ := by
  have := (LinearMap.BilinForm.mem_dualSubmodule _).mp y.2 (embed (m κ) x) ⟨x, hx, rfl⟩
  obtain ⟨k, hk⟩ := Submodule.mem_one.mp this
  exact ⟨k, by simpa using hk⟩

theorem inner_embed (y : EuclideanSpace ℝ (Fin (m κ))) (x : Fin (m κ) → ℤ) :
    ⟪y, embed (m κ) x⟫ = ∑ j, y j * (x j : ℝ) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [embed, mul_comm]

/-- The nonzero dual mass is at most the nonzero mass of `Z^m` at width `√S2 / τ`. -/
theorem dualMassE_le_wt1 (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)))
    (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (hR : ∀ i j, |R i j| ≤ 1) :
    dualMassE (Bmat κ Abar R) (τ κ) ≤
      ∑' u : Fin (m κ) → ℤ, wt1 (τ κ / Real.sqrt (S2 κ)) u := by
  set B := Bmat κ Abar R
  have hker : ∀ i, sv κ Abar R i ∈ kernel B := fun i => sv_mem_kernel κ Abar R i
  choose k hk using fun (y : dualPerp B) (i : Fin (m κ)) => dual_int κ B y _ (hker i)
  -- injectivity
  have hinj0 : ∀ y : dualPerp B, k y = 0 → y = 0 := by
    intro y hy
    have hd : (fun j => (y : EuclideanSpace ℝ (Fin (m κ))) j) = 0 := by
      apply sv_indep κ Abar R
      intro i
      rw [← inner_embed, ← hk y i, hy]; simp
    apply Subtype.ext
    ext j
    exact congrFun hd j
  have hinj : Function.Injective fun y : {y : dualPerp B // y ≠ 0} => k y.1 := by
    intro a b hab
    simp only at hab
    apply Subtype.ext
    have := hinj0 (a.1 - b.1) (by
      funext i
      have h1 := hk (a.1 - b.1) i
      have h2 := hk a.1 i
      have h3 := hk b.1 i
      rw [Submodule.coe_sub, inner_sub_left, ← h2, ← h3, congrFun hab i] at h1
      simp only [sub_self] at h1
      exact_mod_cast h1)
    exact sub_eq_zero.mp this
  have hnorm : ∀ i, ‖embed (m κ) (sv κ Abar R i)‖ ^ 2 ≤ m κ * (Lb κ : ℝ) ^ 2 := by
    intro i
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ j, ‖(embed (m κ) (sv κ Abar R i)) j‖ ^ 2 ≤ ∑ _j : Fin (m κ), (Lb κ : ℝ) ^ 2 :=
          Finset.sum_le_sum fun j _ => by
            have h := abs_sv_le κ Abar R hR i j
            have h' : |((sv κ Abar R i j : ℤ) : ℝ)| ≤ Lb κ := by exact_mod_cast h
            simp only [embed, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply, Real.norm_eq_abs,
              sq_abs]
            nlinarith [abs_nonneg ((sv κ Abar R i j : ℤ) : ℝ), sq_abs ((sv κ Abar R i j : ℤ) : ℝ)]
      _ = _ := by simp
  have hpt : ∀ y : {y : dualPerp B // y ≠ 0},
      ENNReal.ofReal (gaussianWeight (1 / τ κ) ((y.1 : dualPerp B) : EuclideanSpace ℝ (Fin (m κ)))) ≤
        wt1 (τ κ / Real.sqrt (S2 κ)) (k y.1) := by
    intro y
    have hk0 : k y.1 ≠ 0 := fun h => y.2 (hinj0 y.1 h)
    unfold wt1
    rw [if_neg hk0]
    apply ENNReal.ofReal_le_ofReal
    unfold gaussianWeight
    apply Real.exp_le_exp.mpr
    set v : EuclideanSpace ℝ (Fin (m κ)) := ((y.1 : dualPerp B) : EuclideanSpace ℝ (Fin (m κ)))
    have hks : ∑ i, ((k y.1 i : ℤ) : ℝ) ^ 2 ≤ S2 κ * ‖v‖ ^ 2 := by
      calc ∑ i, ((k y.1 i : ℤ) : ℝ) ^ 2 ≤ ∑ _i : Fin (m κ), ‖v‖ ^ 2 * (m κ * (Lb κ : ℝ) ^ 2) :=
            Finset.sum_le_sum fun i _ => by
              rw [hk y.1 i]
              have hcs := abs_real_inner_le_norm v (embed (m κ) (sv κ Abar R i))
              have hsq : ⟪v, embed (m κ) (sv κ Abar R i)⟫ ^ 2 ≤
                  (‖v‖ * ‖embed (m κ) (sv κ Abar R i)‖) ^ 2 := by
                rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hcs 2
              rw [mul_pow] at hsq
              exact hsq.trans (mul_le_mul_of_nonneg_left (hnorm i) (by positivity))
        _ = S2 κ * ‖v‖ ^ 2 := by simp [S2]; ring
    have hS := S2_pos κ
    have hτ := τ_pos κ
    have e1 : -Real.pi * ‖v‖ ^ 2 / (1 / τ κ) ^ 2 = -(Real.pi * τ κ ^ 2 * ‖v‖ ^ 2) := by
      field_simp
    have e2 : -(Real.pi * (τ κ / Real.sqrt (S2 κ)) ^ 2) * ∑ i, ((k y.1 i : ℤ) : ℝ) ^ 2 =
        -(Real.pi * τ κ ^ 2 * ((∑ i, ((k y.1 i : ℤ) : ℝ) ^ 2) / S2 κ)) := by
      rw [div_pow, Real.sq_sqrt hS.le]; ring
    rw [e1, e2, neg_le_neg_iff]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_le_iff₀ hS]; linarith
  calc dualMassE B (τ κ)
      = ∑' y : {y : dualPerp B // y ≠ 0}, ENNReal.ofReal
          (gaussianWeight (1 / τ κ) ((y.1 : dualPerp B) : EuclideanSpace ℝ (Fin (m κ)))) := rfl
    _ ≤ ∑' y : {y : dualPerp B // y ≠ 0}, wt1 (τ κ / Real.sqrt (S2 κ)) (k y.1) :=
        ENNReal.tsum_le_tsum hpt
    _ ≤ _ := tsum_comp_le_tsum_of_injective hinj _


/-- The smoothing condition `e^{−π τ²/S2} ≤ 1/(12 m)`. -/
def SmoothCond : Prop := Real.exp (-(Real.pi * (τ κ / Real.sqrt (S2 κ)) ^ 2)) ≤ 1 / (12 * m κ)

theorem dualMassE_le_half (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)))
    (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (hR : ∀ i j, |R i j| ≤ 1) (hc : SmoothCond κ) :
    dualMassE (Bmat κ Abar R) (τ κ) ≤ 1 / 2 := by
  refine (dualMassE_le_wt1 κ Abar R hR).trans ?_
  set x := Real.pi * (τ κ / Real.sqrt (S2 κ)) ^ 2
  set r := Real.exp (-x)
  have hm : (4 : ℝ) ≤ m κ := by exact_mod_cast m_ge_four κ
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hrm : 12 * r * m κ ≤ 1 := by
    have := hc; unfold SmoothCond at this
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hr : r ≤ 1 / 4 := by nlinarith
  have hA : ∑' k : ℤ, g1 x k ≤ ENNReal.ofReal (1 + 3 * r) := by
    refine le_trans (tsum_g1_le_large (by positivity)) ?_
    rw [geom_eq hr0 (by linarith)]
    exact ENNReal.ofReal_le_ofReal (ratio_le hr0 hr)
  have hZ := tsum_wt1_add_one (m := m κ) (τ κ / Real.sqrt (S2 κ))
  have hpow : (1 + 3 * r) ^ m κ ≤ 1 + 2 * (3 * r * m κ) :=
    one_add_pow_le (by positivity) (m κ) (by nlinarith)
  have h2 : ∑' u : Fin (m κ) → ℤ, wt1 (τ κ / Real.sqrt (S2 κ)) u + 1 ≤ ENNReal.ofReal (1 / 2) + 1 := by
    rw [hZ, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    calc (∑' k : ℤ, g1 x k) ^ m κ ≤ ENNReal.ofReal (1 + 3 * r) ^ m κ := by gcongr
      _ = ENNReal.ofReal ((1 + 3 * r) ^ m κ) := (ENNReal.ofReal_pow (by positivity) _).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  rw [half_ennreal]
  exact ENNReal.le_of_add_le_add_right ENNReal.one_ne_top h2

theorem smoothCond_eventually : ∀ᶠ κ in Filter.atTop, SmoothCond κ := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 10 (by norm_num : (1 : ℝ) < 4)
  have ht1 := (Filter.tendsto_add_atTop_iff_nat 1).mpr ht
  filter_upwards [ht1.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 ^ 26 by norm_num))]
    with κ hκ
  unfold SmoothCond
  have hS := S2_pos κ
  have hm := m_le_real κ
  have hm0 : (1 : ℝ) ≤ m κ := by exact_mod_cast m_pos κ
  set c : ℝ := (κ : ℝ) + 1
  have hc1 : 1 ≤ c := by simp only [c]; linarith [(Nat.cast_nonneg κ : (0 : ℝ) ≤ κ)]
  have hLb : (Lb κ : ℝ) ≤ 20 * c ^ 2 := by
    have : (Lb κ : ℝ) = m κ + 2 := by
      unfold Lb; rw [m_eq_mb κ]; push_cast; ring
    rw [this]; nlinarith
  have hX : 2 ^ 24 * c ^ 10 ≤ (4 : ℝ) ^ κ := by
    have : c ^ 10 / 4 ^ (κ + 1) < 1 / 2 ^ 26 := by
      simpa [c, Nat.cast_add, Nat.cast_one] using hκ
    rw [div_lt_div_iff₀ (by positivity) (by positivity)] at this
    have h4 : (4 : ℝ) ^ (κ + 1) = 4 ^ κ * 4 := pow_succ 4 κ
    rw [h4] at this
    nlinarith
  -- `x = π τ² / S2 ≥ 12 m`
  have hτ2 : τ κ ^ 2 = 64 * 4 ^ κ := by
    unfold τ; rw [← pow_mul, show (κ + 3) * 2 = 2 * κ + 6 by ring, pow_add, pow_mul]; norm_num; ring
  have hS2 : S2 κ ≤ (18 * c ^ 2) ^ 2 * (20 * c ^ 2) ^ 2 := by
    unfold S2
    have h1 : (m κ : ℝ) * (m κ : ℝ) ≤ (18 * c ^ 2) ^ 2 := by
      rw [← sq]; exact pow_le_pow_left₀ (by positivity) hm 2
    have h2 : (Lb κ : ℝ) ^ 2 ≤ (20 * c ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hLb 2
    calc (m κ : ℝ) * (m κ * (Lb κ : ℝ) ^ 2) = ((m κ : ℝ) * m κ) * (Lb κ : ℝ) ^ 2 := by ring
      _ ≤ _ := mul_le_mul h1 h2 (by positivity) (by positivity)
  have hx : 12 * (m κ : ℝ) ≤ Real.pi * (τ κ / Real.sqrt (S2 κ)) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hS.le, hτ2, mul_div_assoc', le_div_iff₀ hS]
    have hpi := Real.pi_gt_three
    calc 12 * (m κ : ℝ) * S2 κ ≤ 12 * (18 * c ^ 2) * ((18 * c ^ 2) ^ 2 * (20 * c ^ 2) ^ 2) :=
          mul_le_mul (by linarith) hS2 hS.le (by positivity)
      _ = 27993600 * c ^ 10 := by ring
      _ ≤ 3 * (64 * 4 ^ κ) := by linarith [pow_nonneg (by linarith : (0 : ℝ) ≤ c) 10]
      _ ≤ Real.pi * (64 * 4 ^ κ) := by gcongr
  have hx0 : 0 < Real.pi * (τ κ / Real.sqrt (S2 κ)) ^ 2 := by
    have := τ_pos κ; positivity
  have hexp := Real.add_one_le_exp (Real.pi * (τ κ / Real.sqrt (S2 κ)) ^ 2)
  calc Real.exp (-(Real.pi * (τ κ / Real.sqrt (S2 κ)) ^ 2))
      ≤ 1 / (1 + Real.pi * (τ κ / Real.sqrt (S2 κ)) ^ 2) := by
        rw [Real.exp_neg, inv_eq_one_div]
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
    _ ≤ 1 / (12 * m κ) := one_div_le_one_div_of_le (by positivity) (by linarith)

end

end SigabaNeo.Lattices.Trapdoor.Family


