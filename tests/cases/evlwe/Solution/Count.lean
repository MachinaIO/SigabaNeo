import SigabaNeoStd.Lattices.Stat
import SigabaNeoStd.Lattices.Prob
import Solution.RandSide
import SigabaNeoStd.Lattices.Gaussian.Smooth

/-!
# Uniform matrices

* `ev_uniform_balanced`: a balanced map (every shift of its values is realized by a permutation)
  pushes the uniform distribution to the uniform one.
* `ev_not_surj_le`: a uniform `B ∈ Z_q^{n×m}` has a nonzero left kernel vector with probability at
  most `q^n / q^m`; otherwise every `u` has a preimage (`surj_of_ker`).
* `ev_zero_col_le`: a uniform `P ∈ Z_q^{n×k}` has a zero column with probability at most `k / q^n`.
* `ev_badT_le`: some entry of a uniform `T ∈ {0, …, h}^{1×k}` is in a set of size `b` with
  probability at most `k b / (h + 1)`.
-/

namespace TestCase.EvLWE

open SigabaNeo.Lattices

open TestCase TestCase.EvLWE Cslib.Probability
open scoped ENNReal Matrix

section
variable {α G : Type*} [Fintype α] [Nonempty α] [Fintype G] [AddCommGroup G] [DecidableEq G]

theorem ev_uniform_balanced (φ : α → G) (hφ : ∀ δ : G, ∃ e : α ≃ α, ∀ x, φ (e x) = φ x + δ)
    (S : Finset G) :
    ev (PMF.uniformOfFintype α) (fun a => ind (φ a ∈ S)) =
      (S.card : ℝ≥0∞) / Fintype.card G := by
  classical
  rw [ev_uniform_ind]
  have h := sum_balanced φ hφ (fun g => if g ∈ S then 1 else 0)
  have h1 : ∑ x, (if φ x ∈ S then 1 else 0) = (Finset.univ.filter fun a => φ a ∈ S).card := by
    rw [Finset.card_filter]
  have h2 : ∑ g : G, (if g ∈ S then 1 else 0) = S.card := by
    rw [← Finset.card_filter]; congr 1; ext g; simp
  rw [h1, h2] at h
  have hG : (Fintype.card G : ℝ≥0∞) ≠ 0 := by
    have : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨0⟩
    exact_mod_cast this.ne'
  have hα : (Fintype.card α : ℝ≥0∞) ≠ 0 := by
    have : 0 < Fintype.card α := Fintype.card_pos
    exact_mod_cast this.ne'
  rw [ENNReal.div_eq_div_iff hG (ENNReal.natCast_ne_top _) hα (ENNReal.natCast_ne_top _)]
  exact_mod_cast h

end

section
variable {n m : ℕ} {q : ℕ} [Fact q.Prime]

/-- If the left kernel of `B` is trivial, every `u` has a preimage. -/
theorem surj_of_ker (B : Matrix (Fin n) (Fin m) (ZMod q)) (hB : ∀ y, y ᵥ* B = 0 → y = 0)
    (u : Fin n → ZMod q) : ∃ x, B *ᵥ x = u := by
  obtain ⟨y, hy⟩ := rowspace_field Bᵀ u fun x hx => by
    have : x ᵥ* B = 0 := by rw [← Matrix.mulVec_transpose]; exact hx
    rw [hB x this, dotProduct_zero]
  exact ⟨y, by rw [← Matrix.vecMul_transpose]; exact hy⟩

theorem card_not_surj_le :
    (Finset.univ.filter fun B : Matrix (Fin n) (Fin m) (ZMod q) => ∃ y ≠ 0, y ᵥ* B = 0).card *
      q ^ m ≤ q ^ n * q ^ (n * m) := by
  classical
  have hsub : (Finset.univ.filter fun B : Matrix (Fin n) (Fin m) (ZMod q) => ∃ y ≠ 0, y ᵥ* B = 0)
      ⊆ (Finset.univ.filter fun y : Fin n → ZMod q => y ≠ 0).biUnion fun y =>
        Finset.univ.filter fun B => y ᵥ* B = 0 := by
    intro B hB
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB
    obtain ⟨y, hy0, hy⟩ := hB
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨y, hy0, hy⟩
  have hK := ZMod.card q
  calc _ ≤ ((Finset.univ.filter fun y : Fin n → ZMod q => y ≠ 0).biUnion fun y =>
          Finset.univ.filter fun B : Matrix (Fin n) (Fin m) (ZMod q) => y ᵥ* B = 0).card * q ^ m :=
        Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ ≤ (∑ y ∈ Finset.univ.filter fun y : Fin n → ZMod q => y ≠ 0,
          (Finset.univ.filter fun B : Matrix (Fin n) (Fin m) (ZMod q) => y ᵥ* B = 0).card) *
          q ^ m := Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = (Finset.univ.filter fun y : Fin n → ZMod q => y ≠ 0).card * q ^ (n * m) := by
        have hc : ∀ y ∈ Finset.univ.filter fun y : Fin n → ZMod q => y ≠ 0,
            (Finset.univ.filter fun B : Matrix (Fin n) (Fin m) (ZMod q) => y ᵥ* B = 0).card *
              q ^ m = q ^ (n * m) := fun y hy => by
          have := card_vecMul_field (K := ZMod q) (n := n) (m := m) y (Finset.mem_filter.mp hy).2 0
          rwa [hK] at this
        rw [Finset.sum_mul, Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul]
    _ ≤ q ^ n * q ^ (n * m) := by
        apply Nat.mul_le_mul_right
        refine (Finset.card_filter_le _ _).trans ?_
        simp [Fintype.card_pi]

theorem ev_not_surj_le :
    ev (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q)))
      (fun B => ind (∃ y ≠ 0, y ᵥ* B = 0)) ≤ (q ^ n : ℝ≥0∞) / (q ^ m : ℝ≥0∞) := by
  classical
  rw [ev_uniform_ind, card_matrix]
  have h := card_not_surj_le (n := n) (m := m) (q := q)
  have hq : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hqt : (q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  set A := (Finset.univ.filter fun B : Matrix (Fin n) (Fin m) (ZMod q) => ∃ y ≠ 0, y ᵥ* B = 0).card
  have h' : (A : ℝ≥0∞) * (q : ℝ≥0∞) ^ m ≤ (q : ℝ≥0∞) ^ n * (q : ℝ≥0∞) ^ (n * m) := by
    exact_mod_cast h
  push_cast
  calc (A : ℝ≥0∞) / (q : ℝ≥0∞) ^ (n * m)
      = (A * (q : ℝ≥0∞) ^ m) / ((q : ℝ≥0∞) ^ (n * m) * (q : ℝ≥0∞) ^ m) :=
        (ENNReal.mul_div_mul_right _ _ (pow_ne_zero _ hq) (ENNReal.pow_ne_top hqt)).symm
    _ ≤ ((q : ℝ≥0∞) ^ n * (q : ℝ≥0∞) ^ (n * m)) / ((q : ℝ≥0∞) ^ (n * m) * (q : ℝ≥0∞) ^ m) := by
        gcongr
    _ = (q : ℝ≥0∞) ^ n / (q : ℝ≥0∞) ^ m := by
        rw [mul_comm ((q : ℝ≥0∞) ^ (n * m))]
        exact ENNReal.mul_div_mul_right _ _ (pow_ne_zero _ hq) (ENNReal.pow_ne_top hqt)

theorem ev_zero_col_le (k : ℕ) :
    ev (PMF.uniformOfFintype (Matrix (Fin n) (Fin k) (ZMod q)))
      (fun P => ind (∃ j ∈ Finset.univ, (fun i => P i j) = 0)) ≤
        (k : ℝ≥0∞) * (1 / (q ^ n : ℝ≥0∞)) := by
  classical
  refine (ev_ind_exists_le _ _ _).trans ?_
  rw [Finset.sum_congr rfl fun j _ => ?_, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have := ev_uniform_balanced (α := Matrix (Fin n) (Fin k) (ZMod q)) (fun P i => P i j) ?_ {0}
  · simp only [Finset.mem_singleton, Finset.card_singleton, Nat.cast_one] at this
    rw [this, Fintype.card_fun, Fintype.card_fin, ZMod.card]; push_cast; rfl
  · intro δ
    refine ⟨Equiv.addRight (Matrix.of fun i j' => if j' = j then δ i else 0), fun P => ?_⟩
    funext i; simp

end

section
variable {κ : ℕ}

/-- Some entry of a uniform `T` lands in `bad`, `|bad| ≤ b`. -/
theorem ev_badT_le (bad : Finset (Fin ((q κ - 1) / 2 + 1))) :
    ev (PMF.uniformOfFintype (Matrix (Fin (ell κ)) (Fin (k κ)) (Fin ((q κ - 1) / 2 + 1))))
      (fun T => ind (∃ j ∈ Finset.univ, T (i0 κ) j ∈ bad)) ≤
        (k κ : ℝ≥0∞) * (bad.card / ((q κ - 1) / 2 + 1 : ℕ)) := by
  classical
  refine (ev_ind_exists_le _ _ _).trans ?_
  rw [Finset.sum_congr rfl fun j _ => ?_, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have := ev_uniform_balanced
    (α := Matrix (Fin (ell κ)) (Fin (k κ)) (Fin ((q κ - 1) / 2 + 1))) (fun T => T (i0 κ) j) ?_ bad
  · rw [this, Fintype.card_fin]
  · intro δ
    refine ⟨Equiv.addRight (Matrix.of fun _ j' => if j' = j then δ else 0), fun T => ?_⟩
    simp

end

end TestCase.EvLWE
