module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

public section

namespace SigabaNeo.Wall1.FiniteRankLaw

open scoped Classical
open Finset

variable {q m n t : ℕ} [Fact q.Prime]
local notation "Mat" m "," n => Matrix (Fin m) (Fin n) (ZMod q)

private theorem matrixCard : Fintype.card (Mat m,n) = q ^ (m * n) := by
  rw [← Nat.card_eq_fintype_card, Matrix.card_matrix]
  simp [Nat.card_eq_fintype_card, Nat.mul_comm]

theorem mul_surjective (F : Mat n,t) (hF : F.rank = t) :
    Function.Surjective (fun A : Mat m,n ↦ A * F) := by
  have hd := F.mulVecLin.finrank_range_add_finrank_ker
  change F.rank + _ = _ at hd
  simp [hF] at hd
  obtain ⟨g, hg⟩ := F.toLin'.exists_leftInverse_of_injective hd
  have hg' := congrArg LinearMap.toMatrix' hg
  simp [LinearMap.toMatrix'_comp] at hg'
  intro B
  exact ⟨B * g.toMatrix', by simp only [Matrix.mul_assoc, hg', Matrix.mul_one]⟩

private theorem factor (F : Mat n,t) (hF : F.rank = t) :
    q ^ (m * n) = q ^ (m * t) * q ^ (m * (n - t)) := by
  have h := F.rank_le_height
  rw [hF] at h
  rw [← pow_add, ← Nat.mul_add, Nat.add_sub_of_le h]

theorem card_mul_fiber (F : Mat n,t) (hF : F.rank = t) (B : Mat m,t) :
    (univ.filter fun A : Mat m,n ↦ A * F = B).card = q ^ (m * (n - t)) := by
  let f : (Mat m,n) →+ (Mat m,t) := Matrix.addMonoidHomMulRight F
  have hs := mul_surjective (m := m) F hF
  have he (C : Mat m,t) := AddMonoidHom.card_fiber_eq_of_mem_range f (hs C) (hs B)
  have h := card_eq_sum_card_fiberwise (s := (univ : Finset (Mat m,n)))
    (t := univ) (f := f) (by simp)
  simp only [he, sum_const, card_univ, smul_eq_mul, matrixCard] at h
  rw [factor (m := m) F hF] at h
  exact (Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : q.Prime).pos _) h).symm

theorem card_fullRank (ht : t ≤ m) :
    (univ.filter fun B : Mat m,t ↦ B.rank = t).card = ∏ i : Fin t, (q ^ m - q ^ i.val) := by
  have hi (B : Mat m,t) : B.rank = t ↔ LinearIndependent (ZMod q) B.col := by
    rw [linearIndependent_iff_card_eq_finrank_span, Matrix.rank_eq_finrank_span_cols]
    simp [Set.finrank, eq_comm]
  let e : {B : Mat m,t // B.rank = t} ≃
      {v : Fin t → Fin m → ZMod q // LinearIndependent (ZMod q) v} :=
    { toFun := fun B ↦ ⟨B.val.col, (hi _).mp B.property⟩
      invFun := fun v ↦ ⟨fun a b ↦ v.val b a, (hi _).mpr v.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, Nat.card_congr e,
    card_linearIndependent (by simpa using ht)]
  simp

theorem prob_mul_fullRank (F : Mat n,t) (hF : F.rank = t) (ht : t ≤ m) :
    ((univ.filter fun A : Mat m,n ↦ (A * F).rank = t).card : ℚ) /
        (univ : Finset (Mat m,n)).card =
      ∏ i : Fin t, (1 - (q : ℚ) ^ i.val / (q : ℚ) ^ m) := by
  have h := sum_card_fiberwise_eq_card_filter (univ : Finset (Mat m,n))
    (univ.filter fun B : Mat m,t ↦ B.rank = t) (fun A ↦ A * F)
  simp [card_mul_fiber F hF, card_fullRank ht] at h
  rw [← h, card_univ, matrixCard, factor (m := m) F hF]
  push_cast
  have hq : (q : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hd : (q : ℚ) ^ (m * (n - t)) ≠ 0 := pow_ne_zero _ hq
  have hp : (∏ _ : Fin t, (q : ℚ) ^ m) = ((q : ℚ) ^ m) ^ t := by simp
  rw [mul_div_mul_right _ _ hd, pow_mul, ← hp]
  simp only [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [Nat.cast_sub (Nat.pow_le_pow_right (Fact.out : q.Prime).pos (i.isLt.le.trans ht))]
  push_cast
  field_simp

#print axioms mul_surjective
#print axioms card_mul_fiber
#print axioms card_fullRank
#print axioms prob_mul_fullRank

end SigabaNeo.Wall1.FiniteRankLaw
