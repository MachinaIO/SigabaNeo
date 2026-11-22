module

public import Mathlib.InformationTheory.Hamming
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Tactic.NormNum

public section

namespace SigabaNeo.Wall1.SubsetCollision

open scoped BigOperators

/-- The binary vectors witnessing a collision also certify its exact squared length. -/
theorem subsetSumCollision {U : Type*} [AddCommGroup U] [Fintype U] {f : ℕ}
    (v : Fin f → U) (h : Fintype.card U < 2 ^ f) :
    ∃ (z : Fin f → ℤ) (a b : Fin f → Bool), a ≠ b ∧
      (∀ i, z i = (a i).toInt - (b i).toInt) ∧ z ≠ 0 ∧
      (∀ i, z i = -1 ∨ z i = 0 ∨ z i = 1) ∧
      (∑ i, z i • v i) = 0 ∧ (∑ i, z i ^ 2) = (hammingDist a b : ℤ) ∧
      (∑ i, z i ^ 2) ≤ f := by
  classical
  let S (a : Fin f → Bool) := ∑ i, (a i).toInt • v i
  obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt S (by simpa using h)
  let z (i : Fin f) := (a i).toInt - (b i).toInt
  have hd : (∑ i, z i ^ 2) = (hammingDist a b : ℤ) := by
    calc
      _ = ∑ i, (if a i ≠ b i then (1 : ℤ) else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [z]
        cases a i <;> cases b i <;> decide
      _ = _ := by simp [hammingDist, Finset.sum_ite]
  refine ⟨z, a, b, hab, fun _ ↦ rfl, ?_, ?_, ?_, hd, ?_⟩
  · intro hz
    apply hab
    funext i
    have hi : (a i).toInt - (b i).toInt = 0 := congrFun hz i
    revert hi
    cases a i <;> cases b i <;> decide
  · intro i
    dsimp only [z]
    cases a i <;> cases b i <;> decide
  · simpa only [z, sub_zsmul, ← sub_eq_add_neg, Finset.sum_sub_distrib, S, sub_eq_zero] using heq
  · rw [hd]
    exact_mod_cast (show hammingDist a b ≤ f by simpa using (hammingDist_le_card_fintype (x := a) (y := b)))

/-- A collision modulo the subgroup yields a short signed sum in the subgroup. -/
theorem subgroupCollision {V : Type*} [AddCommGroup V] (B G : AddSubgroup V) (_hGB : G ≤ B)
    [Fintype (B ⧸ G.comap B.subtype)] {N f : ℕ} (hN : Fintype.card (B ⧸ G.comap B.subtype) ≤ N)
    (w : Fin f → B) (hf : N < 2 ^ f) :
    ∃ z : Fin f → ℤ, z ≠ 0 ∧ (∀ i, z i = -1 ∨ z i = 0 ∨ z i = 1) ∧
      (∑ i, z i • (w i : V)) ∈ G ∧ (∑ i, z i ^ 2) ≤ f := by
  let π := QuotientAddGroup.mk' (G.comap B.subtype)
  obtain ⟨z, _, _, _, _, hn, ht, hs, _, hl⟩ :=
    subsetSumCollision (fun i ↦ π (w i)) (hN.trans_lt hf)
  have hm : π (∑ i, z i • w i) = 0 := by simpa only [map_sum, map_zsmul] using hs
  have hg := (QuotientAddGroup.eq_zero_iff _).mp hm
  refine ⟨z, hn, ht, ?_, hl⟩
  change B.subtype (∑ i, z i • w i) ∈ G at hg
  simpa using hg

#print axioms subsetSumCollision
#print axioms subgroupCollision

end SigabaNeo.Wall1.SubsetCollision
