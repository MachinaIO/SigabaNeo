module

public import SigabaNeo.Lib.Lattices.Research.Wall1.FreshDisplacement
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Rat

public section

namespace SigabaNeo.Wall1.LayerCount

open scoped Classical

variable {V : Type*} [AddCommGroup V] (L : AddSubgroup V) (H : AddSubgroup (V ⧸ L))

/-- Integer multiplication on the finite subgroup, valued in the ambient quotient. -/
def layerMap (k : ℤ) : H →+ V ⧸ L where
  toFun h := k • (h : V ⧸ L)
  map_zero' := by simp
  map_add' := by simp

/-- Averaging the size of a coset layer over a uniform displacement in H. -/
theorem averaged_layer_count [Fintype H] (k : ℤ) (S : Finset V) :
    (∑ h : H, ((S.filter fun x ↦ k • (h : V ⧸ L) = (QuotientAddGroup.mk x : V ⧸ L)).card : ℚ)) / Fintype.card H =
    ((S.filter fun x ↦ (QuotientAddGroup.mk x : V ⧸ L) ∈ (layerMap L H k).range).card : ℚ) /
      Nat.card (layerMap L H k).range := by
  let φ := layerMap L H k
  have hf (x : V) : (∑ h : H, if φ h = (QuotientAddGroup.mk x : V ⧸ L) then (1 : ℚ) else 0) =
      if (QuotientAddGroup.mk x : V ⧸ L) ∈ φ.range then (Nat.card φ.ker : ℚ) else 0 := by
    rw [Finset.sum_boole]
    split_ifs with hx
    · rw [← FreshDisplacement.fiber_card φ _ hx]
      congr 2
      ext h
      simp
    · have hn (h : H) : φ h ≠ (QuotientAddGroup.mk x : V ⧸ L) := fun he ↦ hx ⟨h, he⟩
      simp [hn]
  change (∑ h : H, ((S.filter fun x ↦ φ h = (QuotientAddGroup.mk x : V ⧸ L)).card : ℚ)) / _ = _ / _
  simp_rw [Finset.natCast_card_filter]
  rw [Finset.sum_comm]
  simp_rw [hf]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    Finset.sum_boole]
  rw [← Nat.card_eq_fintype_card, ← AddSubgroup.card_ker_mul_card_range φ, Nat.cast_mul]
  change _ / _ = _ / (Nat.card φ.range : ℚ)
  have hk : (Nat.card φ.ker : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [mul_comm (Nat.card φ.ker : ℚ), mul_div_mul_right _ _ hk]

#print axioms averaged_layer_count

end SigabaNeo.Wall1.LayerCount
