module

public import SigabaNeo.Lib.Lattices.Research.Wall1.FreshDisplacement
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Rat.Defs

public section

namespace SigabaNeo.Wall1.CoprimeMark

open scoped Classical

variable {H : Type*} [AddCommGroup H]

/-- The height mark on the displacement group. -/
abbrev mark (H : Type*) [AddCommGroup H] (j : ℤ) : H →+ H :=
  j • AddMonoidHom.id H

theorem normalization [Finite H] (j : ℤ) :
    Nat.card (mark H j).range * Nat.card (mark H j).ker = Nat.card H := by
  rw [Nat.mul_comm, AddSubgroup.card_ker_mul_card_range]

theorem fiber_coset (j : ℤ) {x t : H} (ht : j • t = x) :
    {h : H | j • h = x} = (fun k : H ↦ t + k) '' (mark H j).ker := by
  ext h
  constructor
  · intro hh
    exact ⟨h - t, show j • (h - t) = 0 by rw [zsmul_sub, ht, show j • h = x from hh, sub_self],
      by simp [add_comm t]⟩
  · rintro ⟨k, hk, rfl⟩
    change j • (t + k) = x
    rw [zsmul_add, ht, show j • k = 0 from hk, add_zero]

theorem fiber_size [Fintype H] (j : ℤ) (x : H) (hx : x ∈ (mark H j).range) :
    (Finset.univ.filter fun h : H ↦ j • h = x).card = Nat.card (mark H j).ker :=
  FreshDisplacement.fiber_card (mark H j) x hx

variable {j : ℤ} {q : ℕ}

theorem inverse_mod (hc : j.gcd q = 1) : j.gcdA q * j ≡ 1 [ZMOD (q : ℤ)] := by
  apply Int.modEq_iff_dvd.mpr
  refine ⟨j.gcdB q, ?_⟩
  have e := Int.gcd_eq_gcd_ab j q
  rw [hc, Nat.cast_one, mul_comm j] at e
  omega

variable (hq : ∀ h : H, q • h = 0) (hc : j.gcd q = 1)
include hq hc

private theorem cancel_mark (x : H) : j.gcdA q • (j • x) = x := by
  obtain ⟨b, hb⟩ := Int.modEq_iff_dvd.mp (inverse_mod hc)
  have he : j.gcdA q * j + b * (q : ℤ) = 1 := by rw [mul_comm b]; omega
  have e := congrArg (fun n : ℤ ↦ n • x) he
  simpa [add_zsmul, mul_smul, hq] using e

theorem mark_bijective : Function.Bijective (fun h : H ↦ j • h) := by
  refine ⟨Function.LeftInverse.injective (g := fun x : H ↦ j.gcdA q • x) (cancel_mark hq hc), fun x ↦ ⟨j.gcdA q • x, ?_⟩⟩
  change j • (j.gcdA q • x) = x
  rw [smul_comm]
  exact cancel_mark hq hc x

theorem solution_iff (x h : H) : j • h = x ↔ h = j.gcdA q • x := by
  constructor
  · rintro rfl
    exact (cancel_mark hq hc h).symm
  · rintro rfl
    rw [smul_comm]
    exact cancel_mark hq hc x

theorem unique_solution (x : H) : ∃! h : H, j • h = x := by
  exact ⟨_, (solution_iff hq hc x _).2 rfl, fun h ↦ (solution_iff hq hc x h).1⟩

/-- Probability under normalized counting measure on H. -/
theorem uniform_mass [Fintype H] (x : H) :
    ((Finset.univ.filter fun h : H ↦ j • h = x).card : ℚ) / Fintype.card H =
      1 / Fintype.card H := by
  have fiber : (Finset.univ.filter fun h : H ↦ j • h = x) = {j.gcdA q • x} := by
    ext h
    simp [solution_iff hq hc x]
  simp [fiber]

#print axioms normalization
#print axioms fiber_coset
#print axioms fiber_size
#print axioms inverse_mod
#print axioms mark_bijective
#print axioms solution_iff
#print axioms unique_solution
#print axioms uniform_mass

end SigabaNeo.Wall1.CoprimeMark
