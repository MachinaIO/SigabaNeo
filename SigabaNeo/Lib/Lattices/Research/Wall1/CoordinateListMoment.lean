module

public import SigabaNeo.Lib.Lattices.Research.Wall1.QaryMembership
public import SigabaNeo.Lib.Lattices.Research.Wall1.FiniteRankLaw
public import SigabaNeo.Lib.Lattices.Attacks.Primal.SampleDeletion
import all SigabaNeo.Lib.Lattices.Research.Wall1.QaryMembership

/-! Part 137, Theorem 5. Split the design into independent uniform kept and deleted columns.
All averages are exact rational finite sums, conditional on the plant. -/

public section
namespace SigabaNeo.Wall1.CoordinateList

open Finset Matrix SigabaNeo.Planted
open scoped Classical

abbrev Mat (r k q : ℕ) := QaryMembership.Design r k q
abbrev Vec (k q : ℕ) := Fin k → ZMod q
abbrev Point (r k : ℕ) := Coord r k → ℤ

def height {r k : ℕ} (z : Point r k) := z (.inr (.inr ()))

noncomputable def avg {α : Type*} [Fintype α] (f : α → ℚ) : ℚ := (∑ a, f a) / Fintype.card α

theorem avg_const {α : Type*} [Fintype α] [Nonempty α] (c : ℚ) :
    avg (fun _ : α ↦ c) = c := by
  simp [avg, Fintype.card_ne_zero]

theorem avg_sum {α β : Type*} [Fintype α] (S : Finset β) (f : α → β → ℚ) :
    avg (fun a ↦ ∑ b ∈ S, f a b) = ∑ b ∈ S, avg (fun a ↦ f a b) := by
  simp only [avg, sum_comm (s := (univ : Finset α)) (t := S), sum_div]

variable {q r k j : ℕ} [Fact q.Prime]

/-- Counting form of uniform evaluation on a nonzero vector of residues. -/
theorem eval_card {y : Vec k q} (hy : y ≠ 0) (b : Vec r q) :
    (univ.filter fun A : Mat r k q ↦ A *ᵥ y = b).card * q ^ r = Fintype.card (Mat r k q) := by
  let z : QaryMembership.Point r k := (fun i ↦ -(b i).val, fun i ↦ (y i).val)
  have hs : QaryMembership.reduce q z.2 = y := by ext i; simp [z, QaryMembership.reduce]
  have he : -QaryMembership.reduce q z.1 = b := by ext i; simp [z, QaryMembership.reduce]
  have h := QaryMembership.kernel_fixed z (hs ▸ hy)
  rw [← card_univ, ← h]
  congr 2
  ext A
  simp only [QaryMembership.designs, QaryMembership.kernel, mem_filter, mem_univ, true_and, hs, he]

private theorem range_card (D : Mat r j q) :
    (univ.filter fun x ↦ x ∈ LinearMap.range D.mulVecLin).card = q ^ D.rank := by
  rw [← Fintype.card_subtype, Module.card_eq_pow_finrank (K := ZMod q), ZMod.card]
  rfl

/-- The column space of the deleted matrix absorbs the discrepancy on the retained rows. -/
def incidence (D : Mat r j q) (A : Mat r k q) (x : Vec r q) (y : Vec k q) : Prop :=
  x + A *ᵥ y ∈ LinearMap.range D.mulVecLin

private theorem incidence_kept (D : Mat r j q) (x : Vec r q) {y : Vec k q} (hy : y ≠ 0) :
    avg (fun A : Mat r k q ↦ if incidence D A x y then 1 else 0) =
      (q : ℚ) ^ D.rank / q ^ r := by
  let S := univ.filter fun u ↦ u ∈ LinearMap.range D.mulVecLin
  have h (u : Vec r q) :
      (univ.filter fun A : Mat r k q ↦ x + A *ᵥ y = u).card * q^r = Fintype.card (Mat r k q) := by
    simpa only [add_comm x, ← eq_sub_iff_add_eq] using eval_card hy (u - x)
  have hf := sum_card_fiberwise_eq_card_filter (univ : Finset (Mat r k q)) S
    (fun A ↦ x + A *ᵥ y)
  have hc : (univ.filter fun A : Mat r k q ↦ incidence D A x y).card * q^r =
      q ^ D.rank * Fintype.card (Mat r k q) := by
    have hs : univ.filter (fun A : Mat r k q ↦ incidence D A x y) =
        univ.filter (fun A : Mat r k q ↦ x + A *ᵥ y ∈ S) := by
      ext A; rw [mem_filter, mem_filter]; simp only [S, mem_filter, mem_univ, true_and, incidence]
    rw [hs, ← hf, sum_mul]
    simp only [h, sum_const, smul_eq_mul, show S.card = q^D.rank from range_card D]
  have hq : (q : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  rw [avg, ← sum_filter, sum_const, nsmul_one, div_eq_div_iff (by simp [Fintype.card_ne_zero])
    (pow_ne_zero _ hq)]
  exact_mod_cast hc

private theorem move_vector {x u : Vec r q} (hx : x ≠ 0) (hu : u ≠ 0) :
    ∃ g : Vec r q ≃ₗ[ZMod q] Vec r q, g x = u := by
  let a := LinearEquiv.toSpanNonzeroSingleton (ZMod q) _ x hx
  let b := LinearEquiv.toSpanNonzeroSingleton (ZMod q) _ u hu
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq (a.symm.trans b)
  have h := hg (a 1)
  simpa [a, b] using (show ∃ g : Vec r q ≃ₗ[ZMod q] Vec r q, g (a 1) = b 1 from
    ⟨g, by simpa using h.symm⟩)

private theorem range_hits_eq {x u : Vec r q} (hx : x ≠ 0) (hu : u ≠ 0) :
    (univ.filter fun D : Mat r j q ↦ x ∈ LinearMap.range D.mulVecLin).card =
    (univ.filter fun D : Mat r j q ↦ u ∈ LinearMap.range D.mulVecLin).card := by
  obtain ⟨g, hg⟩ := move_vector hx hu
  let act (g : Vec r q ≃ₗ[ZMod q] Vec r q) (D : Mat r j q) :=
    (g.toLinearMap.comp D.mulVecLin).toMatrix'
  have ha (g : Vec r q ≃ₗ[ZMod q] Vec r q) (D : Mat r j q) :
      (act g D).mulVecLin = g.toLinearMap.comp D.mulVecLin := Matrix.toLin'.apply_symm_apply _
  refine card_bij' (fun D _ ↦ act g D) (fun D _ ↦ act g.symm D) ?_ ?_ ?_ ?_
  · intro D hD
    obtain ⟨w, hw⟩ := (mem_filter.mp hD).2
    exact mem_filter.mpr ⟨mem_univ _, w, by rw [ha]; exact (congrArg g hw).trans hg⟩
  · intro D hD
    obtain ⟨w, hw⟩ := (mem_filter.mp hD).2
    exact mem_filter.mpr ⟨mem_univ _, w, by rw [ha]; simp [hw, ← hg]⟩
  · intro D _
    apply Matrix.toLin'.injective
    change (act g.symm (act g D)).mulVecLin = D.mulVecLin
    rw [ha, ha]; ext1 w; simp
  · intro D _
    apply Matrix.toLin'.injective
    change (act g (act g.symm D)).mulVecLin = D.mulVecLin
    rw [ha, ha]; ext1 w; simp

private theorem incidence_deleted {x : Vec r q} (hx : x ≠ 0) :
    avg (fun D : Mat r j q ↦ if x ∈ LinearMap.range D.mulVecLin then 1 else 0) =
    avg (fun D : Mat r j q ↦ ((q : ℚ)^D.rank - 1) / (q^r - 1)) := by
  let U := (univ : Finset (Vec r q)).erase 0
  have hU : U.card = q^r - 1 := by simp [U]
  have hpos : 1 < q^r := by
    have hp := card_pos.mpr (show U.Nonempty from ⟨x, by simp [U, hx]⟩)
    omega
  have hD (D : Mat r j q) :
      (U.filter fun u ↦ u ∈ LinearMap.range D.mulVecLin).card = q ^ D.rank - 1 := by
    rw [show U.filter (fun u ↦ u ∈ LinearMap.range D.mulVecLin) =
        (univ.filter fun u ↦ u ∈ LinearMap.range D.mulVecLin).erase 0 by ext; simp [U, and_comm],
      card_erase_of_mem (mem_filter.mpr ⟨mem_univ _, Submodule.zero_mem _⟩), range_card]
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := (univ : Finset (Mat r j q))) (t := U) (fun D u ↦ u ∈ LinearMap.range D.mulVecLin)
  have hh (u) (hu : u ∈ U) := range_hits_eq (j := j) (ne_of_mem_erase hu) hx
  simp only [bipartiteAbove, bipartiteBelow] at h
  rw [sum_congr rfl (fun D _ ↦ hD D), sum_congr rfl hh, sum_const, smul_eq_mul, hU] at h
  have hq : 0 < q := (Fact.out : q.Prime).pos
  have hc := congrArg (Nat.cast : ℕ → ℚ) h
  push_cast [Nat.one_le_pow _ _ hq, hpos.le] at hc
  simp only [avg, ← sum_filter, sum_const, nsmul_one, ← sum_div]
  congr 1
  apply (eq_div_iff (sub_ne_zero.mpr (by exact_mod_cast hpos.ne' : (q : ℚ)^r ≠ 1))).mpr
  linarith

/-- The three audited rank weights, with the expectation over the uniform deleted matrix. -/
noncomputable def rankWeight (j : ℕ) (x : Vec r q) (y : Vec k q) : ℚ :=
  if y ≠ 0 then avg (fun D : Mat r j q ↦ (q : ℚ)^D.rank / q^r)
  else if x = 0 then 1 else avg (fun D : Mat r j q ↦ ((q : ℚ)^D.rank - 1) / (q^r - 1))

/-- Theorem 5, per-vector membership probability for any number of deleted columns. -/
theorem incidence_probability (x : Vec r q) (y : Vec k q) :
    avg (fun D : Mat r j q ↦ avg (fun A : Mat r k q ↦ if incidence D A x y then 1 else 0)) =
      rankWeight j x y := by
  by_cases hy : y ≠ 0
  · simp [rankWeight, hy, incidence_kept]
  · have hy0 := not_ne_iff.mp hy
    subst y
    by_cases hx : x = 0
    · simp [rankWeight, hx, incidence, avg_const]
    · simpa [rankWeight, hx, incidence, avg_const] using incidence_deleted (j := j) hx

def errDiff (q : ℕ) (e : Fin r → ℤ) (z : Point r k) : Vec r q :=
  fun i ↦ ((z (.inl i) - height z * e i : ℤ) : ZMod q)

def secDiff (q : ℕ) (s : Fin k → ℤ) (z : Point r k) : Vec k q :=
  fun i ↦ ((z (.inr (.inl i)) - height z * s i : ℤ) : ZMod q)

/-- Theorem 5 for any finite integer window. Use `integerBall R` for all nonzero points, or
filter that ball by height and erase the signed plants for the competitor first moment. -/
theorem expected_count (e : Fin r → ℤ) (s : Fin k → ℤ) (S : Finset (Point r k)) :
    avg (fun D : Mat r j q ↦ avg (fun A : Mat r k q ↦
      ((S.filter fun z ↦ incidence D A (errDiff q e z) (secDiff q s z)).card : ℚ))) =
    ∑ z ∈ S, rankWeight j (errDiff q e z) (secDiff q s z) := by
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    avg_sum, incidence_probability]

end SigabaNeo.Wall1.CoordinateList

#print axioms SigabaNeo.Wall1.CoordinateList.eval_card
#print axioms SigabaNeo.Wall1.CoordinateList.incidence_probability
#print axioms SigabaNeo.Wall1.CoordinateList.expected_count
