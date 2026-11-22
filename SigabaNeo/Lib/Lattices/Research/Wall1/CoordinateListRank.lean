module

public import SigabaNeo.Lib.Lattices.Research.Wall1.CoordinateListMoment
import all SigabaNeo.Lib.Lattices.Research.Wall1.CoordinateListMoment

public section
namespace SigabaNeo.Wall1.CoordinateList

open Finset Matrix
open scoped Classical
variable {q r k j : ℕ} [Fact q.Prime]

/-- With no deletions, the retained-secret discrepancy has weight q⁻ʳ when nonzero.
A pure error discrepancy has weight zero, and simultaneous zero discrepancies have weight one. -/
theorem rankWeight_zero (x : Vec r q) (y : Vec k q) :
    rankWeight 0 x y = if y ≠ 0 then 1 / (q : ℚ)^r else if x = 0 then 1 else 0 := by
  have hr (D : Mat r 0 q) : D.rank = 0 := Nat.le_zero.mp D.rank_le_width
  simp [rankWeight, hr, avg_const]

/-- Rank-distribution form of both expectations in Theorem 5. Each term uses the number of
deleted matrices of that rank, divided by the total number of deleted matrices. -/
theorem average_by_rank (q r j : ℕ) [Fact q.Prime] (f : ℕ → ℚ) :
    avg (fun D : Mat r j q ↦ f D.rank) =
      (∑ t ∈ range (min r j + 1),
        ((univ.filter fun D : Mat r j q ↦ D.rank = t).card : ℚ) * f t) / (q : ℚ)^(r*j) := by
  have hm (D : Mat r j q) (_ : D ∈ univ) : D.rank ∈ range (min r j + 1) :=
    mem_range.mpr (Nat.lt_succ_of_le (le_min D.rank_le_height D.rank_le_width))
  rw [avg, ← sum_fiberwise_of_maps_to hm]
  congr 1
  · apply sum_congr rfl
    intro t ht
    rw [sum_congr rfl (fun D hD ↦ congrArg f (mem_filter.mp hD).2), sum_const, nsmul_eq_mul]
  · change ((Fintype.card (Fin r → Fin j → ZMod q) : ℕ) : ℚ) = _
    simp [← pow_mul, Nat.mul_comm]

/-- The exact probability of full column rank when the deleted matrix is not wide. -/
theorem fullRank_probability (hjr : j ≤ r) :
    avg (fun D : Mat r j q ↦ if D.rank = j then 1 else 0) =
    (∏ i : Fin j, (q ^ r - q ^ i.val : ℕ) : ℕ) / (q : ℚ)^(r*j) := by
  rw [avg, ← sum_filter, sum_const, nsmul_one, FiniteRankLaw.card_fullRank hjr]
  congr 1
  change ((Fintype.card (Fin r → Fin j → ZMod q) : ℕ) : ℚ) = _
  simp [← pow_mul, Nat.mul_comm]

/-- Selecting distinct rows and columns of one uniform design gives a uniform smaller matrix.
This is a marginal statement, so different selections need not be disjoint. -/
theorem submatrix_average {m n : ℕ} (rows : Fin r ↪ Fin m) (cols : Fin j ↪ Fin n)
    (f : Mat r j q → ℚ) :
    avg (fun A : Mat m n q ↦ f (A.submatrix rows cols)) = avg f := by
  let g : Mat m n q →+ Mat r j q := ⟨⟨fun A ↦ A.submatrix rows cols, rfl⟩, fun _ _ ↦ rfl⟩
  have surj : Function.Surjective g := by
    intro D
    refine ⟨Function.extend rows (fun i ↦ Function.extend cols (D i) 0) 0, ?_⟩
    ext i j
    change Function.extend rows (fun a ↦ Function.extend cols (D a) 0) 0 (rows i) (cols j) = D i j
    rw [rows.injective.extend_apply, cols.injective.extend_apply]
  let k := (univ.filter fun A : Mat m n q ↦ g A = 0).card
  have fiber (D : Mat r j q) : (univ.filter fun A : Mat m n q ↦ g A = D).card = k :=
    AddMonoidHom.card_fiber_eq_of_mem_range g (surj D) (surj 0)
  have hk : k ≠ 0 := card_ne_zero.mpr ⟨0, mem_filter.mpr ⟨mem_univ _, g.map_zero⟩⟩
  have total := card_eq_sum_card_fiberwise (s := (univ : Finset (Mat m n q))) (t := univ)
    (f := g) (fun _ _ ↦ mem_univ _)
  simp only [fiber, sum_const, smul_eq_mul, card_univ] at total
  have hs : ∑ A, f (g A) = ∑ D : Mat r j q, (k : ℚ) * f D := by
    rw [← sum_fiberwise_of_maps_to (fun A (_ : A ∈ univ) ↦ mem_univ (g A))]
    apply sum_congr rfl
    intro D _
    rw [sum_congr rfl (fun A hA ↦ congrArg f (mem_filter.mp hA).2), sum_const,
      nsmul_eq_mul, fiber]
  change (∑ A, f (g A)) / (Fintype.card (Mat m n q) : ℚ) = _
  rw [hs, ← mul_sum, total, Nat.cast_mul]
  unfold avg
  field_simp [hk]

/-- Projective-kernel-line union bound, including wide matrices and zero deleted columns. -/
theorem rankDefect_probability (q r j : ℕ) [Fact q.Prime] :
    avg (fun D : Mat r j q ↦ if D.rank ≠ j then 1 else 0) ≤
      ((q : ℚ)^j - 1) / ((q - 1) * q^r) := by
  let U := (univ : Finset (Vec j q)).erase 0
  let M := Mat r j q
  let K (D : M) := U.filter fun w ↦ D *ᵥ w = 0
  have hK (D : M) : (K D).card = q^(j-D.rank) - 1 := by
    have he : K D = (univ.filter fun w ↦ D *ᵥ w = 0).erase 0 := by
      ext w; simp [K, U, and_comm]
    rw [he, card_erase_of_mem (by simp), ← Fintype.card_subtype]
    rw [Fintype.card_congr (show {w // D *ᵥ w = 0} ≃ LinearMap.ker D.mulVecLin from
      ⟨fun w ↦ ⟨w.val, w.property⟩, fun w ↦ ⟨w.val, w.property⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩)]
    have h := D.mulVecLin.finrank_range_add_finrank_ker
    change D.rank + _ = _ at h
    simp only [Module.finrank_pi, Fintype.card_fin] at h
    rw [Module.card_eq_pow_finrank (K := ZMod q), ZMod.card]
    congr 2
    omega
  let bad := univ.filter fun D : M ↦ D.rank ≠ j
  have hq := (Fact.out : q.Prime).one_lt
  have lo : bad.card * (q-1) ≤ ∑ D, (K D).card := by
    calc _ = ∑ _ ∈ bad, (q-1) := by simp
         _ ≤ ∑ D ∈ bad, (K D).card := sum_le_sum fun D hD ↦ by
           have hne := (mem_filter.mp hD).2
           have hle := D.rank_le_width
           rw [hK]
           exact Nat.sub_le_sub_right (by
             calc q = q^1 := (pow_one q).symm
                  _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)) _
         _ ≤ _ := sum_le_univ_sum_of_nonneg fun _ ↦ Nat.zero_le _
  have hh := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := (univ : Finset M)) (t := U) (fun D w ↦ D *ᵥ w = 0)
  change (∑ D, (K D).card) = _ at hh
  have he : (∑ D, (K D).card) * q^r = (q^j - 1) * Fintype.card M := by
    rw [hh, sum_mul]
    simp only [bipartiteBelow]
    have h (w) (hw : w ∈ U) := eval_card (r := r) (ne_of_mem_erase hw) (0 : Vec r q)
    rw [sum_congr rfl h, sum_const, smul_eq_mul]
    simp [U, M]
  have hn := (Nat.mul_le_mul_right (q^r) lo).trans_eq he
  have hnat : 1 ≤ q^j := Nat.one_le_pow _ _ (by omega)
  have hrat : (bad.card : ℚ) * ((q : ℚ) - 1) * (q : ℚ)^r ≤
      ((q : ℚ)^j - 1) * (Fintype.card M : ℚ) := by
    have hcast := (Nat.cast_le (α := ℚ)).mpr hn
    push_cast [Nat.cast_sub hnat, Nat.cast_sub hq.le] at hcast
    exact hcast
  have hq' : (1 : ℚ) < q := by exact_mod_cast hq
  have hd : 0 < ((q : ℚ)-1) * (q : ℚ)^r := by positivity
  rw [avg, ← sum_filter, sum_const, nsmul_one, div_le_div_iff₀ (by positivity) hd]
  change (bad.card : ℚ) * _ ≤ _
  linarith only [hrat]

end SigabaNeo.Wall1.CoordinateList

#print axioms SigabaNeo.Wall1.CoordinateList.rankWeight_zero
#print axioms SigabaNeo.Wall1.CoordinateList.submatrix_average
#print axioms SigabaNeo.Wall1.CoordinateList.average_by_rank
#print axioms SigabaNeo.Wall1.CoordinateList.fullRank_probability
#print axioms SigabaNeo.Wall1.CoordinateList.rankDefect_probability
