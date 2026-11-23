import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonGramChart

/-! Feasibility of the orbit representatives. The integer encoding covers every Gram test. -/

namespace SigabaNeo.Wall1.Watson.Pivot

open Matrix

private def decode (i : Fin 5) : ℤ := (i.val : ℤ) - 2

private def boxCheck (k : Fin 24) : Prop :=
  (∀ i, |centers k i| ≤ 4) ∧ ∀ a b c d e : Fin 5,
    let z : Z := ![decode a,decode b,decode c,decode d,decode e]
    smallTest z → 0 < sqSum z → 0 ≤ slackInt (centers k) z

private instance (k : Fin 24) : Decidable (boxCheck k) := by unfold boxCheck; infer_instance

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 32768 in
private theorem feasibleChecks (k : Fin 24) : boxCheck k := by
  fin_cases k <;> decide +kernel

theorem center_mem (k : Fin 24) : gramVertex k ∈ gramPolytope := by
  rw [← chart_center]
  refine ⟨⟨⟨fun i j ↦ ?_,?_⟩,fun i ↦ ?_⟩,fun z hn ht ↦ ?_⟩
  · rw [chart_apply]
    split_ifs
    · constructor <;> norm_num
    · have h := abs_le.mp ((feasibleChecks k).1 (edgeIndex i j))
      have lo : (-4 : ℝ) ≤ (centers k (edgeIndex i j) : ℝ) := by exact_mod_cast h.1
      have hi : (centers k (edgeIndex i j) : ℝ) ≤ 4 := by exact_mod_cast h.2
      constructor <;> dsimp [lift] <;> linarith
  · ext i j
    simp only [conjTranspose_apply,star_trivial,chart_apply]
    fin_cases i <;> fin_cases j <;> rfl
  · simp [chart_apply]
  · have small (i : I) : |z i| ≤ 2 := by
      rcases ht with h | ⟨j,h,hh⟩
      · exact (h i).trans (by decide)
      · by_cases he : i = j
        · simpa [he] using h.le
        · exact (hh i he).trans_le (by decide)
    let enc (i : I) : Fin 5 := ⟨(z i + 2).toNat, by have := abs_le.mp (small i); omega⟩
    have dec (i : I) : decode (enc i) = z i := by
      have := abs_le.mp (small i)
      dsimp [decode,enc]
      omega
    have vec : ![decode (enc 0),decode (enc 1),decode (enc 2),decode (enc 3),decode (enc 4)] = z := by
      funext i
      fin_cases i <;> apply dec
    have pos : 0 < sqSum z := by
      obtain ⟨i,hi⟩ := Function.ne_iff.mp hn
      change z i ≠ 0 at hi
      have positive := (sq_pos_of_ne_zero hi).trans_le
        (Finset.single_le_sum (s := Finset.univ) (f := fun j ↦ (z j)^2)
          (fun j _ ↦ sq_nonneg (z j)) (Finset.mem_univ i))
      simpa [sqSum,Fin.sum_univ_succ,add_assoc] using positive
    have h := (feasibleChecks k).2 (enc 0) (enc 1) (enc 2) (enc 3) (enc 4)
    dsimp only at h
    rw [vec] at h
    have bound := h ht pos
    have cast : (0:ℝ) ≤ (slackInt (centers k) z : ℝ) := by exact_mod_cast bound
    simp only [slackInt,Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_sub,Int.cast_one,dot_cast] at cast
    linarith [chart_energy (lift (centers k)) z]

end SigabaNeo.Wall1.Watson.Pivot

#print axioms SigabaNeo.Wall1.Watson.Pivot.center_mem
