import SigabaNeo.Lib.Lattices.Prob
import CslibFrontier.Probability.StatisticalDistance.CloseTo
import CslibFrontier.Probability.StatisticalDistance.TotalVariation
import CslibFrontier.Probability.StatisticalDistance.Product
import CslibFrontier.Probability.Product

/-!
# Statistical closeness

* `closeTo_bind_good`: continuations that are `ε`-close outside a bad event of probability `δ`
  give `ε + δ`-close results.
* `closeTo_shift`: shifting a uniform `t ∈ {0, …, N−1}` by an integer `c` moves it by at most
  `|c| / N` in statistical distance.
* `closeTo_shift_vec`: the same for independent uniform coordinates reduced mod `q`, with the sum of
  the shifts.
-/

namespace SigabaNeo.Lattices

open Cslib.Probability SigabaNeo.Lattices
open scoped ENNReal Cslib.Probability.PMF

section
variable {α β : Type}

theorem toOuterMeasure_eq_ev (p : PMF α) (E : Set α) :
    p.toOuterMeasure E = ev p (fun a => ind (a ∈ E)) := by
  classical
  rw [PMF.toOuterMeasure_apply]
  unfold ev
  refine tsum_congr fun a => ?_
  unfold ind; simp only [Set.indicator_apply]; split_ifs <;> simp

theorem toOuterMeasure_le_one (p : PMF α) (E : Set α) : p.toOuterMeasure E ≤ 1 := by
  rw [toOuterMeasure_eq_ev]; exact ev_le_const _ fun _ => ind_le_one _

/-- Close continuations outside a bad event. -/
theorem closeTo_bind_good (μ : PMF α) (f g : α → PMF β) (good : α → Prop) {ε : ℝ≥0∞}
    (h : ∀ a ∈ μ.support, good a → CloseTo (f a) (g a) ε) :
    CloseTo (μ.bind f) (μ.bind g) (ε + ev μ fun a => ind (¬ good a)) := by
  intro E
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  have h1 : (∑' a, μ a * (f a).toOuterMeasure E) = ev μ fun a => (f a).toOuterMeasure E := rfl
  have h2 : (∑' a, μ a * (g a).toOuterMeasure E) = ev μ fun a => (g a).toOuterMeasure E := rfl
  rw [h1, h2]
  calc ev μ (fun a => (f a).toOuterMeasure E)
      ≤ ev μ (fun a => ((g a).toOuterMeasure E + ε) + ind (¬ good a)) := by
        refine ev_mono_supp _ fun a ha => ?_
        by_cases hg : good a
        · exact (h a ha hg E).trans le_self_add
        · rw [ind_of hg]
          exact (toOuterMeasure_le_one _ _).trans le_add_self
    _ = ev μ (fun a => (g a).toOuterMeasure E) + ε + ev μ fun a => ind (¬ good a) := by
        rw [ev_add, ev_add, ev_const]
    _ ≤ _ := by rw [add_assoc]

end

/-! ### Shifts of uniform intervals -/

theorem sum_fin_shift (N : ℕ) (c : ℤ) (f : ℤ → ℝ≥0∞) :
    ∑ t : Fin N, f ((t : ℤ) - c) = ∑ x ∈ Finset.Ico (-c) (N - c), f x := by
  refine Finset.sum_bij' (fun t _ => (t : ℤ) - c)
    (fun x hx => ⟨(x + c).toNat, by
      have := Finset.mem_Ico.mp hx; omega⟩) (fun t _ => ?_) (fun x _ => Finset.mem_univ _)
    (fun t _ => ?_) (fun x hx => ?_) (fun t _ => rfl)
  · rw [Finset.mem_Ico]; have := t.isLt; omega
  · ext; simp
  · have := Finset.mem_Ico.mp hx; simp only; omega

theorem card_Ico_sdiff_le (N : ℕ) (c : ℤ) :
    (Finset.Ico (-c) (N - c) \ Finset.Ico 0 (N : ℤ)).card ≤ c.natAbs := by
  have h := Finset.card_sdiff_add_card_inter (Finset.Ico (-c) (N - c)) (Finset.Ico 0 (N : ℤ))
  rw [Finset.Ico_inter_Ico, Int.card_Ico, Int.card_Ico] at h
  omega

theorem sum_shift_le (N : ℕ) (c : ℤ) (f : ℤ → ℝ≥0∞) (hf : ∀ x, f x ≤ 1) :
    ∑ t : Fin N, f ((t : ℤ) - c) ≤ (∑ t : Fin N, f t) + c.natAbs := by
  classical
  have h0 := sum_fin_shift N 0 f
  simp only [sub_zero, neg_zero] at h0
  rw [sum_fin_shift, h0, ← Finset.sum_inter_add_sum_sdiff (Finset.Ico (-c) (N - c))
    (Finset.Ico 0 (N : ℤ))]
  gcongr
  · intro x hx
    exact (Finset.mem_inter.mp hx).2
  · refine (Finset.sum_le_sum (fun x _ => hf x)).trans ?_
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast card_Ico_sdiff_le N c

/-- Shifting a uniform `t < N` by `c`. -/
theorem closeTo_shift (N : ℕ) [NeZero N] (c : ℤ) :
    CloseTo ((PMF.uniformOfFintype (Fin N)).map fun t : Fin N => ((t : ℕ) : ℤ) - c)
      ((PMF.uniformOfFintype (Fin N)).map fun t : Fin N => ((t : ℕ) : ℤ)) (c.natAbs / N) := by
  classical
  intro E
  rw [toOuterMeasure_eq_ev, toOuterMeasure_eq_ev]
  simp only [ev_map]
  rw [ev_uniform, ev_uniform, Fintype.card_fin]
  have h := sum_shift_le N c (fun x => ind (x ∈ E)) fun _ => ind_le_one _
  calc (∑ t : Fin N, ((fun x => ind (x ∈ E)) ∘ fun t : Fin N => (t : ℤ) - c) t) / N
      ≤ ((∑ t : Fin N, ind ((t : ℤ) ∈ E)) + c.natAbs) / N := by
        gcongr; exact h
    _ = _ := by rw [ENNReal.add_div]; rfl

/-! ### Vectors -/

section
variable {Q : ℕ} [NeZero Q]

theorem dist_shift_zmod (N : ℕ) [NeZero N] (c : ℤ) :
    dist ((PMF.uniformOfFintype (Fin N)).map fun t : Fin N => ((t : ℕ) : ZMod Q) - (c : ZMod Q))
      ((PMF.uniformOfFintype (Fin N)).map fun t : Fin N => ((t : ℕ) : ZMod Q)) ≤ c.natAbs / N := by
  have h := (closeTo_shift N c).map (fun x : ℤ => (x : ZMod Q))
  rw [PMF.map_comp, PMF.map_comp] at h
  have he1 : ((fun x : ℤ => (x : ZMod Q)) ∘ fun t : Fin N => ((t : ℕ) : ℤ) - c) =
      fun t : Fin N => ((t : ℕ) : ZMod Q) - (c : ZMod Q) := by funext t; simp
  have he2 : ((fun x : ℤ => (x : ZMod Q)) ∘ fun t : Fin N => ((t : ℕ) : ℤ)) =
      fun t : Fin N => ((t : ℕ) : ZMod Q) := by funext t; simp
  rw [he1, he2] at h
  have hc : ((c.natAbs : ℝ≥0∞) / N) = ENNReal.ofReal (c.natAbs / N) := by
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast NeZero.pos N), ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast]
  rw [hc] at h
  exact (closeTo_ofReal_iff_dist_le (by positivity)).mp h

/-- Independent uniform coordinates, each shifted by `c j` and reduced mod `q`. -/
theorem dist_shift_vec (N k : ℕ) [NeZero N] (c : Fin k → ℤ) :
    dist ((PMF.uniformOfFintype (Fin k → Fin N)).map
        fun T j => ((T j : ℕ) : ZMod Q) - (c j : ZMod Q))
      ((PMF.uniformOfFintype (Fin k → Fin N)).map fun T j => ((T j : ℕ) : ZMod Q)) ≤
      ∑ j, ((c j).natAbs : ℝ) / N := by
  rw [← PMF.pi_uniformOfFintype,
    ← PMF.pi_map (fun _ => PMF.uniformOfFintype (Fin N)) (fun j (t : Fin N) =>
      ((t : ℕ) : ZMod Q) - (c j : ZMod Q)),
    ← PMF.pi_map (fun _ => PMF.uniformOfFintype (Fin N)) (fun _ (t : Fin N) => ((t : ℕ) : ZMod Q))]
  exact (PMF.dist_pi_le_sum _ _).trans
    (Finset.sum_le_sum fun j _ => dist_shift_zmod (Q := Q) N (c j))

end

/-! ### Matrices and products -/

theorem card_matrix {q : ℕ} [NeZero q] (r c : ℕ) :
    Fintype.card (Matrix (Fin r) (Fin c) (ZMod q)) = q ^ (r * c) := by
  show Fintype.card (Fin r → Fin c → ZMod q) = _
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  rw [← pow_mul, mul_comm]

theorem ev_point {α : Type*} (p : PMF α) (a : α) : ev p (fun x => ind (x = a)) = p a := by
  unfold ev
  rw [tsum_eq_single a]
  · simp [ind]
  · intro b hb; simp [ind, hb]

theorem sampleList_pi {α β : Type} [Inhabited α] [Finite β] (d : PMF α) (f : α → β) :
    ∀ k, (sampleList d k).map (fun l (j : Fin k) => f (l.getD j default)) =
      PMF.pi (fun _ : Fin k => d.map f)
  | 0 => by
    ext x
    rw [PMF.pi_apply]
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    unfold sampleList
    rw [PMF.pure_map, PMF.pure_apply, if_pos (Subsingleton.elim _ _)]
  | k + 1 => by
    rw [PMF.pi_fin_succ, ← sampleList_pi d f k, PMF.bind_map]
    show ((d.bind fun a => (sampleList d k).map (a :: ·)).map _) = _
    rw [PMF.map_bind]
    congr 1; funext a
    simp only [Function.comp_apply]
    rw [PMF.map_comp]
    have hcomp : ((fun l (j : Fin (k + 1)) => f (l.getD j default)) ∘ fun x => a :: x) =
        Fin.cons (f a) ∘ (fun l (j : Fin k) => f (l.getD j default)) := by
      funext l j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · simp
    rw [hcomp, PMF.map_comp]

end SigabaNeo.Lattices
