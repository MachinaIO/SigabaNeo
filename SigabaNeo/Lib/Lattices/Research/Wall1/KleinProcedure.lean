module

public import SigabaNeo.Lib.Lattices.Research.Wall1.StatDistance
public import SigabaNeo.Lib.Lattices.Research.Wall1.DiscreteGaussianTail

/-! # Sequential Klein sampling on a q-ary lattice (Part 141, §§2 and 5) -/

@[expose] public section

namespace SigabaNeo.Wall1

open Function Matrix

noncomputable section

variable {r t : ℕ}

/-- Mass at the emitted integer in a draw from the coset c + qℤ. -/
def cosetDraw (s : ℝ) (q c h : ℤ) : ℝ :=
  if h ≡ c [ZMOD q] then gs s h / thetaQ s q c else 0

theorem cosetDraw_nonneg {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : q ≠ 0) (c h : ℤ) :
    0 ≤ cosetDraw s q c h := by
  unfold cosetDraw
  split_ifs
  · exact div_nonneg (gs_pos _ _).le (thetaQ_pos hs (Int.cast_ne_zero.mpr hq) _).le
  · exact le_rfl

theorem cosetDraw_hasSum {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : q ≠ 0) (c : ℤ) :
    HasSum (cosetDraw s q c) 1 := by
  let f (k : ℤ) := q*k + c
  have hf : Injective f := fun _ _ h ↦ mul_left_cancel₀ hq (add_right_cancel h)
  refine (hf.hasSum_iff (f := cosetDraw s q c) (fun h hh ↦ ?_)).mp ?_
  · have hn : ¬h ≡ c [ZMOD q] := fun hc ↦ by
      obtain ⟨k, hk⟩ := hc.symm.dvd
      exact hh ⟨k, by dsimp [f]; omega⟩
    simp [cosetDraw, hn]
  · have hm (k : ℤ) : f k ≡ c [ZMOD q] := Int.modEq_iff_dvd.mpr ⟨-k, by dsimp [f]; ring⟩
    have hq' : (q : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hq
    simpa [Function.comp_def, cosetDraw, hm, f, (thetaQ_pos hs hq' c).ne'] using
      (hasSum_coset hs hq' c).div_const (thetaQ s q c)

/-- The two one-dimensional sampling kernels. The head kernel takes the integer centre Muᵢ. -/
structure KleinDraws where
  tail : ℤ → ℝ
  head : ℤ → ℤ → ℝ
  tail_nonneg : ∀ k, 0 ≤ tail k
  head_nonneg : ∀ c k, 0 ≤ head c k
  tail_hasSum : HasSum tail 1
  head_hasSum : ∀ c, HasSum (head c) 1

/-- The ideal kernels in the sequential procedure. -/
def exactKleinDraws {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : q ≠ 0) : KleinDraws where
  tail := dg1 s 0
  head := cosetDraw s q
  tail_nonneg := dg1_nonneg hs 0
  head_nonneg := cosetDraw_nonneg hs hq
  tail_hasSum := dg1_hasSum hs 0
  head_hasSum := cosetDraw_hasSum hs hq

namespace KleinDraws

variable (A : KleinDraws) (M : Matrix (Fin r) (Fin t) ℤ)

/-- Extend the r centres to all natural indices for the seqLaw kernel. -/
def rowCentre (u : Fin t → ℤ) (m : ℕ) : ℤ :=
  if hm : m < r then (M *ᵥ u) ⟨m, hm⟩ else 0

/-- First draw t tail coordinates. Given their values u, draw r head coordinates,
then return the pair in lattice order (h,u). -/
def output (y : (Fin r → ℤ) × (Fin t → ℤ)) : ℝ :=
  seqLaw (fun _ _ ↦ A.tail) t y.2 *
    seqLaw (fun m _ ↦ A.head (rowCentre M y.2 m)) r y.1

theorem output_nonneg (y) : 0 ≤ A.output M y :=
  mul_nonneg (seqLaw_nonneg (fun _ _ ↦ A.tail_nonneg) _ _)
    (seqLaw_nonneg (fun _ _ ↦ A.head_nonneg _) _ _)

theorem output_hasSum : HasSum (A.output M) 1 := by
  rw [← (Equiv.prodComm (Fin t → ℤ) (Fin r → ℤ)).hasSum_iff]
  exact hasSum_bind (seqLaw_nonneg (fun _ _ ↦ A.tail_nonneg) t)
    (seqLaw_hasSum (fun _ _ ↦ A.tail_nonneg) (fun _ _ ↦ A.tail_hasSum) t)
    (fun u ↦ seqLaw_nonneg (fun m _ ↦ A.head_nonneg (rowCentre M u m)) r)
    (fun u ↦ seqLaw_hasSum (fun m _ ↦ A.head_nonneg (rowCentre M u m))
      (fun m _ ↦ A.head_hasSum (rowCentre M u m)) r)

theorem output_eq_kleinLaw {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : q ≠ 0) :
    (exactKleinDraws hs hq).output M = kleinLaw s q M := by
  classical
  funext y
  simp only [output, seqLaw_const, exactKleinDraws, rowCentre, Fin.is_lt, dite_true,
    Fin.eta, dg1, sub_zero, neg_zero, kleinLaw, pTail]
  by_cases hy : y ∈ latticeM q M
  · rw [Set.indicator_of_mem hy]
    simp only [cosetDraw, hy _, ite_true, centre]
  · rw [Set.indicator_of_notMem hy]
    change ¬∀ i, y.1 i ≡ (M *ᵥ y.2) i [ZMOD q] at hy
    obtain ⟨i, hi⟩ := not_forall.mp hy
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [cosetDraw, hi]), mul_zero]

/-- Replacing the two kinds of draws costs at most tη_T + rη_H. -/
theorem sdist_output_le (B : KleinDraws) {ηT ηH : ℝ} (ht : sdist A.tail B.tail ≤ ηT)
    (hh : ∀ c, sdist (A.head c) (B.head c) ≤ ηH) :
    sdist (A.output M) (B.output M) ≤ t * ηT + r * ηH := by
  have ht' := sdist_seqLaw_le (k := fun _ _ ↦ A.tail) (l := fun _ _ ↦ B.tail)
    (ε := fun _ ↦ ηT) (fun _ _ ↦ A.tail_nonneg) (fun _ _ ↦ A.tail_hasSum)
    (fun _ _ ↦ B.tail_nonneg) (fun _ _ ↦ B.tail_hasSum) (fun _ _ ↦ ht) t
  have hh' (u : Fin t → ℤ) := sdist_seqLaw_le
    (k := fun m _ ↦ A.head (rowCentre M u m)) (l := fun m _ ↦ B.head (rowCentre M u m))
    (ε := fun _ ↦ ηH) (fun _ _ ↦ A.head_nonneg _) (fun _ _ ↦ A.head_hasSum _)
    (fun _ _ ↦ B.head_nonneg _) (fun _ _ ↦ B.head_hasSum _) (fun _ _ ↦ hh _) r
  rw [← sdist_comp_equiv (Equiv.prodComm (Fin t → ℤ) (Fin r → ℤ))]
  apply (sdist_bind_le (K := fun u ↦ seqLaw (fun m _ ↦ A.head (rowCentre M u m)) r)
    (L := fun u ↦ seqLaw (fun m _ ↦ B.head (rowCentre M u m)) r)
    (seqLaw_nonneg (fun _ _ ↦ A.tail_nonneg) t)
    (seqLaw_hasSum (fun _ _ ↦ A.tail_nonneg) (fun _ _ ↦ A.tail_hasSum) t)
    (seqLaw_nonneg (fun _ _ ↦ B.tail_nonneg) t)
    (seqLaw_hasSum (fun _ _ ↦ B.tail_nonneg) (fun _ _ ↦ B.tail_hasSum) t)
    (fun u ↦ seqLaw_nonneg (fun m _ ↦ A.head_nonneg (rowCentre M u m)) r)
    (fun u ↦ seqLaw_hasSum (fun m _ ↦ A.head_nonneg (rowCentre M u m))
      (fun m _ ↦ A.head_hasSum (rowCentre M u m)) r)
    (fun u ↦ seqLaw_nonneg (fun m _ ↦ B.head_nonneg (rowCentre M u m)) r)
    (fun u ↦ seqLaw_hasSum (fun m _ ↦ B.head_nonneg (rowCentre M u m))
      (fun m _ ↦ B.head_hasSum (rowCentre M u m)) r)
    (fun u ↦ by simpa using hh' u)).trans
  exact add_le_add_left (by simpa using ht') _

end KleinDraws

theorem sdist_triangle {α : Type*} {P Q D : α → ℝ} (hP : Summable P) (hQ : Summable Q)
    (hD : Summable D) : sdist P D ≤ sdist P Q + sdist Q D := by
  unfold sdist
  rw [← mul_add, ← (summable_abs_sub hP hQ).tsum_add (summable_abs_sub hQ hD)]
  exact mul_le_mul_of_nonneg_left ((summable_abs_sub hP hD).tsum_le_tsum
    (fun a ↦ abs_sub_le (P a) (Q a) (D a))
    ((summable_abs_sub hP hQ).add (summable_abs_sub hQ hD))) (by norm_num)

namespace KleinDraws

variable (A : KleinDraws) (M : Matrix (Fin r) (Fin t) ℤ)
variable {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : 0 < q)
include hs hq

/-- Per-sample distance including the intrinsic bias of the exact Klein sampler. -/
theorem sdist_discGauss_le {ηT ηH : ℝ} (ht : sdist A.tail (dg1 s 0) ≤ ηT)
    (hh : ∀ c, sdist (A.head c) (cosetDraw s q c) ≤ ηH) :
    sdist (A.output M) (discGauss s q M) ≤
      t * ηT + r * ηH + sdist (kleinLaw s q M) (discGauss s q M) := by
  have h := A.sdist_output_le M (exactKleinDraws hs hq.ne') ht hh
  rw [output_eq_kleinLaw M hs hq.ne'] at h
  exact (sdist_triangle (A.output_hasSum M).summable (kleinLaw_hasSum hs hq M).summable
    (discGauss_hasSum hs hq M).summable).trans (add_le_add_left h _)

theorem sdist_discGauss_le_uniform {η : ℝ} (ht : sdist A.tail (dg1 s 0) ≤ η)
    (hh : ∀ c, sdist (A.head c) (cosetDraw s q c) ≤ η) :
    sdist (A.output M) (discGauss s q M) ≤
      (r + t : ℝ) * η + sdist (kleinLaw s q M) (discGauss s q M) := by
  simpa only [add_mul, add_comm ((r : ℝ) * η)] using A.sdist_discGauss_le M hs hq ht hh

/-- For any failure event on the emitted pair, add the same per-sample budget. -/
theorem prob_event_le {η : ℝ} (ht : sdist A.tail (dg1 s 0) ≤ η)
    (hh : ∀ c, sdist (A.head c) (cosetDraw s q c) ≤ η)
    (E : (Fin r → ℤ) × (Fin t → ℤ) → Prop) [DecidablePred E] :
    (∑' y, if E y then A.output M y else 0) ≤ (∑' y, if E y then discGauss s q M y else 0) +
      ((r + t : ℝ) * η + sdist (kleinLaw s q M) (discGauss s q M)) :=
  (prob_le_prob_add_sdist (A.output_nonneg M) (A.output_hasSum M)
    (discGauss_nonneg hs hq M) (discGauss_hasSum hs hq M) E).trans
    (add_le_add_right (A.sdist_discGauss_le_uniform M hs hq ht hh) _)

end KleinDraws
end
end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.cosetDraw_hasSum
#print axioms SigabaNeo.Wall1.KleinDraws.output_hasSum
#print axioms SigabaNeo.Wall1.KleinDraws.output_eq_kleinLaw
#print axioms SigabaNeo.Wall1.KleinDraws.sdist_output_le
#print axioms SigabaNeo.Wall1.sdist_triangle
#print axioms SigabaNeo.Wall1.KleinDraws.sdist_discGauss_le
#print axioms SigabaNeo.Wall1.KleinDraws.sdist_discGauss_le_uniform
#print axioms SigabaNeo.Wall1.KleinDraws.prob_event_le
