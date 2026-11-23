import SigabaNeo.Lib.Lattices.Research.Wall1.AffineGraphMoments

/-! # Exact probabilities after imposing fixed graph equations

This is the rank-increment law used in the fixed-flag collision calculation.
It conditions on containing fixed vectors, not on choosing them as shortest vectors.
Inconsistent refinements have probability zero; no independence of tests is assumed.
-/

noncomputable section
namespace SigabaNeo.Wall1.ConditionalGraphProbability
open Matrix QaryMembership DualExit AffineGraphMoments
open scoped Classical

variable {q m n k l : ℕ} [Fact q.Prime]

/-- All output rows obey a fixed family of linear input tests. -/
def satisfies (X : Matrix (Fin k) (Fin n) (ZMod q))
    (b : Fin m → Fin k → ZMod q) (A : Design m n q) : Prop :=
  ∀ i, X.mulVec (A i) = b i

/-- Conditional probability as the joint-event probability divided by the given event.
The theorems below prove that their conditioning event has positive probability. -/
def conditionalProbability (condition event : Design m n q → Prop) : ℝ :=
  probability (fun A ↦ condition A ∧ event A) / probability condition

/-- Consistency makes conditioning on a fixed system well-defined. -/
theorem conditioning_positive (X : Matrix (Fin k) (Fin n) (ZMod q))
    (b : Fin m → Fin k → ZMod q)
    (hb : ∀ i, b i ∈ LinearMap.range X.mulVecLin) :
    0 < probability (satisfies X b) := by
  change 0 < probability (fun A : Design m n q ↦ ∀ i, X.mulVec (A i) = b i)
  rw [system_probability, ite_eq_left hb]
  have hq : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  positivity

omit [Fact q.Prime] in
/-- The full system implies any family obtained by restricting its rows. -/
theorem restrict_system (X : Matrix (Fin l) (Fin n) (ZMod q))
    (b : Fin m → Fin l → ZMod q) (r : Fin k → Fin l) (A : Design m n q)
    (h : satisfies X b A) :
    satisfies (X.submatrix r id) (fun i ↦ b i ∘ r) A := by
  intro i
  ext j
  exact congrFun (h i) (r j)

/-- Exact conditional incidence probability, with the increment in input rank explicit. -/
theorem nested_system_probability (X : Matrix (Fin l) (Fin n) (ZMod q))
    (b : Fin m → Fin l → ZMod q) (r : Fin k → Fin l)
    (hbase : ∀ i, b i ∘ r ∈ LinearMap.range (X.submatrix r id).mulVecLin) :
    conditionalProbability (satisfies (X.submatrix r id) (fun i ↦ b i ∘ r))
      (satisfies X b) =
      if ∀ i, b i ∈ LinearMap.range X.mulVecLin then
        1 / (q : ℝ) ^ ((X.rank - (X.submatrix r id).rank) * m) else 0 := by
  have hjoint : (fun A ↦ satisfies (X.submatrix r id) (fun i ↦ b i ∘ r) A ∧
      satisfies X b A) = satisfies X b := by
    funext A
    apply propext
    exact ⟨And.right, fun h ↦ ⟨restrict_system X b r A h, h⟩⟩
  rw [conditionalProbability, hjoint]
  change probability (fun A : Design m n q ↦ ∀ i, X.mulVec (A i) = b i) /
    probability (fun A : Design m n q ↦
      ∀ i, (X.submatrix r id).mulVec (A i) = b i ∘ r) = _
  rw [system_probability, system_probability, ite_eq_left hbase]
  split_ifs with hfull
  · have hr := X.rank_submatrix_le r id
    have he : X.rank * m =
        (X.submatrix r id).rank * m + (X.rank - (X.submatrix r id).rank) * m := by
      rw [← Nat.add_mul, Nat.add_sub_of_le hr]
    rw [he, pow_add]
    have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
    field_simp
  · simp

/-- One new independent input direction costs exactly one uniform output vector. -/
theorem one_rank_increment (X : Matrix (Fin l) (Fin n) (ZMod q))
    (b : Fin m → Fin l → ZMod q) (r : Fin k → Fin l)
    (hbase : ∀ i, b i ∘ r ∈ LinearMap.range (X.submatrix r id).mulVecLin)
    (hfull : ∀ i, b i ∈ LinearMap.range X.mulVecLin)
    (hr : X.rank = (X.submatrix r id).rank + 1) :
    conditionalProbability (satisfies (X.submatrix r id) (fun i ↦ b i ∘ r))
      (satisfies X b) = 1 / (q : ℝ) ^ m := by
  rw [nested_system_probability X b r hbase, ite_eq_left hfull, hr]
  simp

end SigabaNeo.Wall1.ConditionalGraphProbability

#print axioms SigabaNeo.Wall1.ConditionalGraphProbability.conditioning_positive
#print axioms SigabaNeo.Wall1.ConditionalGraphProbability.restrict_system
#print axioms SigabaNeo.Wall1.ConditionalGraphProbability.nested_system_probability
#print axioms SigabaNeo.Wall1.ConditionalGraphProbability.one_rank_increment
