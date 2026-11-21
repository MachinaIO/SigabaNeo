module

public import Mathlib

@[expose] public section

/-! The Han admissibility conditions and the nonnegative workload boundary follow
Laarhoven, arXiv:2609.13635v1, HanAdmissible and QuotientHanRogers. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Rogers

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev SL (n : ℕ) := Matrix.SpecialLinearGroup (Fin n) ℝ

def integerGroup (n : ℕ) : Subgroup (SL n) :=
  (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (n := Fin n)).range

abbrev LatticeSpace (n : ℕ) := SL n ⧸ integerGroup n

/-- Generate the set of lattice points before summing. This counts each geometric tuple once. -/
def points {n : ℕ} (L : LatticeSpace n) : Set (E n) :=
  Set.range fun z : Fin n → ℤ ↦ WithLp.toLp 2
    ((Quotient.out L : SL n) • (fun i ↦ (z i : ℝ)))

/-- Every representative gives the same geometric lattice. -/
theorem points_mk {n : ℕ} (g : SL n) :
    points (QuotientGroup.mk g) =
      Set.range (fun z : Fin n → ℤ ↦ WithLp.toLp 2 (g • (fun i ↦ (z i : ℝ)))) := by
  let g' := (QuotientGroup.mk g : LatticeSpace n).out
  have he : (QuotientGroup.mk g : LatticeSpace n) = QuotientGroup.mk g' :=
    (Quotient.out_eq _).symm
  obtain ⟨γ, hγ⟩ := QuotientGroup.eq.mp he
  have hg : g' = g * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ := by
    rw [hγ, ← mul_assoc, mul_inv_cancel, one_mul]
  have hc (z : Fin n → ℤ) : (fun i ↦ ((γ • z) i : ℝ)) =
      Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ • (fun i ↦ (z i : ℝ)) := by
    funext i
    exact RingHom.map_mulVec (Int.castRingHom ℝ) γ.val z i
  change Set.range (fun z : Fin n → ℤ ↦ WithLp.toLp 2 (g' • (fun i ↦ (z i : ℝ)))) = _
  rw [hg]
  ext x
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨γ • z, by dsimp only; rw [hc, mul_smul]⟩
  · rintro ⟨z,rfl⟩
    exact ⟨γ⁻¹ • z, by dsimp only; rw [mul_smul, ← hc, smul_inv_smul]⟩

def tupleWorkload {n k : ℕ} (F : (Fin k → E n) → ℝ≥0∞) (L : LatticeSpace n) : ℝ≥0∞ :=
  ∑' z : Fin k → {x : E n // x ∈ points L ∧ x ≠ 0}, F fun i ↦ z i

structure Diagram (r k q : ℕ) where
  entry : Matrix (Fin r) (Fin k) ℤ
  pivot : Fin r → Fin k
  increasing : StrictMono pivot
  first : ∀ i : Fin r, i.val = 0 → (pivot i).val = 0
  nonzeroColumn : ∀ j, ∃ i, entry i j ≠ 0
  pivotColumn : ∀ i a, entry i (pivot a) = if i = a then (q : ℤ) else 0
  echelon : ∀ i j, j < pivot i → entry i j = 0
  primitive : ∀ d : ℕ, (∀ i j, (d : ℤ) ∣ entry i j) → d = 1

theorem fullRank_denominator {k q : ℕ} (D : Diagram k k q) : q = 1 := by
  apply D.primitive
  intro i j
  have h : D.pivot j = j := le_antisymm (D.increasing.le_id j) (D.increasing.id_le j)
  have he := D.pivotColumn i j
  rw [h] at he
  rw [he]
  split <;> simp

abbrev Coefficients := ∀ k, (r : Fin k) → (q : ℕ) → Diagram (r.val + 1) k (q + 1) → ℝ≥0∞

def diagramSum {n k : ℕ} (c : Coefficients) (F : (Fin k → E n) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ r : Fin k, ∑' q : ℕ, ∑' D : Diagram (r.val + 1) k (q + 1),
    c k r q D * ∫⁻ v : Fin (r.val + 1) → E n,
      F (fun j ↦ ((q + 1 : ℕ) : ℝ)⁻¹ • ∑ i, (D.entry i j : ℝ) • v i)
      ∂Measure.pi (fun _ ↦ volume)

def Admissible {n k : ℕ} (F : (Fin k → E n) → ℝ≥0∞) : Prop :=
  Measurable F ∧ (∃ M < ∞, ∀ z, F z ≤ M) ∧
  (∃ B : ℝ, ∀ z, F z ≠ 0 → ∀ i, ‖z i‖ ≤ B) ∧ (∀ z, F z ≠ 0 → ∀ i, z i ≠ 0)

scoped instance (n : ℕ) : MeasurableSpace (SL n) :=
  borel {A : Matrix (Fin n) (Fin n) ℝ // A.det = 1}

structure ClassicalRogersFormula {n : ℕ} (ν : Measure (LatticeSpace n)) (c : Coefficients) :
    Prop where
  bound : ∀ k r q D, c k r q D ≤ ENNReal.ofReal (((q + 1 : ℕ) : ℝ) ^ (-(n : ℝ)))
  unit : ∀ k r D, c k r 0 D = 1
  formula : ∀ k, 1 ≤ k → k < n → ∀ F : (Fin k → E n) → ℝ≥0∞, Admissible F →
    (∫⁻ L, tupleWorkload F L ∂ν) = diagramSum c F

theorem sieveWorkload {n k : ℕ} {ν : Measure (LatticeSpace n)} {c : Coefficients}
    (h : ClassicalRogersFormula ν c) (hk : k ∈ Finset.Icc 1 3) (hn : k < n)
    {F : (Fin k → E n) → ℝ≥0∞} (hF : Admissible F) :
    (∫⁻ L, tupleWorkload F L ∂ν) = diagramSum c F :=
  h.formula k (Finset.mem_Icc.mp hk).1 hn F hF

private def orderOne : Diagram 1 1 1 where
  entry := fun _ _ ↦ 1
  pivot := id
  increasing := strictMono_id
  first := fun _ h ↦ h
  nonzeroColumn := fun _ ↦ ⟨0, by simp⟩
  pivotColumn := by intro i a; simp [Subsingleton.elim i a]
  echelon := by intro i j h; exact (lt_irrefl i (Subsingleton.elim j i ▸ h)).elim
  primitive := by
    intro d hd
    have h := hd 0 0
    exact Nat.dvd_one.mp (by exact_mod_cast h)

private theorem eq_orderOne (D : Diagram 1 1 1) : D = orderOne := by
  have he : D.entry = fun _ _ ↦ 1 := by
    funext i j
    simpa [Subsingleton.elim (D.pivot j) j, Subsingleton.elim i j] using D.pivotColumn i j
  have hpi : D.pivot = id := Subsingleton.elim _ _
  cases D
  congr

/-- The sole surviving order-one diagram gives the Lebesgue integral with coefficient one. -/
theorem diagramSum_one {n : ℕ} {c : Coefficients} (hc : ∀ D, c 1 0 0 D = 1)
    (f : E n → ℝ≥0∞) :
    diagramSum c (fun v : Fin 1 → E n ↦ f (v 0)) = ∫⁻ x, f x := by
  classical
  unfold diagramSum
  rw [Fin.sum_univ_one, tsum_eq_single 0]
  · simp only [Fin.val_zero, zero_add, Nat.reduceAdd] at *
    rw [tsum_eq_single orderOne]
    · simp [hc, orderOne]
      exact (measurePreserving_funUnique (volume : Measure (E n)) (Fin 1)).lintegral_comp_emb
        (MeasurableEquiv.funUnique (Fin 1) (E n)).measurableEmbedding f
    · intro D hD
      exact (hD (eq_orderOne D)).elim
  · intro q hq
    apply tsum_eq_zero_iff.mpr
    intro D
    have h := fullRank_denominator (k := 1) D
    omega

theorem siegel_of_rogers {n : ℕ} {ν : Measure (LatticeSpace n)} {c : Coefficients}
    (h : ClassicalRogersFormula ν c) (hn : 1 < n) (f : E n → ℝ≥0∞)
    (hf : Admissible (fun v : Fin 1 → E n ↦ f (v 0))) :
    (∫⁻ L, tupleWorkload (fun v : Fin 1 → E n ↦ f (v 0)) L ∂ν) = ∫⁻ x, f x :=
  (h.formula 1 le_rfl hn _ hf).trans (diagramSum_one (h.unit 1 0) f)

end SigabaNeo.Rogers
