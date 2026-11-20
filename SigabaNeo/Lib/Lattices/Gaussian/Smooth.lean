import SigabaNeo.Lib.Lattices.Gaussian
import CslibFrontier.Foundations.Probability.Gaussian.ShiftBounds
import CslibFrontier.Foundations.Probability.Gaussian.DiscreteTail
import SigabaNeo.Lib.Lattices.Gaussian.Sum
import Mathlib.Algebra.Field.ZMod

/-!
# Smoothing for `Λ^⊥(B)`

* `perp_isZLattice`: `Λ^⊥(B)` has full rank (it contains `q·Z^m`).
* `dual_scaled_int`: every dual vector `w` has `q·w ∈ Z^m`, and the integer vector `v = q·w`
  satisfies `v ⬝ x ≡ 0 (mod q)` for every `x` in the integer kernel of `B`.
-/

namespace SigabaNeo.Lattices

open SigabaNeo.Lattices ProbabilityTheory
open scoped Matrix RealInnerProductSpace

variable {n m q : ℕ}

/-- The unit vector `e_i` of `Z^m`, scaled by `q`, is in the integer kernel of `B`. -/
theorem q_single_mem_kernel [NeZero q] (B : Matrix (Fin n) (Fin m) (ZMod q)) (i : Fin m) :
    (q : ℤ) • Pi.single i (1 : ℤ) ∈ kernel B := by
  show B *ᵥ (fun j => ((((q : ℤ) • Pi.single i (1 : ℤ) : Fin m → ℤ) j : ℤ) : ZMod q)) = 0
  have : (fun j => ((((q : ℤ) • Pi.single i (1 : ℤ) : Fin m → ℤ) j : ℤ) : ZMod q)) = 0 := by
    ext j; simp [Pi.single_apply]
  rw [this, Matrix.mulVec_zero]

theorem embed_q_single (i : Fin m) :
    embed m ((q : ℤ) • Pi.single i (1 : ℤ)) =
      (q : ℝ) • EuclideanSpace.single i (1 : ℝ) := by
  ext j
  simp [embed, Pi.single_apply, PiLp.single_apply]

instance perp_isZLattice [NeZero q] (B : Matrix (Fin n) (Fin m) (ZMod q)) :
    IsZLattice ℝ (perp B) where
  span_top := by
    rw [eq_top_iff, ← (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.span_eq]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
    have hmem : (q : ℝ) • EuclideanSpace.single i (1 : ℝ) ∈ (perp B : Set _) := by
      rw [← embed_q_single]
      exact ⟨_, q_single_mem_kernel B i, rfl⟩
    have := Submodule.smul_mem (Submodule.span ℝ (perp B : Set (EuclideanSpace ℝ (Fin m))))
      (q : ℝ)⁻¹ (Submodule.subset_span hmem)
    rw [smul_smul, inv_mul_cancel₀ hq, one_smul] at this
    simpa using this

/-- The dual of `Λ^⊥(B)`. -/
noncomputable abbrev dualPerp (B : Matrix (Fin n) (Fin m) (ZMod q)) :
    Submodule ℤ (EuclideanSpace ℝ (Fin m)) :=
  LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin m))) (perp B)

theorem dual_scaled_int [NeZero q] (B : Matrix (Fin n) (Fin m) (ZMod q))
    (w : EuclideanSpace ℝ (Fin m)) (hw : w ∈ dualPerp B) :
    ∃ v : Fin m → ℤ, (∀ i, (q : ℝ) * w i = v i) ∧
      ∀ x ∈ kernel B, ∑ i, (v i : ZMod q) * (x i : ZMod q) = 0 := by
  have hint (y : EuclideanSpace ℝ (Fin m)) (hy : y ∈ perp B) : ∃ k : ℤ, (k : ℝ) = ⟪w, y⟫ := by
    have := (LinearMap.BilinForm.mem_dualSubmodule _).mp hw y hy
    obtain ⟨k, hk⟩ := Submodule.mem_one.mp this
    exact ⟨k, by simpa using hk⟩
  choose v hv using fun i : Fin m =>
    hint _ ⟨_, q_single_mem_kernel B i, rfl⟩
  have hvq : ∀ i, (q : ℝ) * w i = v i := by
    intro i
    rw [hv i, embed_q_single, inner_smul_right, PiLp.inner_apply]
    simp [PiLp.single_apply]
  refine ⟨v, hvq, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := hint (embed m x) ⟨x, hx, rfl⟩
  have hsum : ((k * q : ℤ) : ℝ) = ((∑ i, v i * x i : ℤ) : ℝ) := by
    push_cast
    rw [hk, PiLp.inner_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hvq i]
    simp [embed]
    ring
  have hz : (k * q : ℤ) = ∑ i, v i * x i := by exact_mod_cast hsum
  have := congrArg (fun z : ℤ => (z : ZMod q)) hz
  simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero, Int.cast_sum] at this
  exact this.symm

/-! ### Row spaces, and counting matrices, over a finite field -/

section Field
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

omit [Fintype K] [DecidableEq K] in
/-- A vector orthogonal to the kernel of `B` is in the row space of `B`. -/
theorem rowspace_field (B : Matrix (Fin n) (Fin m) K) (v : Fin m → K)
    (h : ∀ x, B *ᵥ x = 0 → v ⬝ᵥ x = 0) : ∃ y : Fin n → K, y ᵥ* B = v := by
  let f : (Fin m → K) →ₗ[K] (Fin n → K) := Matrix.mulVecLin B
  let φ : Module.Dual K (Fin m → K) :=
    { toFun := fun x => v ⬝ᵥ x
      map_add' := fun x y => dotProduct_add v x y
      map_smul' := fun c x => by simp [dotProduct_smul] }
  have hφ : φ ∈ (LinearMap.ker f).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    exact h x (by simpa [f] using LinearMap.mem_ker.mp hx)
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hφ
  obtain ⟨ψ, hψ⟩ := hφ
  refine ⟨fun k => ψ (Pi.single k 1), ?_⟩
  ext i
  have hcol : f (Pi.single i 1) = ∑ k, B k i • (Pi.single k (1 : K) : Fin n → K) := by
    ext k
    simp [f, Matrix.mulVec_single, Finset.sum_apply, Pi.single_apply]
  have := congrArg (fun g => g (Pi.single i (1 : K))) hψ
  simp only [LinearMap.dualMap_apply] at this
  rw [hcol, map_sum] at this
  simp only [map_smul, smul_eq_mul] at this
  rw [Matrix.vecMul, dotProduct]
  simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, dotProduct_single, mul_one] at this
  rw [← this]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem card_vecMul_eq_card_field (y : Fin n → K) (hy : y ≠ 0) (v v' : Fin m → K) :
    (Finset.univ.filter fun B : Matrix (Fin n) (Fin m) K => y ᵥ* B = v).card =
      (Finset.univ.filter fun B : Matrix (Fin n) (Fin m) K => y ᵥ* B = v').card := by
  obtain ⟨k0, hk0⟩ : ∃ k, y k ≠ 0 := by
    by_contra h; push Not at h; exact hy (funext h)
  let D : Matrix (Fin n) (Fin m) K := fun k i =>
    if k = k0 then (y k0)⁻¹ * (v' i - v i) else 0
  have hD : y ᵥ* D = v' - v := by
    ext i
    simp [D, Matrix.vecMul, dotProduct, mul_ite, ← mul_assoc, mul_inv_cancel₀ hk0]
  refine Finset.card_bij (fun B _ => B + D) ?_ (fun _ _ _ _ h => add_right_cancel h) ?_
  · intro B hB
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB ⊢
    rw [Matrix.vecMul_add, hB, hD, add_sub_cancel]
  · intro B hB
    refine ⟨B - D, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB ⊢
    rw [Matrix.vecMul_sub, hB, hD, sub_sub_cancel]

theorem card_vecMul_field (y : Fin n → K) (hy : y ≠ 0) (v : Fin m → K) :
    (Finset.univ.filter fun B : Matrix (Fin n) (Fin m) K => y ᵥ* B = v).card *
      Fintype.card K ^ m = Fintype.card K ^ (n * m) := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Matrix (Fin n) (Fin m)
    K))) (t := (Finset.univ : Finset (Fin m → K))) (f := fun B => y ᵥ* B)
    (fun _ _ => Finset.mem_univ _)
  rw [Finset.sum_congr rfl fun v' _ => card_vecMul_eq_card_field y hy v' v, Finset.sum_const,
    Finset.card_univ, Finset.card_univ, smul_eq_mul] at h
  have hc : Fintype.card (Matrix (Fin n) (Fin m) K) = Fintype.card K ^ (n * m) := by
    show Fintype.card (Fin n → Fin m → K) = _
    simp only [Fintype.card_fun, Fintype.card_fin]
    rw [← pow_mul, mul_comm]
  have hm : Fintype.card (Fin m → K) = Fintype.card K ^ m := by simp [Fintype.card_pi]
  rw [← hc, h, hm]; ring

/-- The number of matrices whose row space contains a fixed nonzero vector. -/
theorem card_rowspace_le_field (v : Fin m → K) (hv : v ≠ 0) :
    (Finset.univ.filter fun B : Matrix (Fin n) (Fin m) K => ∃ y, y ᵥ* B = v).card *
      Fintype.card K ^ m ≤ Fintype.card K ^ n * Fintype.card K ^ (n * m) := by
  have hsub : (Finset.univ.filter fun B : Matrix (Fin n) (Fin m) K => ∃ y, y ᵥ* B = v) ⊆
      (Finset.univ.filter fun y : Fin n → K => y ≠ 0).biUnion fun y =>
        Finset.univ.filter fun B => y ᵥ* B = v := by
    intro B hB
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB
    obtain ⟨y, hy⟩ := hB
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy; exact hv hy.symm
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨y, hy0, hy⟩
  calc _ ≤ ((Finset.univ.filter fun y : Fin n → K => y ≠ 0).biUnion fun y =>
          Finset.univ.filter fun B => y ᵥ* B = v).card * Fintype.card K ^ m :=
        Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ ≤ (∑ y ∈ Finset.univ.filter fun y : Fin n → K => y ≠ 0,
          (Finset.univ.filter fun B : Matrix (Fin n) (Fin m) K => y ᵥ* B = v).card) *
          Fintype.card K ^ m := Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = (Finset.univ.filter fun y : Fin n → K => y ≠ 0).card * Fintype.card K ^ (n * m) := by
        rw [Finset.sum_mul, Finset.sum_congr rfl fun y hy => card_vecMul_field y
          (Finset.mem_filter.mp hy).2 v, Finset.sum_const, smul_eq_mul]
    _ ≤ Fintype.card K ^ n * Fintype.card K ^ (n * m) := by
        apply Nat.mul_le_mul_right
        refine (Finset.card_filter_le _ _).trans ?_
        simp [Fintype.card_pi]

end Field

/-! ### The nonzero dual mass, bounded by integer vectors -/

open scoped ENNReal

/-- The weight of `v/q` at width `1/τ`: `exp(−π τ² ‖v‖² / q²)`. -/
noncomputable def wt (τ : ℝ) (q : ℕ) (v : Fin m → ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(Real.pi * τ ^ 2 / (q : ℝ) ^ 2) * ∑ i, ((v i : ℤ) : ℝ) ^ 2))

/-- `v` is orthogonal, mod `q`, to the integer kernel of `B`. -/
def Orth (B : Matrix (Fin n) (Fin m) (ZMod q)) (v : Fin m → ℤ) : Prop :=
  ∀ x ∈ kernel B, ∑ i, (v i : ZMod q) * (x i : ZMod q) = 0

/-- The nonzero dual Gaussian mass at width `1/τ`, in `ℝ≥0∞`. -/
noncomputable def dualMassE (B : Matrix (Fin n) (Fin m) (ZMod q)) (τ : ℝ) : ℝ≥0∞ :=
  ∑' w : {w : dualPerp B // w ≠ 0},
    ENNReal.ofReal (gaussianWeight (1 / τ) ((w.1 : dualPerp B) : EuclideanSpace ℝ (Fin m)))

open Classical in
theorem dualMassE_le [NeZero q] (B : Matrix (Fin n) (Fin m) (ZMod q)) (τ : ℝ) :
    dualMassE B τ ≤ ∑' v : Fin m → ℤ, if v ≠ 0 ∧ Orth B v then wt τ q v else 0 := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  let φ : {w : dualPerp B // w ≠ 0} → (Fin m → ℤ) := fun w =>
    (dual_scaled_int B (w.1 : EuclideanSpace ℝ (Fin m)) w.1.2).choose
  have hφ (w : {w : dualPerp B // w ≠ 0}) :
      (∀ i, (q : ℝ) * (w.1 : EuclideanSpace ℝ (Fin m)) i = (φ w i : ℝ)) ∧ Orth B (φ w) :=
    (dual_scaled_int B (w.1 : EuclideanSpace ℝ (Fin m)) w.1.2).choose_spec
  have hinj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext; apply Subtype.ext
    ext i
    have h1 := (hφ a).1 i
    have h2 := (hφ b).1 i
    rw [show φ a = φ b from hab] at h1
    have : (q : ℝ) * (a.1 : EuclideanSpace ℝ (Fin m)) i = (q : ℝ) * (b.1 : EuclideanSpace ℝ (Fin m)) i := by
      rw [h1, h2]
    exact mul_left_cancel₀ hq this
  refine le_trans (le_of_eq ?_) (tsum_comp_le_tsum_of_injective hinj _)
  unfold dualMassE
  refine tsum_congr fun w => ?_
  have hne : φ w ≠ 0 := by
    intro h0
    apply w.2
    apply Subtype.ext
    ext i
    have := (hφ w).1 i
    rw [h0] at this
    simpa [hq] using this
  rw [if_pos ⟨hne, (hφ w).2⟩]
  unfold wt gaussianWeight
  congr 2
  rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← (hφ w).1 i, Real.norm_eq_abs, sq_abs]
  field_simp

/-- `Orth` puts the reduction of `v` in the row space of `B`. -/
theorem orth_rowspace [Fact q.Prime] (B : Matrix (Fin n) (Fin m) (ZMod q)) (v : Fin m → ℤ)
    (h : Orth B v) : ∃ y : Fin n → ZMod q, y ᵥ* B = fun i => (v i : ZMod q) := by
  have key : ∀ x : Fin m → ZMod q, B *ᵥ x = 0 → (fun i => (v i : ZMod q)) ⬝ᵥ x = 0 := by
    intro x hx
    have hk : (fun i => ((x i).val : ℤ)) ∈ kernel B := by
      show B *ᵥ (fun i => (((x i).val : ℤ) : ZMod q)) = 0
      simpa [ZMod.natCast_zmod_val] using hx
    have := h _ hk
    simpa [dotProduct, ZMod.natCast_zmod_val] using this
  exact rowspace_field (K := ZMod q) B _ key

open Classical in
/-- The number of matrices for which a nonzero `v` is orthogonal to the kernel, times `q^m`. -/
theorem card_orth_le [Fact q.Prime] (v : Fin m → ℤ) :
    (Finset.univ.filter fun B : Matrix (Fin n) (Fin m) (ZMod q) => Orth B v).card * q ^ m ≤
      (if (fun i => (v i : ZMod q)) = 0 then q ^ m * q ^ (n * m) else 0) +
        q ^ n * q ^ (n * m) := by
  by_cases h0 : (fun i => (v i : ZMod q)) = 0
  · rw [if_pos h0]
    have : (Finset.univ.filter fun B : Matrix (Fin n) (Fin m) (ZMod q) => Orth B v).card ≤
        q ^ (n * m) := by
      refine (Finset.card_filter_le _ _).trans ?_
      show Fintype.card (Fin n → Fin m → ZMod q) ≤ _
      simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
      rw [← pow_mul, mul_comm]
    calc _ ≤ q ^ (n * m) * q ^ m := Nat.mul_le_mul_right _ this
      _ = q ^ m * q ^ (n * m) := mul_comm _ _
      _ ≤ _ := Nat.le_add_right _ _
  · rw [if_neg h0, zero_add]
    have hsub : (Finset.univ.filter fun B : Matrix (Fin n) (Fin m) (ZMod q) => Orth B v) ⊆
        Finset.univ.filter fun B => ∃ y, y ᵥ* B = fun i => (v i : ZMod q) := by
      intro B hB
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB ⊢
      exact orth_rowspace B v hB
    have := card_rowspace_le_field (n := n) (K := ZMod q) _ h0
    rw [ZMod.card] at this
    exact le_trans (Nat.mul_le_mul_right _ (Finset.card_le_card hsub)) this

/-- The weight `exp(−π τ² ‖u‖²)` of a nonzero integer vector. -/
noncomputable def wt1 (τ : ℝ) (u : Fin m → ℤ) : ℝ≥0∞ :=
  if u = 0 then 0 else ENNReal.ofReal (Real.exp (-(Real.pi * τ ^ 2) * ∑ i, ((u i : ℤ) : ℝ) ^ 2))

open Classical in
/-- Multiples of `q` among the integer vectors: their weights are those of `Z^m \ 0` at width
`τ`. -/
theorem tsum_wt_multiple_le [NeZero q] (τ : ℝ) :
    ∑' v : Fin m → ℤ, (if (fun i => (v i : ZMod q)) = 0 ∧ v ≠ 0 then wt τ q v else 0) ≤
      ∑' u : Fin m → ℤ, wt1 τ u := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  let S : Set (Fin m → ℤ) := {v | (fun i => (v i : ZMod q)) = 0 ∧ v ≠ 0}
  have hind : (fun v : Fin m → ℤ =>
      if (fun i => (v i : ZMod q)) = 0 ∧ v ≠ 0 then wt τ q v else 0) = S.indicator (wt τ q) := by
    funext v; simp only [Set.indicator_apply, S, Set.mem_ofPred_eq]
  rw [hind, ← tsum_subtype S (wt τ q)]
  let ψ : S → (Fin m → ℤ) :=
    fun v i => v.1 i / q
  have hdiv (v : S) (i : Fin m) :
      v.1 i = q * ψ v i := by
    have := congrFun v.2.1 i
    simp only [Pi.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    exact (Int.mul_ediv_cancel' this).symm
  have hinj : Function.Injective ψ := by
    intro a b h
    apply Subtype.ext; funext i
    rw [hdiv a i, hdiv b i, show ψ a i = ψ b i from congrFun h i]
  refine le_trans (le_of_eq (tsum_congr fun v => ?_)) (tsum_comp_le_tsum_of_injective hinj (wt1 τ))
  have hne : ψ v ≠ 0 := by
    intro h0; apply v.2.2; funext i; rw [hdiv v i, show ψ v i = 0 from congrFun h0 i]; simp
  unfold wt wt1
  rw [if_neg hne]
  congr 2
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hdiv v i]
  push_cast
  field_simp

open Classical in
/-- Summed over all matrices, the nonzero dual mass is small:
`(Σ_B mass(B)) · q^m ≤ q^m q^{nm} · Σ_{u ≠ 0} e^{−π τ² ‖u‖²} + q^n q^{nm} · Σ_v e^{−π τ² ‖v‖²/q²}`. -/
theorem sum_dualMassE_le [Fact q.Prime] (τ : ℝ) :
    (∑ B : Matrix (Fin n) (Fin m) (ZMod q), dualMassE B τ) * (q : ℝ≥0∞) ^ m ≤
      (q : ℝ≥0∞) ^ m * (q : ℝ≥0∞) ^ (n * m) * ∑' u : Fin m → ℤ, wt1 τ u +
        (q : ℝ≥0∞) ^ n * (q : ℝ≥0∞) ^ (n * m) * ∑' v : Fin m → ℤ, wt τ q v := by
  calc (∑ B : Matrix (Fin n) (Fin m) (ZMod q), dualMassE B τ) * (q : ℝ≥0∞) ^ m
      ≤ (∑ B : Matrix (Fin n) (Fin m) (ZMod q),
          ∑' v : Fin m → ℤ, if v ≠ 0 ∧ Orth B v then wt τ q v else 0) * (q : ℝ≥0∞) ^ m := by
        exact mul_le_mul_left (Finset.sum_le_sum fun B _ => dualMassE_le B τ) _
    _ = ∑' v : Fin m → ℤ, ((Finset.univ.filter fun B : Matrix (Fin n) (Fin m) (ZMod q) =>
          v ≠ 0 ∧ Orth B v).card * (q : ℝ≥0∞) ^ m) * wt τ q v := by
        rw [← Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable),
          ← ENNReal.tsum_mul_right]
        refine tsum_congr fun v => ?_
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ ∑' v : Fin m → ℤ, ((q : ℝ≥0∞) ^ m * (q : ℝ≥0∞) ^ (n * m) *
          (if (fun i => (v i : ZMod q)) = 0 ∧ v ≠ 0 then wt τ q v else 0) +
          (q : ℝ≥0∞) ^ n * (q : ℝ≥0∞) ^ (n * m) * wt τ q v) := by
        refine ENNReal.tsum_le_tsum fun v => ?_
        by_cases hv : v = 0
        · simp [hv]
        have hc := card_orth_le (n := n) (q := q) v
        have hfilt : (Finset.univ.filter fun B : Matrix (Fin n) (Fin m) (ZMod q) =>
            v ≠ 0 ∧ Orth B v) = Finset.univ.filter fun B => Orth B v := by
          ext B; simp [hv]
        rw [hfilt]
        have hc' : ((Finset.univ.filter fun B : Matrix (Fin n) (Fin m) (ZMod q) =>
            Orth B v).card * (q : ℝ≥0∞) ^ m) ≤
            (if (fun i => (v i : ZMod q)) = 0 then (q : ℝ≥0∞) ^ m * (q : ℝ≥0∞) ^ (n * m) else 0) +
              (q : ℝ≥0∞) ^ n * (q : ℝ≥0∞) ^ (n * m) := by
          have := (Nat.cast_le (α := ℝ≥0∞)).mpr hc
          push_cast at this
          split_ifs at this ⊢ <;> simpa using this
        calc _ ≤ ((if (fun i => (v i : ZMod q)) = 0 then (q : ℝ≥0∞) ^ m * (q : ℝ≥0∞) ^ (n * m)
                else 0) + (q : ℝ≥0∞) ^ n * (q : ℝ≥0∞) ^ (n * m)) * wt τ q v := by gcongr
          _ = _ := by
            have hiff : ((fun i => (v i : ZMod q)) = 0 ∧ v ≠ 0) ↔ (fun i => (v i : ZMod q)) = 0 :=
              ⟨fun h => h.1, fun h => ⟨h, hv⟩⟩
            simp only [hiff]
            split_ifs <;> simp [add_mul]
    _ = _ := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    _ ≤ _ := add_le_add_left (mul_le_mul_right (tsum_wt_multiple_le τ) _) _

/-! ### Evaluating the two sums -/

/-- The one-dimensional weight `e^{−b k²}`. -/
noncomputable def g1 (b : ℝ) (k : ℤ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-b * (k : ℝ) ^ 2))

theorem prod_g1 (b : ℝ) (v : Fin m → ℤ) :
    ∏ i, g1 b (v i) = ENNReal.ofReal (Real.exp (-b * ∑ i, ((v i : ℤ) : ℝ) ^ 2)) := by
  rw [Finset.mul_sum, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
  rfl

theorem tsum_wt_eq (τ : ℝ) (q : ℕ) :
    ∑' v : Fin m → ℤ, wt τ q v = (∑' k : ℤ, g1 (Real.pi * τ ^ 2 / (q : ℝ) ^ 2) k) ^ m := by
  rw [← tsum_pi_prod]
  exact tsum_congr fun v => (prod_g1 _ v).symm

theorem tsum_wt1_add_one (τ : ℝ) :
    ∑' u : Fin m → ℤ, wt1 τ u + 1 = (∑' k : ℤ, g1 (Real.pi * τ ^ 2) k) ^ m := by
  rw [← tsum_pi_prod]
  conv_rhs => rw [ENNReal.tsum_eq_add_tsum_ite (0 : Fin m → ℤ)]
  have h0 : ∏ i, g1 (Real.pi * τ ^ 2) ((0 : Fin m → ℤ) i) = 1 := by simp [g1]
  rw [h0, add_comm]
  congr 1
  refine tsum_congr fun u => ?_
  unfold wt1
  split_ifs with h
  · rfl
  · rw [prod_g1]

theorem tsum_g1_le_large {a : ℝ} (ha : 0 ≤ a) :
    ∑' k : ℤ, g1 a k ≤ (1 + ENNReal.ofReal (Real.exp (-a))) *
      (1 - ENNReal.ofReal (Real.exp (-a)))⁻¹ := by
  rw [← tsum_int_geom]
  refine ENNReal.tsum_le_tsum fun k => ?_
  unfold g1
  rw [← ENNReal.ofReal_pow (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal (exp_neg_sq_le ha k)

theorem tsum_g1_le_small {c : ℝ} :
    ∑' k : ℤ, g1 (c ^ 2) k ≤ ENNReal.ofReal (Real.exp (1 / 4)) *
      ((1 + ENNReal.ofReal (Real.exp (-c))) * (1 - ENNReal.ofReal (Real.exp (-c)))⁻¹) := by
  rw [← tsum_int_geom, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun k => ?_
  unfold g1
  rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal (exp_neg_sq_le' c k)

end SigabaNeo.Lattices
