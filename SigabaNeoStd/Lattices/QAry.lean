module

public import Mathlib

/-! # Finite-support q-ary mean values

This file proves the uniform matrix average by rank, rank preservation for short integer
tuples, and the first moment, second moment and variance of finite shell counts.
-/

public section

namespace SigabaNeo.QAry
open scoped NNReal

variable {q m k : ℕ} [Fact q.Prime]

/-- Number of matrices whose rows annihilate a fixed tuple. -/
theorem kernelCount (n : ℕ) (X : Matrix (Fin k) (Fin m) (ZMod q)) :
    Fintype.card {A : Fin n → Fin m → ZMod q // ∀ i, X.mulVec (A i) = 0} =
      q ^ ((m - X.rank) * n) := by
  classical
  let K := LinearMap.ker X.mulVecLin
  have h := X.mulVecLin.finrank_range_add_finrank_ker
  change X.rank + Module.finrank (ZMod q) K = _ at h
  simp at h
  have hd : Module.finrank (ZMod q) K = m - X.rank := by omega
  let e : {A : Fin n → Fin m → ZMod q // ∀ i, X.mulVec (A i) = 0} ≃ (Fin n → K) :=
    { toFun := fun A i ↦ ⟨A.val i, A.property i⟩
      invFun := fun A ↦ ⟨fun i ↦ (A i).val, fun i ↦ (A i).property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin,
    Module.card_eq_pow_finrank (K := ZMod q), ZMod.card, hd, pow_mul]

/-- Uniform expectation of a finite weighted sum over tuples in the q-ary lattice.
The tuple can be indexed by any type, in particular by integer matrices reduced modulo q. -/
theorem meanValue {ι : Type*} (n : ℕ) (s : Finset ι)
    (X : ι → Matrix (Fin k) (Fin m) (ZMod q)) (F : ι → ℝ≥0) :
    (∑ A : Fin n → Fin m → ZMod q, ∑ x ∈ s,
      if ∀ i, (X x).mulVec (A i) = 0 then F x else 0) / (q : ℝ≥0) ^ (m * n) =
      ∑ x ∈ s, F x / (q : ℝ≥0) ^ ((X x).rank * n) := by
  classical
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← Fintype.card_subtype,
    kernelCount, Nat.cast_pow]
  have hr := (X x).mulVecLin.finrank_range_add_finrank_ker
  change (X x).rank + _ = _ at hr
  simp at hr
  have he : m * n = (m - (X x).rank) * n + (X x).rank * n := by
    rw [← Nat.add_mul]
    congr 1
    omega
  rw [he, pow_add]
  have hq : (q : ℝ≥0) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  field_simp

#print axioms kernelCount
#print axioms meanValue

private theorem selectCols {K : Type*} [Field K] {a b : ℕ} (M : Matrix (Fin a) (Fin b) K) :
    ∃ c : Fin M.rank ↪ Fin b, LinearIndependent K (M.col ∘ c) ∧
      (M.submatrix id c).rank = M.rank := by
  classical
  obtain ⟨T, f, hf, hs, hi⟩ := exists_linearIndependent' K M.col
  let : Finite T := Finite.of_injective f hf
  let := Fintype.ofFinite T
  have h : Fintype.card T = M.rank := by
    rw [M.rank_eq_finrank_span_cols, ← hs, finrank_span_eq_card hi]
  let e := (Fintype.equivFinOfCardEq h).symm
  let c : Fin M.rank ↪ Fin b := e.toEmbedding.trans ⟨f, hf⟩
  have hli : LinearIndependent K (M.col ∘ c) := hi.comp e e.injective
  refine ⟨c, hli, ?_⟩
  rw [Matrix.rank_eq_finrank_span_cols]
  change Module.finrank K (Submodule.span K (Set.range (M.col ∘ c))) = _
  simp [finrank_span_eq_card hli]

private theorem rankMinor {K : Type*} [Field K] {a b : ℕ} (M : Matrix (Fin a) (Fin b) K) :
    ∃ (r : Fin M.rank ↪ Fin a) (c : Fin M.rank ↪ Fin b), (M.submatrix r c).det ≠ 0 := by
  obtain ⟨c, _, hc⟩ := selectCols M
  let B := (M.submatrix id c).transpose
  have hb : B.rank = M.rank := Matrix.rank_transpose _ |>.trans hc
  obtain ⟨r, hr, _⟩ := selectCols B
  let e := finCongr hb.symm
  let r' := e.toEmbedding.trans r
  refine ⟨r', c, isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_row_iff_isUnit.mp ?_))⟩
  exact hr.comp e e.injective

private theorem hadamard {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    |A.det| ≤ ∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin d))‖ := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  let v := fun i ↦ (WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin d))
  let o := b.toBasis.orientation
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d) := ⟨by simp⟩
  have h := o.abs_volumeForm_apply_le v
  rw [o.volumeForm_robust' b, Module.Basis.det_apply] at h
  have he : b.toBasis.toMatrix v = A.transpose := by ext; rfl
  simpa [he] using h

private theorem rankLE {K L : Type*} [Field K] [Field L] {a b : ℕ}
    (M : Matrix (Fin a) (Fin b) K) (N : Matrix (Fin a) (Fin b) L)
    (h : ∀ d (r : Fin d ↪ Fin a) (c : Fin d ↪ Fin b),
      (M.submatrix r c).det ≠ 0 → (N.submatrix r c).det ≠ 0) : M.rank ≤ N.rank := by
  obtain ⟨r, c, hM⟩ := rankMinor M
  have hu := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (h _ r c hM))
  simpa [(N.submatrix r c).rank_of_isUnit hu] using N.rank_submatrix_le r c

/-- Short integer tuples retain their rational rank modulo a prime exceeding R^k. -/
theorem shortRank (X : Matrix (Fin k) (Fin m) ℤ) (R : ℝ) (hR : 1 ≤ R)
    (hx : ∀ i, ∑ j, (X i j : ℝ)^2 ≤ R^2) (hq : R^k < q) :
    (X.map (Int.castRingHom (ZMod q))).rank = (X.map (Int.castRingHom ℚ)).rank := by
  classical
  have minor (d : ℕ) (r : Fin d ↪ Fin k) (c : Fin d ↪ Fin m) :
      (((X.submatrix r c).det : ℤ) : ZMod q) = 0 ↔ (X.submatrix r c).det = 0 := by
    let Y := X.submatrix r c
    let A := Y.map (Int.castRingHom ℝ)
    have hb (i : Fin d) : ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin d))‖ ≤ R := by
      apply (sq_le_sq₀ (norm_nonneg _) (by linarith)).mp
      rw [EuclideanSpace.real_norm_sq_eq]
      apply le_trans _ (hx (r i))
      change ∑ j, (X (r i) (c j) : ℝ)^2 ≤ _
      rw [← Finset.sum_map (f := fun j ↦ (X (r i) j : ℝ)^2) Finset.univ c]
      exact Finset.sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _
    have hd : d ≤ k := by simpa using Fintype.card_le_of_embedding r
    have hdet : |(Y.det : ℝ)| < q := calc
      _ = |A.det| := congrArg abs ((Int.castRingHom ℝ).map_det Y)
      _ ≤ _ := hadamard A
      _ ≤ ∏ _ : Fin d, R := Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ hb i)
      _ = R^d := by simp
      _ ≤ R^k := pow_le_pow_right₀ hR hd
      _ < q := hq
    change (Y.det : ZMod q) = 0 ↔ Y.det = 0
    refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
    have hv := (ZMod.intCast_zmod_eq_zero_iff_dvd Y.det q).mp h
    by_contra hn
    have hh := Int.le_of_dvd (abs_pos.mpr hn) ((dvd_abs _ _).mpr hv)
    exact (not_le_of_gt hdet) (by exact_mod_cast hh)
  have eqv (d : ℕ) (r : Fin d ↪ Fin k) (c : Fin d ↪ Fin m) :
      (((X.map (Int.castRingHom (ZMod q))).submatrix r c).det = 0) ↔
      (((X.map (Int.castRingHom ℚ)).submatrix r c).det = 0) := by
    change ((Int.castRingHom (ZMod q)).mapMatrix (X.submatrix r c)).det = 0 ↔
      ((Int.castRingHom ℚ).mapMatrix (X.submatrix r c)).det = 0
    rw [← RingHom.map_det, ← RingHom.map_det]
    simpa using minor d r c
  exact le_antisymm (rankLE _ _ fun d r c ↦ (eqv d r c).not.mp)
    (rankLE _ _ fun d r c ↦ (eqv d r c).not.mpr)

#print axioms shortRank

/-- Finite shell count for the kernel lattice of A. -/
def shellCount {n : ℕ} (A : Fin n → Fin m → ZMod q) (s : Finset (Fin m → ℤ)) : ℝ≥0 :=
  ∑ x ∈ s, if ∀ i, (fun j ↦ (x j : ZMod q)) ⬝ᵥ A i = 0 then 1 else 0

private def oneRow (x : Fin m → ℤ) : Matrix (Fin 1) (Fin m) ℤ := fun _ ↦ x

/-- First moment on any finite set of nonzero vectors inside the radius bound. -/
theorem firstMoment (n : ℕ) (s : Finset (Fin m → ℤ)) (R : ℝ)
    (hR : 1 ≤ R) (hq : R < q) (hs : ∀ x ∈ s, x ≠ 0 ∧ ∑ j, (x j : ℝ)^2 ≤ R^2) :
    (∑ A, shellCount (q := q) (n := n) A s) / (q : ℝ≥0)^(m*n) = s.card / (q : ℝ≥0)^n := by
  classical
  let X := fun x ↦ (oneRow (m := m) x).map (Int.castRingHom (ZMod q))
  have hh := meanValue n s X (fun _ ↦ 1)
  have hr (x) (hx : x ∈ s) : (X x).rank = 1 := by
    rw [show (X x).rank = _ from shortRank (oneRow x) R hR (fun _ ↦ (hs x hx).2) (by simpa)]
    rw [Matrix.rank_eq_finrank_span_row]
    change Module.finrank ℚ (Submodule.span ℚ (Set.range (fun _ : Fin 1 ↦
      (fun j ↦ (x j : ℚ))))) = 1
    rw [Set.range_const]
    apply finrank_span_singleton
    intro he
    apply (hs x hx).1
    ext j
    have hj : (x j : ℚ) = 0 := congrFun he j
    change x j = 0
    exact_mod_cast hj
  have hh' := Finset.sum_congr (s₁ := s) rfl fun x hx ↦
    congrArg (fun t : ℕ ↦ (1 : ℝ≥0) / (q : ℝ≥0)^(t*n)) (hr x hx)
  rw [hh'] at hh
  simpa [shellCount, X, oneRow, funext_iff, Matrix.mulVec, Matrix.map_apply,
    Fin.forall_fin_one, nsmul_eq_mul, div_eq_mul_inv] using hh

/-- Two rows indexed by the two members of an ordered pair. -/
def pairRows (p : (Fin m → ℤ) × (Fin m → ℤ)) : Matrix (Fin 2) (Fin m) ℤ :=
  ![p.1, p.2]

/-- Second raw moment, with the exact rational rank of each ordered pair. -/
theorem secondMoment (n : ℕ) (s : Finset (Fin m → ℤ)) (R : ℝ)
    (hR : 1 ≤ R) (hq : R^2 < q) (hs : ∀ x ∈ s, ∑ j, (x j : ℝ)^2 ≤ R^2) :
    (∑ A, (shellCount (q := q) (n := n) A s)^2) / (q : ℝ≥0)^(m*n) =
      ∑ p ∈ s ×ˢ s, 1 / (q : ℝ≥0)^(((pairRows p).map (Int.castRingHom ℚ)).rank*n) := by
  classical
  let X := fun p ↦ (pairRows (m := m) p).map (Int.castRingHom (ZMod q))
  have hh := meanValue n (s ×ˢ s) X (fun _ ↦ 1)
  rw [← Finset.sum_congr rfl (fun p hp ↦ congrArg (fun t : ℕ ↦ (1 : ℝ≥0) / (q : ℝ≥0)^(t*n))
    (shortRank (pairRows p) R hR (by
      intro i
      fin_cases i
      · exact hs _ (Finset.mem_product.mp hp).1
      · exact hs _ (Finset.mem_product.mp hp).2) hq)), ← hh]
  congr 1
  apply Finset.sum_congr rfl
  intro A _
  simp only [shellCount, sq, Finset.sum_mul, Finset.mul_sum, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp [X, pairRows, Matrix.mulVec, funext_iff, Fin.forall_fin_succ, forall_and,
    Matrix.map, Matrix.of_apply]
  split_ifs <;> simp_all

#print axioms firstMoment
#print axioms secondMoment

/-- Variance in the raw-moment convention E[C²] − E[C]², as a sum over rational ranks. -/
theorem variance (n : ℕ) (s : Finset (Fin m → ℤ)) (R : ℝ)
    (hR : 1 ≤ R) (hq : R^2 < q) (hs : ∀ x ∈ s, x ≠ 0 ∧ ∑ j, (x j : ℝ)^2 ≤ R^2) :
    (∑ A, (shellCount (q := q) (n := n) A s)^2) / (q : ℝ≥0)^(m*n) -
      ((∑ A, shellCount (q := q) (n := n) A s) / (q : ℝ≥0)^(m*n))^2 =
      (∑ p ∈ s ×ˢ s, 1 / (q : ℝ≥0)^(((pairRows p).map (Int.castRingHom ℚ)).rank*n)) -
        (s.card / (q : ℝ≥0)^n)^2 := by
  rw [secondMoment n s R hR hq (fun x hx ↦ (hs x hx).2), firstMoment n s R hR (by nlinarith) hs]

#print axioms variance

end SigabaNeo.QAry
