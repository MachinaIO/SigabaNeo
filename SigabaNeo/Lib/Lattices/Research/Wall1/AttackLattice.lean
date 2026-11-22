module

public import SigabaNeo.Lib.Lattices.Research.Wall1.DecoupledDecoder
import all SigabaNeo.Lib.Lattices.Research.Wall1.DecoupledDecoder
import all SigabaNeo.Lib.Lattices.Research.Wall1.RestartLift
import all SigabaNeo.Lib.Lattices.Research.Wall1.RestartReduction
import all SigabaNeo.Lib.Lattices.Research.Wall1.PlantBlindRestart
import Mathlib.Tactic

/-! # The attack lattice from `(A, b)` and the canonical reducer output (PROOF_GAP Wall 1, Part 47)

`DecoupledDecoder.restartDecoder_lwe_choose` took the decoupled lattice `L = L₀ ⊕ ℤu` literally
and assumed, on accepted rows, the plant-free structure `Compatible L₀ pre J F`. This file removes
both modelling steps.

1. **The LWE embedding identity** (`attackLattice_eq`, `attackLattice_plantVec`). For a block with
   design rows `A` (`r × n` over `ZMod q`) and coordinate labelling `σ : Fin N ≃ secret ⊕ error`,
   the attack lattice built from `(A, b)` is
   `L(A, b) = {z ∈ ℤ^{N+1} : z_err + A z_sec ≡ z_height · b (mod q)} ⊆ ℝ^{N+1}`
   (`attackLattice`). Its height-zero sublattice is, for every `b`, the plant-free q-ary lattice
   `L₀ = {(z, 0) : z_err + A z_sec ≡ 0}` (`nullLattice₀`, `mem_nullLattice₀_iff`). If
   `b = e + A s` for the plant `X = (s, e)`, then `L(A, b) = L₀ ⊕ ℤ (X, 1)`.
2. **Canonical prefix and final block** (`prefixOf`, `finalOf`). From an ordered `ℤ`-basis `B`
   of the null lattice of length `J + d = N`: the prefix is `B` at height zero with Mathlib's
   Gram–Schmidt (first `J` vectors used); `Q` is the matrix of the orthogonal projection onto
   `W_hᗮ` (`W_h` the span of the first `J` vectors); `V` is spanned by the projections of the
   remaining `d` vectors, which form the final-block basis. `Compatible` holds automatically
   (`compatible_ofBasis`); in fact `L₀ ∩ W = K` (`nullLattice₀_inf_prefixSpan`). The only
   arithmetic input is full rank, from `q ℤ^N ⊆ L₀` (`single_mem_span`,
   `basisVec_linearIndependent`), which needs `q ≠ 0`.
3. **End-to-end** (`restartAttack_lwe`). The reducer is any map from block rows (and coins) to
   an ordered basis of `L₀` (`Reducer`); the decoder runs on `L(A, b)` with `b` computed from the
   true `(s, e)`. Then `Pr[secret read off ≠ s] ≤ ∏ δᵢ + ε + ℓ`, with no compatibility hypothesis.
   The residual numerical hypotheses are `J i + d i = N i` (basis length equals rank) and
   `NeZero q`. -/

public section

namespace SigabaNeo.Wall1.AttackLattice

open SigabaNeo.Wall1 SigabaNeo.Wall1.MultiBlock SigabaNeo.Wall1.PlantBlindRestart
open SigabaNeo.Wall1.RestartReduction SigabaNeo.Wall1.RestartLift
open SigabaNeo.Wall1.DecoupledDecoder
open SampleDeletion CBDTail Classical InnerProductSpace

/-! ## 1. The q-ary lattices of a block -/

section Lattice

variable {N n r q : ℕ}

/-- The coordinate embedding `ℤ^M → ℝ^M`. -/
@[expose] noncomputable def intEmb (M : ℕ) : (Fin M → ℤ) →+ EuclideanSpace ℝ (Fin M) where
  toFun z := WithLp.toLp 2 fun c ↦ (z c : ℝ)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

@[simp] theorem intEmb_apply (M : ℕ) (z : Fin M → ℤ) (c : Fin M) : intEmb M z c = z c := rfl

/-- The residue of a horizontal integer vector against the block design `A` (rows `a`), with
coordinates labelled by `σ : Fin N ≃ secret ⊕ error`: `z_{err a} + ⟨A_a, z_sec⟩ mod q`. -/
@[expose] def residue (A : Fin r → Fin n → ZMod q) (σ : Fin N ≃ Fin n ⊕ Fin r) :
    (Fin N → ℤ) →+ (Fin r → ZMod q) where
  toFun z a := (z (σ.symm (.inr a)) : ZMod q) + ∑ j, A a j * (z (σ.symm (.inl j)) : ZMod q)
  map_zero' := by ext; simp
  map_add' x y := by
    ext a
    simp only [Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]
    ring

@[simp] theorem residue_apply (A : Fin r → Fin n → ZMod q) (σ : Fin N ≃ Fin n ⊕ Fin r)
    (z : Fin N → ℤ) (a : Fin r) :
    residue A σ z a =
      (z (σ.symm (.inr a)) : ZMod q) + ∑ j, A a j * (z (σ.symm (.inl j)) : ZMod q) := rfl

/-- The residue of an `(N+1)`-dimensional integer vector against the observed `b`:
`z_{err a} + ⟨A_a, z_sec⟩ − z_height · b_a mod q`. -/
@[expose] def attackResidue (A : Fin r → Fin n → ZMod q) (σ : Fin N ≃ Fin n ⊕ Fin r)
    (bv : Fin r → ZMod q) : (Fin (N + 1) → ℤ) →+ (Fin r → ZMod q) where
  toFun z a := (z (σ.symm (.inr a)).castSucc : ZMod q) +
    ∑ j, A a j * (z (σ.symm (.inl j)).castSucc : ZMod q) - (z (Fin.last N) : ZMod q) * bv a
  map_zero' := by ext; simp
  map_add' x y := by
    ext a
    simp only [Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib, add_mul]
    ring

@[simp] theorem attackResidue_apply (A : Fin r → Fin n → ZMod q) (σ : Fin N ≃ Fin n ⊕ Fin r)
    (bv : Fin r → ZMod q) (z : Fin (N + 1) → ℤ) (a : Fin r) :
    attackResidue A σ bv z a = (z (σ.symm (.inr a)).castSucc : ZMod q) +
      ∑ j, A a j * (z (σ.symm (.inl j)).castSucc : ZMod q) - (z (Fin.last N) : ZMod q) * bv a :=
  rfl

/-- The horizontal embedding `a ↦ (a, 0)` of `ℝ^N` into `ℝ^{N+1}`. -/
@[expose] noncomputable def horiz (N : ℕ) : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] Amb N where
  toFun a := snocE a 0
  map_add' a a' := by rw [snocE_add, add_zero]
  map_smul' c a := by
    ext i
    refine Fin.lastCases ?_ (fun c ↦ ?_) i <;> simp [snocE]

theorem horiz_apply (a : EuclideanSpace ℝ (Fin N)) : horiz N a = snocE a 0 := rfl

theorem horiz_injective : Function.Injective (horiz N) := by
  intro a a' h
  ext c
  have := congrArg (fun v : Amb N ↦ v c.castSucc) h
  simpa [horiz_apply, snocE_castSucc] using this

/-- The plant-free q-ary lattice of the block in `ℝ^N` (Part 47's punctured design):
`{z ∈ ℤ^N : z_err + A z_sec ≡ 0 mod q}`. It depends on the design rows only. -/
@[expose] noncomputable def nullLattice (A : Fin r → Fin n → ZMod q) (σ : Fin N ≃ Fin n ⊕ Fin r) :
    AddSubgroup (EuclideanSpace ℝ (Fin N)) :=
  (residue A σ).ker.map (intEmb N)

/-- `L₀`: the null lattice placed at height `0` in `ℝ^{N+1}`. -/
@[expose] noncomputable def nullLattice₀ (A : Fin r → Fin n → ZMod q)
    (σ : Fin N ≃ Fin n ⊕ Fin r) : AddSubgroup (Amb N) :=
  (nullLattice A σ).map (horiz N).toAddMonoidHom

/-- **The attack lattice built from `(A, b)`**:
`L = {z ∈ ℤ^{N+1} : z_err + A z_sec ≡ z_height · b mod q}`. -/
@[expose] noncomputable def attackLattice (A : Fin r → Fin n → ZMod q) (σ : Fin N ≃ Fin n ⊕ Fin r)
    (bv : Fin r → ZMod q) : AddSubgroup (Amb N) :=
  (attackResidue A σ bv).ker.map (intEmb (N + 1))

/-- **`L₀` is the height-zero sublattice of the attack lattice, for every `b`.** -/
theorem mem_nullLattice₀_iff (A : Fin r → Fin n → ZMod q) (σ : Fin N ≃ Fin n ⊕ Fin r)
    (bv : Fin r → ZMod q) (v : Amb N) :
    v ∈ nullLattice₀ A σ ↔ v ∈ attackLattice A σ bv ∧ v (Fin.last N) = 0 := by
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨⟨Fin.snoc (α := fun _ ↦ ℤ) z 0, ?_, ?_⟩, ?_⟩
    · simp only [SetLike.mem_coe, AddMonoidHom.mem_ker] at hz ⊢
      ext a
      have := congrFun hz a
      simpa using this
    · ext i
      refine Fin.lastCases ?_ (fun c ↦ ?_) i <;> simp [horiz_apply, snocE]
    · simp [horiz_apply, snocE]
  · rintro ⟨⟨z, hz, rfl⟩, h0⟩
    have hz0 : z (Fin.last N) = 0 := by
      have h := h0
      simp only [intEmb_apply] at h
      exact_mod_cast h
    refine ⟨intEmb N fun c ↦ z c.castSucc, ⟨fun c ↦ z c.castSucc, ?_, rfl⟩, ?_⟩
    · simp only [SetLike.mem_coe, AddMonoidHom.mem_ker] at hz ⊢
      ext a
      have := congrFun hz a
      simpa [hz0] using this
    · ext i
      refine Fin.lastCases ?_ (fun c ↦ ?_) i <;> simp [horiz_apply, snocE, hz0]

/-- **The LWE embedding identity.** If `b = e + A s` for the integer plant `X = (s, e)` (in the
coordinates `σ`), the attack lattice built from `(A, b)` is `L₀ ⊕ ℤu` with `u = (X, 1)`. -/
theorem attackLattice_eq (A : Fin r → Fin n → ZMod q) (σ : Fin N ≃ Fin n ⊕ Fin r)
    (X : Fin N → ℤ) :
    attackLattice A σ (residue A σ X) =
      decoupled (nullLattice₀ A σ) (snocE (intEmb N X) 1) := by
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    set t := z (Fin.last N)
    set z' : Fin N → ℤ := fun c ↦ z c.castSucc - t * X c
    have hz' : z' ∈ (residue A σ).ker := by
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker] at hz ⊢
      ext a
      have := congrFun hz a
      simp only [attackResidue_apply, residue_apply, Pi.zero_apply] at this ⊢
      simp only [z', Int.cast_sub, Int.cast_mul, mul_sub, Finset.sum_sub_distrib]
      rw [show ∑ j, A a j * ((t : ZMod q) * (X (σ.symm (.inl j)) : ZMod q)) =
          (t : ZMod q) * ∑ j, A a j * (X (σ.symm (.inl j)) : ZMod q) by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring]
      linear_combination this
    refine AddSubgroup.mem_sup.2 ⟨horiz N (intEmb N z'), ⟨intEmb N z', ⟨z', hz', rfl⟩, rfl⟩,
      t • snocE (intEmb N X) 1, AddSubgroup.mem_zmultiples_iff.2 ⟨t, rfl⟩, ?_⟩
    ext i
    refine Fin.lastCases ?_ (fun c ↦ ?_) i
    · simp [horiz_apply, snocE, t]
    · simp [horiz_apply, snocE, z', zsmul_eq_mul]
  · intro hv
    obtain ⟨h, ⟨y, ⟨z', hz', rfl⟩, rfl⟩, w, hw, rfl⟩ := AddSubgroup.mem_sup.1 hv
    obtain ⟨t, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hw
    refine ⟨Fin.snoc (α := fun _ ↦ ℤ) (z' + t • X) t, ?_, ?_⟩
    · simp only [SetLike.mem_coe, AddMonoidHom.mem_ker] at hz' ⊢
      ext a
      have := congrFun hz' a
      simp only [attackResidue_apply, residue_apply, Pi.zero_apply] at this ⊢
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Int.cast_add, Int.cast_mul, mul_add, Finset.sum_add_distrib]
      rw [show ∑ j, A a j * ((t : ZMod q) * (X (σ.symm (.inl j)) : ZMod q)) =
          (t : ZMod q) * ∑ j, A a j * (X (σ.symm (.inl j)) : ZMod q) by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring]
      linear_combination this
    · ext i
      refine Fin.lastCases ?_ (fun c ↦ ?_) i
      · simp [horiz_apply, snocE]
      · simp [horiz_apply, snocE, zsmul_eq_mul]

/-- The embedding identity for a CBD(3) plant `x`: `L(A, e + A s) = L₀ ⊕ ℤ (x, 1)`. -/
theorem attackLattice_plantVec (A : Fin r → Fin n → ZMod q) (σ : Fin N ≃ Fin n ⊕ Fin r)
    (x : Fin N → Digit 3) :
    attackLattice A σ (residue A σ fun c ↦ centered (x c)) =
      decoupled (nullLattice₀ A σ) (plantVec x) := by
  rw [attackLattice_eq, plantVec_eq]
  rfl

/-- The plant lies in the attack lattice. -/
theorem plantVec_mem_attackLattice (A : Fin r → Fin n → ZMod q) (σ : Fin N ≃ Fin n ⊕ Fin r)
    (x : Fin N → Digit 3) :
    plantVec x ∈ attackLattice A σ (residue A σ fun c ↦ centered (x c)) := by
  rw [attackLattice_plantVec]
  exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)

/-- The null lattice contains `q ℤ^N`; in particular it has full rank. -/
theorem single_mem_span [NeZero q] (A : Fin r → Fin n → ZMod q) (σ : Fin N ≃ Fin n ⊕ Fin r)
    (c : Fin N) :
    ∃ y ∈ nullLattice A σ, EuclideanSpace.single c (1 : ℝ) = (1 / (q : ℝ)) • y := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  set z : Fin N → ℤ := fun c' ↦ if c' = c then (q : ℤ) else 0
  refine ⟨intEmb N z, ⟨z, ?_, rfl⟩, ?_⟩
  · simp only [SetLike.mem_coe, AddMonoidHom.mem_ker]
    have h0 (c' : Fin N) : ((z c' : ℤ) : ZMod q) = 0 := by
      by_cases h : c' = c
      · subst h; simp [z]
      · simp [z, h]
    ext a
    simp [h0]
  · ext c'
    by_cases h : c' = c
    · subst h; simp [z, hq]
    · simp [z, h]

end Lattice

/-! ## 2. The canonical prefix and final block of an ordered basis -/

section Canonical

variable {N J d : ℕ}

local notation "E" N => EuclideanSpace ℝ (Fin N)

/-- Prefix vectors `β₀, …, β_{J-1}` of an ordered family. -/
@[expose] def preVec (β : Fin (J + d) → E N) (m : Fin J) : E N := β (Fin.castAdd d m)

/-- Remaining vectors `β_J, …, β_{J+d-1}`. -/
@[expose] def remVec (β : Fin (J + d) → E N) (j : Fin d) : E N := β (Fin.natAdd J j)

/-- The horizontal prefix span `W_h`. -/
@[expose] noncomputable def preSpan (β : Fin (J + d) → E N) : Submodule ℝ (E N) :=
  Submodule.span ℝ (Set.range (preVec β))

/-- The orthogonal projection of `ℝ^N` onto `W_hᗮ`. -/
@[expose] noncomputable def hproj (β : Fin (J + d) → E N) : (E N) →L[ℝ] E N :=
  (preSpan β)ᗮ.starProjection

/-- `Q`: the matrix of `hproj` in the standard basis. -/
@[expose] noncomputable def projMatrix (β : Fin (J + d) → E N) : Matrix (Fin N) (Fin N) ℝ :=
  LinearMap.toMatrix (PiLp.basisFun 2 ℝ (Fin N)) (PiLp.basisFun 2 ℝ (Fin N))
    (hproj β).toLinearMap

theorem projMatrix_mulVec (β : Fin (J + d) → E N) (a : E N) :
    (projMatrix β).mulVec (WithLp.ofLp a) = WithLp.ofLp (hproj β a) := by
  have h := LinearMap.toMatrix_mulVec_repr (PiLp.basisFun 2 ℝ (Fin N))
    (PiLp.basisFun 2 ℝ (Fin N)) (hproj β).toLinearMap a
  have e (x : E N) : ⇑((PiLp.basisFun 2 ℝ (Fin N)).repr x) = WithLp.ofLp x := by
    funext i; simp
  rw [e, e] at h
  exact h

theorem toLp_projMatrix_mulVec (β : Fin (J + d) → E N) (a : E N) :
    WithLp.toLp 2 ((projMatrix β).mulVec (WithLp.ofLp a)) = hproj β a := by
  rw [projMatrix_mulVec]

theorem hproj_mem (β : Fin (J + d) → E N) (a : E N) : hproj β a ∈ (preSpan β)ᗮ :=
  Submodule.starProjection_apply_mem _ a

theorem hproj_idem (β : Fin (J + d) → E N) (a : E N) : hproj β (hproj β a) = hproj β a :=
  Submodule.starProjection_eq_self_iff.2 (hproj_mem β a)

theorem hproj_eq_zero (β : Fin (J + d) → E N) {a : E N} (ha : a ∈ preSpan β) :
    hproj β a = 0 := by
  rw [hproj, Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]
  exact ha

theorem projMatrix_symm (β : Fin (J + d) → E N) : (projMatrix β).transpose = projMatrix β := by
  ext i j
  have key (i j : Fin N) : projMatrix β i j =
      inner ℝ (EuclideanSpace.single i (1 : ℝ)) (hproj β (EuclideanSpace.single j 1)) := by
    rw [EuclideanSpace.inner_single_left]
    simp [projMatrix, LinearMap.toMatrix_apply]
  rw [Matrix.transpose_apply, key, key, hproj, ← Submodule.inner_starProjection_left_eq_right,
    real_inner_comm]

theorem projMatrix_idem (β : Fin (J + d) → E N) : projMatrix β * projMatrix β = projMatrix β := by
  rw [projMatrix, ← LinearMap.toMatrix_mul]
  congr 1
  refine LinearMap.ext fun x ↦ ?_
  simp only [Module.End.mul_apply, ContinuousLinearMap.coe_coe]
  exact hproj_idem β x

theorem disjoint_pre_rem {β : Fin (J + d) → E N} (hli : LinearIndependent ℝ β) :
    Disjoint (preSpan β) (Submodule.span ℝ (Set.range (remVec β))) := by
  have h := hli.disjoint_span_image (s := Set.range (Fin.castAdd d))
    (t := Set.range (Fin.natAdd J)) (by
      rw [Set.disjoint_left]
      rintro _ ⟨m, rfl⟩ ⟨j, hj⟩
      have := congrArg Fin.val hj
      simp at this
      omega)
  rw [← Set.range_comp, ← Set.range_comp] at h
  exact h

theorem finrank_preSpan {β : Fin (J + d) → E N} (hli : LinearIndependent ℝ β) :
    Module.finrank ℝ (preSpan β) = J := by
  change Module.finrank ℝ (Submodule.span ℝ (Set.range (β ∘ Fin.castAdd d))) = J
  rw [finrank_span_eq_card (hli.comp _ (Fin.castAdd_injective J d)), Fintype.card_fin]

theorem finrank_perp {β : Fin (J + d) → E N} (hJ : J + d = N) (hli : LinearIndependent ℝ β) :
    Module.finrank ℝ (preSpan β)ᗮ = d := by
  have h := Submodule.finrank_add_finrank_orthogonal (preSpan β)
  rw [finrank_preSpan hli, finrank_euclideanSpace_fin] at h
  omega

theorem projMatrix_trace {β : Fin (J + d) → E N} (hJ : J + d = N) (hli : LinearIndependent ℝ β) :
    (projMatrix β).trace = d := by
  have hp : LinearMap.IsProj (preSpan β)ᗮ (hproj β).toLinearMap :=
    ⟨fun x ↦ hproj_mem β x, fun x hx ↦ Submodule.starProjection_eq_self_iff.2 hx⟩
  rw [projMatrix, ← LinearMap.trace_eq_matrix_trace, hp.trace, finrank_perp hJ hli]

/-- The projected remaining vectors `P β_J, …, P β_{J+d-1}`. -/
@[expose] noncomputable def projRem (β : Fin (J + d) → E N) (j : Fin d) : E N :=
  hproj β (remVec β j)

theorem projRem_linearIndependent {β : Fin (J + d) → E N} (hli : LinearIndependent ℝ β) :
    LinearIndependent ℝ (projRem β) := by
  have hrem : LinearIndependent ℝ (remVec β) := hli.comp _ (Fin.natAdd_injective _ _)
  refine hrem.map (f := (hproj β).toLinearMap) ?_
  rw [Submodule.disjoint_def]
  intro x hx hk
  have hW : x ∈ preSpan β := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hproj,
      Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal] at hk
    exact hk
  exact Submodule.disjoint_def.1 (disjoint_pre_rem hli) x hW hx

/-- `V`: the real span of the projected remaining vectors. -/
@[expose] noncomputable def finalSpan (β : Fin (J + d) → E N) : Submodule ℝ (E N) :=
  Submodule.span ℝ (Set.range (projRem β))

theorem finalSpan_le (β : Fin (J + d) → E N) : finalSpan β ≤ (preSpan β)ᗮ := by
  rw [finalSpan, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact hproj_mem β _

/-- **The canonical final block** of an ordered real-independent family `β` of length `J + d = N`:
`Q` is the matrix of the projection onto `W_hᗮ`, `V` the span of the projected remaining vectors,
and the basis is those projected vectors. -/
@[expose] noncomputable def canonicalFinal (hJ : J + d = N) (β : Fin (J + d) → E N)
    (hli : LinearIndependent ℝ β) : FinalBlock N d where
  Q := projMatrix β
  symmetric := projMatrix_symm β
  idempotent := projMatrix_idem β
  trace_eq := projMatrix_trace hJ hli
  V := finalSpan β
  fixed h := by
    rw [projMatrix_mulVec]
    exact congrArg WithLp.ofLp
      (Submodule.starProjection_eq_self_iff.2 (finalSpan_le β h.2))
  basis := Module.Basis.span (projRem_linearIndependent hli)

/-- The full ordered basis placed at height `0` (indices `≥ J + d` padded with `0`). -/
@[expose] noncomputable def heightZeroFamily (β : Fin (J + d) → E N) (m : ℕ) : Amb N :=
  if h : m < J + d then horiz N (β ⟨m, h⟩) else 0

theorem heightZeroFamily_horiz (β : Fin (J + d) → E N) (m : ℕ) :
    heightZeroFamily β m (Fin.last N) = 0 := by
  unfold heightZeroFamily
  split_ifs
  · simp [horiz_apply, snocE_last]
  · simp

/-- **The canonical prefix data**: the ordered basis at height zero with Mathlib's Gram–Schmidt. -/
@[expose] noncomputable def canonicalPrefix (β : Fin (J + d) → E N) : PrefixData N :=
  PrefixData.ofGramSchmidt (heightZeroFamily β) (heightZeroFamily_horiz β)

theorem canonicalPrefix_b (β : Fin (J + d) → E N) (m : Fin J) :
    (canonicalPrefix β).b m = horiz N (preVec β m) := by
  change heightZeroFamily β m = _
  rw [heightZeroFamily, dite_eq_left_of_eq_true (eq_true (by omega))]
  rfl

theorem prefixSpan_canonical (β : Fin (J + d) → E N) :
    prefixSpan (canonicalPrefix β).b J = (preSpan β).map (horiz N) := by
  rw [prefixSpan, preSpan, Submodule.map_span, ← Set.range_comp]
  congr 2
  funext m
  exact canonicalPrefix_b β m

theorem inner_snocE (a a' : E N) (t t' : ℝ) :
    inner ℝ (snocE a t) (snocE a' t') = inner ℝ a a' + t * t' := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_castSucc]
  simp [snocE]
  ring

/-- **`proj_snoc` for the canonical prefix**: `P (a, t) = (Q a, t)`. -/
theorem canonical_proj_snoc (β : Fin (J + d) → E N) (a : E N) (t : ℝ) :
    perpProj (canonicalPrefix β).b J (snocE a t) =
      snocE (WithLp.toLp 2 ((projMatrix β).mulVec (WithLp.ofLp a))) t := by
  rw [toLp_projMatrix_mulVec, perpProj]
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [Submodule.mem_orthogonal]
    intro u hu
    rw [prefixSpan_canonical] at hu
    obtain ⟨w, hw, rfl⟩ := hu
    rw [horiz_apply, inner_snocE, zero_mul, add_zero]
    exact Submodule.inner_right_of_mem_orthogonal hw (hproj_mem β a)
  · intro w hw
    have hsub : snocE a t - snocE (hproj β a) t = horiz N (a - hproj β a) := by
      ext i
      refine Fin.lastCases ?_ (fun c ↦ ?_) i <;> simp [horiz_apply, snocE]
    have hmem : horiz N (a - hproj β a) ∈ prefixSpan (canonicalPrefix β).b J := by
      rw [prefixSpan_canonical]
      refine ⟨a - hproj β a, ?_, rfl⟩
      have := Submodule.sub_starProjection_mem_orthogonal (K := (preSpan β)ᗮ) a
      rwa [Submodule.orthogonal_orthogonal] at this
    rw [hsub]
    exact Submodule.inner_right_of_mem_orthogonal hmem hw

end Canonical

/-! ## 3. Canonical compatibility for an ordered basis of the null lattice -/

section Compat

variable {N n r q J d : ℕ}

/-- The real vectors of an ordered `ℤ`-basis of the null lattice. -/
@[expose] noncomputable def basisVec {A : Fin r → Fin n → ZMod q} {σ : Fin N ≃ Fin n ⊕ Fin r}
    (B : Module.Basis (Fin (J + d)) ℤ (nullLattice A σ)) (t : Fin (J + d)) :
    EuclideanSpace ℝ (Fin N) :=
  (B t : EuclideanSpace ℝ (Fin N))

/-- Every vector of the null lattice is an integer combination of the basis, split into prefix
and remaining parts. -/
theorem basis_decomp {A : Fin r → Fin n → ZMod q} {σ : Fin N ≃ Fin n ⊕ Fin r}
    (B : Module.Basis (Fin (J + d)) ℤ (nullLattice A σ)) {y : EuclideanSpace ℝ (Fin N)}
    (hy : y ∈ nullLattice A σ) :
    ∃ c : Fin (J + d) → ℤ, y = (∑ m, c (Fin.castAdd d m) • preVec (basisVec B) m) +
      ∑ j, c (Fin.natAdd J j) • remVec (basisVec B) j := by
  refine ⟨B.repr ⟨y, hy⟩, ?_⟩
  have h := congrArg (nullLattice A σ).subtype.toIntLinearMap (B.sum_repr ⟨y, hy⟩)
  rw [map_sum] at h
  simp only [map_smul] at h
  refine (h.symm.trans ?_ : y = _)
  rw [Fin.sum_univ_add]
  rfl

/-- **Full rank**: an ordered `ℤ`-basis of the null lattice of length `J + d = N` is real-linearly
independent. -/
theorem basisVec_linearIndependent [NeZero q] {A : Fin r → Fin n → ZMod q}
    {σ : Fin N ≃ Fin n ⊕ Fin r} (hJ : J + d = N)
    (B : Module.Basis (Fin (J + d)) ℤ (nullLattice A σ)) :
    LinearIndependent ℝ (basisVec B) := by
  have hspan : ∀ y ∈ nullLattice A σ, y ∈ Submodule.span ℝ (Set.range (basisVec B)) := by
    intro y hy
    obtain ⟨c, rfl⟩ := basis_decomp B hy
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun m _ ↦ ?_)
      (Submodule.sum_mem _ fun j _ ↦ ?_)
    · exact zsmul_mem (Submodule.subset_span (Set.mem_range_self _)) _
    · exact zsmul_mem (Submodule.subset_span (Set.mem_range_self _)) _
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by
    rw [Fintype.card_fin, finrank_euclideanSpace_fin, hJ])
  rw [← (PiLp.basisFun 2 ℝ (Fin N)).span_eq, Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  obtain ⟨y, hy, he⟩ := single_mem_span A σ c
  rw [PiLp.basisFun_apply]
  change EuclideanSpace.single c (1 : ℝ) ∈ _
  rw [he]
  exact Submodule.smul_mem _ _ (hspan y hy)

/-- The canonical final block of an ordered basis of the null lattice. -/
@[expose] noncomputable def finalOf [NeZero q] {A : Fin r → Fin n → ZMod q}
    {σ : Fin N ≃ Fin n ⊕ Fin r} (hJ : J + d = N)
    (B : Module.Basis (Fin (J + d)) ℤ (nullLattice A σ)) : FinalBlock N d :=
  canonicalFinal hJ (basisVec B) (basisVec_linearIndependent hJ B)

/-- The canonical prefix of an ordered basis of the null lattice. -/
@[expose] noncomputable def prefixOf {A : Fin r → Fin n → ZMod q} {σ : Fin N ≃ Fin n ⊕ Fin r}
    (B : Module.Basis (Fin (J + d)) ℤ (nullLattice A σ)) : PrefixData N :=
  canonicalPrefix (basisVec B)

/-- **`Compatible` holds automatically** for the canonical prefix and final block of any ordered
`ℤ`-basis of the null lattice (`J + d = N`). -/
theorem compatible_ofBasis [NeZero q] {A : Fin r → Fin n → ZMod q} {σ : Fin N ≃ Fin n ⊕ Fin r}
    (hJ : J + d = N) (B : Module.Basis (Fin (J + d)) ℤ (nullLattice A σ)) :
    Compatible (nullLattice₀ A σ) (prefixOf B) J (finalOf hJ B) := by
  have hli := basisVec_linearIndependent hJ B
  set β := basisVec B
  refine ⟨?_, fun a t ↦ canonical_proj_snoc β a t, ?_⟩
  · -- primitive
    rintro _ ⟨y, hy, rfl⟩ hW
    change horiz N y ∈ _ at hW
    change horiz N y ∈ _
    rw [prefixOf, prefixSpan_canonical] at hW
    obtain ⟨w, hw, hwy⟩ := hW
    rw [horiz_injective hwy] at hw
    obtain ⟨c, hc⟩ := basis_decomp B hy
    set p := ∑ m, c (Fin.castAdd d m) • preVec β m
    set s := ∑ j, c (Fin.natAdd J j) • remVec β j
    have hp : p ∈ preSpan β :=
      Submodule.sum_mem _ fun m _ ↦ zsmul_mem (Submodule.subset_span (Set.mem_range_self m)) _
    have hs : s ∈ Submodule.span ℝ (Set.range (remVec β)) :=
      Submodule.sum_mem _ fun j _ ↦ zsmul_mem (Submodule.subset_span (Set.mem_range_self j)) _
    have hsW : s ∈ preSpan β := by
      have : s = y - p := by rw [hc]; abel
      rw [this]; exact Submodule.sub_mem _ hw hp
    have hs0 : s = 0 := Submodule.disjoint_def.1 (disjoint_pre_rem hli) s hsW hs
    rw [hc, hs0, add_zero, map_sum]
    refine AddSubgroup.sum_mem _ fun m _ ↦ ?_
    rw [map_zsmul, prefixOf, ← canonicalPrefix_b]
    exact AddSubgroup.zsmul_mem _ (Submodule.subset_span (Set.mem_range_self m)) _
  · -- proj_null
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, hc⟩ := basis_decomp B hy
    let V := finalSpan β
    let bas : Module.Basis (Fin d) ℝ V := Module.Basis.span (projRem_linearIndependent hli)
    refine ⟨V.subtype.toAddMonoidHom (∑ j, c (Fin.natAdd J j) • bas j),
      ⟨_, Submodule.mem_toAddSubgroup _ |>.2 (Submodule.sum_mem _ fun j _ ↦
        zsmul_mem (Submodule.subset_span (Set.mem_range_self j)) _), rfl⟩, ?_⟩
    change perpProj _ J (snocE y 0) = _
    rw [prefixOf, canonical_proj_snoc, toLp_projMatrix_mulVec, hc, map_add, map_sum, map_sum]
    congr 1
    rw [Finset.sum_eq_zero (fun m _ ↦ by
      rw [map_zsmul, hproj_eq_zero β (Submodule.subset_span (Set.mem_range_self m)), smul_zero]), zero_add,
      map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_zsmul, map_zsmul]
    congr 1
    simp only [bas, LinearMap.toAddMonoidHom_coe, Submodule.subtype_apply]
    exact (congrArg Subtype.val (Module.Basis.span_apply (projRem_linearIndependent hli) j)).symm

/-- **The prefix generates the primitive sublattice exactly**: `L₀ ∩ W = K` for the canonical
prefix of an ordered basis of the null lattice (so `fiber_eq_coset` applies). -/
theorem nullLattice₀_inf_prefixSpan [NeZero q] {A : Fin r → Fin n → ZMod q}
    {σ : Fin N ≃ Fin n ⊕ Fin r} (hJ : J + d = N)
    (B : Module.Basis (Fin (J + d)) ℤ (nullLattice A σ)) :
    nullLattice₀ A σ ⊓ (prefixSpan (prefixOf B).b J).toAddSubgroup =
      prefixLattice (prefixOf B).b J := by
  apply le_antisymm
  · rintro v ⟨h1, h2⟩
    exact (compatible_ofBasis hJ B).primitive v h1 h2
  · intro v hv
    have hle : Submodule.span ℤ (Set.range fun m : Fin J ↦ (prefixOf B).b m) ≤
        (nullLattice₀ A σ ⊓ (prefixSpan (prefixOf B).b J).toAddSubgroup).toIntSubmodule := by
      rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      refine ⟨?_, Submodule.subset_span ⟨m, rfl⟩⟩
      change (canonicalPrefix (basisVec B)).b m ∈ nullLattice₀ A σ
      rw [canonicalPrefix_b]
      exact ⟨_, (B (Fin.castAdd d m)).2, rfl⟩
    exact hle hv

end Compat


/-! ## 4. End-to-end theorem with the reducer as an ordered basis of `L₀` -/

section Restart

variable {Y ι : Type*} [Fintype Y] [Fintype ι] [DecidableEq ι] {k : ℕ}
  {r : Fin k → ℕ} {N d : Fin k → ℕ} {n q : ℕ}

/-- The design of a block: row `a` is the design row `row (z a)` of the `a`-th sample (a sample
`y : Y` may also carry per-row coins). -/
@[expose] def blockDesign (row : Y → Fin n → ZMod q) {r : ℕ} (z : Fin r → Y) :
    Fin r → Fin n → ZMod q :=
  fun a ↦ row (z a)

/-- The observed LWE vector of block `i`, computed from `(A, s, e)`: `b_a = e_{b i a} + ⟨A_a, s⟩`
(centered CBD(3) values, mod `q`). -/
@[expose] def observed (row : Y → Fin n → ZMod q) (σ : ∀ i, Fin (N i) ≃ Fin n ⊕ Fin (r i))
    (b : ∀ i, Fin (r i) → ι) (i : Fin k) (p : (Fin n → Digit 3) × (ι → Digit 3))
    (z : Fin (r i) → Y) : Fin (r i) → ZMod q :=
  residue (blockDesign row z) (σ i) fun c ↦ centered (lwePlant σ b i p c)

omit [Fintype Y] [Fintype ι] [DecidableEq ι] in
theorem observed_apply (row : Y → Fin n → ZMod q) (σ : ∀ i, Fin (N i) ≃ Fin n ⊕ Fin (r i))
    (b : ∀ i, Fin (r i) → ι) (i : Fin k) (p : (Fin n → Digit 3) × (ι → Digit 3))
    (z : Fin (r i) → Y) (a : Fin (r i)) :
    observed row σ b i p z a =
      (centered (p.2 (b i a)) : ZMod q) + ∑ j, row (z a) j * (centered (p.1 j) : ZMod q) := by
  simp [observed, blockDesign, lwePlant]

/-- **A plant-free reducer**: any map from the rows (and coins) of block `i` to an ordered
`ℤ`-basis of length `J i + d i` of the block's null lattice. -/
abbrev Reducer (row : Y → Fin n → ZMod q) (σ : ∀ i, Fin (N i) ≃ Fin n ⊕ Fin (r i))
    (J : Fin k → ℕ) (d : Fin k → ℕ) : Type _ :=
  ∀ i (z : Fin (r i) → Y), Module.Basis (Fin (J i + d i)) ℤ (nullLattice (blockDesign row z) (σ i))

/-- Canonical prefixes of the reducer output. -/
@[expose] noncomputable def prefixes {row : Y → Fin n → ZMod q}
    {σ : ∀ i, Fin (N i) ≃ Fin n ⊕ Fin (r i)} {J : Fin k → ℕ} (red : Reducer row σ J d) (i : Fin k)
    (z : Fin (r i) → Y) : PrefixData (N i) :=
  prefixOf (red i z)

/-- Canonical final blocks of the reducer output. -/
@[expose] noncomputable def finals [NeZero q] {row : Y → Fin n → ZMod q}
    {σ : ∀ i, Fin (N i) ≃ Fin n ⊕ Fin (r i)} {J : Fin k → ℕ} (hJ : ∀ i, J i + d i = N i)
    (red : Reducer row σ J d) (i : Fin k) (z : Fin (r i) → Y) : FinalBlock (N i) (d i) :=
  finalOf (hJ i) (red i z)

/-- The attack fails on block `i`: run the concrete decoder (choice SVP oracle on `P L`, orient,
choice lift, Babai on the canonical prefix) on the attack lattice **built from `(A, b)`**, and the
secret read off is not the true centered secret. -/
@[expose] def attackFail (row : Y → Fin n → ZMod q) (σ : ∀ i, Fin (N i) ≃ Fin n ⊕ Fin (r i))
    (b : ∀ i, Fin (r i) → ι) {J : Fin k → ℕ} (red : Reducer row σ J d) (i : Fin k)
    (p : (Fin n → Digit 3) × (ι → Digit 3)) (z : Fin (r i) → Y) : Prop :=
  readSecret σ i (decode chooseSVP chooseLift (prefixes red i z) (J i)
      (attackLattice (blockDesign row z) (σ i) (observed row σ b i p z))) ≠
    fun j ↦ (centered (p.1 j) : ℝ)

omit [Fintype Y] [Fintype ι] [DecidableEq ι] in
theorem attackFail_iff (row : Y → Fin n → ZMod q) (σ : ∀ i, Fin (N i) ≃ Fin n ⊕ Fin (r i))
    (b : ∀ i, Fin (r i) → ι) {J : Fin k → ℕ} (red : Reducer row σ J d) (i : Fin k)
    (p : (Fin n → Digit 3) × (ι → Digit 3)) (z : Fin (r i) → Y) :
    attackFail row σ b red i p z ↔
      secretFail (fun _ ↦ chooseSVP) (fun _ ↦ chooseLift)
        (fun i z ↦ nullLattice₀ (blockDesign row z) (σ i)) (prefixes red) J σ b i p z := by
  unfold attackFail secretFail blockOutput observed
  rw [attackLattice_plantVec]

/-- **End-to-end LWE theorem with a concrete attack lattice and an arbitrary plant-free reducer.**
`k` disjoint row blocks; on block `i` the attack lattice is built from the block design and the
observed `b = e + A s`, and the reducer is any map `red` from the block rows (and coins) to an
ordered `ℤ`-basis of the null lattice, of length `J i + d i = N i`. The prefix is its first `J i`
vectors; the final block is the canonical one. With the canonical choice oracles,
`Pr[secret read off ≠ s, or no block accepted] ≤ ∏ δᵢ + ε + ℓ`, where `ε ≥ reductionError` and
`ℓ ≥ Σ_{m<J i} 2 exp(−(gp i m)²/12)`. No compatibility hypothesis remains. -/
theorem restartAttack_lwe [NeZero q] {w : Y → ℚ} (hw : ∑ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y)
    (row : Y → Fin n → ZMod q) (σ : ∀ i, Fin (N i) ≃ Fin n ⊕ Fin (r i)) (J : Fin k → ℕ)
    (hJ : ∀ i, J i + d i = N i) (red : Reducer row σ J d) (gp : Fin k → ℕ → ℝ)
    (hgp : ∀ i m, 0 ≤ gp i m)
    {g L : Fin k → ℝ} (hg : ∀ i, 0 < g i) (hL : ∀ i, 0 ≤ L i)
    (gap : ∀ i, 0 < L i ^ 2 - 1 - (3/2) * (d i : ℝ))
    (b : ∀ i, Fin (r i) → ι) (hb : Function.Injective (fun q : (Σ i, Fin (r i)) ↦ b q.1 q.2))
    {ε ℓ : ℝ} (hε0 : 0 ≤ ε) (hε : ∀ i, reductionError (N i) (d i) (g i) (L i) ≤ ε)
    (hℓ : ∀ i, ∑ m ∈ Finset.range (J i), 2 * Real.exp (-gp i m ^ 2 / 12) ≤ ℓ) (hℓ0 : 0 ≤ ℓ) :
    (failProb w (plantWeight n cbdQ) (accept (finals hJ red) g L (prefixFloor (prefixes red) J gp))
        (attackFail row σ b red) b : ℝ) ≤
      (∏ i, (rejectProb w (accept (finals hJ red) g L (prefixFloor (prefixes red) J gp)) i : ℝ))
        + ε + ℓ := by
  have hρ0 (p : (Fin n → Digit 3) × (ι → Digit 3)) : 0 ≤ plantWeight n cbdQ p := by
    unfold plantWeight
    exact mul_nonneg (Finset.prod_nonneg fun j _ ↦ cbdQ_nonneg _)
      (Finset.prod_nonneg fun j _ ↦ cbdQ_nonneg _)
  refine le_trans ?_ (restartDecoder_lwe_choose hw hw0 σ
    (fun i z ↦ nullLattice₀ (blockDesign row z) (σ i)) (finals hJ red) (prefixes red) J gp hgp
    hg hL gap (fun i z _ ↦ compatible_ofBasis (hJ i) (red i z)) b hb hε0 hε hℓ hℓ0)
  exact_mod_cast failProb_mono hw0 hρ0 _ b fun i p z _ hf ↦
    (attackFail_iff row σ b red i p z).1 hf

end Restart

end SigabaNeo.Wall1.AttackLattice

#print axioms SigabaNeo.Wall1.AttackLattice.mem_nullLattice₀_iff
#print axioms SigabaNeo.Wall1.AttackLattice.attackLattice_eq
#print axioms SigabaNeo.Wall1.AttackLattice.attackLattice_plantVec
#print axioms SigabaNeo.Wall1.AttackLattice.plantVec_mem_attackLattice
#print axioms SigabaNeo.Wall1.AttackLattice.single_mem_span
#print axioms SigabaNeo.Wall1.AttackLattice.projMatrix_symm
#print axioms SigabaNeo.Wall1.AttackLattice.projMatrix_idem
#print axioms SigabaNeo.Wall1.AttackLattice.projMatrix_trace
#print axioms SigabaNeo.Wall1.AttackLattice.canonicalFinal
#print axioms SigabaNeo.Wall1.AttackLattice.canonical_proj_snoc
#print axioms SigabaNeo.Wall1.AttackLattice.basisVec_linearIndependent
#print axioms SigabaNeo.Wall1.AttackLattice.compatible_ofBasis
#print axioms SigabaNeo.Wall1.AttackLattice.nullLattice₀_inf_prefixSpan
#print axioms SigabaNeo.Wall1.AttackLattice.observed_apply
#print axioms SigabaNeo.Wall1.AttackLattice.attackFail_iff
#print axioms SigabaNeo.Wall1.AttackLattice.restartAttack_lwe
